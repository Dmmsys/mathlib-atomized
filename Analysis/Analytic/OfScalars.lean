/-
Copyright (c) 2024 Edward Watine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward Watine
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius

/-!
# Scalar series

This file contains API for analytic functions `∑ cᵢ • xⁱ` defined in terms of scalars
`c₀, c₁, c₂, …`.

## Main definitions / results:
* `FormalMultilinearSeries.ofScalars`: the formal power series `∑ cᵢ • xⁱ`.
* `FormalMultilinearSeries.ofScalarsSum`: the sum of such a power series, if it exists, and zero
  otherwise.
* `FormalMultilinearSeries.ofScalars_radius_eq_(zero/inv/top)_of_tendsto`:
  the ratio test for an analytic function defined in terms of a formal power series `∑ cᵢ • xⁱ`.
* `FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto_ENNReal`:
  the ratio test for an analytic function using `ENNReal` division for all values `ℝ≥0∞`.
-/

@[expose] public section

namespace FormalMultilinearSeries

section Field

open ContinuousMultilinearMap

variable {𝕜 : Type*} (E : Type*) [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E]
  [IsTopologicalRing E] {c : ℕ → 𝕜}

/-- Formal power series of `∑ cᵢ • xⁱ` for some scalar field `𝕜` and ring algebra `E` -/
/-
**FormalMultilinearSeries.ofScalars** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinear
Series`。
形式化陈述：ofScalars (c : Nat -> 𝕜) : FormalMultilinearSeries 𝕜 E E
参数：c : Nat -> 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formal power series of `∑ cᵢ • xⁱ` for some scalar field `𝕜` and ring algebra `E
`
-/
def ofScalars (c : ℕ → 𝕜) : FormalMultilinearSeries 𝕜 E E :=
  fun n ↦ c n • ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E

@[simp]
/-
**FormalMultilinearSeries.ofScalars_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalMul
tilinearSeries`。
形式化陈述：ofScalars_eq_zero [Nontrivial E] (n : Nat) : ofScalars E c n = 0 ↔ c n = 0
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalars.eq_1`：∀ {𝕜 : Type u_1} (E : Type u_2) 
[inst : Field 𝕜] [inst_1 : Ring E] [inst_2 : Algebra 𝕜 E] [inst_3 : TopologicalS
pace E]   [inst_4 : IsTopolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousMultilinearMap.ext_iff`：∀ {R : Type u} {ι : Type v} {M₁ : ι → 
Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : AddC…
· 使用定理 `not_forall_of_exists_not`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, ¬p x) →
 ¬∀ (x : α), p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem ofScalars_eq_zero [Nontrivial E] (n : ℕ) : ofScalars E c n = 0 ↔ c n = 0 := by
  rw [ofScalars, smul_eq_zero]
  refine or_iff_left (ContinuousMultilinearMap.ext_iff.1.mt <| not_forall_of_exists_not ?_)
  use fun _ ↦ 1
  simp

@[simp]
/-
**FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero** 是 Mathlib 中的一个定理，位于
命名空间 `FormalMultilinearSeries`。
形式化陈述：ofScalars_eq_zero_of_scalar_zero {n : Nat} (hc : c n = 0) : ofScalars E c 
n = 0
参数：hc : c n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalars.eq_1`：∀ {𝕜 : Type u_1} (E : Type u_2) 
[inst : Field 𝕜] [inst_1 : Ring E] [inst_2 : Algebra 𝕜 E] [inst_3 : TopologicalS
pace E]   [inst_4 : IsTopolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem ofScalars_eq_zero_of_scalar_zero {n : ℕ} (hc : c n = 0) : ofScalars E c n = 0 := by
  rw [ofScalars, hc, zero_smul 𝕜 (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]

@[simp]
/-
**FormalMultilinearSeries.ofScalars_series_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fo
rmalMultilinearSeries`。
形式化陈述：ofScalars_series_eq_zero [Nontrivial E] : ofScalars E c = 0 ↔ c = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofScalars_series_eq_zero [Nontrivial E] : ofScalars E c = 0 ↔ c = 0 := by
  simp [FormalMultilinearSeries.ext_iff, funext_iff]

variable (𝕜) in
@[simp]
/-
**FormalMultilinearSeries.ofScalars_series_eq_zero_of_scalar_zero** 是 Mathlib 中的
一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：ofScalars_series_eq_zero_of_scalar_zero : ofScalars E (0 : Nat -> 𝕜) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero`：ofScalars_eq_z
ero_of_scalar_zero {n : Nat} (hc : c n = 0) : ofScalars E c n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ofScalars_series_eq_zero_of_scalar_zero : ofScalars E (0 : ℕ → 𝕜) = 0 := by
  simp [FormalMultilinearSeries.ext_iff]

@[simp]
/-
**FormalMultilinearSeries.ofScalars_series_of_subsingleton** 是 Mathlib 中的一个定理，位于
命名空间 `FormalMultilinearSeries`。
形式化陈述：ofScalars_series_of_subsingleton [Subsingleton E] : ofScalars E c = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
-/
theorem ofScalars_series_of_subsingleton [Subsingleton E] : ofScalars E c = 0 := by
  simp_rw [FormalMultilinearSeries.ext_iff, ofScalars, ContinuousMultilinearMap.ext_iff]
  exact fun _ _ ↦ Subsingleton.allEq _ _

variable (𝕜) in
/-
**FormalMultilinearSeries.ofScalars_series_injective** 是 Mathlib 中的一个定理，位于命名空间 `
FormalMultilinearSeries`。
形式化陈述：ofScalars_series_injective [Nontrivial E] : Function.Injective (ofScalars 
E (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem ofScalars_series_injective [Nontrivial E] : Function.Injective (ofScalars E (𝕜 := 𝕜)) := by
  intro _ _ h
  ext n
  simpa [ofScalars] using congrArg (fun p ↦ p n fun _ ↦ (1 : E)) h

variable (c)

@[simp]
/-
**FormalMultilinearSeries.ofScalars_series_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `For
malMultilinearSeries`。
形式化陈述：ofScalars_series_eq_iff [Nontrivial E] (c' : Nat -> 𝕜) : ofScalars E c = o
fScalars E c' ↔ c = c'
参数：c' : Nat -> 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `FormalMultilinearSeries.ofScalars_series_injective`：ofScalars_series_inj
ective [Nontrivial E] : Function.Injective (ofScalars E (𝕜
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ofScalars_series_eq_iff [Nontrivial E] (c' : ℕ → 𝕜) :
    ofScalars E c = ofScalars E c' ↔ c = c' :=
  ⟨fun e => ofScalars_series_injective 𝕜 E e, _root_.congrArg _⟩
/-
**FormalMultilinearSeries.ofScalars_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：ofScalars_apply_zero (n : Nat) : ofScalars E c n (fun _ => 0) = Pi.single 
(M
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalars.eq_1`：∀ {𝕜 : Type u_1} (E : Type u_2) 
[inst : Field 𝕜] [inst_1 : Ring E] [inst_2 : Algebra 𝕜 E] [inst_3 : TopologicalS
pace E]   [inst_4 : IsTopolo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem ofScalars_apply_zero (n : ℕ) :
    ofScalars E c n (fun _ => 0) = Pi.single (M := fun _ => E) 0 (c 0 • 1) n := by
  rw [ofScalars]
  cases n <;> simp

@[simp]
/-
**FormalMultilinearSeries.coeff_ofScalars** 是 Mathlib 中的一个引理，位于命名空间 `FormalMulti
linearSeries`。
形式化陈述：coeff_ofScalars {𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n 
: Nat} : (FormalMultilinearSeries.ofScalars 𝕜 p).coeff n = p n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `List.prod_ofFn`：prod_ofFn {n : Nat} {f : Fin n -> M} : (ofFn f).prod = ∏
 i, f i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_ofScalars {𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : ℕ → 𝕜} {n : ℕ} :
    (FormalMultilinearSeries.ofScalars 𝕜 p).coeff n = p n := by
  simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]
/-
**FormalMultilinearSeries.ofScalars_add** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultili
nearSeries`。
形式化陈述：ofScalars_add (c' : Nat -> 𝕜) : ofScalars E (c + c') = ofScalars E c + ofS
calars E c'
参数：c' : Nat -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofScalars_add (c' : ℕ → 𝕜) : ofScalars E (c + c') = ofScalars E c + ofScalars E c' := by
  ext; simp [ofScalars, add_smul]
/-
**FormalMultilinearSeries.ofScalars_sub** 是 Mathlib 中的一个引理，位于命名空间 `FormalMultili
nearSeries`。
形式化陈述：ofScalars_sub (c' : Nat -> 𝕜) : ofScalars E (c - c') = ofScalars E c - ofS
calars E c'
参数：c' : Nat -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousMultilinearMap.instIsSubApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Ring R] [inst_1 : (i : ι) → AddComm
Group (M₁ i)]   [inst_2 : AddCommGr…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofScalars_sub (c' : ℕ → 𝕜) : ofScalars E (c - c') = ofScalars E c - ofScalars E c' := by
  ext; simp [ofScalars, sub_smul]
/-
**FormalMultilinearSeries.ofScalars_smul** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultil
inearSeries`。
形式化陈述：ofScalars_smul (x : 𝕜) : ofScalars E (x • c) = x • ofScalars E c
参数：x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofScalars_smul (x : 𝕜) : ofScalars E (x • c) = x • ofScalars E c := by
  ext; simp [ofScalars, smul_smul]
/-
**FormalMultilinearSeries.ofScalars_comp_neg_id** 是 Mathlib 中的一个定理，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：ofScalars_comp_neg_id : (ofScalars E c).compContinuousLinearMap (-Continuo
usLinearMap.id _ _) = (ofScalars E (fun k => (-1) ^ k * c k))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用引理 `List.prod_map_neg`：prod_map_neg (l : List M) : (l.map Neg.neg).prod = (-
1) ^ l.length * l.prod
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousMultilinearMap.instIsNegApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Ring R] [inst_1 : (i : ι) → AddComm
Group (M₁ i)]   [inst_2 : AddCommGr…
-/
theorem ofScalars_comp_neg_id :
    (ofScalars E c).compContinuousLinearMap (-ContinuousLinearMap.id _ _) =
    (ofScalars E (fun k ↦ (-1) ^ k * c k)) := by
  ext n
  rcases n.even_or_odd with (h | h) <;>
  simp [ofScalars, show ((-ContinuousLinearMap.id 𝕜 E : _) : E → E) = Neg.neg by rfl,
    ← List.map_ofFn, h.neg_one_pow]
/-
**FormalMultilinearSeries.ofScalars_comp_neg** 是 Mathlib 中的一个定理，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：ofScalars_comp_neg (f : E ->L[𝕜] E) : (ofScalars E c).compContinuousLinear
Map (-f) = (ofScalars E (fun k => (-1) ^ k * c k)).compContinuousLinearMap f
参数：f : E ->L[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.id_comp`：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘
SL f = f
· 使用定理 `ContinuousLinearMap.neg_comp`：neg_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [
IsTopologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂) : (-g) ∘SL 
f = -g ∘SL f
· 使用定理 `FormalMultilinearSeries.compContinuousLinearMap_comp`：compContinuousLine
arMap_comp (p : FormalMultilinearSeries 𝕜 G H) (u₁ : F ->L[𝕜] G) (u₂ : E ->L[𝕜] 
F) : (p.compContinuousLinearMap u₁).compCo…
· 使用定理 `FormalMultilinearSeries.ofScalars_comp_neg_id`：ofScalars_comp_neg_id : (
ofScalars E c).compContinuousLinearMap (-ContinuousLinearMap.id _ _) = (ofScalar
s E (fun k => (-1) ^ k * c k))
-/
theorem ofScalars_comp_neg (f : E →L[𝕜] E) :
    (ofScalars E c).compContinuousLinearMap (-f) =
    (ofScalars E (fun k ↦ (-1) ^ k * c k)).compContinuousLinearMap f := by
  conv => lhs; rw [← ContinuousLinearMap.id_comp f, ← ContinuousLinearMap.neg_comp]
  rw [← FormalMultilinearSeries.compContinuousLinearMap_comp, ofScalars_comp_neg_id]

variable (𝕜) in
/-- The submodule generated by scalar series on `FormalMultilinearSeries 𝕜 E E`. -/
/-
**FormalMultilinearSeries.ofScalarsSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：ofScalarsSubmodule : Submodule 𝕜 (FormalMultilinearSeries 𝕜 E E) where car
rier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule generated by scalar series on `FormalMultilinearSeries 𝕜 E E`.
-/
def ofScalarsSubmodule : Submodule 𝕜 (FormalMultilinearSeries 𝕜 E E) where
  carrier := {ofScalars E f | f}
  add_mem' := fun ⟨c, hc⟩ ⟨c', hc'⟩ ↦ ⟨c + c', hc' ▸ hc ▸ ofScalars_add E c c'⟩
  zero_mem' := ⟨0, ofScalars_series_eq_zero_of_scalar_zero 𝕜 E⟩
  smul_mem' := fun x _ ⟨c, hc⟩ ↦ ⟨x • c, hc ▸ ofScalars_smul E c x⟩

variable {E}
/-
**FormalMultilinearSeries.ofScalars_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：ofScalars_apply_eq (x : E) (n : Nat) : ofScalars E c n (fun _ => x) = c n 
• x ^ n
参数：x : E；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofScalars_apply_eq (x : E) (n : ℕ) :
    ofScalars E c n (fun _ ↦ x) = c n • x ^ n := by
  simp [ofScalars]

/-- This naming follows the convention of `NormedSpace.expSeries_apply_eq'`. -/
/-
**FormalMultilinearSeries.ofScalars_apply_eq'** 是 Mathlib 中的一个定理，位于命名空间 `FormalM
ultilinearSeries`。
形式化陈述：ofScalars_apply_eq' (x : E) : (fun n => ofScalars E c n (fun _ => x)) = fu
n n => c n • x ^ n
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This naming follows the convention of `NormedSpace.expSeries_apply_eq'`.
-/
theorem ofScalars_apply_eq' (x : E) :
    (fun n ↦ ofScalars E c n (fun _ ↦ x)) = fun n ↦ c n • x ^ n := by
  simp [ofScalars]

/-- The sum of the formal power series. Takes the value `0` outside the radius of convergence. -/
/-
**FormalMultilinearSeries.ofScalarsSum** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilin
earSeries`。
形式化陈述：ofScalarsSum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of the formal power series. Takes the value `0` outside the radius of co
nvergence.
-/
noncomputable def ofScalarsSum := (ofScalars E c).sum
/-
**FormalMultilinearSeries.ofScalars_sum_eq** 是 Mathlib 中的一个定理，位于命名空间 `FormalMult
ilinearSeries`。
形式化陈述：ofScalars_sum_eq (x : E) : ofScalarsSum c x = ∑' n, c n • x ^ n
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `FormalMultilinearSeries.ofScalars_apply_eq`：ofScalars_apply_eq (x : E) (
n : Nat) : ofScalars E c n (fun _ => x) = c n • x ^ n
-/
theorem ofScalars_sum_eq (x : E) : ofScalarsSum c x =
    ∑' n, c n • x ^ n := tsum_congr fun n => ofScalars_apply_eq c x n
/-
**FormalMultilinearSeries.ofScalarsSum_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：ofScalarsSum_eq_tsum : ofScalarsSum c = fun (x : E) => ∑' n : Nat, c n • x
 ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FormalMultilinearSeries.ofScalars_sum_eq`：ofScalars_sum_eq (x : E) : ofS
calarsSum c x = ∑' n, c n • x ^ n
-/
theorem ofScalarsSum_eq_tsum : ofScalarsSum c =
    fun (x : E) => ∑' n : ℕ, c n • x ^ n := funext (ofScalars_sum_eq c)

@[simp]
/-
**FormalMultilinearSeries.ofScalarsSum_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalMul
tilinearSeries`。
形式化陈述：ofScalarsSum_zero : ofScalarsSum c (0 : E) = c 0 • 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FormalMultilinearSeries.ofScalarsSum_eq_tsum`：ofScalarsSum_eq_tsum : ofS
calarsSum c = fun (x : E) => ∑' n : Nat, c n • x ^ n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FormalMultilinearSeries.ofScalars_apply_zero`：ofScalars_apply_zero (n : 
Nat) : ofScalars E c n (fun _ => 0) = Pi.single (M
· 使用定理 `tsum_pi_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] [inst_2 : DecidableEq β] (b : β)   (a : α), ∑' (b
' : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofScalarsSum_zero : ofScalarsSum c (0 : E) = c 0 • 1 := by
  simp [ofScalarsSum_eq_tsum, ← ofScalars_apply_eq, ofScalars_apply_zero]

@[simp]
/-
**FormalMultilinearSeries.ofScalarsSum_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：ofScalarsSum_of_subsingleton [Subsingleton E] {x : E} : ofScalarsSum c x =
 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalarsSum.congr_simp`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : Field 𝕜] [inst_1 : Ring E] [inst_2 : Algebra 𝕜 E] [inst_3 : Top
ologicalSpace E]   [inst_4 : IsTopolo…
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofScalarsSum_of_subsingleton [Subsingleton E] {x : E} : ofScalarsSum c x = 0 := by
  simp [Subsingleton.eq_zero (α := E)]

@[simp]
/-
**FormalMultilinearSeries.ofScalarsSum_op** 是 Mathlib 中的一个定理，位于命名空间 `FormalMulti
linearSeries`。
形式化陈述：ofScalarsSum_op [T2Space E] (x : E) : ofScalarsSum c (MulOpposite.op x) = 
MulOpposite.op (ofScalarsSum c x)
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalRingMulOpposite`：∀ {R : Type u_1} [inst : NonUnitalNonA
ssocRing R] [inst_1 : TopologicalSpace R] [IsTopologicalRing R],   IsTopological
Ring Rᵐᵒᵖ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalars_sum_eq`：ofScalars_sum_eq (x : E) : ofS
calarsSum c x = ∑' n, c n • x ^ n
· 使用定理 `tsum_op`：tsum_op [T2Space α] : ∑'[L] x, op (f x) = op (∑'[L] x, f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofScalarsSum_op [T2Space E] (x : E) :
    ofScalarsSum c (MulOpposite.op x) = MulOpposite.op (ofScalarsSum c x) := by
  simp [ofScalars_sum_eq, ← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]
/-
**FormalMultilinearSeries.ofScalarsSum_unop** 是 Mathlib 中的一个定理，位于命名空间 `FormalMul
tilinearSeries`。
形式化陈述：ofScalarsSum_unop [T2Space E] (x : Eᵐᵒᵖ) : ofScalarsSum c (MulOpposite.uno
p x) = MulOpposite.unop (ofScalarsSum c x)
参数：x : Eᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalRingMulOpposite`：∀ {R : Type u_1} [inst : NonUnitalNonA
ssocRing R] [inst_1 : TopologicalSpace R] [IsTopologicalRing R],   IsTopological
Ring Rᵐᵒᵖ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalars_sum_eq`：ofScalars_sum_eq (x : E) : ofS
calarsSum c x = ∑' n, c n • x ^ n
· 使用定理 `tsum_unop`：tsum_unop [T2Space α] {f : β -> αᵐᵒᵖ} : ∑'[L] x, unop (f x) =
 unop (∑'[L] x, f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofScalarsSum_unop [T2Space E] (x : Eᵐᵒᵖ) :
    ofScalarsSum c (MulOpposite.unop x) = MulOpposite.unop (ofScalarsSum c x) := by
  simp [ofScalars_sum_eq, ← MulOpposite.unop_pow, ← MulOpposite.unop_smul, tsum_unop]

end Field

section Seminormed

open Filter ENNReal
open scoped Topology NNReal

variable {𝕜 : Type*} (E : Type*) [NontriviallyNormedField 𝕜] [SeminormedRing E]
    [NormedAlgebra 𝕜 E] (c : ℕ → 𝕜) (n : ℕ)

@[simp]
/-
**FormalMultilinearSeries.ofScalars_norm_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：ofScalars_norm_eq_mul : ‖ofScalars E c n‖ = ‖c n‖ * ‖ContinuousMultilinear
Map.mkPiAlgebraFin 𝕜 n E‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalars.eq_1`：∀ {𝕜 : Type u_1} (E : Type u_2) 
[inst : Field 𝕜] [inst_1 : Ring E] [inst_2 : Algebra 𝕜 E] [inst_3 : TopologicalS
pace E]   [inst_4 : IsTopolo…
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
theorem ofScalars_norm_eq_mul :
    ‖ofScalars E c n‖ = ‖c n‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E‖ := by
  rw [ofScalars, norm_smul]
/-
**FormalMultilinearSeries.ofScalars_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `FormalMul
tilinearSeries`。
形式化陈述：ofScalars_norm_le (hn : n > 0) : ‖ofScalars E c n‖ <= ‖c n‖
参数：hn : n > 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalars_norm_eq_mul`：ofScalars_norm_eq_mul : ‖
ofScalars E c n‖ = ‖c n‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E‖
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos`：norm_mkPiAlgebra
Fin_le_of_pos (hn : 0 < n) : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ <= 
1
-/
theorem ofScalars_norm_le (hn : n > 0) : ‖ofScalars E c n‖ ≤ ‖c n‖ := by
  simp only [ofScalars_norm_eq_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _)
    (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos hn))
/-
**FormalMultilinearSeries.ofScalars_norm** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultil
inearSeries`。
形式化陈述：ofScalars_norm [NormOneClass E] : ‖ofScalars E c n‖ = ‖c n‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `FormalMultilinearSeries.ofScalars_norm_eq_mul`：ofScalars_norm_eq_mul : ‖
ofScalars E c n‖ = ‖c n‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E‖
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin`：norm_mkPiAlgebraFin [NormO
neClass A] : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofScalars_norm [NormOneClass E] : ‖ofScalars E c n‖ = ‖c n‖ := by
  simp

end Seminormed

section Normed

open Filter ENNReal
open scoped Topology NNReal

variable {𝕜 : Type*} (E : Type*) [NontriviallyNormedField 𝕜] [NormedRing E]
    [NormedAlgebra 𝕜 E] (c : ℕ → 𝕜) (n : ℕ)

/-
**FormalMultilinearSeries.tendsto_succ_norm_div_norm** 是 Mathlib 中的一个定理，位于命名空间 `
FormalMultilinearSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tendsto_succ_norm_div_norm {r r' : ℝ≥0} (hr' : r' ≠ 0)
    (hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) :
      Tendsto (fun n ↦ ‖‖c (n + 1)‖ * r' ^ (n + 1)‖ /
        ‖‖c n‖ * r' ^ n‖) atTop (𝓝 ↑(r' * r)) := by
  simp_rw [norm_mul, norm_norm, mul_div_mul_comm, ← norm_div, pow_succ, mul_div_right_comm,
    div_self (pow_ne_zero _ (NNReal.coe_ne_zero.mpr hr')), one_mul, norm_div, NNReal.norm_eq]
  exact mul_comm r' r ▸ hc.mul tendsto_const_nhds
/-
**FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto** 是 Mathlib 中的一个定理，
位于命名空间 `FormalMultilinearSeries`。
形式化陈述：inv_le_ofScalars_radius_of_tendsto {r : Real>=0} (hr : r != 0) (hc : Tends
to (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) : ofNNReal r⁻¹ <= (ofScalars E c).
radius
参数：hr : r != 0；hc : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `FormalMultilinearSeries.le_radius_of_summable_norm`：le_radius_of_summabl
e_norm (p : FormalMultilinearSeries 𝕜 E F) (hs : Summable fun n => ‖p n‖ * (r : 
Real) ^ n) : ↑r <= p.radius
· 使用定理 `Summable.of_norm_bounded_eventually`：Summable.of_norm_bounded_eventually
 {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i in cofinite, ‖f i
‖ <= g i) : Summable f
· 使用定理 `summable_of_ratio_test_tendsto_lt_one`：summable_of_ratio_test_tendsto_lt
_one {α : Type*} [NormedAddCommGroup α] [CompleteSpace α] {f : Nat -> α} {l : Re
al} (hl₁ : l < 1) (hf : for…
· 使用定理 `NNReal.lt_inv_iff_mul_lt`：lt_inv_iff_mul_lt {r p : Real>=0} (h : p != 0)
 : r < p⁻¹ ↔ r * p < 1
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ne`：Filter.Tendsto.eventually_ne {X} [Topologi
calSpace Y] [T1Space Y] {g : X -> Y} {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g 
l (𝓝 b₁)) (hb : b₁…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_ne_zero`：∀ {r : NNReal}, ↑r ≠ 0 ↔ r ≠ 0
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
（共 54 条，此处仅展示前 30 条）
-/
theorem inv_le_ofScalars_radius_of_tendsto {r : ℝ≥0} (hr : r ≠ 0)
    (hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) :
      ofNNReal r⁻¹ ≤ (ofScalars E c).radius := by
  refine le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  rw [coe_lt_coe, NNReal.lt_inv_iff_mul_lt hr] at hr'
  by_cases hrz : r' = 0
  · simp [hrz]
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_norm_bounded_eventually (g := fun n ↦ ‖‖c n‖ * r' ^ n‖) ?_ ?_
  · refine summable_of_ratio_test_tendsto_lt_one hr' ?_ ?_
    · refine (hc.eventually_ne (NNReal.coe_ne_zero.mpr hr)).mp (Eventually.of_forall ?_)
      simp_all
    · simp_rw [norm_norm]
      exact tendsto_succ_norm_div_norm c hrz hc
  · filter_upwards [eventually_cofinite_ne 0] with n hn
    simp only [norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
    gcongr
    exact ofScalars_norm_le E c n (Nat.pos_iff_ne_zero.mpr hn)

/-- The radius of convergence of a scalar series is the inverse of the non-zero limit
`fun n ↦ ‖c n.succ‖ / ‖c n‖`. -/
/-
**FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto** 是 Mathlib 中的一个定理，
位于命名空间 `FormalMultilinearSeries`。
形式化陈述：ofScalars_radius_eq_inv_of_tendsto [NormOneClass E] {r : Real>=0} (hr : r 
!= 0) (hc : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) : (ofScalars E c)
.radius = ofNNReal r⁻¹
参数：hr : r != 0；hc : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `NNReal.le_inv_iff_mul_le`：le_inv_iff_mul_le {r p : Real>=0} (h : p != 0)
 : r <= p⁻¹ ↔ r * p <= 1
· 使用定理 `FormalMultilinearSeries.summable_norm_mul_pow`：summable_norm_mul_pow (p 
: FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : ↑r < p.radius) : Summable fu
n n : Nat => ‖p n‖ * (r : Real) ^ n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_summable_of_ratio_test_tendsto_gt_one`：not_summable_of_ratio_test_te
ndsto_gt_one {α : Type*} [SeminormedAddCommGroup α] {f : Nat -> α} {l : Real} (h
l : 1 < l) (h : Tendsto (fun n …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FormalMultilinearSeries.ofScalars_norm`：ofScalars_norm [NormOneClass E] 
: ‖ofScalars E c n‖ = ‖c n‖
· 使用定理 `_private.Mathlib.Analysis.Analytic.OfScalars.0.FormalMultilinearSeries.t
endsto_succ_norm_div_norm`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] (
c : ℕ → 𝕜) {r r' : NNReal},   r' ≠ 0 →     Filter.Tendsto (fun n => ‖c n.succ‖ /
 ‖c n‖)…
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto`：inv_le_ofSca
lars_radius_of_tendsto {r : Real>=0} (hr : r != 0) (hc : Tendsto (fun n => ‖c n.
succ‖ / ‖c n‖) atTop (𝓝 r)) : ofNNReal r⁻¹ <= (o…

--- 原说明 ---
The radius of convergence of a scalar series is the inverse of the non-zero limi
t
`fun n ↦ ‖c n.succ‖ / ‖c n‖`.
-/
theorem ofScalars_radius_eq_inv_of_tendsto [NormOneClass E] {r : ℝ≥0} (hr : r ≠ 0)
    (hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = ofNNReal r⁻¹ := by
  refine le_antisymm ?_ (inv_le_ofScalars_radius_of_tendsto E c hr hc)
  refine le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  rw [coe_le_coe, NNReal.le_inv_iff_mul_le hr]
  have := FormalMultilinearSeries.summable_norm_mul_pow _ hr'
  contrapose! this
  apply not_summable_of_ratio_test_tendsto_gt_one this
  simp_rw [ofScalars_norm]
  exact tendsto_succ_norm_div_norm c (by aesop) hc

/-- A convenience lemma restating the result of `ofScalars_radius_eq_inv_of_tendsto` under
the inverse ratio. -/
/-
**FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名
空间 `FormalMultilinearSeries`。
形式化陈述：ofScalars_radius_eq_of_tendsto [NormOneClass E] {r : NNReal} (hr : r != 0)
 (hc : Tendsto (fun n => ‖c n‖ / ‖c n.succ‖) atTop (𝓝 r)) : (ofScalars E c).radi
us = ofNNReal r
参数：hr : r != 0；hc : Tendsto (fun n => ‖c n‖ / ‖c n.succ‖) atTop (𝓝 r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.inv₀`：Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a
)) (ha : a != 0) : Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_ne_zero`：∀ {r : NNReal}, ↑r ≠ 0 ↔ r ≠ 0
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto`：ofScalars_ra
dius_eq_inv_of_tendsto [NormOneClass E] {r : Real>=0} (hr : r != 0) (hc : Tendst
o (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) : (…
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0

--- 原说明 ---
A convenience lemma restating the result of `ofScalars_radius_eq_inv_of_tendsto`
 under
the inverse ratio.
-/
theorem ofScalars_radius_eq_of_tendsto [NormOneClass E] {r : NNReal} (hr : r ≠ 0)
    (hc : Tendsto (fun n ↦ ‖c n‖ / ‖c n.succ‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = ofNNReal r := by
  suffices Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r⁻¹) by
    convert! ofScalars_radius_eq_inv_of_tendsto E c (inv_ne_zero hr) this
    simp
  convert hc.inv₀ (NNReal.coe_ne_zero.mpr hr)
  simp

/-- The ratio test stating that if `‖c n.succ‖ / ‖c n‖` tends to zero, the radius is unbounded.
This requires that the coefficients are eventually non-zero as
`‖c n.succ‖ / 0 = 0` by convention. -/
/-
**FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto** 是 Mathlib 中的一个定理，
位于命名空间 `FormalMultilinearSeries`。
形式化陈述：ofScalars_radius_eq_top_of_tendsto (hc : forallᶠ n in atTop, c n != 0) (hc
' : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0)) : (ofScalars E c).radius 
= ⊤
参数：hc : forallᶠ n in atTop, c n != 0；hc' : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖)
 atTop (𝓝 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_summable_norm`：radius_eq_top_of
_summable_norm (p : FormalMultilinearSeries 𝕜 E F) (hs : forall r : Real>=0, Sum
mable fun n => ‖p n‖ * (r : Real) ^ n) : p.r…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Summable.comp_nat_add`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1
 : TopologicalSpace M] [ContinuousAdd M] {f : ℕ → M} {k : ℕ},   (Summable fun n 
=> f (n + k…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FormalMultilinearSeries.ofScalars_norm_eq_mul`：ofScalars_norm_eq_mul : ‖
ofScalars E c n‖ = ‖c n‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E‖
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Summable.of_norm_bounded_eventually`：Summable.of_norm_bounded_eventually
 {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i in cofinite, ‖f i
‖ <= g i) : Summable f
· 使用定理 `summable_of_ratio_test_tendsto_lt_one`：summable_of_ratio_test_tendsto_lt
_one {α : Type*} [NormedAddCommGroup α] [CompleteSpace α] {f : Nat -> α} {l : Re
al} (hl₁ : l < 1) (hf : for…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
The ratio test stating that if `‖c n.succ‖ / ‖c n‖` tends to zero, the radius is
 unbounded.
This requires that the coefficients are eventually non-zero as
`‖c n.succ‖ / 0 = 0` by convention.
-/
theorem ofScalars_radius_eq_top_of_tendsto (hc : ∀ᶠ n in atTop, c n ≠ 0)
    (hc' : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0)) : (ofScalars E c).radius = ⊤ := by
  refine radius_eq_top_of_summable_norm _ fun r' ↦ ?_
  by_cases hrz : r' = 0
  · apply Summable.comp_nat_add (k := 1)
    simp [hrz]
  · refine Summable.of_norm_bounded_eventually (g := fun n ↦ ‖‖c n‖ * r' ^ n‖) ?_ ?_
    · apply summable_of_ratio_test_tendsto_lt_one zero_lt_one (hc.mp (Eventually.of_forall ?_))
      · simp only [norm_norm]
        exact mul_zero (_ : ℝ) ▸ tendsto_succ_norm_div_norm _ hrz (NNReal.coe_zero ▸ hc')
      · simp_all
    · filter_upwards [eventually_cofinite_ne 0] with n hn
      simp only [norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
      gcongr
      exact ofScalars_norm_le E c n (Nat.pos_iff_ne_zero.mpr hn)

/-- If `‖c n.succ‖ / ‖c n‖` is unbounded, then the radius of convergence is zero. -/
/-
**FormalMultilinearSeries.ofScalars_radius_eq_zero_of_tendsto** 是 Mathlib 中的一个定理
，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：ofScalars_radius_eq_zero_of_tendsto [NormOneClass E] (hc : Tendsto (fun n 
=> ‖c n.succ‖ / ‖c n‖) atTop atTop) : (ofScalars E c).radius = 0
参数：hc : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `FormalMultilinearSeries.summable_norm_mul_pow`：summable_norm_mul_pow (p 
: FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : ↑r < p.radius) : Summable fu
n n : Nat => ‖p n‖ * (r : Real) ^ n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_summable_of_ratio_norm_eventually_ge`：not_summable_of_ratio_norm_eve
ntually_ge {α : Type*} [SeminormedAddCommGroup α] {f : Nat -> α} {r : Real} (hr 
: 1 < r) (hf : existsᶠ n in at…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_tendsto_atTop_of_tendsto_nhds`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{a : α} {l : Filter β} …
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
（共 67 条，此处仅展示前 30 条）

--- 原说明 ---
If `‖c n.succ‖ / ‖c n‖` is unbounded, then the radius of convergence is zero.
-/
theorem ofScalars_radius_eq_zero_of_tendsto [NormOneClass E]
    (hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop atTop) : (ofScalars E c).radius = 0 := by
  suffices (ofScalars E c).radius ≤ 0 by simp_all
  refine le_of_forall_nnreal_lt (fun r hr ↦ ?_)
  rw [← coe_zero, coe_le_coe]
  have := FormalMultilinearSeries.summable_norm_mul_pow _ hr
  contrapose! this
  refine not_summable_of_ratio_norm_eventually_ge (r := 2) (by simp) ?_ ?_
  · contrapose! hc
    apply not_tendsto_atTop_of_tendsto_nhds (a := 0)
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hc] with n hc'
    rw [ofScalars_norm, norm_mul, norm_norm, mul_eq_zero] at hc'
    cases hc' <;> aesop
  · filter_upwards [hc.eventually_ge_atTop (2 * r⁻¹), eventually_ne_atTop 0] with n hc hn
    simp only [ofScalars_norm, norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
    rw [mul_comm ‖c n‖, ← mul_assoc, ← div_le_div_iff₀, mul_div_assoc]
    · convert! hc
      rw [pow_succ, div_mul_cancel_left₀, NNReal.coe_inv]
      aesop
    · simp_all
    · refine Ne.lt_of_le (fun hr' ↦ Not.elim ?_ hc) (norm_nonneg _)
      rw [← hr']
      simp [this]

/-- This theorem combines the results of the special cases above, using `ENNReal` division to remove
the requirement that the ratio is eventually non-zero. -/
/-
**FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto_ENNReal** 是 Mathlib
 中的一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：ofScalars_radius_eq_inv_of_tendsto_ENNReal [NormOneClass E] {r : Real>=0∞}
 (hc' : Tendsto (fun n => ENNReal.ofReal ‖c n.succ‖ / ENNReal.ofReal ‖c n‖) atTo
p (𝓝 r)) : (ofScalars E c).radius = r⁻¹
参数：hc' : Tendsto (fun n => ENNReal.ofReal ‖c n.succ‖ / ENNReal.ofReal ‖c n‖) atT
op (𝓝 r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto`：ofScalars_ra
dius_eq_top_of_tendsto (hc : forallᶠ n in atTop, c n != 0) (hc' : Tendsto (fun n
 => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0)) : (ofScalar…
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_toReal`：tendsto_toReal {a : Real>=0∞} (ha : a != ∞) : Te
ndsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal)
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero`：radius_eq_t
op_of_eventually_eq_zero (h : forallᶠ n in atTop, p n = 0) : p.radius = ∞
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
（共 78 条，此处仅展示前 30 条）

--- 原说明 ---
This theorem combines the results of the special cases above, using `ENNReal` di
vision to remove
the requirement that the ratio is eventually non-zero.
-/
theorem ofScalars_radius_eq_inv_of_tendsto_ENNReal [NormOneClass E] {r : ℝ≥0∞}
    (hc' : Tendsto (fun n ↦ ENNReal.ofReal ‖c n.succ‖ / ENNReal.ofReal ‖c n‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = r⁻¹ := by
  rcases ENNReal.trichotomy r with (hr | hr | hr)
  · simp_rw [hr, inv_zero] at hc' ⊢
    by_cases h : (∀ᶠ (n : ℕ) in atTop, c n ≠ 0)
    · apply ofScalars_radius_eq_top_of_tendsto E c h ?_
      refine Tendsto.congr' ?_ <| (tendsto_toReal zero_ne_top).comp hc'
      filter_upwards [h]
      simp
    · apply (ofScalars E c).radius_eq_top_of_eventually_eq_zero
      simp only [eventually_atTop, not_exists, not_forall, not_not] at h ⊢
      obtain ⟨ti, hti⟩ := eventually_atTop.mp (hc'.eventually_ne zero_ne_top)
      obtain ⟨zi, hzi, z⟩ := h ti
      refine ⟨zi, Nat.le_induction (ofScalars_eq_zero_of_scalar_zero E z) fun n hmn a ↦ ?_⟩
      nontriviality E
      simp only [ofScalars_eq_zero] at a ⊢
      contrapose! hti
      exact ⟨n, hzi.trans hmn, ENNReal.div_eq_top.mpr (by simp [a, hti])⟩
  · simp_rw [hr, inv_top] at hc' ⊢
    apply ofScalars_radius_eq_zero_of_tendsto E c ((tendsto_add_atTop_iff_nat 1).mp ?_)
    refine tendsto_ofReal_nhds_top.mp (Tendsto.congr' ?_ ((tendsto_add_atTop_iff_nat 1).mpr hc'))
    filter_upwards [hc'.eventually_ne top_ne_zero] with n hn
    apply (ofReal_div_of_pos (Ne.lt_of_le (Ne.symm ?_) (norm_nonneg _))).symm
    simp_all
  · have hr' := toReal_ne_zero.mp hr.ne.symm
    have hr'' := toNNReal_ne_zero.mpr hr' -- this result could go in ENNReal
    convert! ofScalars_radius_eq_inv_of_tendsto E c hr'' ?_
    · simp [ENNReal.coe_inv hr'', ENNReal.coe_toNNReal (toReal_ne_zero.mp hr.ne.symm).2]
    · simp_rw [ENNReal.coe_toNNReal_eq_toReal]
      refine Tendsto.congr' ?_ <| (tendsto_toReal hr'.2).comp hc'
      filter_upwards [hc'.eventually_ne hr'.1, hc'.eventually_ne hr'.2]
      simp

end Normed

end FormalMultilinearSeries

