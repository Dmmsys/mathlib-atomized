/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Order.Antidiag.Tendsto
public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Multivariate restricted power series

`IsRestricted` : We say a multivariate power series over a normed ring `R` is restricted for a
tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section

namespace MvPowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] {σ : Type*}

/-- A multivariate powe0r series over a normed ring `R` is restricted for a
  tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter. -/
/-
**MvPowerSeries.IsRestricted** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：IsRestricted (c : σ -> Real) (f : MvPowerSeries σ R)
参数：c : σ -> Real；f : MvPowerSeries σ R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multivariate powe0r series over a normed ring `R` is restricted for a
  tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite
 filter.
-/
def IsRestricted (c : σ → ℝ) (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ ‖coeff t f‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)

@[simp]
/-
**MvPowerSeries.isRestricted_abs_iff** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：isRestricted_abs_iff (c : σ -> Real) (f : MvPowerSeries σ R) : IsRestricte
d |c| f ↔ IsRestricted c f
参数：c : σ -> Real；f : MvPowerSeries σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `norm_prod`：norm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖ = ∏ b
 in s, ‖f b‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `abs_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddL
eftMono α] [AddRightMono α] (a : α), |(|a|)| = |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isRestricted_abs_iff (c : σ → ℝ) (f : MvPowerSeries σ R) :
    IsRestricted |c| f ↔ IsRestricted c f := by
  simp [IsRestricted, NormedAddGroup.tendsto_nhds_zero, Finsupp.prod]
/-
**MvPowerSeries.isRestricted_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：isRestricted_zero (c : σ -> Real) : IsRestricted c (0 : MvPowerSeries σ R)
参数：c : σ -> Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma isRestricted_zero (c : σ → ℝ) : IsRestricted c (0 : MvPowerSeries σ R) := by
  simpa [IsRestricted] using tendsto_const_nhds
/-
**MvPowerSeries.isRestricted_monomial** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：isRestricted_monomial (c : σ -> Real) (n : σ ->₀ Nat) (a : R) : IsRestrict
ed c (monomial n a)
参数：c : σ -> Real；n : σ ->₀ Nat；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isRestricted_monomial (c : σ → ℝ) (n : σ →₀ ℕ) (a : R) :
    IsRestricted c (monomial n a) := by
  classical
  refine tendsto_nhds_of_eventually_eq (Set.Subsingleton.finite ?_)
  simp [Set.Subsingleton, coeff_monomial]
/-
**MvPowerSeries.isRestricted_one** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：isRestricted_one (c : σ -> Real) : IsRestricted c (1 : MvPowerSeries σ R)
参数：c : σ -> Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.isRestricted_monomial`：isRestricted_monomial (c : σ -> Rea
l) (n : σ ->₀ Nat) (a : R) : IsRestricted c (monomial n a)
-/
lemma isRestricted_one (c : σ → ℝ) : IsRestricted c (1 : MvPowerSeries σ R) :=
  isRestricted_monomial c 0 1
/-
**MvPowerSeries.isRestricted_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：isRestricted_C (c : σ -> Real) (a : R) : IsRestricted c (C a)
参数：c : σ -> Real；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.isRestricted_monomial`：isRestricted_monomial (c : σ -> Rea
l) (n : σ ->₀ Nat) (a : R) : IsRestricted c (monomial n a)
-/
lemma isRestricted_C (c : σ → ℝ) (a : R) : IsRestricted c (C a) := by
  simpa [monomial_zero_eq_C_apply] using isRestricted_monomial c 0 a
/-
**MvPowerSeries.isRestricted.add** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.isRest
ricted`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] {σ : Type u_2} (c : σ → ℝ) {f g : M
vPowerSeries σ R},   MvPowerSeries.IsRestricted c f → MvPowerSeries.IsRestricted
 c g → MvPowerSeries.IsRestricted c (f + g)
参数：c : σ → ℝ；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPowerSeries.isRestricted_abs_iff`：isRestricted_abs_iff (c : σ -> Real)
 (f : MvPowerSeries σ R) : IsRestricted |c| f ↔ IsRestricted c f
· 使用定理 `MvPowerSeries.IsRestricted.eq_1`：∀ {R : Type u_1} [inst : NormedRing R] 
{σ : Type u_2} (c : σ → ℝ) (f : MvPowerSeries σ R),   MvPowerSeries.IsRestricted
 c f =     Filter.Ten…
· 使用定理 `Filter.Tendsto.squeeze`：∀ {α : Type u} {β : Type v} [ts : TopologicalSpa
ce α] [inst : Preorder α] [OrderTopology α] {f g h : β → α}   {b : Filter β} {a 
: α},   Filt…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
-/
lemma isRestricted.add (c : σ → ℝ) {f g : MvPowerSeries σ R} (hf : IsRestricted c f)
    (hg : IsRestricted c g) : IsRestricted c (f + g) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  refine tendsto_const_nhds.squeeze (add_zero (0 : ℝ) ▸ hf.add hg) (fun n ↦ ?_) fun n ↦ ?_
  · dsimp [Finsupp.prod]; positivity -- TODO: add positivity extension for Finsupp.prod
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le ..) (by dsimp [Finsupp.prod]; positivity)
/-
**MvPowerSeries.isRestricted.neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.isRest
ricted`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] {σ : Type u_2} (c : σ → ℝ) {f : MvP
owerSeries σ R},   MvPowerSeries.IsRestricted c f → MvPowerSeries.IsRestricted c
 (-f)
参数：c : σ → ℝ；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPowerSeries.isRestricted_abs_iff`：isRestricted_abs_iff (c : σ -> Real)
 (f : MvPowerSeries σ R) : IsRestricted |c| f ↔ IsRestricted c f
· 使用定理 `MvPowerSeries.IsRestricted.eq_1`：∀ {R : Type u_1} [inst : NormedRing R] 
{σ : Type u_2} (c : σ → ℝ) (f : MvPowerSeries σ R),   MvPowerSeries.IsRestricted
 c f =     Filter.Ten…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
-/
lemma isRestricted.neg (c : σ → ℝ) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (-f) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  simpa [IsRestricted] using hf

open IsUltrametricDist

open Finset.HasAntidiagonal in
/-
**MvPowerSeries.tendsto_antidiagonal** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：tendsto_antidiagonal {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M
] [NormedRing S] [IsUltrametricDist S] {C : M -> Real} (hC : forall a b, C (a + 
b) = C a * C b) {f g : M -> S} (hf : Tendsto (fun i => ‖f i‖ * C i) cofinite (𝓝 
0)) (hg : Tendsto (fun i => ‖g i‖ * C i) cofinite (𝓝 0)) : Tendsto (fun a => ‖∑ 
p in Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0)
参数：hC : forall a b, C (a + b) = C a * C b；hf : Tendsto (fun i => ‖f i‖ * C i) co
finite (𝓝 0)；hg : Tendsto (fun i => ‖g i‖ * C i) cofinite (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Filter.Tendsto.squeeze`：∀ {α : Type u} {β : Type v} [ts : TopologicalSpa
ce α] [inst : Preorder α] [OrderTopology α] {f g h : β → α}   {b : Filter β} {a 
: α},   Filt…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.HasAntidiagonal.nonempty_antidiagonal`：∀ {M : Type u_2} [inst : A
ddMonoid M] [inst_1 : Finset.HasAntidiagonal M] (a : M),   (Finset.HasAntidiagon
al.antidiagonal a).Nonempty
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Finset.HasAntidiagonal.tendsto_sup'_antidiagonal_cofinite`：∀ {M : Type u
_1} {R : Type u_2} [inst : AddMonoid M] [inst_1 : Finset.HasAntidiagonal M] {f :
 M × M → R}   [inst_2 : LinearOrder R] {F : Fil…
· 使用定理 `tendsto_mul_cofinite_nhds_zero`：tendsto_mul_cofinite_nhds_zero {f : α ->
 M} {g : β -> M} (hf : Tendsto f cofinite (𝓝 0)) (hg : Tendsto g cofinite (𝓝 0))
 : Tendsto (fun i : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Finset.Nonempty.norm_sum_le_sup'_norm`：∀ {M : Type u_1} {ι : Type u_2} [
inst : SeminormedAddCommGroup M] [IsUltrametricDist M] {s : Finset ι} (hs : s.No
nempty)   (f : ι → M), ‖∑ i…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_mul₀`：∀ {ι : Type u_1} {G₀ : Type u_3} [inst : GroupWithZero
 G₀] [inst_1 : SemilatticeSup G₀] {a : G₀} [MulPosReflectLT G₀],   0 ≤ a → ∀ (f 
: ι → …
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Finset.sup'_mono_fun`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eSup α] {s : Finset β} {hs : s.Nonempty} {f g : β → α},   (∀ b ∈ s, f b ≤ g b) →
 s.sup' hs…
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
（共 46 条，此处仅展示前 30 条）
-/
lemma tendsto_antidiagonal {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] [NormedRing S]
    [IsUltrametricDist S] {C : M → ℝ} (hC : ∀ a b, C (a + b) = C a * C b) {f g : M → S}
    (hf : Tendsto (fun i ↦ ‖f i‖ * C i) cofinite (𝓝 0))
    (hg : Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0)) :
    Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0) := by
  wlog hC' : 0 ≤ C generalizing C
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using this (C := |C|) (by simp [hC]) (by simpa using hf.norm)
      (by simpa using hg.norm) (fun _ => by simp)
  refine .squeeze tendsto_const_nhds
    (tendsto_sup'_antidiagonal_cofinite (tendsto_mul_cofinite_nhds_zero hf hg))
    (fun x ↦ mul_nonneg (by simp) (hC' x)) fun a ↦ ?_
  have : 0 ≤ C a := hC' a
  grw [(nonempty_antidiagonal _).norm_sum_le_sup'_norm, Finset.sup'_mul₀ this]
  refine Finset.sup'_mono_fun fun x hx ↦ ?_
  grw [mul_mul_mul_comm, ← hC, Finset.mem_antidiagonal.mp hx, ← norm_mul_le]
/-
**MvPowerSeries.isRestricted.mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.isRest
ricted`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] {σ : Type u_2} [IsUltrametricDist R
] (c : σ → ℝ) {f g : MvPowerSeries σ R},   MvPowerSeries.IsRestricted c f → MvPo
werSeries.IsRestricted c g → MvPowerSeries.IsRestricted c (f * g)
参数：c : σ → ℝ；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPowerSeries.isRestricted_abs_iff`：isRestricted_abs_iff (c : σ -> Real)
 (f : MvPowerSeries σ R) : IsRestricted |c| f ↔ IsRestricted c f
· 使用定理 `MvPowerSeries.IsRestricted.eq_1`：∀ {R : Type u_1} [inst : NormedRing R] 
{σ : Type u_2} (c : σ → ℝ) (f : MvPowerSeries σ R),   MvPowerSeries.IsRestricted
 c f =     Filter.Ten…
· 使用引理 `MvPowerSeries.tendsto_antidiagonal`：tendsto_antidiagonal {M S : Type*} [
AddMonoid M] [Finset.HasAntidiagonal M] [NormedRing S] [IsUltrametricDist S] {C 
: M -> Real} (hC : foral…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.prod_add_index'`：prod_add_index' [AddZeroClass M] [CommMonoid N]
 {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a, h a 0 = 1) (h_add : foral
l a b₁ b₂, h …
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
-/
lemma isRestricted.mul [IsUltrametricDist R] (c : σ → ℝ) {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) := by
  classical
  rw [← isRestricted_abs_iff, IsRestricted] at *
  exact tendsto_antidiagonal (by simp [Finsupp.prod_add_index', pow_add]) hf hg

namespace IsRestricted

/-- Restricted power series as an additive subgroup of `MvPowerSeries σ R`. -/
/-
**MvPowerSeries.IsRestricted.addSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSerie
s.IsRestricted`。
形式化陈述：{R : Type u_1} → [inst : NormedRing R] → {σ : Type u_2} → (σ → ℝ) → AddSub
group (MvPowerSeries σ R)
参数：σ → ℝ；MvPowerSeries σ R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.isRestricted.add`：∀ {R : Type u_1} [inst : NormedRing R] {
σ : Type u_2} (c : σ → ℝ) {f g : MvPowerSeries σ R},   MvPowerSeries.IsRestricte
d c f → MvPowerSerie…
· 使用引理 `MvPowerSeries.isRestricted_zero`：isRestricted_zero (c : σ -> Real) : IsR
estricted c (0 : MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.isRestricted.neg`：∀ {R : Type u_1} [inst : NormedRing R] {
σ : Type u_2} (c : σ → ℝ) {f : MvPowerSeries σ R},   MvPowerSeries.IsRestricted 
c f → MvPowerSeries.…

--- 原说明 ---
Restricted power series as an additive subgroup of `MvPowerSeries σ R`.
-/
protected def addSubgroup (c : σ → ℝ) : AddSubgroup (MvPowerSeries σ R) where
  carrier := {f | IsRestricted c f}
  zero_mem' := isRestricted_zero c
  add_mem' := isRestricted.add c
  neg_mem' := isRestricted.neg c

variable [IsUltrametricDist R]

/-- Restricted power series as a subring of `MvPowerSeries σ R`. -/
/-
**MvPowerSeries.IsRestricted.subring** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries.Is
Restricted`。
形式化陈述：{R : Type u_1} → [inst : NormedRing R] → {σ : Type u_2} → [IsUltrametricDi
st R] → (σ → ℝ) → Subring (MvPowerSeries σ R)
参数：σ → ℝ；MvPowerSeries σ R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.isRestricted.mul`：∀ {R : Type u_1} [inst : NormedRing R] {
σ : Type u_2} [IsUltrametricDist R] (c : σ → ℝ) {f g : MvPowerSeries σ R},   MvP
owerSeries.IsRestric…
· 使用引理 `MvPowerSeries.isRestricted_one`：isRestricted_one (c : σ -> Real) : IsRes
tricted c (1 : MvPowerSeries σ R)

--- 原说明 ---
Restricted power series as a subring of `MvPowerSeries σ R`.
-/
protected def subring (c : σ → ℝ) : Subring (MvPowerSeries σ R) where
  __ := IsRestricted.addSubgroup c
  one_mem' := isRestricted_one c
  mul_mem' := isRestricted.mul c

end MvPowerSeries.IsRestricted

