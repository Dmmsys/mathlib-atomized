/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology

import Mathlib.Combinatorics.Enumerative.Pentagonal.Ring
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Pentagonal number theorem for power series

This file proves the pentagonal number theorem for power series:

$$ \prod_{n = 0}^{\infty} (1 - x^{n + 1}) = \sum_{k=-\infty}^{\infty} (-1)^k x^{a_k} $$

where $a_k = k(3k - 1)/2$ are the pentagonal numbers. We state the theorem in two parts by
introducing the intermediate power series `PowerSeries.pentagonalSeries`, whose coefficients are
defined using pentagonal numbers. We then show that this series is equal to both sides.

## Main theorems

* `PowerSeries.WithPiTopology.hasProd_one_sub_X_pow`: `PowerSeries.pentagonalSeries` is equal to
  infinite product on the left-hand side of the formula.
* `PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq` restates the left-hand side without requiring
  topology.
* `PowerSeries.WithPiTopology.hasSum_pentagonalSeries`: `PowerSeries.pentagonalSeries` is equal to
  the infinite sum on the right-hand side of the formula.
* `PowerSeries.coeff_pentagonalSeries` restates the right-hand side without requiring topology.
-/

open Filter PowerSeries WithPiTopology Topology
variable (R : Type*) [CommRing R]

namespace Pentagonal
-- private auxiliary lemma

/-
**Pentagonal.tendsto_order_pow_mul_prod_one_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 `P
entagonal`。
形式化陈述：tendsto_order_pow_mul_prod_one_sub_pow (k : Nat) : Tendsto (fun n => (X ^ 
((k + 1) * n) * ∏ i in Finset.range (n + 1), (1 - X ^ (k + i + 1)) : R⟦X⟧).order
) atTop (𝓝 ⊤)
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_order_pow_mul_prod_one_sub_pow (k : ℕ) :
    Tendsto (fun n ↦ (X ^ ((k + 1) * n) *
      ∏ i ∈ Finset.range (n + 1), (1 - X ^ (k + i + 1)) : R⟦X⟧).order) atTop (𝓝 ⊤) := by
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ eventually_atTop.mpr ⟨n + 1, ?_⟩
  intro m hm
  grw [← le_order_mul, order_X_pow]
  refine lt_add_of_lt_of_nonneg ?_ (by simp)
  norm_cast
  grind
/-
**Pentagonal.tendsto_order_neg_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Pentagonal`。
形式化陈述：tendsto_order_neg_X_pow (k : Nat) : Tendsto (fun i => (-(X : R⟦X⟧) ^ (i + 
k + 1)).order) atTop (𝓝 ⊤)
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_order_neg_X_pow (k : ℕ) :
    Tendsto (fun i ↦ (-(X : R⟦X⟧) ^ (i + k + 1)).order) atTop (𝓝 ⊤) := by
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  simp_rw [order_neg, order_X_pow, add_assoc]
  exact ENat.tendsto_natCast_nhds_top.comp (tendsto_add_atTop_nat _)

variable [TopologicalSpace R]
/-
**Pentagonal.summable_pow_mul_prod_one_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 `Pentag
onal`。
形式化陈述：summable_pow_mul_prod_one_sub_pow (k : Nat) : Summable fun n => (X ^ ((k +
 1) * n) * ∏ i in Finset.range (n + 1), (1 - X ^ (k + i + 1)) : R⟦X⟧)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem summable_pow_mul_prod_one_sub_pow (k : ℕ) :
    Summable
      fun n ↦ (X ^ ((k + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - X ^ (k + i + 1)) : R⟦X⟧) :=
  summable_of_tendsto_order_atTop_nhds_top R (tendsto_order_pow_mul_prod_one_sub_pow R k)
/-
**Pentagonal.multipliable_one_sub_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Pentagonal`。
形式化陈述：multipliable_one_sub_X_pow (k : Nat) : Multipliable fun n => (1 : R⟦X⟧) - 
X ^ (n + k + 1)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multipliable_one_sub_X_pow (k : ℕ) : Multipliable fun n ↦ (1 : R⟦X⟧) - X ^ (n + k + 1) := by
  simpa [sub_eq_add_neg] using
    multipliable_one_add_of_tendsto_order_atTop_nhds_top R (tendsto_order_neg_X_pow R k)

end Pentagonal

public section Public
namespace PowerSeries

open Classical in
/-- The power series $\sum_{k=-\infty}^{\infty}(-1)^k x^{k * (3k - 1) / 2}$. -/
noncomputable
/-
**PowerSeries.pentagonalSeries** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：pentagonalSeries : R⟦X⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pentagonalSeries : R⟦X⟧ :=
  .mk fun n ↦ if h : ∃ k, pentagonal k = n then
    Int.negOnePow h.choose
  else
    0
/-
**PowerSeries.coeff_pentagonalSeries_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSer
ies`。
形式化陈述：coeff_pentagonalSeries_eq_zero {n : Nat} (h : n ∉ Set.range pentagonal) : 
(pentagonalSeries R).coeff n = 0
参数：h : n ∉ Set.range pentagonal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
theorem coeff_pentagonalSeries_eq_zero {n : ℕ} (h : n ∉ Set.range pentagonal) :
    (pentagonalSeries R).coeff n = 0 := dif_neg <| by simpa using h

@[simp]
/-
**PowerSeries.coeff_pentagonalSeries_pentagonal** 是 Mathlib 中的一个定理，位于命名空间 `Power
Series`。
形式化陈述：coeff_pentagonalSeries_pentagonal (k : Int) : (pentagonalSeries R).coeff (
pentagonal k) = Int.negOnePow k
参数：k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_pentagonalSeries_pentagonal (k : ℤ) :
    (pentagonalSeries R).coeff (pentagonal k) = Int.negOnePow k := by
  simp [pentagonalSeries]

@[simp]
/-
**PowerSeries.coeff_pentagonalSeries_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Powe
rSeries`。
形式化陈述：coeff_pentagonalSeries_eq_zero_iff [Nontrivial R] {n : Nat} : (pentagonalS
eries R).coeff n = 0 ↔ n ∉ Set.range pentagonal
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_pentagonalSeries_eq_zero_iff [Nontrivial R] {n : ℕ} :
    (pentagonalSeries R).coeff n = 0 ↔ n ∉ Set.range pentagonal := by
  grind [pentagonalSeries, coeff_mk, neg_one_pow_ne_zero, Int.coe_negOnePow]

namespace WithPiTopology
variable [TopologicalSpace R]

/-- `PowerSeries.pentagonalSeries` as an infinite sum over integers -/
/-
**PowerSeries.WithPiTopology.hasSum_pentagonalSeries** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries.WithPiTopology`。
形式化陈述：hasSum_pentagonalSeries : HasSum (fun k : Int => (Int.negOnePow k : R⟦X⟧) 
* X ^ pentagonal k) (pentagonalSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : 
α} {g : γ → β}, Fun…
· 使用定理 `pentagonal_injective`：pentagonal_injective : Function.Injective pentagon
al
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.coeff_pentagonalSeries_eq_zero`：coeff_pentagonalSeries_eq_ze
ro {n : Nat} (h : n ∉ Set.range pentagonal) : (pentagonalSeries R).coeff n = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `PowerSeries.monomial_eq_C_mul_X_pow`：monomial_eq_C_mul_X_pow (r : R) (n 
: Nat) : monomial n r = C r * X ^ n
· 使用定理 `PowerSeries.hasSum_of_monomials_self`：hasSum_of_monomials_self (f : Powe
rSeries R) : HasSum (fun d : Nat => monomial d (coeff d f)) f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用定理 `PowerSeries.coeff_pentagonalSeries_pentagonal`：coeff_pentagonalSeries_pe
ntagonal (k : Int) : (pentagonalSeries R).coeff (pentagonal k) = Int.negOnePow k
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…

--- 原说明 ---
`PowerSeries.pentagonalSeries` as an infinite sum over integers
-/
theorem hasSum_pentagonalSeries :
    HasSum (fun k : ℤ ↦ (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal k) (pentagonalSeries R) := by
  suffices HasSum ((fun n ↦ C ((pentagonalSeries R).coeff n) * X ^ n) ∘ pentagonal)
      (pentagonalSeries R) by
    convert this
    simp
  rw [pentagonal_injective.hasSum_iff fun n hn ↦ by simp [coeff_pentagonalSeries_eq_zero R hn]]
  simpa [monomial_eq_C_mul_X_pow] using (pentagonalSeries R).hasSum_of_monomials_self
/-
**PowerSeries.WithPiTopology.pentagonalSeries_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 
`PowerSeries.WithPiTopology`。
形式化陈述：pentagonalSeries_eq_tsum [T2Space R] : pentagonalSeries R = ∑' k, (Int.neg
OnePow k : R⟦X⟧) * X ^ pentagonal k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `PowerSeries.WithPiTopology.hasSum_pentagonalSeries`：hasSum_pentagonalSer
ies : HasSum (fun k : Int => (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal k) (penta
gonalSeries R)
-/
theorem pentagonalSeries_eq_tsum [T2Space R] :
    pentagonalSeries R = ∑' k, (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal k :=
  (hasSum_pentagonalSeries R).tsum_eq.symm

/-- `PowerSeries.pentagonalSeries` as an infinite sum over natural numbers. In this version, terms
are ordered by strictly increasing exponent `pentagonal k` for `k = 0, 1, -1, 2, -2, 3, ...`,
and every two terms are grouped together. -/
/-
**PowerSeries.WithPiTopology.hasSum_pow_pentagonal_sub_pentagonalSeries** 是 Math
lib 中的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：hasSum_pow_pentagonal_sub_pentagonalSeries : HasSum (fun k : Nat => (-1) ^
 k * (X ^ pentagonal (-k) - X ^ pentagonal (k + 1))) (pentagonalSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.WithPiTopology.hasSum_pentagonalSeries`：hasSum_pentagonalSer
ies : HasSum (fun k : Int => (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal k) (penta
gonalSeries R)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.negOnePow_add`：negOnePow_add (n₁ n₂ : Int) : (n₁ + n₂).negOnePow = n
₁.negOnePow * n₂.negOnePow
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Int.negOnePow_neg`：negOnePow_neg (n : Int) : (-n).negOnePow = n.negOnePo
w
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
`PowerSeries.pentagonalSeries` as an infinite sum over natural numbers. In this 
version, terms
are ordered by strictly increasing exponent `pentagonal k` for `k = 0, 1, -1, 2,
 -2, 3, ...`,
and every two terms are grouped together.
-/
theorem hasSum_pow_pentagonal_sub_pentagonalSeries :
    HasSum (fun k : ℕ ↦ (-1) ^ k * (X ^ pentagonal (-k) - X ^ pentagonal (k + 1)))
      (pentagonalSeries R) := by
  have h := hasSum_pentagonalSeries R
  rw [← neg_injective.hasSum_iff (fun x hx ↦ by absurd hx; use -x; simp)] at h
  convert h.nat_add_neg_add_one using 2 with k
  simp_rw [Function.comp_apply, neg_neg, Int.negOnePow_add]
  simp
  ring
/-
**PowerSeries.WithPiTopology.pentagonalSeries_eq_tsum_pow_pentagonal_sub** 是 Mat
hlib 中的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：pentagonalSeries_eq_tsum_pow_pentagonal_sub [T2Space R] : pentagonalSeries
 R = ∑' (k : Nat), (-1) ^ k * (X ^ pentagonal (-k) - X ^ pentagonal (k + 1))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `PowerSeries.WithPiTopology.hasSum_pow_pentagonal_sub_pentagonalSeries`：h
asSum_pow_pentagonal_sub_pentagonalSeries : HasSum (fun k : Nat => (-1) ^ k * (X
 ^ pentagonal (-k) - X ^ pentagonal (k + 1))) (pentagonalSe…
-/
theorem pentagonalSeries_eq_tsum_pow_pentagonal_sub [T2Space R] :
    pentagonalSeries R = ∑' (k : ℕ), (-1) ^ k * (X ^ pentagonal (-k) - X ^ pentagonal (k + 1)) :=
  (hasSum_pow_pentagonal_sub_pentagonalSeries R).tsum_eq.symm

/-- See the public version `PowerSeries.WithPiTopology.tprod_one_sub_X_pow` that removes
`IsTopologicalRing`. -/
/-
**PowerSeries.WithPiTopology.tprod_one_sub_X_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Pow
erSeries.WithPiTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See the public version `PowerSeries.WithPiTopology.tprod_one_sub_X_pow` that rem
oves
`IsTopologicalRing`.
-/
private theorem tprod_one_sub_X_pow' [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentagonalSeries R := by
  nontriviality R
  rw [pentagonalSeries_eq_tsum_pow_pentagonal_sub]
  refine Pentagonal.tprod_one_sub_pow ?_ ?_ ?_ ?_ ?_
  · rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto]
    refine fun d ↦ tendsto_atTop_of_eventually_const fun i (hi : i ≥ d + 1) ↦ ?_
    grind
  · exact Pentagonal.summable_pow_mul_prod_one_sub_pow R
  · exact Pentagonal.multipliable_one_sub_X_pow R
  · exact (hasSum_pow_pentagonal_sub_pentagonalSeries R).summable
  · rw [tendsto_iff_coeff_tendsto]
    refine fun n ↦ tendsto_atTop_of_eventually_const fun k (hk : k ≥ n) ↦ ?_
    rw [map_zero]
    apply coeff_of_lt_order
    grw [← le_order_mul, ← le_order_mul]
    refine (lt_add_of_lt_of_nonneg (lt_add_of_nonneg_of_lt (by simp) ?_) (by simp))
    rw [order_X_pow, Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
    apply Nat.mul_le_mul <;> linarith

end WithPiTopology

/-- **Pentagonal number theorem** for power series, expressed as the statement that the coefficients
of the product `∏ n, 1 - X ^ (n + 1)` are eventually constants as `(pentagonalSeries R).coeff`. -/
/-
**PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries`。
形式化陈述：coeff_prod_one_sub_X_pow_eventually_eq (n : Nat) : forallᶠ s in atTop, (∏ 
n in s, (1 - X ^ (n + 1) : R⟦X⟧)).coeff n = (pentagonalSeries R).coeff n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `PowerSeries.WithPiTopology.multipliable_one_sub_X_pow`：multipliable_one_
sub_X_pow : Multipliable fun n => (1 : R⟦X⟧) - X ^ (n + 1)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SummationFilter.unconditional_filter`：∀ (β : Type u_2), (SummationFilter
.unconditional β).filter = Filter.atTop
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`：tendsto_iff_coeff_
tendsto [Semiring R] {ι : Type*} (f : ι -> PowerSeries R) (u : Filter ι) (g : Po
werSeries R) : Tendsto f u (nhds g) ↔ fora…
· 使用定理 `HasProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [ins
t_1 : TopologicalSpace α] (f : β → α) (a : α)   (L : SummationFilter β), HasProd
 f…
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries.0.Powe
rSeries.WithPiTopology.tprod_one_sub_X_pow'`：∀ (R : Type u_1) [inst : CommRing R
] [inst_1 : TopologicalSpace R] [IsTopologicalRing R] [T2Space R],   ∏' (n : ℕ),
 (1 - PowerSeries.X ^ (n …
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R

--- 原说明 ---
**Pentagonal number theorem** for power series, expressed as the statement that 
the coefficients
of the product `∏ n, 1 - X ^ (n + 1)` are eventually constants as `(pentagonalSe
ries R).coeff`.
-/
theorem coeff_prod_one_sub_X_pow_eventually_eq (n : ℕ) :
    ∀ᶠ s in atTop, (∏ n ∈ s, (1 - X ^ (n + 1) : R⟦X⟧)).coeff n = (pentagonalSeries R).coeff n := by
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have h := (multipliable_one_sub_X_pow R).hasProd
  rw [tprod_one_sub_X_pow' R, HasProd, tendsto_iff_coeff_tendsto] at h
  simpa using h n

namespace WithPiTopology
variable [TopologicalSpace R]

/-- **Pentagonal number theorem** for power series, expressed as an infinite product. See also
`PowerSeries.WithPiTopology.hasSum_pentagonalSeries` that expresses `pentagonalSeries` as an
infinite sum. -/
/-
**PowerSeries.WithPiTopology.hasProd_one_sub_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Po
werSeries.WithPiTopology`。
形式化陈述：hasProd_one_sub_X_pow : HasProd (fun n => (1 - X ^ (n + 1) : R⟦X⟧)) (penta
gonalSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [ins
t_1 : TopologicalSpace α] (f : β → α) (a : α)   (L : SummationFilter β), HasProd
 f…
· 使用定理 `PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`：tendsto_iff_coeff_
tendsto [Semiring R] {ι : Type*} (f : ι -> PowerSeries R) (u : Filter ι) (g : Po
werSeries R) : Tendsto f u (nhds g) ↔ fora…
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SummationFilter.unconditional_filter`：∀ (β : Type u_2), (SummationFilter
.unconditional β).filter = Filter.atTop
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq`：coeff_prod_one_sub_X
_pow_eventually_eq (n : Nat) : forallᶠ s in atTop, (∏ n in s, (1 - X ^ (n + 1) :
 R⟦X⟧)).coeff n = (pentagonalSeries R).c…

--- 原说明 ---
**Pentagonal number theorem** for power series, expressed as an infinite product
. See also
`PowerSeries.WithPiTopology.hasSum_pentagonalSeries` that expresses `pentagonalS
eries` as an
infinite sum.
-/
theorem hasProd_one_sub_X_pow :
    HasProd (fun n ↦ (1 - X ^ (n + 1) : R⟦X⟧)) (pentagonalSeries R) := by
  rw [HasProd, tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_nhds_of_eventually_eq
  simpa using coeff_prod_one_sub_X_pow_eventually_eq R n
/-
**PowerSeries.WithPiTopology.tprod_one_sub_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Powe
rSeries.WithPiTopology`。
形式化陈述：tprod_one_sub_X_pow [T2Space R] : ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentago
nalSeries R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `PowerSeries.WithPiTopology.hasProd_one_sub_X_pow`：hasProd_one_sub_X_pow 
: HasProd (fun n => (1 - X ^ (n + 1) : R⟦X⟧)) (pentagonalSeries R)
-/
theorem tprod_one_sub_X_pow [T2Space R] : ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentagonalSeries R :=
  (hasProd_one_sub_X_pow R).tprod_eq

end WithPiTopology
end PowerSeries
end Public

