/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yakov Pechersky
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Integral elements over the ring of integers of a valuation

The ring of integers is integrally closed inside the original ring.
-/

public section


universe u v w

namespace Valuation

namespace Integers

section CommRing

variable {R : Type u} {Γ₀ : Type v} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation R Γ₀} {O : Type w} [CommRing O] [Algebra O R] (hv : Integers v O)
include hv

open Polynomial

/-
**Valuation.Integers.isIntegral_iff_v_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuatio
n.Integers`。
形式化陈述：isIntegral_iff_v_le_one {x : R} : IsIntegral O x ↔ v x <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Valuation.Integers.nontrivial_iff`：nontrivial_iff (hv : v.Integers O) : 
Nontrivial O ↔ Nontrivial R
· 使用引理 `Polynomial.natDegree_eq_zero`：natDegree_eq_zero {p : R[X]} : p.natDegree
 = 0 ↔ exists x, C x = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.Monic.ne_zero_of_C`：∀ {R : Type u} [inst : Semiring R] [Nontr
ivial R] {c : R}, (Polynomial.C c).Monic → c ≠ 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Valuation.map_sum_lt`：map_sum_lt {ι : Type*} {s : Finset ι} {f : ι -> R}
 {g : Γ₀} (hg : g != 0) (hf : forall i in s, v (f i) < g) : v (∑ i in s, f i) < 
g
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → 
c < b → c < a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
（共 74 条，此处仅展示前 30 条）
-/
lemma isIntegral_iff_v_le_one {x : R} :
    IsIntegral O x ↔ v x ≤ 1 := by
  nontriviality R
  have : Nontrivial O := hv.nontrivial_iff.mpr inferInstance
  constructor
  · rintro ⟨f, hm, hf⟩
    by_cases hn : f.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hn
      obtain ⟨c, rfl⟩ := hn
      simp [map_eq_zero_iff _ hv.hom_inj, hm.ne_zero_of_C] at hf
    simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
      one_mul, add_eq_zero_iff_eq_neg] at hf
    apply_fun v at hf
    simp only [map_neg, map_pow] at hf
    contrapose! hf
    refine ne_of_lt (v.map_sum_lt ?_ ?_)
    · simp [hn, (hf.trans' (zero_lt_one)).ne']
    · simp only [Finset.mem_range, map_mul, map_pow]
      intro _ hi
      exact mul_lt_of_le_one_of_lt (hv.map_le_one _) <| pow_lt_pow_right₀ hf hi
  · intro h
    obtain ⟨y, rfl⟩ := hv.exists_of_le_one h
    exact ⟨Polynomial.X - .C y, by monicity, by simp⟩
/-
**Valuation.Integers.mem_of_integral** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Intege
rs`。
形式化陈述：mem_of_integral {x : R} (hx : IsIntegral O x) : x in v.integer
参数：hx : IsIntegral O x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Valuation.Integers.isIntegral_iff_v_le_one`：isIntegral_iff_v_le_one {x :
 R} : IsIntegral O x ↔ v x <= 1
-/
theorem mem_of_integral {x : R} (hx : IsIntegral O x) : x ∈ v.integer :=
  hv.isIntegral_iff_v_le_one.mp hx
/-
**Valuation.Integers.integralClosure** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Intege
rs`。
形式化陈述：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRing R] [inst_1 : LinearOrderedCo
mmGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Type w} [inst_2 : CommRing O] [i
nst_3 : Algebra O R], v.Integers O → integralClosure O R = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Valuation.Integers.exists_of_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst 
: CommRing R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀} 
  {O : Type w} [inst_2 : …
· 使用定理 `Valuation.Integers.mem_of_integral`：mem_of_integral {x : R} (hx : IsInte
gral O x) : x in v.integer
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
-/
protected theorem integralClosure : integralClosure O R = ⊥ :=
  bot_unique fun _ hr =>
    let ⟨x, hx⟩ := hv.3 (hv.mem_of_integral hr)
    Algebra.mem_bot.2 ⟨x, hx⟩

end CommRing

section FractionField

variable {K : Type u} {Γ₀ : Type v} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation K Γ₀} {O : Type w} [CommRing O]
variable [Algebra O K]
variable (hv : Integers v O)

include hv in
/-
**Valuation.Integers.isIntegrallyClosed** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Int
egers`。
形式化陈述：isIntegrallyClosed : IsIntegrallyClosed O
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integers.isFractionRing`：∀ {𝒪 : Type u} {K : Type v} {Γ : Type
 w} [inst : CommRing 𝒪] [inst_1 : Field K] [inst_2 : Algebra 𝒪 K]   [inst_3 : Li
nearOrderedCommGroupWit…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegrallyClosed.integralClosure_eq_bot_iff`：integralClosure_eq_bot_if
f : integralClosure R K = ⊥ ↔ IsIntegrallyClosed R
· 使用定理 `Valuation.Integers.integralClosure`：∀ {R : Type u} {Γ₀ : Type v} [inst :
 CommRing R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}  
 {O : Type w} [inst_2 : …
-/
theorem isIntegrallyClosed : IsIntegrallyClosed O := by
  have : IsFractionRing O K := hv.isFractionRing
  exact
    (IsIntegrallyClosed.integralClosure_eq_bot_iff K).mp (Valuation.Integers.integralClosure hv)
/-
**Valuation.Integers.isIntegrallyClosed_integers** 是 Mathlib 中的一个实例，位于命名空间 `Valu
ation.Integers`。
形式化陈述：isIntegrallyClosed_integers (v : Valuation K Γ₀) : IsIntegrallyClosed v.in
teger
参数：v : Valuation K Γ₀。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integers.isIntegrallyClosed`：isIntegrallyClosed : IsIntegrally
Closed O
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
instance isIntegrallyClosed_integers (v : Valuation K Γ₀) :
    IsIntegrallyClosed v.integer :=
  (Valuation.integer.integers v).isIntegrallyClosed

end FractionField

end Integers

end Valuation

