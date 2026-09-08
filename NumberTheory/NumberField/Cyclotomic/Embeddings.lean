/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Cyclotomic extensions of `ℚ` are totally complex number fields.

We prove that cyclotomic extensions of `ℚ` are totally complex, meaning that
`NrRealPlaces K = 0` if `IsCyclotomicExtension {n} ℚ K` and `2 < n`.

## Main results
* `nrRealPlaces_eq_zero`: If `K` is an `n`-th cyclotomic extension of `ℚ`, where `2 < n`,
  then there are no real places of `K`.
-/

public section

universe u

namespace IsCyclotomicExtension.Rat

open NumberField InfinitePlace Module Complex Nat Polynomial

variable {n : ℕ} [NeZero n] (K : Type u) [Field K] [CharZero K]

/-- If `K` is an `n`-th cyclotomic extension of `ℚ`, where `2 < n`, then there are no real places
of `K`. -/
/-
**IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsCy
clotomicExtension.Rat`。
形式化陈述：nrRealPlaces_eq_zero [IsCyclotomicExtension {n} Rat K] (hn : 2 < n) : have
I
参数：hn : 2 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
`：nrRealPlaces_eq_zero_of_two_lt (hk : 2 < k) (hζ : IsPrimitiveRoot ζ k) : Numbe
rField.InfinitePlace.nrRealPlaces K = 0
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n

--- 原说明 ---
If `K` is an `n`-th cyclotomic extension of `ℚ`, where `2 < n`, then there are n
o real places
of `K`.
-/
theorem nrRealPlaces_eq_zero [IsCyclotomicExtension {n} ℚ K] (hn : 2 < n) :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    nrRealPlaces K = 0 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  apply (IsCyclotomicExtension.zeta_spec n ℚ K).nrRealPlaces_eq_zero_of_two_lt hn
/-
**IsCyclotomicExtension.Rat.isTotallyComplex** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclot
omicExtension.Rat`。
形式化陈述：isTotallyComplex [IsCyclotomicExtension {n} Rat K] (hn : 2 < n) : IsTotall
yComplex K
参数：hn : 2 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.nrRealPlaces_eq_zero_iff`：nrRealPlaces_eq_zero_iff [NumberFi
eld K] : nrRealPlaces K = 0 ↔ IsTotallyComplex K
· 使用定理 `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`：nrRealPlaces_eq_zero [Is
CyclotomicExtension {n} Rat K] (hn : 2 < n) : haveI
-/
theorem isTotallyComplex [IsCyclotomicExtension {n} ℚ K] (hn : 2 < n) :
    IsTotallyComplex K := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  exact nrRealPlaces_eq_zero_iff.mp <| nrRealPlaces_eq_zero K hn

variable (n)

/-- If `K` is an `n`-th cyclotomic extension of `ℚ`, then there are `φ n / n` complex places
of `K`. Note that this uses `1 / 2 = 0` in the cases `n = 1, 2`. -/
/-
**IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two** 是 Mathlib 中的一个定
理，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：nrComplexPlaces_eq_totient_div_two [h : IsCyclotomicExtension {n} Rat K] :
 haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.totient_even`：totient_even {n : Nat} (hn : 2 < n) : Even n.totient
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`：card_add_two_mu
l_card_eq_rank : nrRealPlaces K + 2 * nrComplexPlaces K = finrank Rat K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_right_inj`：∀ {a b c : ℕ}, a ≠ 0 → (a * b = a * c ↔ b = c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `IsCyclotomicExtension.finrank`：finrank (hirr : Irreducible (cyclotomic n
 K)) : finrank K L = n.totient
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`：nrRealPlaces_eq_zero [Is
CyclotomicExtension {n} Rat K] (hn : 2 < n) : haveI
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Nat.totient_two`：totient_two : φ 2 = 1
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `K` is an `n`-th cyclotomic extension of `ℚ`, then there are `φ n / n` comple
x places
of `K`. Note that this uses `1 / 2 = 0` in the cases `n = 1, 2`.
-/
theorem nrComplexPlaces_eq_totient_div_two [h : IsCyclotomicExtension {n} ℚ K] :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    nrComplexPlaces K = φ n / 2 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  by_cases hn : 2 < n
  · obtain ⟨k, hk : φ n = k + k⟩ := totient_even hn
    have key := card_add_two_mul_card_eq_rank K
    rw [nrRealPlaces_eq_zero K hn, zero_add, IsCyclotomicExtension.finrank (n := n) K
      (cyclotomic.irreducible_rat (NeZero.pos _)), hk, ← two_mul,
      Nat.mul_right_inj (by simp)] at key
    simp [hk, key, ← two_mul]
  · have : φ n = 1 := by
      by_cases h1 : 1 < n
      · convert! totient_two
        exact (eq_of_le_of_not_lt (succ_le_of_lt h1) hn).symm
      · convert! totient_one
        exact eq_of_le_of_not_lt (not_lt.mp h1) (by simp [NeZero.ne _])
    rw [this]
    apply nrComplexPlaces_eq_zero_of_finrank_eq_one
    rw [IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat (NeZero.pos n)), this]

end IsCyclotomicExtension.Rat

