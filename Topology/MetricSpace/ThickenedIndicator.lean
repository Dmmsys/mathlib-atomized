/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Data.ENNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Thickened indicators

This file is about thickened indicators of sets in (pseudo e)metric spaces. For a decreasing
sequence of thickening radii tending to 0, the thickened indicators of a closed set form a
decreasing pointwise converging approximation of the indicator function of the set, where the
members of the approximating sequence are nonnegative bounded continuous functions.

## Main definitions

* `thickenedIndicatorAux δ E`: The `δ`-thickened indicator of a set `E` as an
  unbundled `ℝ≥0∞`-valued function.
* `thickenedIndicator δ E`: The `δ`-thickened indicator of a set `E` as a bundled
  bounded continuous `ℝ≥0`-valued function.

## Main results

* For a sequence of thickening radii tending to 0, the `δ`-thickened indicators of a set `E` tend
  pointwise to the indicator of `closure E`.
  - `thickenedIndicatorAux_tendsto_indicator_closure`: The version is for the
    unbundled `ℝ≥0∞`-valued functions.
  - `thickenedIndicator_tendsto_indicator_closure`: The version is for the bundled `ℝ≥0`-valued
    bounded continuous functions.

-/

@[expose] public section

open NNReal ENNReal Topology BoundedContinuousFunction Set Metric Filter

noncomputable section thickenedIndicator

variable {α : Type*} [PseudoEMetricSpace α]

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `infEDist _ E`.

`thickenedIndicatorAux` is the unbundled `ℝ≥0∞`-valued function. See `thickenedIndicator`
for the (bundled) bounded continuous function with `ℝ≥0`-values. -/
/-
**thickenedIndicatorAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux (δ : Real) (E : Set α) : α -> Real>=0∞
参数：δ : Real；E : Set α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `infEDist _ E`.

`thickenedIndicatorAux` is the unbundled `ℝ≥0∞`-valued function. See `thickenedI
ndicator`
for the (bundled) bounded continuous function with `ℝ≥0`-values.
-/
def thickenedIndicatorAux (δ : ℝ) (E : Set α) : α → ℝ≥0∞ :=
  fun x : α => (1 : ℝ≥0∞) - infEDist x E / ENNReal.ofReal δ
/-
**continuous_thickenedIndicatorAux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_thickenedIndicatorAux {δ : Real} (δ_pos : 0 < δ) (E : Set α) : 
Continuous (thickenedIndicatorAux δ E)
参数：δ_pos : 0 < δ；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ENNReal.continuous_nnreal_sub`：continuous_nnreal_sub {a : Real>=0} : Con
tinuous fun x : Real>=0∞ => (a : Real>=0∞) - x
· 使用定理 `ENNReal.continuous_div_const`：∀ (c : ENNReal), c ≠ 0 → Continuous fun x 
=> x / c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Metric.continuous_infEDist`：continuous_infEDist : Continuous fun x => in
fEDist x s
-/
theorem continuous_thickenedIndicatorAux {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    Continuous (thickenedIndicatorAux δ E) := by
  unfold thickenedIndicatorAux
  let f := fun x : α => (⟨1, infEDist x E / ENNReal.ofReal δ⟩ : ℝ≥0 × ℝ≥0∞)
  let sub := fun p : ℝ≥0 × ℝ≥0∞ => (p.1 : ℝ≥0∞) - p.2
  rw [show (fun x : α => (1 : ℝ≥0∞) - infEDist x E / ENNReal.ofReal δ) = sub ∘ f by rfl]
  apply (@ENNReal.continuous_nnreal_sub 1).comp
  apply (ENNReal.continuous_div_const (ENNReal.ofReal δ) _).comp continuous_infEDist
  norm_num [δ_pos]
/-
**thickenedIndicatorAux_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux_le_one (δ : Real) (E : Set α) (x : α) : thickenedInd
icatorAux δ E x <= 1
参数：δ : Real；E : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
theorem thickenedIndicatorAux_le_one (δ : ℝ) (E : Set α) (x : α) :
    thickenedIndicatorAux δ E x ≤ 1 := by
  apply tsub_le_self (α := ℝ≥0∞)

@[aesop safe (rule_sets := [finiteness])]
/-
**thickenedIndicatorAux_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux_lt_top {δ : Real} {E : Set α} {x : α} : thickenedInd
icatorAux δ E x < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `thickenedIndicatorAux_le_one`：thickenedIndicatorAux_le_one (δ : Real) (E
 : Set α) (x : α) : thickenedIndicatorAux δ E x <= 1
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
-/
theorem thickenedIndicatorAux_lt_top {δ : ℝ} {E : Set α} {x : α} :
    thickenedIndicatorAux δ E x < ∞ :=
  lt_of_le_of_lt (thickenedIndicatorAux_le_one _ _ _) one_lt_top
/-
**thickenedIndicatorAux_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux_closure_eq (δ : Real) (E : Set α) : thickenedIndicat
orAux δ (closure E) = thickenedIndicatorAux δ E
参数：δ : Real；E : Set α。
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
· 使用定理 `Metric.infEDist_closure`：infEDist_closure : infEDist x (closure s) = inf
EDist x s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem thickenedIndicatorAux_closure_eq (δ : ℝ) (E : Set α) :
    thickenedIndicatorAux δ (closure E) = thickenedIndicatorAux δ E := by
  simp +unfoldPartialApp only [thickenedIndicatorAux, infEDist_closure]
/-
**thickenedIndicatorAux_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux_one (δ : Real) (E : Set α) {x : α} (x_in_E : x in E)
 : thickenedIndicatorAux δ E x = 1
参数：δ : Real；E : Set α；x_in_E : x in E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_zero_of_mem`：infEDist_zero_of_mem (h : x in s) : infEDis
t x s = 0
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem thickenedIndicatorAux_one (δ : ℝ) (E : Set α) {x : α} (x_in_E : x ∈ E) :
    thickenedIndicatorAux δ E x = 1 := by
  simp [thickenedIndicatorAux, infEDist_zero_of_mem x_in_E, tsub_zero]
/-
**thickenedIndicatorAux_one_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux_one_of_mem_closure (δ : Real) (E : Set α) {x : α} (x
_mem : x in closure E) : thickenedIndicatorAux δ E x = 1
参数：δ : Real；E : Set α；x_mem : x in closure E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `thickenedIndicatorAux_closure_eq`：thickenedIndicatorAux_closure_eq (δ : 
Real) (E : Set α) : thickenedIndicatorAux δ (closure E) = thickenedIndicatorAux 
δ E
· 使用定理 `thickenedIndicatorAux_one`：thickenedIndicatorAux_one (δ : Real) (E : Set
 α) {x : α} (x_in_E : x in E) : thickenedIndicatorAux δ E x = 1
-/
theorem thickenedIndicatorAux_one_of_mem_closure (δ : ℝ) (E : Set α) {x : α}
    (x_mem : x ∈ closure E) : thickenedIndicatorAux δ E x = 1 := by
  rw [← thickenedIndicatorAux_closure_eq, thickenedIndicatorAux_one δ (closure E) x_mem]
/-
**thickenedIndicatorAux_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux_zero {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α} 
(x_out : x ∉ thickening δ E) : thickenedIndicatorAux δ E x = 0
参数：δ_pos : 0 < δ；E : Set α；x_out : x ∉ thickening δ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `tsub_le_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemi
group α] [inst_2 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b 
→ …
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ENNReal.div_le_div`：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Metric.thickening.eq_1`：∀ {α : Type u} [inst : PseudoEMetricSpace α] (δ 
: ℝ) (E : Set α),   Metric.thickening δ E = {x | Metric.infEDist x E < ENNReal.o
fReal δ}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem thickenedIndicatorAux_zero {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_out : x ∉ thickening δ E) : thickenedIndicatorAux δ E x = 0 := by
  rw [thickening, mem_ofPred_eq, not_lt] at x_out
  unfold thickenedIndicatorAux
  apply le_antisymm _ bot_le
  have key := tsub_le_tsub
    (@rfl _ (1 : ℝ≥0∞)).le (ENNReal.div_le_div x_out (@rfl _ (ENNReal.ofReal δ : ℝ≥0∞)).le)
  rw [ENNReal.div_self (ne_of_gt (ENNReal.ofReal_pos.mpr δ_pos)) ofReal_ne_top] at key
  simpa [tsub_self] using key
/-
**thickenedIndicatorAux_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α) : t
hickenedIndicatorAux δ₁ E <= thickenedIndicatorAux δ₂ E
参数：hle : δ₁ <= δ₂；E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_le_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemi
group α] [inst_2 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b 
→ …
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ENNReal.div_le_div`：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
-/
theorem thickenedIndicatorAux_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickenedIndicatorAux δ₁ E ≤ thickenedIndicatorAux δ₂ E :=
  fun _ => tsub_le_tsub (@rfl ℝ≥0∞ 1).le (ENNReal.div_le_div rfl.le (ofReal_le_ofReal hle))
/-
**indicator_le_thickenedIndicatorAux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indicator_le_thickenedIndicatorAux (δ : Real) (E : Set α) : (E.indicator f
un _ => (1 : Real>=0∞)) <= thickenedIndicatorAux δ E
参数：δ : Real；E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `thickenedIndicatorAux_one`：thickenedIndicatorAux_one (δ : Real) (E : Set
 α) {x : α} (x_in_E : x in E) : thickenedIndicatorAux δ E x = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem indicator_le_thickenedIndicatorAux (δ : ℝ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0∞)) ≤ thickenedIndicatorAux δ E := by
  intro a
  by_cases h : a ∈ E
  · simp only [h, indicator_of_mem, thickenedIndicatorAux_one δ E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]
/-
**thickenedIndicatorAux_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux_subset (δ : Real) {E₁ E₂ : Set α} (subset : E₁ subse
teq E₂) : thickenedIndicatorAux δ E₁ <= thickenedIndicatorAux δ E₂
参数：δ : Real；subset : E₁ subseteq E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_le_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemi
group α] [inst_2 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b 
→ …
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ENNReal.div_le_div`：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
· 使用定理 `Metric.infEDist_anti`：infEDist_anti (h : s subseteq t) : infEDist x t <=
 infEDist x s
-/
theorem thickenedIndicatorAux_subset (δ : ℝ) {E₁ E₂ : Set α} (subset : E₁ ⊆ E₂) :
    thickenedIndicatorAux δ E₁ ≤ thickenedIndicatorAux δ E₂ :=
  fun _ => tsub_le_tsub (@rfl ℝ≥0∞ 1).le (ENNReal.div_le_div (infEDist_anti subset) rfl.le)
/-
**thickenedIndicatorAux_mono_infEDist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux_mono_infEDist (δ : Real) {E : Set α} {x y : α} (h : 
infEDist x E <= infEDist y E) : thickenedIndicatorAux δ E y <= thickenedIndicato
rAux δ E x
参数：δ : Real；h : infEDist x E <= infEDist y E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.sub_le_sub_iff_left`：sub_le_sub_iff_left (h : c <= a) (h' : a !=
 ∞) : (a - b <= a - c) ↔ c <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.div_le_div`：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma thickenedIndicatorAux_mono_infEDist (δ : ℝ) {E : Set α} {x y : α}
    (h : infEDist x E ≤ infEDist y E) :
    thickenedIndicatorAux δ E y ≤ thickenedIndicatorAux δ E x := by
  simp only [thickenedIndicatorAux]
  rcases le_total (infEDist x E / ENNReal.ofReal δ) 1 with hle | hle
  · rw [ENNReal.sub_le_sub_iff_left hle (by simp)]
    gcongr
  · rw [tsub_eq_zero_of_le hle, tsub_eq_zero_of_le]
    exact hle.trans (by gcongr)

@[deprecated (since := "2026-01-08")]
alias thickenedIndicatorAux_mono_infEdist := thickenedIndicatorAux_mono_infEDist

/-- As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in α) tends
pointwise (i.e., w.r.t. the product topology on `α → ℝ≥0∞`) to the indicator function of the
closure of E.

This statement is for the unbundled `ℝ≥0∞`-valued functions `thickenedIndicatorAux δ E`, see
`thickenedIndicator_tendsto_indicator_closure` for the version for bundled `ℝ≥0`-valued
bounded continuous functions. -/
/-
**thickenedIndicatorAux_tendsto_indicator_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicatorAux_tendsto_indicator_closure {δseq : Nat -> Real} (δseq
_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) : Tendsto (fun n => thickenedIndica
torAux (δseq n) E) atTop (𝓝 (indicator (closure E) fun _ => (1 : Real>=0∞)))
参数：δseq_lim : Tendsto δseq atTop (𝓝 0)；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `thickenedIndicatorAux_one_of_mem_closure`：thickenedIndicatorAux_one_of_m
em_closure (δ : Real) (E : Set α) {x : α} (x_mem : x in closure E) : thickenedIn
dicatorAux δ E x = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Metric.exists_real_pos_lt_infEDist_of_notMem_closure`：exists_real_pos_lt
_infEDist_of_notMem_closure {x : α} {E : Set α} (h : x ∉ closure E) : exists ε :
 Real, 0 < ε ∧ ENNReal.ofReal ε < infEDist…
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `thickenedIndicatorAux_mono`：thickenedIndicatorAux_mono {δ₁ δ₂ : Real} (h
le : δ₁ <= δ₂) (E : Set α) : thickenedIndicatorAux δ₁ E <= thickenedIndicatorAux
 δ₂ E
· 使用定理 `lt_of_abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder
 α] {a b : α}, |a| < b → a < b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `thickenedIndicatorAux_zero`：thickenedIndicatorAux_zero {δ : Real} (δ_pos
 : 0 < δ) (E : Set α) {x : α} (x_out : x ∉ thickening δ E) : thickenedIndicatorA
ux δ E x = 0
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in 
α) tends
pointwise (i.e., w.r.t. the product topology on `α → ℝ≥0∞`) to the indicator fun
ction of the
closure of E.

This statement is for the unbundled `ℝ≥0∞`-valued functions `thickenedIndicatorA
ux δ E`, see
`thickenedIndicator_tendsto_indicator_closure` for the version for bundled `ℝ≥0`
-valued
bounded continuous functions.
-/
theorem thickenedIndicatorAux_tendsto_indicator_closure {δseq : ℕ → ℝ}
    (δseq_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) :
    Tendsto (fun n => thickenedIndicatorAux (δseq n) E) atTop
      (𝓝 (indicator (closure E) fun _ => (1 : ℝ≥0∞))) := by
  rw [tendsto_pi_nhds]
  intro x
  by_cases x_mem_closure : x ∈ closure E
  · simp_rw [thickenedIndicatorAux_one_of_mem_closure _ E x_mem_closure]
    rw [show (indicator (closure E) fun _ => (1 : ℝ≥0∞)) x = 1 by
        simp only [x_mem_closure, indicator_of_mem]]
    exact tendsto_const_nhds
  · rw [show (closure E).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 by
        simp only [x_mem_closure, indicator_of_notMem, not_false_iff]]
    rcases exists_real_pos_lt_infEDist_of_notMem_closure x_mem_closure with ⟨ε, ⟨ε_pos, ε_lt⟩⟩
    rw [Metric.tendsto_nhds] at δseq_lim
    specialize δseq_lim ε ε_pos
    simp only [dist_zero_right, Real.norm_eq_abs, eventually_atTop] at δseq_lim
    rcases δseq_lim with ⟨N, hN⟩
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro n n_large
    have key : x ∉ thickening ε E := by simpa only [thickening, mem_ofPred_eq, not_lt] using ε_lt.le
    refine le_antisymm ?_ bot_le
    apply (thickenedIndicatorAux_mono (lt_of_abs_lt (hN n n_large)).le E x).trans
    exact (thickenedIndicatorAux_zero ε_pos E key).le

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `infEDist _ E`.

`thickenedIndicator` is the (bundled) bounded continuous function with `ℝ≥0`-values.
See `thickenedIndicatorAux` for the unbundled `ℝ≥0∞`-valued function. -/
@[simps]
/-
**thickenedIndicator** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：thickenedIndicator {δ : Real} (δ_pos : 0 < δ) (E : Set α) : α ->ᵇ Real>=0 
where toFun
参数：δ_pos : 0 < δ；E : Set α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `infEDist _ E`.

`thickenedIndicator` is the (bundled) bounded continuous function with `ℝ≥0`-val
ues.
See `thickenedIndicatorAux` for the unbundled `ℝ≥0∞`-valued function.
-/
def thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) : α →ᵇ ℝ≥0 where
  toFun := fun x : α => (thickenedIndicatorAux δ E x).toNNReal
  continuous_toFun := by
    apply ContinuousOn.comp_continuous continuousOn_toNNReal
      (continuous_thickenedIndicatorAux δ_pos E)
    intro x
    exact (lt_of_le_of_lt (@thickenedIndicatorAux_le_one _ _ δ E x) one_lt_top).ne
  map_bounded' := by
    use 2
    intro x y
    rw [NNReal.dist_eq]
    apply (abs_sub _ _).trans
    rw [NNReal.abs_eq, NNReal.abs_eq, ← one_add_one_eq_two]
    have key := @thickenedIndicatorAux_le_one _ _ δ E
    apply add_le_add <;>
      · norm_cast
        exact (toNNReal_le_toNNReal (lt_of_le_of_lt (key _) one_lt_top).ne one_ne_top).mpr (key _)
/-
**thickenedIndicator.coeFn_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicator.coeFn_eq_comp {δ : Real} (δ_pos : 0 < δ) (E : Set α) : 
⇑(thickenedIndicator δ_pos E) = ENNReal.toNNReal ∘ thickenedIndicatorAux δ E
参数：δ_pos : 0 < δ；E : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem thickenedIndicator.coeFn_eq_comp {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    ⇑(thickenedIndicator δ_pos E) = ENNReal.toNNReal ∘ thickenedIndicatorAux δ E :=
  rfl
/-
**thickenedIndicator_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicator_le_one {δ : Real} (δ_pos : 0 < δ) (E : Set α) (x : α) :
 thickenedIndicator δ_pos E x <= 1
参数：δ_pos : 0 < δ；E : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `thickenedIndicator.coeFn_eq_comp`：thickenedIndicator.coeFn_eq_comp {δ : 
Real} (δ_pos : 0 < δ) (E : Set α) : ⇑(thickenedIndicator δ_pos E) = ENNReal.toNN
Real ∘ thickenedIndica…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toNNReal_le_toNNReal`：toNNReal_le_toNNReal (ha : a != ∞) (hb : b
 != ∞) : a.toNNReal <= b.toNNReal ↔ a <= b
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `thickenedIndicatorAux_lt_top`：thickenedIndicatorAux_lt_top {δ : Real} {E
 : Set α} {x : α} : thickenedIndicatorAux δ E x < ∞
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `thickenedIndicatorAux_le_one`：thickenedIndicatorAux_le_one (δ : Real) (E
 : Set α) (x : α) : thickenedIndicatorAux δ E x <= 1
-/
theorem thickenedIndicator_le_one {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α) :
    thickenedIndicator δ_pos E x ≤ 1 := by
  rw [thickenedIndicator.coeFn_eq_comp]
  simpa using (toNNReal_le_toNNReal (by finiteness) one_ne_top).mpr
    (thickenedIndicatorAux_le_one δ E x)
/-
**thickenedIndicator_one_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicator_one_of_mem_closure {δ : Real} (δ_pos : 0 < δ) (E : Set 
α) {x : α} (x_mem : x in closure E) : thickenedIndicator δ_pos E x = 1
参数：δ_pos : 0 < δ；E : Set α；x_mem : x in closure E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `thickenedIndicator_apply`：∀ {α : Type u_1} [inst : PseudoEMetricSpace α]
 {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α),   (thickenedIndicator δ_pos E) x =
 (thickenedInd…
· 使用定理 `thickenedIndicatorAux_one_of_mem_closure`：thickenedIndicatorAux_one_of_m
em_closure (δ : Real) (E : Set α) {x : α} (x_mem : x in closure E) : thickenedIn
dicatorAux δ E x = 1
· 使用定理 `ENNReal.toNNReal_one`：ENNReal.toNNReal 1 = 1
-/
theorem thickenedIndicator_one_of_mem_closure {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_mem : x ∈ closure E) : thickenedIndicator δ_pos E x = 1 := by
  rw [thickenedIndicator_apply, thickenedIndicatorAux_one_of_mem_closure δ E x_mem, toNNReal_one]
/-
**one_le_thickenedIndicator_apply'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_thickenedIndicator_apply' {X : Type _} [PseudoEMetricSpace X] {δ : 
Real} (δ_pos : 0 < δ) {F : Set X} {x : X} (hxF : x in closure F) : 1 <= thickene
dIndicator δ_pos F x
参数：δ_pos : 0 < δ；hxF : x in closure F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `thickenedIndicator_one_of_mem_closure`：thickenedIndicator_one_of_mem_clo
sure {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_mem : x in closure E) : t
hickenedIndicator δ_pos E x…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma one_le_thickenedIndicator_apply' {X : Type _} [PseudoEMetricSpace X]
    {δ : ℝ} (δ_pos : 0 < δ) {F : Set X} {x : X} (hxF : x ∈ closure F) :
    1 ≤ thickenedIndicator δ_pos F x := by
  rw [thickenedIndicator_one_of_mem_closure δ_pos F hxF]
/-
**one_le_thickenedIndicator_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_thickenedIndicator_apply (X : Type _) [PseudoEMetricSpace X] {δ : R
eal} (δ_pos : 0 < δ) {F : Set X} {x : X} (hxF : x in F) : 1 <= thickenedIndicato
r δ_pos F x
参数：X : Type _；δ_pos : 0 < δ；hxF : x in F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `one_le_thickenedIndicator_apply'`：one_le_thickenedIndicator_apply' {X : 
Type _} [PseudoEMetricSpace X] {δ : Real} (δ_pos : 0 < δ) {F : Set X} {x : X} (h
xF : x in closure F) :…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma one_le_thickenedIndicator_apply (X : Type _) [PseudoEMetricSpace X]
    {δ : ℝ} (δ_pos : 0 < δ) {F : Set X} {x : X} (hxF : x ∈ F) :
    1 ≤ thickenedIndicator δ_pos F x :=
  one_le_thickenedIndicator_apply' δ_pos (subset_closure hxF)
/-
**thickenedIndicator_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicator_one {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_i
n_E : x in E) : thickenedIndicator δ_pos E x = 1
参数：δ_pos : 0 < δ；E : Set α；x_in_E : x in E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `thickenedIndicator_one_of_mem_closure`：thickenedIndicator_one_of_mem_clo
sure {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_mem : x in closure E) : t
hickenedIndicator δ_pos E x…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem thickenedIndicator_one {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_in_E : x ∈ E) :
    thickenedIndicator δ_pos E x = 1 :=
  thickenedIndicator_one_of_mem_closure _ _ (subset_closure x_in_E)
/-
**thickenedIndicator_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicator_zero {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_
out : x ∉ thickening δ E) : thickenedIndicator δ_pos E x = 0
参数：δ_pos : 0 < δ；E : Set α；x_out : x ∉ thickening δ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `thickenedIndicator_apply`：∀ {α : Type u_1} [inst : PseudoEMetricSpace α]
 {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α),   (thickenedIndicator δ_pos E) x =
 (thickenedInd…
· 使用定理 `thickenedIndicatorAux_zero`：thickenedIndicatorAux_zero {δ : Real} (δ_pos
 : 0 < δ) (E : Set α) {x : α} (x_out : x ∉ thickening δ E) : thickenedIndicatorA
ux δ E x = 0
· 使用定理 `ENNReal.toNNReal_zero`：ENNReal.toNNReal 0 = 0
-/
theorem thickenedIndicator_zero {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_out : x ∉ thickening δ E) : thickenedIndicator δ_pos E x = 0 := by
  rw [thickenedIndicator_apply, thickenedIndicatorAux_zero δ_pos E x_out, toNNReal_zero]
/-
**indicator_le_thickenedIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indicator_le_thickenedIndicator {δ : Real} (δ_pos : 0 < δ) (E : Set α) : (
E.indicator fun _ => (1 : Real>=0)) <= thickenedIndicator δ_pos E
参数：δ_pos : 0 < δ；E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `thickenedIndicator_one`：thickenedIndicator_one {δ : Real} (δ_pos : 0 < δ
) (E : Set α) {x : α} (x_in_E : x in E) : thickenedIndicator δ_pos E x = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem indicator_le_thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0)) ≤ thickenedIndicator δ_pos E := by
  intro a
  by_cases h : a ∈ E
  · simp only [h, indicator_of_mem, thickenedIndicator_one δ_pos E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]
/-
**thickenedIndicator_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicator_mono {δ₁ δ₂ : Real} (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂)
 (hle : δ₁ <= δ₂) (E : Set α) : ⇑(thickenedIndicator δ₁_pos E) <= thickenedIndic
ator δ₂_pos E
参数：δ₁_pos : 0 < δ₁；δ₂_pos : 0 < δ₂；hle : δ₁ <= δ₂；E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toNNReal_le_toNNReal`：toNNReal_le_toNNReal (ha : a != ∞) (hb : b
 != ∞) : a.toNNReal <= b.toNNReal ↔ a <= b
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `thickenedIndicatorAux_lt_top`：thickenedIndicatorAux_lt_top {δ : Real} {E
 : Set α} {x : α} : thickenedIndicatorAux δ E x < ∞
· 使用定理 `thickenedIndicatorAux_mono`：thickenedIndicatorAux_mono {δ₁ δ₂ : Real} (h
le : δ₁ <= δ₂) (E : Set α) : thickenedIndicatorAux δ₁ E <= thickenedIndicatorAux
 δ₂ E
-/
theorem thickenedIndicator_mono {δ₁ δ₂ : ℝ} (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂) (hle : δ₁ ≤ δ₂)
    (E : Set α) : ⇑(thickenedIndicator δ₁_pos E) ≤ thickenedIndicator δ₂_pos E := by
  intro x
  apply (toNNReal_le_toNNReal (by finiteness) (by finiteness)).mpr
  apply thickenedIndicatorAux_mono hle
/-
**thickenedIndicator_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicator_subset {δ : Real} (δ_pos : 0 < δ) {E₁ E₂ : Set α} (subs
et : E₁ subseteq E₂) : ⇑(thickenedIndicator δ_pos E₁) <= thickenedIndicator δ_po
s E₂
参数：δ_pos : 0 < δ；subset : E₁ subseteq E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toNNReal_le_toNNReal`：toNNReal_le_toNNReal (ha : a != ∞) (hb : b
 != ∞) : a.toNNReal <= b.toNNReal ↔ a <= b
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `thickenedIndicatorAux_lt_top`：thickenedIndicatorAux_lt_top {δ : Real} {E
 : Set α} {x : α} : thickenedIndicatorAux δ E x < ∞
· 使用定理 `thickenedIndicatorAux_subset`：thickenedIndicatorAux_subset (δ : Real) {E
₁ E₂ : Set α} (subset : E₁ subseteq E₂) : thickenedIndicatorAux δ E₁ <= thickene
dIndicatorAux δ E₂
-/
theorem thickenedIndicator_subset {δ : ℝ} (δ_pos : 0 < δ) {E₁ E₂ : Set α} (subset : E₁ ⊆ E₂) :
    ⇑(thickenedIndicator δ_pos E₁) ≤ thickenedIndicator δ_pos E₂ := fun x =>
  (toNNReal_le_toNNReal (by finiteness) (by finiteness)).mpr
    (thickenedIndicatorAux_subset δ subset x)

@[gcongr only]
/-
**thickenedIndicator_mono_infEDist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：thickenedIndicator_mono_infEDist {δ : Real} (δ_pos : 0 < δ) {E : Set α} {x
 y : α} (h : infEDist x E <= infEDist y E) : thickenedIndicator δ_pos E y <= thi
ckenedIndicator δ_pos E x
参数：δ_pos : 0 < δ；h : infEDist x E <= infEDist y E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `thickenedIndicator_apply`：∀ {α : Type u_1} [inst : PseudoEMetricSpace α]
 {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α),   (thickenedIndicator δ_pos E) x =
 (thickenedInd…
· 使用定理 `ENNReal.toNNReal_mono`：toNNReal_mono (hb : b != ∞) (h : a <= b) : a.toNN
Real <= b.toNNReal
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `thickenedIndicatorAux_lt_top`：thickenedIndicatorAux_lt_top {δ : Real} {E
 : Set α} {x : α} : thickenedIndicatorAux δ E x < ∞
· 使用引理 `thickenedIndicatorAux_mono_infEDist`：thickenedIndicatorAux_mono_infEDist
 (δ : Real) {E : Set α} {x y : α} (h : infEDist x E <= infEDist y E) : thickened
IndicatorAux δ E y <= thi…
-/
lemma thickenedIndicator_mono_infEDist {δ : ℝ} (δ_pos : 0 < δ) {E : Set α} {x y : α}
    (h : infEDist x E ≤ infEDist y E) :
    thickenedIndicator δ_pos E y ≤ thickenedIndicator δ_pos E x := by
  simp only [thickenedIndicator_apply]
  gcongr
  · finiteness
  · exact thickenedIndicatorAux_mono_infEDist δ h

@[deprecated (since := "2026-01-08")]
alias thickenedIndicator_mono_infEdist := thickenedIndicator_mono_infEDist

/-- As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in α) tends
pointwise to the indicator function of the closure of E.

Note: This version is for the bundled bounded continuous functions, but the topology is not
the topology on `α →ᵇ ℝ≥0`. Coercions to functions `α → ℝ≥0` are done first, so the topology
/-
**is** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：is nearly impossible to state nicely in terms of `cfcHom` (see `cfcHom_com
p`). An additional advantage of the unbundled approach is that expressions like 
`fun x : R ↦ x⁻¹` are valid arguments to `cfc`, and a bundled continuous counter
part can only make sense when the spectrum of `a` does not contain zero and when
 we have an `⁻¹` operation on the domain.  A reader familiar with C⋆-algebra the
ory may be somewhat surprised at the level of abstraction here. For instance, wh
y not require `A` to be an
参数：see `cfcHom_comp`。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance is the product topology (the topology of pointwise convergence). -/
/-
**thickenedIndicator_tendsto_indicator_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickenedIndicator_tendsto_indicator_closure {δseq : Nat -> Real} (δseq_po
s : forall n, 0 < δseq n) (δseq_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) : Te
ndsto (fun n : Nat => ((↑) : (α ->ᵇ Real>=0) -> α -> Real>=0) (thickenedIndicato
r (δseq_pos n) E)) atTop (𝓝 (indicator (closure E) fun _ => (1 : Real>=0)))
参数：δseq_pos : forall n, 0 < δseq n；δseq_lim : Tendsto δseq atTop (𝓝 0)；E : Set α
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `thickenedIndicatorAux_tendsto_indicator_closure`：thickenedIndicatorAux_t
endsto_indicator_closure {δseq : Nat -> Real} (δseq_lim : Tendsto δseq atTop (𝓝 
0)) (E : Set α) : Tendsto (fun n => t…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Set.comp_indicator_const`：∀ {α : Type u_1} {M : Type u_3} {N : Type u_4}
 [inst : Zero M] [inst_1 : Zero N] {s : Set α} (c : M) (f : M → N),   f 0 = 0 → 
(fun x => f (s…
· 使用定理 `ENNReal.toNNReal_zero`：ENNReal.toNNReal 0 = 0
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_toNNReal`：tendsto_toNNReal {a : Real>=0∞} (ha : a != ∞) 
: Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in 
α) tends
pointwise to the indicator function of the closure of E.

Note: This version is for the bundled bounded continuous functions, but the topo
logy is not
the topology on `α →ᵇ ℝ≥0`. Coercions to functions `α → ℝ≥0` are done first, so 
the topology
instance is the product topology (the topology of pointwise convergence).
-/
theorem thickenedIndicator_tendsto_indicator_closure {δseq : ℕ → ℝ} (δseq_pos : ∀ n, 0 < δseq n)
    (δseq_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) :
    Tendsto (fun n : ℕ => ((↑) : (α →ᵇ ℝ≥0) → α → ℝ≥0) (thickenedIndicator (δseq_pos n) E)) atTop
      (𝓝 (indicator (closure E) fun _ => (1 : ℝ≥0))) := by
  have key := thickenedIndicatorAux_tendsto_indicator_closure δseq_lim E
  rw [tendsto_pi_nhds] at *
  intro x
  rw [show indicator (closure E) (fun _ => (1 : ℝ≥0)) x =
        (indicator (closure E) (fun _ => (1 : ℝ≥0∞)) x).toNNReal
      by refine (congr_fun (comp_indicator_const 1 ENNReal.toNNReal toNNReal_zero) x).symm]
  refine Tendsto.comp (tendsto_toNNReal ?_) (key x)
  by_cases x_mem : x ∈ closure E <;> simp [x_mem]
/-
**lipschitzWith_thickenedIndicator** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lipschitzWith_thickenedIndicator {δ : Real} (δ_pos : 0 < δ) (E : Set α) : 
LipschitzWith δ.toNNReal⁻¹ (thickenedIndicator δ_pos E)
参数：δ_pos : 0 < δ；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `thickenedIndicator_apply`：∀ {α : Type u_1} [inst : PseudoEMetricSpace α]
 {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α),   (thickenedIndicator δ_pos E) x =
 (thickenedInd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.toReal_sub_of_le`：toReal_sub_of_le (hba : b <= a) (ha : a != ∞) 
: (a - b).toReal = a.toReal - b.toReal
· 使用引理 `thickenedIndicatorAux_mono_infEDist`：thickenedIndicatorAux_mono_infEDist
 (δ : Real) {E : Set α} {x y : α} (h : infEDist x E <= infEDist y E) : thickened
IndicatorAux δ E y <= thi…
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `thickenedIndicatorAux_lt_top`：thickenedIndicatorAux_lt_top {δ : Real} {E
 : Set α} {x : α} : thickenedIndicatorAux δ E x < ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.abs_toReal`：abs_toReal {x : Real>=0∞} : |x.toReal| = x.toReal
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `ENNReal.sub_sub_sub_cancel_left`：sub_sub_sub_cancel_left (ha : a != ∞) (
h : b <= a) : a - c - (a - b) = b - c
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.sub_mul`：∀ {a b c : ENNReal}, (0 < b → b < a → c ≠ ⊤) → (a - b) 
* c = a * c - b * c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
（共 44 条，此处仅展示前 30 条）
-/
lemma lipschitzWith_thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    LipschitzWith δ.toNNReal⁻¹ (thickenedIndicator δ_pos E) := by
  intro x y
  wlog h : infEDist x E ≤ infEDist y E generalizing x y
  · specialize this y x (le_of_not_ge h)
    rwa [edist_comm, edist_comm x]
  simp_rw [edist_dist, NNReal.dist_eq, thickenedIndicator_apply, coe_toNNReal_eq_toReal]
  rw [← ENNReal.toReal_sub_of_le (thickenedIndicatorAux_mono_infEDist _ h) (by finiteness)]
  simp only [thickenedIndicatorAux, abs_toReal, ne_eq, sub_eq_top_iff, one_ne_top, false_and,
    not_false_eq_true, and_true, ofReal_toReal]
  rw [ENNReal.coe_inv (by simp [δ_pos]), ENNReal.ofReal, div_eq_mul_inv, div_eq_mul_inv]
  by_cases h_le : infEDist y E * (↑δ.toNNReal)⁻¹ ≤ 1
  · calc 1 - infEDist x E * (↑δ.toNNReal)⁻¹ - (1 - infEDist y E * (↑δ.toNNReal)⁻¹)
    _ ≤ infEDist y E * (↑δ.toNNReal)⁻¹ - infEDist x E * (↑δ.toNNReal)⁻¹ := by
      rw [ENNReal.sub_sub_sub_cancel_left (by finiteness) h_le]
    _ ≤ (↑δ.toNNReal)⁻¹ * edist x y := by
      rw [← ENNReal.sub_mul (by simp [δ_pos]), mul_comm, edist_comm]
      gcongr
      simp only [tsub_le_iff_right]
      exact infEDist_le_edist_add_infEDist
  · simp only [tsub_le_iff_right]
    rw [tsub_eq_zero_of_le (not_le.mp h_le).le, add_zero, mul_comm]
    calc 1
    _ ≤ infEDist y E * (↑δ.toNNReal)⁻¹ := (not_le.mp h_le).le
    _ ≤ edist x y * (↑δ.toNNReal)⁻¹ + infEDist x E * (↑δ.toNNReal)⁻¹ := by
      rw [← add_mul, edist_comm]
      gcongr
      exact infEDist_le_edist_add_infEDist

end thickenedIndicator

section indicator

variable {α : Type*} [PseudoEMetricSpace α] {β : Type*} [One β]

/-- Pointwise, the multiplicative indicators of δ-thickenings of a set eventually coincide
with the multiplicative indicator of the set as δ>0 tends to zero. -/
@[to_additive /-- Pointwise, the indicators of δ-thickenings of a set eventually coincide
with the indicator of the set as δ>0 tends to zero. -/]
/-
**mulIndicator_thickening_eventually_eq_mulIndicator_closure** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：mulIndicator_thickening_eventually_eq_mulIndicator_closure (f : α -> β) (E
 : Set α) (x : α) : forallᶠ δ in 𝓝[>] (0 : Real), (Metric.thickening δ E).mulInd
icator f x = (closure E).mulIndicator f x
参数：f : α -> β；E : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `Metric.closure_subset_thickening`：closure_subset_thickening {δ : Real} (
δ_pos : 0 < δ) (E : Set α) : closure E subseteq thickening δ E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Metric.eventually_notMem_thickening_of_infEDist_pos`：eventually_notMem_t
hickening_of_infEDist_pos {E : Set α} {x : α} (h : x ∉ closure E) : forallᶠ δ in
 𝓝 (0 : Real), x ∉ Metric.thickening δ E
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mulIndicator_thickening_eventually_eq_mulIndicator_closure (f : α → β) (E : Set α) (x : α) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (Metric.thickening δ E).mulIndicator f x = (closure E).mulIndicator f x := by
  by_cases x_mem_closure : x ∈ closure E
  · filter_upwards [self_mem_nhdsWithin] with δ δ_pos
    simp only [closure_subset_thickening δ_pos E x_mem_closure, mulIndicator_of_mem, x_mem_closure]
  · have obs := eventually_notMem_thickening_of_infEDist_pos x_mem_closure
    filter_upwards [mem_nhdsWithin_of_mem_nhds obs, self_mem_nhdsWithin]
      with δ x_notin_thE _
    simp only [x_notin_thE, not_false_eq_true, mulIndicator_of_notMem, x_mem_closure]

/-- Pointwise, the multiplicative indicators of closed δ-thickenings of a set eventually coincide
with the multiplicative indicator of the set as δ tends to zero. -/
@[to_additive /-- Pointwise, the indicators of closed δ-thickenings of a set eventually coincide
with the indicator of the set as δ tends to zero. -/]
/-
**mulIndicator_cthickening_eventually_eq_mulIndicator_closure** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：mulIndicator_cthickening_eventually_eq_mulIndicator_closure (f : α -> β) (
E : Set α) (x : α) : forallᶠ δ in 𝓝 (0 : Real), (Metric.cthickening δ E).mulIndi
cator f x = (closure E).mulIndicator f x
参数：f : α -> β；E : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Metric.closure_subset_cthickening`：closure_subset_cthickening (δ : Real)
 (E : Set α) : closure E subseteq cthickening δ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用引理 `Metric.eventually_notMem_cthickening_of_infEDist_pos`：eventually_notMem_
cthickening_of_infEDist_pos {E : Set α} {x : α} (h : x ∉ closure E) : forallᶠ δ 
in 𝓝 (0 : Real), x ∉ Metric.cthickening δ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulIndicator_cthickening_eventually_eq_mulIndicator_closure (f : α → β) (E : Set α) (x : α) :
    ∀ᶠ δ in 𝓝 (0 : ℝ),
      (Metric.cthickening δ E).mulIndicator f x = (closure E).mulIndicator f x := by
  by_cases x_mem_closure : x ∈ closure E
  · filter_upwards [univ_mem] with δ _
    have obs : x ∈ cthickening δ E := closure_subset_cthickening δ E x_mem_closure
    rw [mulIndicator_of_mem obs f, mulIndicator_of_mem x_mem_closure f]
  · filter_upwards [eventually_notMem_cthickening_of_infEDist_pos x_mem_closure] with δ hδ
    simp only [hδ, not_false_eq_true, mulIndicator_of_notMem, x_mem_closure]

variable [TopologicalSpace β]

/-- The multiplicative indicators of δ-thickenings of a set tend pointwise to the multiplicative
indicator of the set, as δ>0 tends to zero. -/
@[to_additive /-- The indicators of δ-thickenings of a set tend pointwise to the indicator of the
set, as δ>0 tends to zero. -/]
/-
**tendsto_mulIndicator_thickening_mulIndicator_closure** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：tendsto_mulIndicator_thickening_mulIndicator_closure (f : α -> β) (E : Set
 α) : Tendsto (fun δ => (Metric.thickening δ E).mulIndicator f) (𝓝[>] 0) (𝓝 ((cl
osure E).mulIndicator f))
参数：f : α -> β；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用引理 `mulIndicator_thickening_eventually_eq_mulIndicator_closure`：mulIndicator
_thickening_eventually_eq_mulIndicator_closure (f : α -> β) (E : Set α) (x : α) 
: forallᶠ δ in 𝓝[>] (0 : Real), (Metric.thickeni…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma tendsto_mulIndicator_thickening_mulIndicator_closure (f : α → β) (E : Set α) :
    Tendsto (fun δ ↦ (Metric.thickening δ E).mulIndicator f) (𝓝[>] 0)
      (𝓝 ((closure E).mulIndicator f)) := by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_congr' (mulIndicator_thickening_eventually_eq_mulIndicator_closure f E x)]
  apply tendsto_const_nhds

/-- The multiplicative indicators of closed δ-thickenings of a set tend pointwise to the
multiplicative indicator of the set, as δ tends to zero. -/
@[to_additive /-- The indicators of closed δ-thickenings of a set tend pointwise to the indicator
of the set, as δ tends to zero. -/]
/-
**tendsto_mulIndicator_cthickening_mulIndicator_closure** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：tendsto_mulIndicator_cthickening_mulIndicator_closure (f : α -> β) (E : Se
t α) : Tendsto (fun δ => (Metric.cthickening δ E).mulIndicator f) (𝓝 0) (𝓝 ((clo
sure E).mulIndicator f))
参数：f : α -> β；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用引理 `mulIndicator_cthickening_eventually_eq_mulIndicator_closure`：mulIndicato
r_cthickening_eventually_eq_mulIndicator_closure (f : α -> β) (E : Set α) (x : α
) : forallᶠ δ in 𝓝 (0 : Real), (Metric.cthickenin…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma tendsto_mulIndicator_cthickening_mulIndicator_closure (f : α → β) (E : Set α) :
    Tendsto (fun δ ↦ (Metric.cthickening δ E).mulIndicator f) (𝓝 0)
      (𝓝 ((closure E).mulIndicator f)) := by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_congr' (mulIndicator_cthickening_eventually_eq_mulIndicator_closure f E x)]
  apply tendsto_const_nhds

end indicator

