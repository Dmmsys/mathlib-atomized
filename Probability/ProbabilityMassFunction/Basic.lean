/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in
`Mathlib/Probability/ProbabilityMassFunction/Monad.lean`, other constructions of `PMF`s are found in
`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`.

Given `p : PMF α`, `PMF.toOuterMeasure` constructs an `OuterMeasure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `Measure` on `α`, see `PMF.toMeasure`.
`PMF.toMeasure.isProbabilityMeasure` shows this associated measure is a probability measure.
Conversely, given a probability measure `μ` on a measurable space `α` with all singleton sets
measurable, `μ.toPMF` constructs a `PMF` on `α`, setting the probability mass of a point `x`
to be the measure of the singleton set `{x}`.

## Tags

probability mass function, discrete probability measure
-/

@[expose] public section


noncomputable section

variable {α : Type*}

open NNReal ENNReal MeasureTheory

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0∞` such
  that the values have (infinite) sum `1`. -/
/-
**PMF.** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A probability mass function, or discrete probability measures is a function `α →
 ℝ≥0∞` such
  that the values have (infinite) sum `1`.
-/
def PMF.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // HasSum f 1 }

namespace PMF

/-
**PMF.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `PMF`。
形式化陈述：instFunLike : FunLike (PMF α) α Real>=0∞ where coe p a
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (PMF α) α ℝ≥0∞ where
  coe p a := p.1 a
  coe_injective _ _ h := Subtype.ext h

@[ext]
/-
**PMF.ext** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
参数：∀ (x : α), p x = q x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
protected theorem ext {p q : PMF α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h
/-
**PMF.hasSum_coe_one** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：hasSum_coe_one (p : PMF α) : HasSum p 1
参数：p : PMF α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem hasSum_coe_one (p : PMF α) : HasSum p 1 :=
  p.2

@[simp]
/-
**PMF.tsum_coe** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：tsum_coe (p : PMF α) : ∑' a, p a = 1
参数：p : PMF α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `PMF.hasSum_coe_one`：hasSum_coe_one (p : PMF α) : HasSum p 1
-/
theorem tsum_coe (p : PMF α) : ∑' a, p a = 1 :=
  p.hasSum_coe_one.tsum_eq
/-
**PMF.tsum_coe_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：tsum_coe_ne_top (p : PMF α) : ∑' a, p a != ∞
参数：p : PMF α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PMF.tsum_coe`：tsum_coe (p : PMF α) : ∑' a, p a = 1
-/
theorem tsum_coe_ne_top (p : PMF α) : ∑' a, p a ≠ ∞ :=
  p.tsum_coe.symm ▸ ENNReal.one_ne_top
/-
**PMF.tsum_coe_indicator_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：tsum_coe_indicator_ne_top (p : PMF α) (s : Set α) : ∑' a, s.indicator p a 
!= ∞
参数：p : PMF α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `Set.indicator_apply_le`：∀ {α : Type u_2} {M : Type u_3} [inst : AddMonoi
d M] [inst_1 : PartialOrder M] [CanonicallyOrderedAdd M] {a : α}   {s : Set α} {
f g : α → M}…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `PMF.tsum_coe_ne_top`：tsum_coe_ne_top (p : PMF α) : ∑' a, p a != ∞
-/
theorem tsum_coe_indicator_ne_top (p : PMF α) (s : Set α) : ∑' a, s.indicator p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt
    (ENNReal.tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl))
    (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

@[simp]
/-
**PMF.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：coe_ne_zero (p : PMF α) : ⇑p != 0
参数：p : PMF α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `PMF.tsum_coe`：tsum_coe (p : PMF α) : ∑' a, p a = 1
-/
theorem coe_ne_zero (p : PMF α) : ⇑p ≠ 0 := fun hp =>
  zero_ne_one ((tsum_zero.symm.trans (tsum_congr fun x => symm (congr_fun hp x))).trans p.tsum_coe)

/-- The support of a `PMF` is the set where it is nonzero. -/
/-
**PMF.support** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：support (p : PMF α) : Set α
参数：p : PMF α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a `PMF` is the set where it is nonzero.
-/
def support (p : PMF α) : Set α :=
  Function.support p

@[simp]
/-
**PMF.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_iff (p : PMF α) (a : α) : a in p.support ↔ p a != 0
参数：p : PMF α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_support_iff (p : PMF α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := Iff.rfl

@[simp]
/-
**PMF.support_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_nonempty (p : PMF α) : p.support.Nonempty
参数：p : PMF α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_nonempty_iff`：∀ {ι : Type u_1} {M : Type u_3} [inst : Z
ero M] {f : ι → M}, (Function.support f).Nonempty ↔ f ≠ 0
· 使用定理 `PMF.coe_ne_zero`：coe_ne_zero (p : PMF α) : ⇑p != 0
-/
theorem support_nonempty (p : PMF α) : p.support.Nonempty :=
  Function.support_nonempty_iff.2 p.coe_ne_zero

@[simp]
/-
**PMF.support_countable** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_countable (p : PMF α) : p.support.Countable
参数：p : PMF α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.countable_support_ennreal`：∀ {α : Type u_1} {f : α → ENNReal}, 
∑' (i : α), f i ≠ ⊤ → (Function.support f).Countable
· 使用定理 `PMF.tsum_coe_ne_top`：tsum_coe_ne_top (p : PMF α) : ∑' a, p a != ∞
-/
theorem support_countable (p : PMF α) : p.support.Countable :=
  Summable.countable_support_ennreal (tsum_coe_ne_top p)
/-
**PMF.apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：apply_eq_zero_iff (p : PMF α) (a : α) : p a = 0 ↔ a ∉ p.support
参数：p : PMF α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.mem_support_iff`：mem_support_iff (p : PMF α) (a : α) : a in p.suppor
t ↔ p a != 0
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem apply_eq_zero_iff (p : PMF α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, Classical.not_not]
/-
**PMF.apply_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：apply_pos_iff (p : PMF α) (a : α) : 0 < p a ↔ a in p.support
参数：p : PMF α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `PMF.mem_support_iff`：mem_support_iff (p : PMF α) (a : α) : a in p.suppor
t ↔ p a != 0
-/
theorem apply_pos_iff (p : PMF α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm
/-
**PMF.apply_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：apply_eq_one_iff (p : PMF α) (a : α) : p a = 1 ↔ p.support = {a}
参数：p : PMF α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Summable.tsum_ne_zero_iff`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : PartialOrder α] [IsOrderedAddMonoid α]   [CanonicallyOrder
edAdd α] [inst_…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ite_ne_left_iff`：ite_ne_left_iff : ite P a b != a ↔ ¬P ∧ a != b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `PMF.mem_support_iff`：mem_support_iff (p : PMF α) (a : α) : a in p.suppor
t ↔ p a != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ENNReal.add_lt_add_of_le_of_lt`：∀ {a b c d : ENNReal}, a ≠ ⊤ → a ≤ b → c
 < d → a + c < b + d
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ENNReal.tsum_add`：∀ {α : Type u_1} {f g : α → ENNReal}, ∑' (a : α), (f a
 + g a) = ∑' (a : α), f a + ∑' (a : α), g a
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 44 条，此处仅展示前 30 条）
-/
theorem apply_eq_one_iff (p : PMF α) (a : α) : p a = 1 ↔ p.support = {a} := by
  refine ⟨fun h => Set.Subset.antisymm (fun a' ha' => by_contra fun ha => ?_)
    fun a' ha' => ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one <| ha.symm.trans h,
    fun h => _root_.trans (symm <| tsum_eq_single a
      fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha')) p.tsum_coe⟩
  suffices 1 < ∑' a, p a from ne_of_lt this p.tsum_coe.symm
  classical
  have : 0 < ∑' b, ite (b = a) 0 (p b) := by
    rw [pos_iff_ne_zero, ENNReal.summable.tsum_ne_zero_iff]
    exact ⟨a', ite_ne_left_iff.2 ⟨ha, Ne.symm <| (p.mem_support_iff a').2 ha'⟩⟩
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ < p a + ∑' b, ite (b = a) 0 (p b) :=
      (ENNReal.add_lt_add_of_le_of_lt ENNReal.one_ne_top (le_of_eq h.symm) this)
    _ = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) := by rw [eq_self_iff_true, if_true]
    _ = (∑' b, ite (b = a) (p b) 0) + ∑' b, ite (b = a) 0 (p b) := by
      congr
      exact symm (tsum_eq_single a fun b hb => if_neg hb)
    _ = ∑' b, (ite (b = a) (p b) 0 + ite (b = a) 0 (p b)) := ENNReal.tsum_add.symm
    _ = ∑' b, p b := tsum_congr fun b => by split_ifs <;> simp only [zero_add, add_zero]
/-
**PMF.coe_le_one** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：coe_le_one (p : PMF α) (a : α) : p a <= 1
参数：p : PMF α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasSum_le`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst
 : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `hasSum_ite_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] (b : β)   [inst_2 : DecidablePred fun x => x = b] 
(a …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `PMF.hasSum_coe_one`：hasSum_coe_one (p : PMF α) : HasSum p 1
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
theorem coe_le_one (p : PMF α) (a : α) : p a ≤ 1 := by
  classical
  refine hasSum_le (fun b => ?_) (hasSum_ite_eq a (p a)) (hasSum_coe_one p)
  split_ifs with h <;> simp [h]
/-
**PMF.apply_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：apply_ne_top (p : PMF α) (a : α) : p a != ∞
参数：p : PMF α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `PMF.coe_le_one`：coe_le_one (p : PMF α) (a : α) : p a <= 1
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
-/
theorem apply_ne_top (p : PMF α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)
/-
**PMF.apply_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：apply_lt_top (p : PMF α) (a : α) : p a < ∞
参数：p : PMF α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `PMF.apply_ne_top`：apply_ne_top (p : PMF α) (a : α) : p a != ∞
-/
theorem apply_lt_top (p : PMF α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)

section OuterMeasure

open OuterMeasure

/-- Construct an `OuterMeasure` from a `PMF`, by assigning measure to each set `s : Set α` equal
  to the sum of `p x` for each `x ∈ α`. -/
/-
**PMF.toOuterMeasure** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure (p : PMF α) : OuterMeasure α
参数：p : PMF α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an `OuterMeasure` from a `PMF`, by assigning measure to each set `s : 
Set α` equal
  to the sum of `p x` for each `x ∈ α`.
-/
def toOuterMeasure (p : PMF α) : OuterMeasure α :=
  OuterMeasure.sum fun x : α => p x • dirac x

variable (p : PMF α) (s : Set α)
/-
**PMF.toOuterMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_apply : p.toOuterMeasure s = ∑' x, s.indicator p x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `MeasureTheory.OuterMeasure.smul_dirac_apply`：smul_dirac_apply (a : Real>
=0∞) (b : α) (s : Set α) : (a • dirac b) s = indicator s (fun _ => a) b
-/
theorem toOuterMeasure_apply : p.toOuterMeasure s = ∑' x, s.indicator p x :=
  tsum_congr fun x => smul_dirac_apply (p x) x s

@[simp]
/-
**PMF.toOuterMeasure_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_caratheodory : p.toOuterMeasure.caratheodory = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.OuterMeasure.dirac_caratheodory`：dirac_caratheodory (a : α
) : (dirac a).caratheodory = ⊤
· 使用定理 `MeasureTheory.OuterMeasure.le_smul_caratheodory`：le_smul_caratheodory (a
 : Real>=0∞) (m : OuterMeasure α) : m.caratheodory <= (a • m).caratheodory
· 使用定理 `MeasureTheory.OuterMeasure.le_sum_caratheodory`：le_sum_caratheodory {ι} 
(m : ι -> OuterMeasure α) : ⨅ i, (m i).caratheodory <= (sum m).caratheodory
-/
theorem toOuterMeasure_caratheodory : p.toOuterMeasure.caratheodory = ⊤ := by
  refine eq_top_iff.2 <| le_trans (le_sInf fun x hx => ?_) (le_sum_caratheodory _)
  have ⟨y, hy⟩ := hx
  exact
    ((le_of_eq (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eq hy)

@[simp]
/-
**PMF.toOuterMeasure_apply_finset** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_apply_finset (s : Finset α) : p.toOuterMeasure s = ∑ x in s
, p x
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `tsum_eq_sum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop] {s
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
-/
theorem toOuterMeasure_apply_finset (s : Finset α) : p.toOuterMeasure s = ∑ x ∈ s, p x := by
  refine (toOuterMeasure_apply p s).trans ((tsum_eq_sum (s := s) ?_).trans ?_)
  · exact fun x hx => Set.indicator_of_notMem (Finset.mem_coe.not.2 hx) _
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (Finset.mem_coe.2 hx) _
/-
**PMF.toOuterMeasure_apply_singleton** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_apply_singleton (a : α) : p.toOuterMeasure {a} = p a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ite_eq_right_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y 
: α}, (if p then x else y) = y ↔ p → x = y
· 使用定理 `ite_eq_left_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y :
 α}, (if p then x else y) = x ↔ ¬p → y = x
-/
theorem toOuterMeasure_apply_singleton (a : α) : p.toOuterMeasure {a} = p a := by
  refine (p.toOuterMeasure_apply {a}).trans ((tsum_eq_single a fun b hb => ?_).trans ?_)
  · classical exact ite_eq_right_iff.2 fun hb' => False.elim <| hb hb'
  · classical exact ite_eq_left_iff.2 fun ha' => False.elim <| ha' rfl
/-
**PMF.toOuterMeasure_injective** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_injective : (toOuterMeasure : PMF α -> OuterMeasure α).Inje
ctive
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PMF.toOuterMeasure_apply_singleton`：toOuterMeasure_apply_singleton (a : 
α) : p.toOuterMeasure {a} = p a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toOuterMeasure_injective : (toOuterMeasure : PMF α → OuterMeasure α).Injective :=
  fun p q h => PMF.ext fun x => (p.toOuterMeasure_apply_singleton x).symm.trans
    ((congr_fun (congr_arg _ h) _).trans <| q.toOuterMeasure_apply_singleton x)

@[simp]
/-
**PMF.toOuterMeasure_inj** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_inj {p q : PMF α} : p.toOuterMeasure = q.toOuterMeasure ↔ p
 = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `PMF.toOuterMeasure_injective`：toOuterMeasure_injective : (toOuterMeasure
 : PMF α -> OuterMeasure α).Injective
-/
theorem toOuterMeasure_inj {p q : PMF α} : p.toOuterMeasure = q.toOuterMeasure ↔ p = q :=
  toOuterMeasure_injective.eq_iff
/-
**PMF.toOuterMeasure_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_apply_eq_zero_iff : p.toOuterMeasure s = 0 ↔ Disjoint p.sup
port s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `ENNReal.tsum_eq_zero`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (i : α), f 
i = 0 ↔ ∀ (i : α), f i = 0
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Set.indicator_eq_zero'`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] 
{s : Set α} {f : α → M},   s.indicator f = 0 ↔ Disjoint (Function.support f) s
-/
theorem toOuterMeasure_apply_eq_zero_iff : p.toOuterMeasure s = 0 ↔ Disjoint p.support s := by
  rw [toOuterMeasure_apply, ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'
/-
**PMF.toOuterMeasure_apply_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_apply_eq_one_iff : p.toOuterMeasure s = 1 ↔ p.support subse
teq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.indicator_apply_eq_zero`：∀ {α : Type u_1} {M : Type u_3} [inst : Zer
o M] {s : Set α} {f : α → M} {a : α}, s.indicator f a = 0 ↔ a ∈ s → f a = 0
· 使用定理 `PMF.apply_pos_iff`：apply_pos_iff (p : PMF α) (a : α) : 0 < p a ↔ a in p.
support
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_lt_tsum`：tsum_lt_tsum {f g : α -> Real>=0∞} {i : α} (hfi : 
tsum f != ∞) (h : forall a : α, f a <= g a) (hi : f i < g i) : ∑' x, f x < ∑' x,
 g x
· 使用定理 `PMF.tsum_coe_indicator_ne_top`：tsum_coe_indicator_ne_top (p : PMF α) (s 
: Set α) : ∑' a, s.indicator p a != ∞
· 使用定理 `Set.indicator_apply_le`：∀ {α : Type u_2} {M : Type u_3} [inst : AddMonoi
d M] [inst_1 : PartialOrder M] [CanonicallyOrderedAdd M] {a : α}   {s : Set α} {
f g : α → M}…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.tsum_coe`：tsum_coe (p : PMF α) : ∑' a, p a = 1
· 使用定理 `PMF.apply_eq_zero_iff`：apply_eq_zero_iff (p : PMF α) (a : α) : p a = 0 ↔
 a ∉ p.support
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_eq_left_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y :
 α}, (if p then x else y) = x ↔ ¬p → y = x
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
-/
theorem toOuterMeasure_apply_eq_one_iff : p.toOuterMeasure s = 1 ↔ p.support ⊆ s := by
  refine (p.toOuterMeasure_apply s).symm ▸ ⟨fun h a hap => ?_, fun h => ?_⟩
  · refine by_contra fun hs => ne_of_lt ?_ (h.trans p.tsum_coe.symm)
    have hs' : s.indicator p a = 0 := Set.indicator_apply_eq_zero.2 fun hs' => False.elim <| hs hs'
    have hsa : s.indicator p a < p a := hs'.symm ▸ (p.apply_pos_iff a).2 hap
    exact ENNReal.tsum_lt_tsum (p.tsum_coe_indicator_ne_top s)
      (fun x => Set.indicator_apply_le fun _ => le_rfl) hsa
  · classical suffices ∀ (x) (_ : x ∉ s), p x = 0 from
      _root_.trans (tsum_congr
        fun a => (Set.indicator_apply s p a).trans
          (ite_eq_left_iff.2 <| symm ∘ this a)) p.tsum_coe
    exact fun a ha => (p.apply_eq_zero_iff a).2 <| Set.notMem_subset h ha

@[simp]
/-
**PMF.toOuterMeasure_apply_inter_support** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_apply_inter_support : p.toOuterMeasure (s inter p.support) 
= p.toOuterMeasure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.indicator_inter_support`：∀ {α : Type u_1} {M : Type u_3} [inst : Zer
o M] (s : Set α) (f : α → M),   (s ∩ Function.support f).indicator f = s.indicat
or f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toOuterMeasure_apply_inter_support :
    p.toOuterMeasure (s ∩ p.support) = p.toOuterMeasure s := by
  simp only [toOuterMeasure_apply, PMF.support, Set.indicator_inter_support]

/-- Slightly stronger than `OuterMeasure.mono` having an intersection with `p.support`. -/
/-
**PMF.toOuterMeasure_mono** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_mono {s t : Set α} (h : s inter p.support subseteq t) : p.t
oOuterMeasure s <= p.toOuterMeasure t
参数：h : s inter p.support subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PMF.toOuterMeasure_apply_inter_support`：toOuterMeasure_apply_inter_suppo
rt : p.toOuterMeasure (s inter p.support) = p.toOuterMeasure s
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂

--- 原说明 ---
Slightly stronger than `OuterMeasure.mono` having an intersection with `p.suppor
t`.
-/
theorem toOuterMeasure_mono {s t : Set α} (h : s ∩ p.support ⊆ t) :
    p.toOuterMeasure s ≤ p.toOuterMeasure t :=
  le_trans (le_of_eq (toOuterMeasure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)
/-
**PMF.toOuterMeasure_apply_eq_of_inter_support_eq** 是 Mathlib 中的一个定理，位于命名空间 `PMF
`。
形式化陈述：toOuterMeasure_apply_eq_of_inter_support_eq {s t : Set α} (h : s inter p.s
upport = t inter p.support) : p.toOuterMeasure s = p.toOuterMeasure t
参数：h : s inter p.support = t inter p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `PMF.toOuterMeasure_mono`：toOuterMeasure_mono {s t : Set α} (h : s inter 
p.support subseteq t) : p.toOuterMeasure s <= p.toOuterMeasure t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toOuterMeasure_apply_eq_of_inter_support_eq {s t : Set α}
    (h : s ∩ p.support = t ∩ p.support) : p.toOuterMeasure s = p.toOuterMeasure t :=
  le_antisymm (p.toOuterMeasure_mono (h.symm ▸ Set.inter_subset_left))
    (p.toOuterMeasure_mono (h ▸ Set.inter_subset_left))

@[simp]
/-
**PMF.toOuterMeasure_apply_fintype** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.ind
icator p x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `tsum_eq_sum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop] {s
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem toOuterMeasure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.indicator p x :=
  (p.toOuterMeasure_apply s).trans (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)

end OuterMeasure

section Measure

/-- Since every set is Carathéodory-measurable under `PMF.toOuterMeasure`,
  we can further extend this `OuterMeasure` to a `Measure` on `α`. -/
/-
**PMF.toMeasure** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：toMeasure [MeasurableSpace α] (p : PMF α) : Measure α
参数：p : PMF α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since every set is Carathéodory-measurable under `PMF.toOuterMeasure`,
  we can further extend this `OuterMeasure` to a `Measure` on `α`.
-/
def toMeasure [MeasurableSpace α] (p : PMF α) : Measure α :=
  p.toOuterMeasure.toMeasure (p.toOuterMeasure_caratheodory.symm ▸ le_top)

variable [MeasurableSpace α] (p : PMF α) {s : Set α}
/-
**PMF.toOuterMeasure_apply_le_toMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_apply_le_toMeasure_apply (s : Set α) : p.toOuterMeasure s <
= p.toMeasure s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_toMeasure_apply`：le_toMeasure_apply (m : OuterMeasure α
) (h : ms <= m.caratheodory) (s : Set α) : m s <= m.toMeasure h s
-/
theorem toOuterMeasure_apply_le_toMeasure_apply (s : Set α) : p.toOuterMeasure s ≤ p.toMeasure s :=
  le_toMeasure_apply p.toOuterMeasure _ s
/-
**PMF.toMeasure_apply_eq_toOuterMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply_eq_toOuterMeasure_apply (hs : MeasurableSet s) : p.toMeasu
re s = p.toOuterMeasure s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.toMeasure_apply`：toMeasure_apply (m : OuterMeasure α) (h :
 ms <= m.caratheodory) {s : Set α} (hs : MeasurableSet s) : m.toMeasure h s = m 
s
-/
theorem toMeasure_apply_eq_toOuterMeasure_apply (hs : MeasurableSet s) :
    p.toMeasure s = p.toOuterMeasure s :=
  toMeasure_apply p.toOuterMeasure _ hs
/-
**PMF.toMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply (hs : MeasurableSet s) : p.toMeasure s = ∑' x, s.indicator
 p x
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
-/
theorem toMeasure_apply (hs : MeasurableSet s) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply hs).trans (p.toOuterMeasure_apply s)
/-
**PMF.toMeasure_apply_singleton** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply_singleton (a : α) (h : MeasurableSet ({a} : Set α)) : p.to
Measure {a} = p a
参数：a : α；h : MeasurableSet ({a} : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_apply_singleton`：toOuterMeasure_apply_singleton (a : 
α) : p.toOuterMeasure {a} = p a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMeasure_apply_singleton (a : α) (h : MeasurableSet ({a} : Set α)) :
    p.toMeasure {a} = p a := by
  simp [p.toMeasure_apply_eq_toOuterMeasure_apply h, toOuterMeasure_apply_singleton]
/-
**PMF.toMeasure_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply_eq_zero_iff (hs : MeasurableSet s) : p.toMeasure s = 0 ↔ D
isjoint p.support s
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_apply_eq_zero_iff`：toOuterMeasure_apply_eq_zero_iff :
 p.toOuterMeasure s = 0 ↔ Disjoint p.support s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toMeasure_apply_eq_zero_iff (hs : MeasurableSet s) :
    p.toMeasure s = 0 ↔ Disjoint p.support s := by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs, toOuterMeasure_apply_eq_zero_iff]
/-
**PMF.toMeasure_apply_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply_eq_one_iff (hs : MeasurableSet s) : p.toMeasure s = 1 ↔ p.
support subseteq s
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.toOuterMeasure_apply_eq_one_iff`：toOuterMeasure_apply_eq_one_iff : p
.toOuterMeasure s = 1 ↔ p.support subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
-/
theorem toMeasure_apply_eq_one_iff (hs : MeasurableSet s) : p.toMeasure s = 1 ↔ p.support ⊆ s :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply hs).symm ▸ p.toOuterMeasure_apply_eq_one_iff s
/-
**PMF.toMeasure_mono** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_mono {t : Set α} (hs : MeasurableSet s) (h : s inter p.support s
ubseteq t) : p.toMeasure s <= p.toMeasure t
参数：hs : MeasurableSet s；h : s inter p.support subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `PMF.toOuterMeasure_mono`：toOuterMeasure_mono {s t : Set α} (h : s inter 
p.support subseteq t) : p.toOuterMeasure s <= p.toOuterMeasure t
· 使用定理 `PMF.toOuterMeasure_apply_le_toMeasure_apply`：toOuterMeasure_apply_le_toM
easure_apply (s : Set α) : p.toOuterMeasure s <= p.toMeasure s
-/
theorem toMeasure_mono {t : Set α} (hs : MeasurableSet s)
    (h : s ∩ p.support ⊆ t) : p.toMeasure s ≤ p.toMeasure t := by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]
  exact (p.toOuterMeasure_mono h).trans (p.toOuterMeasure_apply_le_toMeasure_apply t)

@[simp]
/-
**PMF.toMeasure_apply_inter_support** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply_inter_support (hs : MeasurableSet s) : p.toMeasure (s inte
r p.support) = p.toMeasure s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `PMF.toMeasure_mono`：toMeasure_mono {t : Set α} (hs : MeasurableSet s) (h
 : s inter p.support subseteq t) : p.toMeasure s <= p.toMeasure t
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem toMeasure_apply_inter_support (hs : MeasurableSet s) :
    p.toMeasure (s ∩ p.support) = p.toMeasure s :=
  (measure_mono s.inter_subset_left).antisymm (p.toMeasure_mono hs (refl _))

@[simp]
/-
**PMF.restrict_toMeasure_support** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：restrict_toMeasure_support : p.toMeasure.restrict p.support = p.toMeasure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `PMF.toMeasure_apply_inter_support`：toMeasure_apply_inter_support (hs : M
easurableSet s) : p.toMeasure (s inter p.support) = p.toMeasure s
-/
theorem restrict_toMeasure_support : p.toMeasure.restrict p.support = p.toMeasure := by
  ext s hs
  rw [Measure.restrict_apply hs, p.toMeasure_apply_inter_support hs]
/-
**PMF.toMeasure_apply_eq_of_inter_support_eq** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply_eq_of_inter_support_eq {t : Set α} (hs : MeasurableSet s) 
(ht : MeasurableSet t) (h : s inter p.support = t inter p.support) : p.toMeasure
 s = p.toMeasure t
参数：hs : MeasurableSet s；ht : MeasurableSet t；h : s inter p.support = t inter p.s
upport。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_apply_eq_of_inter_support_eq`：toOuterMeasure_apply_eq
_of_inter_support_eq {s t : Set α} (h : s inter p.support = t inter p.support) :
 p.toOuterMeasure s = p.toOuterMeasur…
-/
theorem toMeasure_apply_eq_of_inter_support_eq {t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : s ∩ p.support = t ∩ p.support) : p.toMeasure s = p.toMeasure t := by
  simpa only [p.toMeasure_apply_eq_toOuterMeasure_apply, hs, ht] using
    p.toOuterMeasure_apply_eq_of_inter_support_eq h

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

/-
**PMF.toMeasure_injective** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_injective : (toMeasure : PMF α -> Measure α).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PMF.toMeasure_apply_singleton`：toMeasure_apply_singleton (a : α) (h : Me
asurableSet ({a} : Set α)) : p.toMeasure {a} = p a
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
-/
theorem toMeasure_injective : (toMeasure : PMF α → Measure α).Injective := by
  intro p q h
  ext x
  rw [← p.toMeasure_apply_singleton x <| measurableSet_singleton x,
    ← q.toMeasure_apply_singleton x <| measurableSet_singleton x, h]

@[simp]
/-
**PMF.toMeasure_inj** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_inj {p q : PMF α} : p.toMeasure = q.toMeasure ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `PMF.toMeasure_injective`：toMeasure_injective : (toMeasure : PMF α -> Mea
sure α).Injective
-/
theorem toMeasure_inj {p q : PMF α} : p.toMeasure = q.toMeasure ↔ p = q :=
  toMeasure_injective.eq_iff
/-
**PMF.toMeasure_apply_eq_toOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply_eq_toOuterMeasure (s : Set α) : p.toMeasure s = p.toOuterM
easure s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `PMF.support_countable`：support_countable (p : PMF α) : p.support.Countab
le
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PMF.restrict_toMeasure_support`：restrict_toMeasure_support : p.toMeasure
.restrict p.support = p.toMeasure
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_apply_inter_support`：toOuterMeasure_apply_inter_suppo
rt : p.toOuterMeasure (s inter p.support) = p.toOuterMeasure s
-/
theorem toMeasure_apply_eq_toOuterMeasure (s : Set α) : p.toMeasure s = p.toOuterMeasure s := by
  have hs := (p.support_countable.mono s.inter_subset_right).measurableSet
  rw [← restrict_toMeasure_support, Measure.restrict_apply' p.support_countable.measurableSet,
    p.toMeasure_apply_eq_toOuterMeasure_apply hs, toOuterMeasure_apply_inter_support]

@[simp]
/-
**PMF.toMeasure_apply_finset** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply_finset (s : Finset α) : p.toMeasure s = ∑ x in s, p x
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure`：toMeasure_apply_eq_toOuterMeasure
 (s : Set α) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_apply_finset`：toOuterMeasure_apply_finset (s : Finset
 α) : p.toOuterMeasure s = ∑ x in s, p x
-/
theorem toMeasure_apply_finset (s : Finset α) : p.toMeasure s = ∑ x ∈ s, p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_finset s)
/-
**PMF.toMeasure_apply_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply_eq_tsum (s : Set α) : p.toMeasure s = ∑' x, s.indicator p 
x
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure`：toMeasure_apply_eq_toOuterMeasure
 (s : Set α) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
-/
theorem toMeasure_apply_eq_tsum (s : Set α) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply s)

@[simp]
/-
**PMF.toMeasure_apply_fintype** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_apply_fintype (s : Set α) [Fintype α] : p.toMeasure s = ∑ x, s.i
ndicator p x
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure`：toMeasure_apply_eq_toOuterMeasure
 (s : Set α) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_apply_fintype`：toOuterMeasure_apply_fintype [Fintype 
α] : p.toOuterMeasure s = ∑ x, s.indicator p x
-/
theorem toMeasure_apply_fintype (s : Set α) [Fintype α] : p.toMeasure s = ∑ x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_fintype s)

end MeasurableSingletonClass

end Measure

end PMF

namespace MeasureTheory

open PMF

namespace Measure

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any probability measure into a `PMF`, where the mass of a point
is the measure of the singleton set under the original measure. -/
/-
**MeasureTheory.Measure.toPMF** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：toPMF [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : 
Measure α) [h : IsProbabilityMeasure μ] : PMF α
参数：μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given that `α` is a countable, measurable space with all singleton sets measurab
le,
we can convert any probability measure into a `PMF`, where the mass of a point
is the measure of the singleton set under the original measure.
-/
def toPMF [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
    [h : IsProbabilityMeasure μ] : PMF α :=
  ⟨fun x => μ ({x} : Set α),
    ENNReal.summable.hasSum_iff.2
      (_root_.trans
        (symm <|
          (tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ).symm.trans
            (tsum_congr fun x => congr_fun (Set.indicator_univ _) x))
        h.measure_univ)⟩

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
  [IsProbabilityMeasure μ]
/-
**MeasureTheory.Measure.toPMF_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：toPMF_apply (x : α) : μ.toPMF x = μ {x}
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPMF_apply (x : α) : μ.toPMF x = μ {x} := rfl

@[simp]
/-
**MeasureTheory.Measure.toPMF_toMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：toPMF_toMeasure : μ.toPMF.toMeasure = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toMeasure_apply`：toMeasure_apply (hs : MeasurableSet s) : p.toMeasur
e s = ∑' x, s.indicator p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.tsum_indicator_apply_singleton`：tsum_indicator_app
ly_singleton [Countable α] [MeasurableSingletonClass α] (μ : Measure α) (s : Set
 α) (hs : MeasurableSet s) : (∑' x : α, s.…
-/
theorem toPMF_toMeasure : μ.toPMF.toMeasure = μ :=
  Measure.ext fun s hs => by
    rw [μ.toPMF.toMeasure_apply hs, ← μ.tsum_indicator_apply_singleton s hs]
    rfl

end Measure

end MeasureTheory

namespace PMF

/-- The measure associated to a `PMF` by `toMeasure` is a probability measure. -/
/-
**PMF.toMeasure.isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `PMF.toMeasure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] (p : PMF α), MeasureTheory.IsP
robabilityMeasure p.toMeasure
参数：p : PMF α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.indicator_univ`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f :
 α → M), Set.univ.indicator f = f
· 使用定理 `PMF.tsum_coe`：tsum_coe (p : PMF α) : ∑' a, p a = 1

--- 原说明 ---
The measure associated to a `PMF` by `toMeasure` is a probability measure.
-/
instance toMeasure.isProbabilityMeasure [MeasurableSpace α] (p : PMF α) :
    IsProbabilityMeasure p.toMeasure :=
  ⟨by
    simpa only [MeasurableSet.univ, toMeasure_apply_eq_toOuterMeasure_apply, Set.indicator_univ,
      toOuterMeasure_apply, ENNReal.coe_eq_one] using tsum_coe p⟩

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α)

@[simp]
/-
**PMF.toMeasure_toPMF** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_toPMF : p.toMeasure.toPMF = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `PMF.toMeasure.isProbabilityMeasure`：∀ {α : Type u_1} [inst : MeasurableS
pace α] (p : PMF α), MeasureTheory.IsProbabilityMeasure p.toMeasure
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PMF.toMeasure_apply_singleton`：toMeasure_apply_singleton (a : α) (h : Me
asurableSet ({a} : Set α)) : p.toMeasure {a} = p a
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `MeasureTheory.Measure.toPMF_apply`：toPMF_apply (x : α) : μ.toPMF x = μ {
x}
-/
theorem toMeasure_toPMF : p.toMeasure.toPMF = p :=
  PMF.ext fun x => by
    rw [← p.toMeasure_apply_singleton x (measurableSet_singleton x), p.toMeasure.toPMF_apply]
/-
**PMF.toMeasure_eq_iff_eq_toPMF** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_eq_iff_eq_toPMF (μ : Measure α) [IsProbabilityMeasure μ] : p.toM
easure = μ ↔ p = μ.toPMF
参数：μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PMF.toMeasure_inj`：toMeasure_inj {p q : PMF α} : p.toMeasure = q.toMeasu
re ↔ p = q
· 使用定理 `MeasureTheory.Measure.toPMF_toMeasure`：toPMF_toMeasure : μ.toPMF.toMeasu
re = μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toMeasure_eq_iff_eq_toPMF (μ : Measure α) [IsProbabilityMeasure μ] :
    p.toMeasure = μ ↔ p = μ.toPMF := by rw [← toMeasure_inj, Measure.toPMF_toMeasure]
/-
**PMF.toPMF_eq_iff_toMeasure_eq** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toPMF_eq_iff_toMeasure_eq (μ : Measure α) [IsProbabilityMeasure μ] : μ.toP
MF = p ↔ μ = p.toMeasure
参数：μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PMF.toMeasure_inj`：toMeasure_inj {p q : PMF α} : p.toMeasure = q.toMeasu
re ↔ p = q
· 使用定理 `MeasureTheory.Measure.toPMF_toMeasure`：toPMF_toMeasure : μ.toPMF.toMeasu
re = μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toPMF_eq_iff_toMeasure_eq (μ : Measure α) [IsProbabilityMeasure μ] :
    μ.toPMF = p ↔ μ = p.toMeasure := by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

end PMF

