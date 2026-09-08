/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Indexed product measures

In this file we define and prove properties about finite products of measures
(and at some point, countable products of measures).

## Main definition

* `MeasureTheory.Measure.pi`: The product of finitely many σ-finite measures.
  Given `μ : (i : ι) → Measure (α i)` for `[Fintype ι]` it has type `Measure ((i : ι) → α i)`.

To apply Fubini's theorem or Tonelli's theorem along some subset, we recommend using the marginal
construction `MeasureTheory.lmarginal` and (todo) `MeasureTheory.marginal`. This allows you to
apply these theorems without any bookkeeping with measurable equivalences.

## Implementation Notes

We define `MeasureTheory.OuterMeasure.pi`, the product of finitely many outer measures, as the
maximal outer measure `n` with the property that `n (pi univ s) ≤ ∏ i, m i (s i)`,
where `pi univ s` is the product of the sets `{s i | i : ι}`.

We then show that this induces a product of measures, called `MeasureTheory.Measure.pi`.
For a collection of σ-finite measures `μ` and a collection of measurable sets `s` we show that
`Measure.pi μ (pi univ s) = ∏ i, m i (s i)`. To do this, we follow the following steps:
* We know that there is some ordering on `ι`, given by an element of `[Countable ι]`.
* Using this, we have an equivalence `MeasurableEquiv.piMeasurableEquivTProd` between
  `∀ i, α i` and an iterated product of `α i`, called `List.tprod α l` for some list `l`.
* On this iterated product we can easily define a product measure `MeasureTheory.Measure.tprod`
  by iterating `MeasureTheory.Measure.prod`
* Using the previous two steps we construct `MeasureTheory.Measure.pi'` on `(i : ι) → α i` for
  countable `ι`.
* We know that `MeasureTheory.Measure.pi'` sends products of sets to products of measures, and
  since `MeasureTheory.Measure.pi` is the maximal such measure (or at least, it comes from an outer
  measure which is the maximal such outer measure), we get the same rule for
  `MeasureTheory.Measure.pi`.

## Tags

finitary product measure

-/

@[expose] public section

noncomputable section

open Function Set MeasureTheory.OuterMeasure Filter MeasurableSpace Encodable

open scoped Topology ENNReal

universe u v

variable {ι ι' : Type*} {α : ι → Type*}

namespace MeasureTheory

variable [Fintype ι] {m : ∀ i, OuterMeasure (α i)}

/-- An upper bound for the measure in a finite product space.
  It is defined by taking the image of the set under all projections, and taking the product
  of the measures of these images.
  For measurable boxes it is equal to the correct measure. -/
/-
**MeasureTheory.piPremeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：piPremeasure (m : forall i, OuterMeasure (α i)) (s : Set (forall i, α i)) 
: Real>=0∞
参数：m : forall i, OuterMeasure (α i)；s : Set (forall i, α i)。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An upper bound for the measure in a finite product space.
  It is defined by taking the image of the set under all projections, and taking
 the product
  of the measures of these images.
  For measurable boxes it is equal to the correct measure.
-/
def piPremeasure (m : ∀ i, OuterMeasure (α i)) (s : Set (∀ i, α i)) : ℝ≥0∞ :=
  ∏ i, m i (eval i '' s)
/-
**MeasureTheory.piPremeasure_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：piPremeasure_pi {s : forall i, Set (α i)} (hs : (pi univ s).Nonempty) : pi
Premeasure m (pi univ s) = ∏ i, m i (s i)
参数：α i；hs : (pi univ s).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.eval_image_univ_pi`：eval_image_univ_pi (ht : (pi univ t).Nonempty) :
 (fun f : forall i, α i => f i) '' pi univ t = t i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piPremeasure_pi {s : ∀ i, Set (α i)} (hs : (pi univ s).Nonempty) :
    piPremeasure m (pi univ s) = ∏ i, m i (s i) := by simp [hs, piPremeasure]
/-
**MeasureTheory.piPremeasure_pi'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：piPremeasure_pi' {s : forall i, Set (α i)} : piPremeasure m (pi univ s) = 
∏ i, m i (s i)
参数：α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_pi_eq_empty_iff`：univ_pi_eq_empty_iff : pi univ t = ∅ ↔ exists 
i, t i = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.eval_image_univ_pi`：eval_image_univ_pi (ht : (pi univ t).Nonempty) :
 (fun f : forall i, α i => f i) '' pi univ t = t i
-/
theorem piPremeasure_pi' {s : ∀ i, Set (α i)} : piPremeasure m (pi univ s) = ∏ i, m i (s i) := by
  cases isEmpty_or_nonempty ι
  · simp [piPremeasure]
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩
    have : ∃ i, m i (s i) = 0 := ⟨i, by simp [hi]⟩
    simpa [h, Finset.card_univ, zero_pow Fintype.card_ne_zero, @eq_comm _ (0 : ℝ≥0∞),
      Finset.prod_eq_zero_iff, piPremeasure]
  · simp [h, piPremeasure]
/-
**MeasureTheory.piPremeasure_pi_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：piPremeasure_pi_mono {s t : Set (forall i, α i)} (h : s subseteq t) : piPr
emeasure m s <= piPremeasure m t
参数：forall i, α i；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem piPremeasure_pi_mono {s t : Set (∀ i, α i)} (h : s ⊆ t) :
    piPremeasure m s ≤ piPremeasure m t :=
  Finset.prod_le_prod' fun _ _ => measure_mono (Set.image_mono h)
/-
**MeasureTheory.piPremeasure_pi_eval** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：piPremeasure_pi_eval {s : Set (forall i, α i)} : piPremeasure m (pi univ f
un i => eval i '' s) = piPremeasure m s
参数：forall i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `MeasureTheory.piPremeasure_pi'`：piPremeasure_pi' {s : forall i, Set (α i
)} : piPremeasure m (pi univ s) = ∏ i, m i (s i)
-/
theorem piPremeasure_pi_eval {s : Set (∀ i, α i)} :
    piPremeasure m (pi univ fun i => eval i '' s) = piPremeasure m s := by
  simp only [eval, piPremeasure_pi']; rfl

namespace OuterMeasure

/-- `OuterMeasure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{s i | i : ι}`. -/
/-
**MeasureTheory.OuterMeasure.pi** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.OuterMe
asure`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_3} →     [Fintype ι] → ((i : ι) → Measu
reTheory.OuterMeasure (α i)) → MeasureTheory.OuterMeasure ((i : ι) → α i)
参数：(i : ι) → MeasureTheory.OuterMeasure (α i)；(i : ι) → α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OuterMeasure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{s i | i : ι}`.
-/
protected def pi (m : ∀ i, OuterMeasure (α i)) : OuterMeasure (∀ i, α i) :=
  boundedBy (piPremeasure m)
/-
**MeasureTheory.OuterMeasure.pi_pi_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：pi_pi_le (m : forall i, OuterMeasure (α i)) (s : forall i, Set (α i)) : Ou
terMeasure.pi m (pi univ s) <= ∏ i, m i (s i)
参数：m : forall i, OuterMeasure (α i)；s : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_le`：boundedBy_le (s : Set α) : boun
dedBy m s <= m s
· 使用定理 `MeasureTheory.piPremeasure_pi`：piPremeasure_pi {s : forall i, Set (α i)}
 (hs : (pi univ s).Nonempty) : piPremeasure m (pi univ s) = ∏ i, m i (s i)
-/
theorem pi_pi_le (m : ∀ i, OuterMeasure (α i)) (s : ∀ i, Set (α i)) :
    OuterMeasure.pi m (pi univ s) ≤ ∏ i, m i (s i) := by
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · simp [h]
  exact (boundedBy_le _).trans_eq (piPremeasure_pi h)
/-
**MeasureTheory.OuterMeasure.le_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Oute
rMeasure`。
形式化陈述：le_pi {m : forall i, OuterMeasure (α i)} {n : OuterMeasure (forall i, α i)
} : n <= OuterMeasure.pi m ↔ forall s : forall i, Set (α i), (pi univ s).Nonempt
y -> n (pi univ s) <= ∏ i, m i (s i)
参数：α i；forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.pi.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_3} 
[inst : Fintype ι] (m : (i : ι) → MeasureTheory.OuterMeasure (α i)),   MeasureTh
eory.OuterMeasure.pi m =…
· 使用定理 `MeasureTheory.OuterMeasure.le_boundedBy'`：le_boundedBy' {μ : OuterMeasur
e α} : μ <= boundedBy m ↔ forall s : Set α, s.Nonempty -> μ s <= m s
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.piPremeasure_pi`：piPremeasure_pi {s : forall i, Set (α i)}
 (hs : (pi univ s).Nonempty) : piPremeasure m (pi univ s) = ∏ i, m i (s i)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.subset_pi_eval_image`：subset_pi_eval_image (s : Set ι) (u : Set (for
all i, α i)) : u subseteq pi s fun i => eval i '' u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem le_pi {m : ∀ i, OuterMeasure (α i)} {n : OuterMeasure (∀ i, α i)} :
    n ≤ OuterMeasure.pi m ↔
      ∀ s : ∀ i, Set (α i), (pi univ s).Nonempty → n (pi univ s) ≤ ∏ i, m i (s i) := by
  rw [OuterMeasure.pi, le_boundedBy']; constructor
  · intro h s hs; refine (h _ hs).trans_eq (piPremeasure_pi hs)
  · intro h s hs; refine le_trans (n.mono <| subset_pi_eval_image univ s) (h _ ?_)
    simp [univ_pi_nonempty_iff, hs]

end OuterMeasure

namespace Measure

variable [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))

section Tprod

open List

variable {δ : Type*} {X : δ → Type*} [∀ i, MeasurableSpace (X i)]

-- for some reason the equation compiler doesn't like this definition
/-- A product of measures in `tprod α l`. -/
/-
**MeasureTheory.Measure.tprod** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：{δ : Type u_4} →   {X : δ → Type u_5} →     [inst : (i : δ) → MeasurableSp
ace (X i)] →       (l : List δ) → ((i : δ) → MeasureTheory.Measure (X i)) → Meas
ureTheory.Measure (List.TProd X l)
参数：i : δ；X i；l : List δ；(i : δ) → MeasureTheory.Measure (X i)；List.TProd X l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product of measures in `tprod α l`.
-/
protected def tprod (l : List δ) (μ : ∀ i, Measure (X i)) : Measure (TProd X l) := by
  induction l with
  | nil => exact dirac PUnit.unit
  | cons i l ih => exact (μ i).prod (α := X i) ih

@[simp]
/-
**MeasureTheory.Measure.tprod_nil** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：tprod_nil (μ : forall i, Measure (X i)) : Measure.tprod [] μ = dirac PUnit
.unit
参数：μ : forall i, Measure (X i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tprod_nil (μ : ∀ i, Measure (X i)) : Measure.tprod [] μ = dirac PUnit.unit :=
  rfl

@[simp]
/-
**MeasureTheory.Measure.tprod_cons** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：tprod_cons (i : δ) (l : List δ) (μ : forall i, Measure (X i)) : Measure.tp
rod (i :: l) μ = (μ i).prod (Measure.tprod l μ)
参数：i : δ；l : List δ；μ : forall i, Measure (X i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tprod_cons (i : δ) (l : List δ) (μ : ∀ i, Measure (X i)) :
    Measure.tprod (i :: l) μ = (μ i).prod (Measure.tprod l μ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.Measure.sigmaFinite_tprod** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：sigmaFinite_tprod (l : List δ) (μ : forall i, Measure (X i)) [forall i, Si
gmaFinite (μ i)] : SigmaFinite (Measure.tprod l μ)
参数：l : List δ；μ : forall i, Measure (X i)；μ i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.tprod_nil`：tprod_nil (μ : forall i, Measure (X i))
 : Measure.tprod [] μ = dirac PUnit.unit
· 使用定理 `MeasureTheory.Measure.dirac.instSigmaFinite`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {a : α}, MeasureTheory.SigmaFinite (MeasureTheory.Measure.dirac
 a)
· 使用定理 `MeasureTheory.Measure.tprod_cons`：tprod_cons (i : δ) (l : List δ) (μ : f
orall i, Measure (X i)) : Measure.tprod (i :: l) μ = (μ i).prod (Measure.tprod l
 μ)
· 使用定理 `MeasureTheory.Measure.prod.instSigmaFinite`：∀ {α : Type u_4} {β : Type u
_5} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFi
nite μ]   {x_1 : MeasurableSpace…
-/
instance sigmaFinite_tprod (l : List δ) (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] :
    SigmaFinite (Measure.tprod l μ) := by
  induction l with
  | nil => rw [tprod_nil]; infer_instance
  | cons i l ih => rw [tprod_cons]; exact @prod.instSigmaFinite _ _ _ _ _ _ _ ih

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.Measure.tprod_tprod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：tprod_tprod (l : List δ) (μ : forall i, Measure (X i)) [forall i, SigmaFin
ite (μ i)] (s : forall i, Set (X i)) : Measure.tprod l μ (Set.tprod l s) = (l.ma
p fun i => (μ i) (s i)).prod
参数：l : List δ；μ : forall i, Measure (X i)；μ i；s : forall i, Set (X i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.tprod_cons`：tprod_cons (i : δ) (l : List δ) (μ : f
orall i, Measure (X i)) : Measure.tprod (i :: l) μ = (μ i).prod (Measure.tprod l
 μ)
· 使用定理 `Set.tprod.eq_2`：∀ {ι : Type u} {α : ι → Type v} (x : (i : ι) → Set (α i)
) (i : ι) (is : List ι),   Set.tprod (i :: is) x = x i ×ˢ Set.tprod is x
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
-/
theorem tprod_tprod (l : List δ) (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (s : ∀ i, Set (X i)) :
    Measure.tprod l μ (Set.tprod l s) = (l.map fun i => (μ i) (s i)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [tprod_cons, Set.tprod]
    simp only [foldr_cons, prod_cons, map_cons]
    rw [prod_prod, ih]

end Tprod

section Encodable

open List

variable [Encodable ι]

open scoped Classical in
/-- The product measure on an encodable finite type, defined by mapping `Measure.tprod` along the
  equivalence `MeasurableEquiv.piMeasurableEquivTProd`.
  The definition `MeasureTheory.Measure.pi` should be used instead of this one. -/
/-
**MeasureTheory.Measure.pi'** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：pi' : Measure (forall i, α i)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.mem_sortedUniv`：mem_sortedUniv {α} [Fintype α] [Encodable α] (
x : α) : x in sortedUniv α

--- 原说明 ---
The product measure on an encodable finite type, defined by mapping `Measure.tpr
od` along the
  equivalence `MeasurableEquiv.piMeasurableEquivTProd`.
  The definition `MeasureTheory.Measure.pi` should be used instead of this one.
-/
def pi' : Measure (∀ i, α i) :=
  Measure.map (TProd.elim' mem_sortedUniv) (Measure.tprod (sortedUniv ι) μ)
/-
**MeasureTheory.Measure.pi'_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`
。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [inst_2 : 
Encodable ι] [∀ (i : ι), MeasureTheory.SigmaFinite (μ i)]   (s : (i : ι) → Set (
α i)), (MeasureTheory.Measure.pi' μ) (Set.univ.pi s) = ∏ i, (μ i) (s i)
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；s : (i : ι) → S
et (α i)；MeasureTheory.Measure.pi' μ；Set.univ.pi s；μ i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.mem_sortedUniv`：mem_sortedUniv {α} [Fintype α] [Encodable α] (
x : α) : x in sortedUniv α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.pi'.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_3} [ins
t : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → Measu
reTheory.Measure (α …
· 使用定理 `Encodable.sortedUniv_nodup`：sortedUniv_nodup (α) [Fintype α] [Encodable 
α] : (sortedUniv α).Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEquiv.piMeasurableEquivTProd_symm_apply`：∀ {δ' : Type u_5} {π 
: δ' → Type u_6} [inst : (x : δ') → MeasurableSpace (π x)] [inst_1 : DecidableEq
 δ'] {l : List δ'}   (hnd : l.Nodup) (h…
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `Set.elim_preimage_pi`：elim_preimage_pi [DecidableEq ι] {l : List ι} (hnd
 : l.Nodup) (h : forall i, i in l) (t : forall i, Set (α i)) : TProd.elim' h ⁻¹'
 pi univ t…
· 使用定理 `MeasureTheory.Measure.tprod_tprod`：tprod_tprod (l : List δ) (μ : forall 
i, Measure (X i)) [forall i, SigmaFinite (μ i)] (s : forall i, Set (X i)) : Meas
ure.tprod l μ (Set.tpro…
· 使用定理 `List.prod_toFinset`：prod_toFinset {M : Type*} [DecidableEq ι] [CommMonoi
d M] (f : ι -> M) : forall {l : List ι} (_hl : l.Nodup), l.toFinset.prod f = (l.
map f).p…
· 使用定理 `Encodable.sortedUniv_toFinset`：sortedUniv_toFinset (α) [Fintype α] [Enco
dable α] [DecidableEq α] : (sortedUniv α).toFinset = Finset.univ
-/
theorem pi'_pi [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) :
    pi' μ (pi univ s) = ∏ i, μ i (s i) := by
  classical
  rw [pi']
  rw [← MeasurableEquiv.piMeasurableEquivTProd_symm_apply, MeasurableEquiv.map_apply,
    MeasurableEquiv.piMeasurableEquivTProd_symm_apply, elim_preimage_pi, tprod_tprod _ μ, ←
    List.prod_toFinset, sortedUniv_toFinset] <;>
  exact sortedUniv_nodup ι

end Encodable

/-
**MeasureTheory.Measure.pi_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：pi_caratheodory : MeasurableSpace.pi <= (OuterMeasure.pi fun i => (μ i).to
OuterMeasure).caratheodory
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.comap.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) 
(m : MeasurableSpace β),   MeasurableSpace.comap f m =     { MeasurableSet' := f
un s => ∃ s', Me…
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_caratheodory`：boundedBy_caratheodor
y {m : Set α -> Real>=0∞} {s : Set α} (hs : forall t, m (t inter s) + m (t \ s) 
<= m t) : MeasurableSet[(boundedBy m).c…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Finset.prod_add_prod_le'`：prod_add_prod_le' (hi : i in s) (h2i : g i + h
 i <= f i) (hgf : forall j in s, j != i -> g j <= f j) (hhf : forall j in s, j !
= i -> h j <= …
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
· 使用定理 `Set.image_sdiff_preimage`：image_sdiff_preimage {f : α -> β} {s : Set α} 
{t : Set β} : f '' (s \ f ⁻¹' t) = f '' s \ t
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
theorem pi_caratheodory :
    MeasurableSpace.pi ≤ (OuterMeasure.pi fun i => (μ i).toOuterMeasure).caratheodory := by
  refine iSup_le ?_
  intro i s hs
  rw [MeasurableSpace.comap] at hs
  rcases hs with ⟨s, hs, rfl⟩
  apply boundedBy_caratheodory
  intro t
  simp_rw [piPremeasure]
  refine Finset.prod_add_prod_le' (Finset.mem_univ i) ?_ ?_ ?_
  · simp [image_inter_preimage, image_sdiff_preimage, measure_inter_add_sdiff _ hs]
  · rintro j - _; gcongr; apply inter_subset_left
  · rintro j - _; gcongr; apply sdiff_subset

/-- `Measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be measure corresponding to `MeasureTheory.OuterMeasure.pi`. -/
protected irreducible_def pi : Measure (∀ i, α i) :=
  toMeasure (OuterMeasure.pi fun i => (μ i).toOuterMeasure) (pi_caratheodory μ)

/-
**MeasureTheory.Measure._root_.MeasureTheory.MeasureSpace.pi** 是 Mathlib 中的一个实例，
位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.MeasureTheory.MeasureSpace.pi {α : ι → Type*} [∀ i, MeasureSpace (α i)] :
    MeasureSpace (∀ i, α i) :=
  ⟨Measure.pi fun _ => volume⟩
/-
**MeasureTheory.Measure.pi_pi_aux** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：pi_pi_aux [forall i, SigmaFinite (μ i)] (s : forall i, Set (α i)) (hs : fo
rall i, MeasurableSet (s i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
参数：μ i；s : forall i, Set (α i)；hs : forall i, MeasurableSet (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.Measure.pi_caratheodory`：pi_caratheodory : MeasurableSpace
.pi <= (OuterMeasure.pi fun i => (μ i).toOuterMeasure).caratheodory
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.pi_def`：∀ {ι : Type u_4} {α : ι → Type u_5} [inst 
: Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → Measure
Theory.Measure (α …
· 使用定理 `MeasureTheory.toMeasure_apply`：toMeasure_apply (m : OuterMeasure α) (h :
 ms <= m.caratheodory) {s : Set α} (hs : MeasurableSet s) : m.toMeasure h s = m 
s
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Set.countable_univ`：countable_univ [Countable α] : (univ : Set α).Counta
ble
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.OuterMeasure.pi_pi_le`：pi_pi_le (m : forall i, OuterMeasur
e (α i)) (s : forall i, Set (α i)) : OuterMeasure.pi m (pi univ s) <= ∏ i, m i (
s i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi'_pi`：∀ {ι : Type u_1} {α : ι → Type u_3} [inst 
: Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → Measure
Theory.Measure (α …
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `MeasureTheory.OuterMeasure.le_pi`：le_pi {m : forall i, OuterMeasure (α i
)} {n : OuterMeasure (forall i, α i)} : n <= OuterMeasure.pi m ↔ forall s : fora
ll i, Set (α i), (pi u…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem pi_pi_aux [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) (hs : ∀ i, MeasurableSet (s i)) :
    Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
  refine le_antisymm ?_ ?_
  · rw [Measure.pi, toMeasure_apply _ _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
    apply OuterMeasure.pi_pi_le
  · have : Encodable ι := Fintype.toEncodable ι
    simp_rw [← pi'_pi μ s, Measure.pi,
      toMeasure_apply _ _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
    suffices (pi' μ).toOuterMeasure ≤ OuterMeasure.pi fun i => (μ i).toOuterMeasure by exact this _
    clear hs s
    rw [OuterMeasure.le_pi]
    intro s _
    exact (pi'_pi μ s).le

variable {μ}

/-- `Measure.pi μ` has finite spanning sets in rectangles of finite spanning sets. -/
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.pi** 是 Mathlib 中的一个定义，位于命名空间 `Measu
reTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_3} →     [inst : Fintype ι] →       [in
st_1 : (i : ι) → MeasurableSpace (α i)] →         {μ : (i : ι) → MeasureTheory.M
easure (α i)} →           {C : (i : ι) → Set (Set (α i))} →             ((i : ι)
 → (μ i).FiniteSpanningSetsIn (C i)) →               (MeasureTheory.Measure.pi μ
).FiniteSpanningSetsIn (Set.univ.pi '' Set.univ.pi C)
参数：i : ι；α i；i : ι；α i；i : ι；Set (α i)；(i : ι) → (μ i).FiniteSpanningSetsIn (C i
)；MeasureTheory.Measure.pi μ；Set.univ.pi '' Set.univ.pi C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Measure.pi μ` has finite spanning sets in rectangles of finite spanning sets.
-/
def FiniteSpanningSetsIn.pi {C : ∀ i, Set (Set (α i))}
    (hμ : ∀ i, (μ i).FiniteSpanningSetsIn (C i)) :
    (Measure.pi μ).FiniteSpanningSetsIn (pi univ '' pi univ C) := by
  haveI := fun i => (hμ i).sigmaFinite
  haveI := Fintype.toEncodable ι
  refine ⟨fun n => Set.pi univ fun i => (hμ i).set ((@decode (ι → ℕ) _ n).getD default i),
    fun n => ?_, fun n => ?_, ?_⟩ <;>
  -- TODO (kmill) If this let comes before the refine, while the noncomputability checker
  -- correctly sees this definition is computable, the Lean VM fails to see the binding is
  -- computationally irrelevant. The `noncomputable section` doesn't help because all it does
  -- is insert `noncomputable` for you when necessary.
  let e : ℕ → ι → ℕ := fun n => (@decode (ι → ℕ) _ n).getD default
  · refine mem_image_of_mem _ fun i _ => (hμ i).set_mem _
  · calc
      Measure.pi μ (Set.pi univ fun i => (hμ i).set (e n i)) ≤
          Measure.pi μ (Set.pi univ fun i => toMeasurable (μ i) ((hμ i).set (e n i))) :=
        measure_mono (pi_mono fun i _ => subset_toMeasurable _ _)
      _ = ∏ i, μ i (toMeasurable (μ i) ((hμ i).set (e n i))) :=
        (pi_pi_aux μ _ fun i => measurableSet_toMeasurable _ _)
      _ = ∏ i, μ i ((hμ i).set (e n i)) := by simp only [measure_toMeasurable]
      _ < ∞ := ENNReal.prod_lt_top fun i _ => (hμ i).finite _
  · simp_rw [(surjective_decode_getD (ι → ℕ) default).iUnion_comp fun x =>
        Set.pi univ fun i => (hμ i).set (x i),
      iUnion_univ_pi fun i => (hμ i).set, (hμ _).spanning, Set.pi_univ]

/-- A measure on a finite product space equals the product measure if they are equal on rectangles
  with as sides sets that generate the corresponding σ-algebras. -/
/-
**MeasureTheory.Measure.pi_eq_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：pi_eq_generateFrom {C : forall i, Set (Set (α i))} (hC : forall i, generat
eFrom (C i) = by apply_assumption) (h2C : forall i, IsPiSystem (C i)) (h3C : for
all i, (μ i).FiniteSpanningSetsIn (C i)) {μν : Measure (forall i, α i)} (h₁ : fo
rall s : forall i, Set (α i), (forall i, s i in C i) -> μν (pi univ s) = ∏ i, μ 
i (s i)) : Measure.pi μ = μν
参数：Set (α i)；hC : forall i, generateFrom (C i) = by apply_assumption；h2C : foral
l i, IsPiSystem (C i)；h3C : forall i, (μ i).FiniteSpanningSetsIn (C i)；forall i,
 α i；h₁ : forall s : forall i, Set (α i), (forall i, s i in C i) -> μν (pi univ 
s) = ∏ i, μ i (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.ext`：∀ {α : Type u_1} {m0 : M
easurableSpace α} {μ ν : MeasureTheory.Measure α} {C : Set (Set α)},   m0 = Meas
urableSpace.generateFrom C → IsPiSys…
· 使用定理 `generateFrom_eq_pi`：generateFrom_eq_pi [h : forall i, MeasurableSpace (α
 i)] {C : forall i, Set (Set (α i))} (hC : forall i, generateFrom (C i) = h i) (
h2C : fo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.isCountablySpanning`：∀ {α : T
ype u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)
}   (h : μ.FiniteSpanningSetsIn C), IsCountablySpann…
· 使用定理 `IsPiSystem.pi`：IsPiSystem.pi {C : forall i, Set (Set (α i))} (hC : foral
l i, IsPiSystem (C i)) : IsPiSystem (pi univ '' pi univ C)
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.sigmaFinite`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (h :
 μ.FiniteSpanningSetsIn C), MeasureTheory.Si…
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.pi_pi_aux`：pi_pi_aux [forall i, SigmaFinite (μ i)]
 (s : forall i, Set (α i)) (hs : forall i, MeasurableSet (s i)) : Measure.pi μ (
pi univ s) = ∏ i, μ i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A measure on a finite product space equals the product measure if they are equal
 on rectangles
  with as sides sets that generate the corresponding σ-algebras.
-/
theorem pi_eq_generateFrom {C : ∀ i, Set (Set (α i))}
    (hC : ∀ i, generateFrom (C i) = by apply_assumption) (h2C : ∀ i, IsPiSystem (C i))
    (h3C : ∀ i, (μ i).FiniteSpanningSetsIn (C i)) {μν : Measure (∀ i, α i)}
    (h₁ : ∀ s : ∀ i, Set (α i), (∀ i, s i ∈ C i) → μν (pi univ s) = ∏ i, μ i (s i)) :
    Measure.pi μ = μν := by
  have h4C : ∀ (i) (s : Set (α i)), s ∈ C i → MeasurableSet s := by
    intro i s hs; rw [← hC]; exact measurableSet_generateFrom hs
  refine
    (FiniteSpanningSetsIn.pi h3C).ext
      (generateFrom_eq_pi hC fun i => (h3C i).isCountablySpanning).symm (IsPiSystem.pi h2C) ?_
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_univ_pi] at hs
  have := fun i => (h3C i).sigmaFinite
  simp_rw [h₁ s hs, pi_pi_aux μ s fun i => h4C i _ (hs i)]

/-- A measure on a finite product space equals the product measure if they are equal on
  rectangles. -/
/-
**MeasureTheory.Measure.pi_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：pi_eq [forall i, SigmaFinite (μ i)] {μ' : Measure (forall i, α i)} (h : fo
rall s : forall i, Set (α i), (forall i, MeasurableSet (s i)) -> μ' (pi univ s) 
= ∏ i, μ i (s i)) : Measure.pi μ = μ'
参数：μ i；forall i, α i；h : forall s : forall i, Set (α i), (forall i, MeasurableSe
t (s i)) -> μ' (pi univ s) = ∏ i, μ i (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi_eq_generateFrom`：pi_eq_generateFrom {C : forall
 i, Set (Set (α i))} (hC : forall i, generateFrom (C i) = by apply_assumption) (
h2C : forall i, IsPiSystem (C …
· 使用定理 `MeasurableSpace.generateFrom_measurableSet`：generateFrom_measurableSet [
MeasurableSpace α] : generateFrom {s : Set α | MeasurableSet s} = ‹_›
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }

--- 原说明 ---
A measure on a finite product space equals the product measure if they are equal
 on
  rectangles.
-/
theorem pi_eq [∀ i, SigmaFinite (μ i)] {μ' : Measure (∀ i, α i)}
    (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) → μ' (pi univ s) = ∏ i, μ i (s i)) :
    Measure.pi μ = μ' :=
  pi_eq_generateFrom (fun _ => generateFrom_measurableSet) (fun _ => isPiSystem_measurableSet)
    (fun i => (μ i).toFiniteSpanningSetsIn) h

variable (μ)
/-
**MeasureTheory.Measure.pi'_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [inst_2 : 
Encodable ι] [∀ (i : ι), MeasureTheory.SigmaFinite (μ i)],   MeasureTheory.Measu
re.pi' μ = MeasureTheory.Measure.pi μ
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.Measure.pi'_pi`：∀ {ι : Type u_1} {α : ι → Type u_3} [inst 
: Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → Measure
Theory.Measure (α …
-/
theorem pi'_eq_pi [Encodable ι] [∀ i, SigmaFinite (μ i)] : pi' μ = Measure.pi μ :=
  Eq.symm <| pi_eq fun s _ => pi'_pi μ s

@[simp]
/-
**MeasureTheory.Measure.pi_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：pi_pi [forall i, SigmaFinite (μ i)] (s : (i : ι) -> Set (α i)) : Measure.p
i μ (pi univ s) = ∏ i, μ i (s i)
参数：μ i；s : (i : ι) -> Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi'_eq_pi`：∀ {ι : Type u_1} {α : ι → Type u_3} [in
st : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → Meas
ureTheory.Measure (α …
· 使用定理 `MeasureTheory.Measure.pi'_pi`：∀ {ι : Type u_1} {α : ι → Type u_3} [inst 
: Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → Measure
Theory.Measure (α …
-/
theorem pi_pi [∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i)) :
    Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
  have : Encodable ι := Fintype.toEncodable ι
  rw [← pi'_eq_pi, pi'_pi]

nonrec theorem pi_univ [∀ i, SigmaFinite (μ i)] : Measure.pi μ univ = ∏ i, μ i univ := by
  rw [← pi_univ, pi_pi μ]
/-
**MeasureTheory.Measure.pi_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [∀ (i : ι)
, MeasureTheory.SigmaFinite (μ i)] (f : (i : ι) → α i),   (MeasureTheory.Measure
.pi μ) {f} = ∏ i, (μ i) {f i}
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；f : (i : ι) → α
 i；MeasureTheory.Measure.pi μ；μ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_pi_singleton`：univ_pi_singleton (f : forall i, α i) : (pi univ 
fun i => {f i}) = ({f} : Set (forall i, α i))
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
-/
@[simp] lemma pi_singleton [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i) :
    Measure.pi μ {f} = ∏ i, μ i {f i} := by
  simpa [Set.univ_pi_singleton, -pi_pi] using pi_pi μ fun i ↦ {f i}
/-
**MeasureTheory.Measure.pi.instIsFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [∀ (i : ι)
, MeasureTheory.IsFiniteMeasure (μ i)],   MeasureTheory.IsFiniteMeasure (Measure
Theory.Measure.pi μ)
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；MeasureTheory.M
easure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.prod_lt_top`：prod_lt_top (h : forall a in s, f a < ∞) : ∏ a in s
, f a < ∞
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_univ`：∀ {ι : Type u_1} {α : ι → Type u_3} [inst
 : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → Measur
eTheory.Measure (α …
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
instance pi.instIsFiniteMeasure [∀ i, IsFiniteMeasure (μ i)] :
    IsFiniteMeasure (Measure.pi μ) :=
  ⟨Measure.pi_univ μ ▸ ENNReal.prod_lt_top (fun i _ ↦ measure_lt_top (μ i) _)⟩
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : ι → Type*} [∀ i, MeasureSpace (α i)] [∀ i, IsFiniteMeasure (volume : Measure (α i))] :
    IsFiniteMeasure (volume : Measure (∀ i, α i)) :=
  pi.instIsFiniteMeasure _
/-
**MeasureTheory.Measure.pi.instIsProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure.pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [∀ (i : ι)
, MeasureTheory.IsProbabilityMeasure (μ i)],   MeasureTheory.IsProbabilityMeasur
e (MeasureTheory.Measure.pi μ)
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；MeasureTheory.M
easure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.pi_univ`：∀ {ι : Type u_1} {α : ι → Type u_3} [inst
 : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → Measur
eTheory.Measure (α …
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance pi.instIsProbabilityMeasure [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (Measure.pi μ) :=
  ⟨by simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

@[simp]
/-
**MeasureTheory.Measure.pi_pi_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：pi_pi_finset [forall i, IsProbabilityMeasure (μ i)] (f : (i : ι) -> Set (α
 i)) (s : Finset ι) : Measure.pi μ ((s : Set ι).pi f) = ∏ i in s, μ i (f i)
参数：μ i；f : (i : ι) -> Set (α i)；s : Finset ι。
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
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `Finset.prod_ite_mem`：prod_ite_mem [DecidableEq ι] (s t : Finset ι) (f : 
ι -> M) : ∏ i in s, (if i in t then f i else 1) = ∏ i in s inter t, f i
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pi_pi_finset [∀ i, IsProbabilityMeasure (μ i)] (f : (i : ι) → Set (α i)) (s : Finset ι) :
    Measure.pi μ ((s : Set ι).pi f) = ∏ i ∈ s, μ i (f i) := by
  classical simp [← Set.univ_pi_ite, pi_pi, apply_ite]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : ι → Type*} [∀ i, MeasureSpace (α i)]
    [∀ i, IsProbabilityMeasure (volume : Measure (α i))] :
    IsProbabilityMeasure (volume : Measure (∀ i, α i)) :=
  pi.instIsProbabilityMeasure _

variable [∀ i, SigmaFinite (μ i)]
/-
**MeasureTheory.Measure.pi_ball** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：pi_ball [forall i, MetricSpace (α i)] (x : forall i, α i) {r : Real} (hr :
 0 < r) : Measure.pi μ (Metric.ball x r) = ∏ i, μ i (Metric.ball (x i) r)
参数：α i；x : forall i, α i；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ball_pi`：ball_pi (x : forall b, X b) {r : Real} (hr : 0 < r) : ball x r 
= Set.pi univ fun b => ball (x b) r
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
-/
theorem pi_ball [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 < r) :
    Measure.pi μ (Metric.ball x r) = ∏ i, μ i (Metric.ball (x i) r) := by rw [ball_pi _ hr, pi_pi]
/-
**MeasureTheory.Measure.pi_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：pi_closedBall [forall i, MetricSpace (α i)] (x : forall i, α i) {r : Real}
 (hr : 0 <= r) : Measure.pi μ (Metric.closedBall x r) = ∏ i, μ i (Metric.closedB
all (x i) r)
参数：α i；x : forall i, α i；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `closedBall_pi`：closedBall_pi (x : forall b, X b) {r : Real} (hr : 0 <= r
) : closedBall x r = Set.pi univ fun b => closedBall (x b) r
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
-/
theorem pi_closedBall [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 ≤ r) :
    Measure.pi μ (Metric.closedBall x r) = ∏ i, μ i (Metric.closedBall (x i) r) := by
  rw [closedBall_pi _ hr, pi_pi]
/-
**MeasureTheory.Measure.pi.sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure.pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [∀ (i : ι)
, MeasureTheory.SigmaFinite (μ i)],   MeasureTheory.SigmaFinite (MeasureTheory.M
easure.pi μ)
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；MeasureTheory.M
easure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.sigmaFinite`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (h :
 μ.FiniteSpanningSetsIn C), MeasureTheory.Si…
-/
instance pi.sigmaFinite : SigmaFinite (Measure.pi μ) :=
  (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).sigmaFinite
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : ι → Type*} [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] :
    SigmaFinite (volume : Measure (∀ i, α i)) :=
  pi.sigmaFinite _
/-
**MeasureTheory.Measure.pi_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：pi_of_empty {α : Type*} [Fintype α] [IsEmpty α] {β : α -> Type*} {m : fora
ll a, MeasurableSpace (β a)} (μ : forall a : α, Measure (β a)) (x : forall a, β 
a
参数：β a；μ : forall a : α, Measure (β a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.prod_empty`：prod_empty [IsEmpty ι] (f : ι -> M) : ∏ x : ι, f x =
 1
· 使用定理 `MeasureTheory.Measure.dirac_apply_of_mem`：dirac_apply_of_mem {a : α} (h 
: a in s) : dirac a s = 1
-/
theorem pi_of_empty {α : Type*} [Fintype α] [IsEmpty α] {β : α → Type*}
    {m : ∀ a, MeasurableSpace (β a)} (μ : ∀ a : α, Measure (β a)) (x : ∀ a, β a := isEmptyElim) :
    Measure.pi μ = dirac x := by
  have : ∀ a, SigmaFinite (μ a) := isEmptyElim
  refine pi_eq fun s _ => ?_
  rw [Fintype.prod_empty, dirac_apply_of_mem]
  exact isEmptyElim (α := α)
/-
**MeasureTheory.Measure.volume_pi_eq_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：volume_pi_eq_dirac {ι : Type*} [Fintype ι] [IsEmpty ι] {α : ι -> Type*} [f
orall i, MeasureSpace (α i)] (x : forall a, α a
参数：α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi_of_empty`：pi_of_empty {α : Type*} [Fintype α] [
IsEmpty α] {β : α -> Type*} {m : forall a, MeasurableSpace (β a)} (μ : forall a 
: α, Measure (β a)) (x …
-/
lemma volume_pi_eq_dirac {ι : Type*} [Fintype ι] [IsEmpty ι]
    {α : ι → Type*} [∀ i, MeasureSpace (α i)] (x : ∀ a, α a := isEmptyElim) :
    (volume : Measure (∀ i, α i)) = Measure.dirac x :=
  Measure.pi_of_empty _ _

@[simp]
/-
**MeasureTheory.Measure.pi_empty_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：pi_empty_univ {α : Type*} [Fintype α] [IsEmpty α] {β : α -> Type*} {m : fo
rall α, MeasurableSpace (β α)} (μ : forall a : α, Measure (β a)) : Measure.pi μ 
(Set.univ) = 1
参数：β α；μ : forall a : α, Measure (β a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.pi_of_empty`：pi_of_empty {α : Type*} [Fintype α] [
IsEmpty α] {β : α -> Type*} {m : forall a, MeasurableSpace (β a)} (μ : forall a 
: α, Measure (β a)) (x …
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
-/
theorem pi_empty_univ {α : Type*} [Fintype α] [IsEmpty α] {β : α → Type*}
    {m : ∀ α, MeasurableSpace (β α)} (μ : ∀ a : α, Measure (β a)) :
    Measure.pi μ (Set.univ) = 1 := by
  rw [pi_of_empty, measure_univ]
/-
**MeasureTheory.Measure.pi_eval_preimage_null** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：pi_eval_preimage_null {i : ι} {s : Set (α i)} (hs : μ i s = 0) : Measure.p
i μ (eval i ⁻¹' s) = 0
参数：α i；hs : μ i s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_update_univ`：univ_pi_update_univ [DecidableEq ι] (i : ι) (s 
: Set (α i)) : pi univ (update (fun j : ι => (univ : Set (α j))) i s) = eval i ⁻
¹' s
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem pi_eval_preimage_null {i : ι} {s : Set (α i)} (hs : μ i s = 0) :
    Measure.pi μ (eval i ⁻¹' s) = 0 := by
  classical
  -- WLOG, `s` is measurable
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, _, hμt⟩
  suffices Measure.pi μ (eval i ⁻¹' t) = 0 from measure_mono_null (preimage_mono hst) this
  -- Now rewrite it as `Set.pi`, and apply `pi_pi`
  rw [← univ_pi_update_univ, pi_pi]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hμt]
/-
**MeasureTheory.Measure.quasiMeasurePreserving_eval** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：quasiMeasurePreserving_eval (i : ι) : QuasiMeasurePreserving (Function.eva
l i) (Measure.pi μ) (μ i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.pi_eval_preimage_null`：pi_eval_preimage_null {i : 
ι} {s : Set (α i)} (hs : μ i s = 0) : Measure.pi μ (eval i ⁻¹' s) = 0
-/
theorem quasiMeasurePreserving_eval (i : ι) :
    QuasiMeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨by fun_prop, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply (by fun_prop) hs, pi_eval_preimage_null μ h2s]
/-
**MeasureTheory.Measure.pi_map_eval** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：pi_map_eval [DecidableEq ι] (i : ι) : (Measure.pi μ).map (Function.eval i)
 = (∏ j in Finset.univ.erase i, μ j Set.univ) • (μ i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_update_univ`：univ_pi_update_univ [DecidableEq ι] (i : ι) (s 
: Set (α i)) : pi univ (update (fun j : ι => (univ : Set (α j))) i s) = eval i ⁻
¹' s
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Finset.prod_erase_mul`：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
lemma pi_map_eval [DecidableEq ι] (i : ι) :
     (Measure.pi μ).map (Function.eval i) = (∏ j ∈ Finset.univ.erase i, μ j Set.univ) • (μ i) := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs, ← Set.univ_pi_update_univ, Measure.pi_pi,
    Measure.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (a := i) (by simp)]
  congrm ?_ * ?_
  swap; · simp
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  simp [Function.update, Finset.ne_of_mem_erase hj]
/-
**MeasureTheory.Measure.pi_map_pi** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：pi_map_pi {X Y : ι -> Type*} {mX : forall i, MeasurableSpace (X i)} {μ : (
i : ι) -> Measure (X i)} [forall i, MeasurableSpace (Y i)] {f : (i : ι) -> X i -
> Y i} [hμ : forall i, SigmaFinite ((μ i).map (f i))] (hf : forall i, AEMeasurab
le (f i) (μ i)) : (Measure.pi μ).map (fun x i => (f i (x i))) = Measure.pi (fun 
i => (μ i).map (f i))
参数：X i；i : ι；X i；Y i；i : ι；(μ i).map (f i)；hf : forall i, AEMeasurable (f i) (μ 
i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SigmaFinite.of_map`：∀ {α : Type u_1} {β : Type u_2} {m0 : 
MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α)   {f
 : α → β},   AEMeasura…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_eval`：quasiMeasurePreservin
g_eval (i : ι) : QuasiMeasurePreserving (Function.eval i) (Measure.pi μ) (μ i)
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma pi_map_pi {X Y : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    [∀ i, MeasurableSpace (Y i)] {f : (i : ι) → X i → Y i} [hμ : ∀ i, SigmaFinite ((μ i).map (f i))]
    (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    (Measure.pi μ).map (fun x i ↦ (f i (x i))) = Measure.pi (fun i ↦ (μ i).map (f i)) := by
  have (i : ι) := (hμ i).of_map _ (hf i)
  refine (pi_eq fun s hs ↦ ?_).symm
  rw [map_apply_of_aemeasurable _ (.univ_pi hs)]
  swap
  · exact aemeasurable_pi_lambda _
      fun i ↦ (hf i).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval _ i)
  have : (fun (x : Π i, X i) i ↦ f i (x i)) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i ↦ (f i) ⁻¹' (s i)) := by ext x; simp
  rw [this, pi_pi]
  congr with i
  rw [map_apply_of_aemeasurable (hf i) (hs i)]

omit [∀ i, SigmaFinite (μ i)] in
/-
**MeasureTheory.Measure._root_.MeasureTheory.measurePreserving_eval** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.measurePreserving_eval [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨measurable_pi_apply i, ?_⟩
  classical
  rw [Measure.pi_map_eval, Finset.prod_eq_one, one_smul]
  exact fun _ _ ↦ measure_univ
/-
**MeasureTheory.Measure.pi_hyperplane** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：pi_hyperplane (i : ι) [NullSingletonClass (μ i)] (x : α i) : Measure.pi μ 
{ f : forall i, α i | f i = x } = 0
参数：i : ι；μ i；x : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi_eval_preimage_null`：pi_eval_preimage_null {i : 
ι} {s : Set (α i)} (hs : μ i s = 0) : Measure.pi μ (eval i ⁻¹' s) = 0
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem pi_hyperplane (i : ι) [NullSingletonClass (μ i)] (x : α i) :
    Measure.pi μ { f : ∀ i, α i | f i = x } = 0 :=
  show Measure.pi μ (eval i ⁻¹' {x}) = 0 from pi_eval_preimage_null _ (measure_singleton x)
/-
**MeasureTheory.Measure.ae_eval_ne** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：ae_eval_ne (i : ι) [NullSingletonClass (μ i)] (x : α i) : forallᵐ y : fora
ll i, α i ∂Measure.pi μ, y i != x
参数：i : ι；μ i；x : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.compl_mem_ae_iff`：compl_mem_ae_iff {s : Set α} : sᶜ in ae 
μ ↔ μ s = 0
· 使用定理 `MeasureTheory.Measure.pi_hyperplane`：pi_hyperplane (i : ι) [NullSingleto
nClass (μ i)] (x : α i) : Measure.pi μ { f : forall i, α i | f i = x } = 0
-/
theorem ae_eval_ne (i : ι) [NullSingletonClass (μ i)] (x : α i) :
    ∀ᵐ y : ∀ i, α i ∂Measure.pi μ, y i ≠ x :=
  compl_mem_ae_iff.2 (pi_hyperplane μ i x)
/-
**MeasureTheory.Measure.restrict_pi_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：restrict_pi_pi (s : (i : ι) -> Set (α i)) : (Measure.pi μ).restrict (Set.u
niv.pi fun i => s i) = .pi (fun i => (μ i).restrict (s i))
参数：s : (i : ι) -> Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.Restrict.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ] (s : Set α),  
 MeasureTheory.SigmaFini…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_pi_pi (s : (i : ι) → Set (α i)) :
    (Measure.pi μ).restrict (Set.univ.pi fun i ↦ s i) = .pi (fun i ↦ (μ i).restrict (s i)) := by
  refine (pi_eq fun _ h ↦ ?_).symm
  simp_rw [restrict_apply (MeasurableSet.univ_pi h), restrict_apply (h _),
    ← Set.pi_inter_distrib, pi_pi]

variable {μ}
/-
**MeasureTheory.Measure.tendsto_eval_ae_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：tendsto_eval_ae_ae {i : ι} : Tendsto (eval i) (ae (Measure.pi μ)) (ae (μ i
))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.pi_eval_preimage_null`：pi_eval_preimage_null {i : 
ι} {s : Set (α i)} (hs : μ i s = 0) : Measure.pi μ (eval i ⁻¹' s) = 0
-/
theorem tendsto_eval_ae_ae {i : ι} : Tendsto (eval i) (ae (Measure.pi μ)) (ae (μ i)) := fun _ hs =>
  pi_eval_preimage_null μ hs
/-
**MeasureTheory.Measure.ae_pi_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：ae_pi_le_pi : ae (Measure.pi μ) <= Filter.pi fun i => ae (μ i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `MeasureTheory.Measure.tendsto_eval_ae_ae`：tendsto_eval_ae_ae {i : ι} : T
endsto (eval i) (ae (Measure.pi μ)) (ae (μ i))
-/
theorem ae_pi_le_pi : ae (Measure.pi μ) ≤ Filter.pi fun i => ae (μ i) :=
  le_iInf fun _ => tendsto_eval_ae_ae.le_comap
/-
**MeasureTheory.Measure.ae_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：ae_eq_pi {β : ι -> Type*} {f f' : forall i, α i -> β i} (h : forall i, f i
 =ᵐ[μ i] f' i) : (fun (x : forall i, α i) i => f i (x i)) =ᵐ[Measure.pi μ] fun x
 i => f' i (x i)
参数：h : forall i, f i =ᵐ[μ i] f' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `MeasureTheory.Measure.tendsto_eval_ae_ae`：tendsto_eval_ae_ae {i : ι} : T
endsto (eval i) (ae (Measure.pi μ)) (ae (μ i))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ae_eq_pi {β : ι → Type*} {f f' : ∀ i, α i → β i} (h : ∀ i, f i =ᵐ[μ i] f' i) :
    (fun (x : ∀ i, α i) i => f i (x i)) =ᵐ[Measure.pi μ] fun x i => f' i (x i) :=
  (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => funext hx
/-
**MeasureTheory.Measure.ae_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：ae_le_pi {β : ι -> Type*} [forall i, Preorder (β i)] {f f' : forall i, α i
 -> β i} (h : forall i, f i <=ᵐ[μ i] f' i) : (fun (x : forall i, α i) i => f i (
x i)) <=ᵐ[Measure.pi μ] fun x i => f' i (x i)
参数：β i；h : forall i, f i <=ᵐ[μ i] f' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `MeasureTheory.Measure.tendsto_eval_ae_ae`：tendsto_eval_ae_ae {i : ι} : T
endsto (eval i) (ae (Measure.pi μ)) (ae (μ i))
-/
theorem ae_le_pi {β : ι → Type*} [∀ i, Preorder (β i)] {f f' : ∀ i, α i → β i}
    (h : ∀ i, f i ≤ᵐ[μ i] f' i) :
    (fun (x : ∀ i, α i) i => f i (x i)) ≤ᵐ[Measure.pi μ] fun x i => f' i (x i) :=
  (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => hx
/-
**MeasureTheory.Measure.ae_le_set_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：ae_le_set_pi {I : Set ι} {s t : forall i, Set (α i)} (h : forall i in I, s
 i <=ᵐ[μ i] t i) : Set.pi I s <=ᵐ[Measure.pi μ] Set.pi I t
参数：α i；h : forall i in I, s i <=ᵐ[μ i] t i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all_finite`：eventually_all_finite {ι} {I : Set ι} (hI 
: I.Finite) {l} {p : ι -> α -> Prop} : (forallᶠ x in l, forall i in I, p i x) ↔ 
forall i in I, for…
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `MeasureTheory.Measure.tendsto_eval_ae_ae`：tendsto_eval_ae_ae {i : ι} : T
endsto (eval i) (ae (Measure.pi μ)) (ae (μ i))
-/
theorem ae_le_set_pi {I : Set ι} {s t : ∀ i, Set (α i)} (h : ∀ i ∈ I, s i ≤ᵐ[μ i] t i) :
    Set.pi I s ≤ᵐ[Measure.pi μ] Set.pi I t :=
  ((eventually_all_finite I.toFinite).2 fun i hi => tendsto_eval_ae_ae.eventually (h i hi)).mono
    fun _ hst hx i hi => hst i hi <| hx i hi
/-
**MeasureTheory.Measure.ae_eq_set_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：ae_eq_set_pi {I : Set ι} {s t : forall i, Set (α i)} (h : forall i in I, s
 i =ᵐ[μ i] t i) : Set.pi I s =ᵐ[Measure.pi μ] Set.pi I t
参数：α i；h : forall i in I, s i =ᵐ[μ i] t i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `MeasureTheory.Measure.ae_le_set_pi`：ae_le_set_pi {I : Set ι} {s t : fora
ll i, Set (α i)} (h : forall i in I, s i <=ᵐ[μ i] t i) : Set.pi I s <=ᵐ[Measure.
pi μ] Set.pi I t
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem ae_eq_set_pi {I : Set ι} {s t : ∀ i, Set (α i)} (h : ∀ i ∈ I, s i =ᵐ[μ i] t i) :
    Set.pi I s =ᵐ[Measure.pi μ] Set.pi I t :=
  (ae_le_set_pi fun i hi => (h i hi).le).antisymm (ae_le_set_pi fun i hi => (h i hi).symm.le)
/-
**MeasureTheory.Measure.pi_map_piOptionEquivProd** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：pi_map_piOptionEquivProd {β : Option ι -> Type*} [forall i, MeasurableSpac
e (β i)] (μ : (i : Option ι) -> Measure (β i)) [forall (i : Option ι), SigmaFini
te (μ i)] : ((Measure.pi fun i => μ (some i)).prod (μ none)).map (MeasurableEqui
v.piOptionEquivProd β).symm = Measure.pi μ
参数：β i；μ : (i : Option ι) -> Measure (β i)；i : Option ι；μ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_insertNone`：prod_insertNone (f : Option α -> M) (s : Finset 
α) : ∏ x in insertNone s, f x = f none * ∏ x in s, f (some x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pi_map_piOptionEquivProd {β : Option ι → Type*} [∀ i, MeasurableSpace (β i)]
    (μ : (i : Option ι) → Measure (β i)) [∀ (i : Option ι), SigmaFinite (μ i)] :
    ((Measure.pi fun i ↦ μ (some i)).prod (μ none)).map
      (MeasurableEquiv.piOptionEquivProd β).symm = Measure.pi μ := by
  refine pi_eq (fun s _ ↦ ?_) |>.symm
  let e_meas : ((i : ι) → β (some i)) × β none ≃ᵐ ((i : Option ι) → β i) :=
    MeasurableEquiv.piOptionEquivProd β |>.symm
  have me := MeasurableEquiv.measurableEmbedding e_meas
  have : e_meas ⁻¹' pi univ s = (pi univ (fun i ↦ s (some i))) ×ˢ (s none) := by
    ext x
    simp only [mem_preimage, Set.mem_pi, mem_univ, forall_true_left, mem_prod]
    refine ⟨by tauto, fun _ i ↦ ?_⟩
    rcases i <;> tauto
  simp only [e_meas, me.map_apply, univ_option, Finset.prod_insertNone, this,
    prod_prod, pi_pi, mul_comm]

section Intervals

variable [∀ i, PartialOrder (α i)] [∀ i, NullSingletonClass (μ i)]

/-
**MeasureTheory.Measure.pi_Iio_ae_eq_pi_Iic** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：pi_Iio_ae_eq_pi_Iic {s : Set ι} {f : forall i, α i} : (pi s fun i => Iio (
f i)) =ᵐ[Measure.pi μ] pi s fun i => Iic (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ae_eq_set_pi`：ae_eq_set_pi {I : Set ι} {s t : fora
ll i, Set (α i)} (h : forall i in I, s i =ᵐ[μ i] t i) : Set.pi I s =ᵐ[Measure.pi
 μ] Set.pi I t
· 使用定理 `MeasureTheory.Iio_ae_eq_Iic`：Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a
-/
theorem pi_Iio_ae_eq_pi_Iic {s : Set ι} {f : ∀ i, α i} :
    (pi s fun i => Iio (f i)) =ᵐ[Measure.pi μ] pi s fun i => Iic (f i) :=
  ae_eq_set_pi fun _ _ => Iio_ae_eq_Iic
/-
**MeasureTheory.Measure.pi_Ioi_ae_eq_pi_Ici** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：pi_Ioi_ae_eq_pi_Ici {s : Set ι} {f : forall i, α i} : (pi s fun i => Ioi (
f i)) =ᵐ[Measure.pi μ] pi s fun i => Ici (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ae_eq_set_pi`：ae_eq_set_pi {I : Set ι} {s t : fora
ll i, Set (α i)} (h : forall i in I, s i =ᵐ[μ i] t i) : Set.pi I s =ᵐ[Measure.pi
 μ] Set.pi I t
· 使用定理 `MeasureTheory.Ioi_ae_eq_Ici`：Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a
-/
theorem pi_Ioi_ae_eq_pi_Ici {s : Set ι} {f : ∀ i, α i} :
    (pi s fun i => Ioi (f i)) =ᵐ[Measure.pi μ] pi s fun i => Ici (f i) :=
  ae_eq_set_pi fun _ _ => Ioi_ae_eq_Ici
/-
**MeasureTheory.Measure.univ_pi_Iio_ae_eq_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：univ_pi_Iio_ae_eq_Iic {f : forall i, α i} : (pi univ fun i => Iio (f i)) =
ᵐ[Measure.pi μ] Iic f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ_Iic`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → P
reorder (α i)] (x : (i : ι) → α i),   (Set.univ.pi fun i => Set.Iic (x i)) = Set
.Iic …
· 使用定理 `MeasureTheory.Measure.pi_Iio_ae_eq_pi_Iic`：pi_Iio_ae_eq_pi_Iic {s : Set 
ι} {f : forall i, α i} : (pi s fun i => Iio (f i)) =ᵐ[Measure.pi μ] pi s fun i =
> Iic (f i)
-/
theorem univ_pi_Iio_ae_eq_Iic {f : ∀ i, α i} :
    (pi univ fun i => Iio (f i)) =ᵐ[Measure.pi μ] Iic f := by
  rw [← pi_univ_Iic]; exact pi_Iio_ae_eq_pi_Iic
/-
**MeasureTheory.Measure.univ_pi_Ioi_ae_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：univ_pi_Ioi_ae_eq_Ici {f : forall i, α i} : (pi univ fun i => Ioi (f i)) =
ᵐ[Measure.pi μ] Ici f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ_Ici`：pi_univ_Ici : (pi univ fun i => Ici (x i)) = Ici x
· 使用定理 `MeasureTheory.Measure.pi_Ioi_ae_eq_pi_Ici`：pi_Ioi_ae_eq_pi_Ici {s : Set 
ι} {f : forall i, α i} : (pi s fun i => Ioi (f i)) =ᵐ[Measure.pi μ] pi s fun i =
> Ici (f i)
-/
theorem univ_pi_Ioi_ae_eq_Ici {f : ∀ i, α i} :
    (pi univ fun i => Ioi (f i)) =ᵐ[Measure.pi μ] Ici f := by
  rw [← pi_univ_Ici]; exact pi_Ioi_ae_eq_pi_Ici
/-
**MeasureTheory.Measure.pi_Ioo_ae_eq_pi_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：pi_Ioo_ae_eq_pi_Icc {s : Set ι} {f g : forall i, α i} : (pi s fun i => Ioo
 (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ae_eq_set_pi`：ae_eq_set_pi {I : Set ι} {s t : fora
ll i, Set (α i)} (h : forall i in I, s i =ᵐ[μ i] t i) : Set.pi I s =ᵐ[Measure.pi
 μ] Set.pi I t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Icc`：Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b
-/
theorem pi_Ioo_ae_eq_pi_Icc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioo_ae_eq_Icc
/-
**MeasureTheory.Measure.pi_Ioo_ae_eq_pi_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：pi_Ioo_ae_eq_pi_Ioc {s : Set ι} {f g : forall i, α i} : (pi s fun i => Ioo
 (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Ioc (f i) (g i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ae_eq_set_pi`：ae_eq_set_pi {I : Set ι} {s t : fora
ll i, Set (α i)} (h : forall i in I, s i =ᵐ[μ i] t i) : Set.pi I s =ᵐ[Measure.pi
 μ] Set.pi I t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
-/
theorem pi_Ioo_ae_eq_pi_Ioc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Ioc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioo_ae_eq_Ioc
/-
**MeasureTheory.Measure.univ_pi_Ioo_ae_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：univ_pi_Ioo_ae_eq_Icc {f g : forall i, α i} : (pi univ fun i => Ioo (f i) 
(g i)) =ᵐ[Measure.pi μ] Icc f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ_Icc`：pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc 
x y
· 使用定理 `MeasureTheory.Measure.pi_Ioo_ae_eq_pi_Icc`：pi_Ioo_ae_eq_pi_Icc {s : Set 
ι} {f g : forall i, α i} : (pi s fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] pi s
 fun i => Icc (f i) (g i)
-/
theorem univ_pi_Ioo_ae_eq_Icc {f g : ∀ i, α i} :
    (pi univ fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ioo_ae_eq_pi_Icc
/-
**MeasureTheory.Measure.pi_Ioc_ae_eq_pi_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：pi_Ioc_ae_eq_pi_Icc {s : Set ι} {f g : forall i, α i} : (pi s fun i => Ioc
 (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ae_eq_set_pi`：ae_eq_set_pi {I : Set ι} {s t : fora
ll i, Set (α i)} (h : forall i in I, s i =ᵐ[μ i] t i) : Set.pi I s =ᵐ[Measure.pi
 μ] Set.pi I t
· 使用定理 `MeasureTheory.Ioc_ae_eq_Icc`：Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b
-/
theorem pi_Ioc_ae_eq_pi_Icc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioc_ae_eq_Icc
/-
**MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：univ_pi_Ioc_ae_eq_Icc {f g : forall i, α i} : (pi univ fun i => Ioc (f i) 
(g i)) =ᵐ[Measure.pi μ] Icc f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ_Icc`：pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc 
x y
· 使用定理 `MeasureTheory.Measure.pi_Ioc_ae_eq_pi_Icc`：pi_Ioc_ae_eq_pi_Icc {s : Set 
ι} {f g : forall i, α i} : (pi s fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] pi s
 fun i => Icc (f i) (g i)
-/
theorem univ_pi_Ioc_ae_eq_Icc {f g : ∀ i, α i} :
    (pi univ fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ioc_ae_eq_pi_Icc
/-
**MeasureTheory.Measure.pi_Ico_ae_eq_pi_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：pi_Ico_ae_eq_pi_Icc {s : Set ι} {f g : forall i, α i} : (pi s fun i => Ico
 (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ae_eq_set_pi`：ae_eq_set_pi {I : Set ι} {s t : fora
ll i, Set (α i)} (h : forall i in I, s i =ᵐ[μ i] t i) : Set.pi I s =ᵐ[Measure.pi
 μ] Set.pi I t
· 使用定理 `MeasureTheory.Ico_ae_eq_Icc`：Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b
-/
theorem pi_Ico_ae_eq_pi_Icc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ico (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ico_ae_eq_Icc
/-
**MeasureTheory.Measure.univ_pi_Ico_ae_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：univ_pi_Ico_ae_eq_Icc {f g : forall i, α i} : (pi univ fun i => Ico (f i) 
(g i)) =ᵐ[Measure.pi μ] Icc f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ_Icc`：pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc 
x y
· 使用定理 `MeasureTheory.Measure.pi_Ico_ae_eq_pi_Icc`：pi_Ico_ae_eq_pi_Icc {s : Set 
ι} {f g : forall i, α i} : (pi s fun i => Ico (f i) (g i)) =ᵐ[Measure.pi μ] pi s
 fun i => Icc (f i) (g i)
-/
theorem univ_pi_Ico_ae_eq_Icc {f g : ∀ i, α i} :
    (pi univ fun i => Ico (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ico_ae_eq_pi_Icc

end Intervals

/-- If one of the measures `μ i` has value zero on singeltons, them `Measure.pi µ`
has value zero on singletons. The instance below assumes that all `μ i` have value zero on
singletons. -/
/-
**MeasureTheory.Measure.pi_nullSingletonClass** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：pi_nullSingletonClass (i : ι) [NullSingletonClass (μ i)] : NullSingletonCl
ass (Measure.pi μ)
参数：i : ι；μ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.pi_hyperplane`：pi_hyperplane (i : ι) [NullSingleto
nClass (μ i)] (x : α i) : Measure.pi μ { f : forall i, α i | f i = x } = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s

--- 原说明 ---
If one of the measures `μ i` has value zero on singeltons, them `Measure.pi µ`
has value zero on singletons. The instance below assumes that all `μ i` have val
ue zero on
singletons.
-/
theorem pi_nullSingletonClass (i : ι) [NullSingletonClass (μ i)] :
    NullSingletonClass (Measure.pi μ) :=
  ⟨fun x => flip measure_mono_null (pi_hyperplane μ i (x i)) (singleton_subset_iff.2 rfl)⟩

@[deprecated (since := "2026-06-09")]
alias pi_noAtoms := pi_nullSingletonClass
/-
**MeasureTheory.Measure.pi_nullSingletonClass'** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：pi_nullSingletonClass' [h : Nonempty ι] [forall i, NullSingletonClass (μ i
)] : NullSingletonClass (Measure.pi μ)
参数：μ i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `MeasureTheory.Measure.pi_nullSingletonClass`：pi_nullSingletonClass (i : 
ι) [NullSingletonClass (μ i)] : NullSingletonClass (Measure.pi μ)
-/
instance pi_nullSingletonClass' [h : Nonempty ι] [∀ i, NullSingletonClass (μ i)] :
    NullSingletonClass (Measure.pi μ) :=
  h.elim fun i => pi_nullSingletonClass i

@[deprecated (since := "2026-06-09")]
alias pi_noAtoms' := pi_nullSingletonClass'
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : ι → Type*} [Nonempty ι] [∀ i, MeasureSpace (α i)]
    [∀ i, SigmaFinite (volume : Measure (α i))] [∀ i, NullSingletonClass (volume : Measure (α i))] :
    NullSingletonClass (volume : Measure (∀ i, α i)) :=
  pi_nullSingletonClass'
/-
**MeasureTheory.Measure.pi.isLocallyFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   {μ : (i : ι) → MeasureTheory.Measure (α i)} [∀ (i : ι)
, MeasureTheory.SigmaFinite (μ i)]   [inst_3 : (i : ι) → TopologicalSpace (α i)]
 [∀ (i : ι), MeasureTheory.IsLocallyFiniteMeasure (μ i)],   MeasureTheory.IsLoca
llyFiniteMeasure (MeasureTheory.Measure.pi μ)
参数：i : ι；α i；i : ι；α i；i : ι；μ i；i : ι；α i；i : ι；μ i；MeasureTheory.Measure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `set_pi_mem_nhds`：set_pi_mem_nhds {i : Set ι} {s : forall a, Set (A a)} {
x : forall a, A a} (hi : i.Finite) (hs : forall a in i, s a in 𝓝 (x a)) : pi i s
 in 𝓝…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用引理 `ENNReal.prod_lt_top`：prod_lt_top (h : forall a in s, f a < ∞) : ∏ a in s
, f a < ∞
· 使用定理 `MeasureTheory.Measure.exists_isOpen_measure_lt_top`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α) 
  [MeasureTheory.IsLocallyFiniteMeasure …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance pi.isLocallyFiniteMeasure
    [∀ i, TopologicalSpace (α i)] [∀ i, IsLocallyFiniteMeasure (μ i)] :
    IsLocallyFiniteMeasure (Measure.pi μ) := by
  refine ⟨fun x => ?_⟩
  choose s hxs ho hμ using fun i => (μ i).exists_isOpen_measure_lt_top (x i)
  refine ⟨pi univ s, set_pi_mem_nhds finite_univ fun i _ => IsOpen.mem_nhds (ho i) (hxs i), ?_⟩
  rw [pi_pi]
  exact ENNReal.prod_lt_top fun i _ => hμ i
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MeasureSpace (X i)]
    [∀ i, SigmaFinite (volume : Measure (X i))]
    [∀ i, IsLocallyFiniteMeasure (volume : Measure (X i))] :
    IsLocallyFiniteMeasure (volume : Measure (∀ i, X i)) :=
  pi.isLocallyFiniteMeasure
/-
**MeasureTheory.Measure._root_.IsUnifLocDoublingMeasure.pi** 是 Mathlib 中的一个实例，位于
命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.IsUnifLocDoublingMeasure.pi {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] [∀ i, IsUnifLocDoublingMeasure (μ i)] :
    IsUnifLocDoublingMeasure (Measure.pi μ) := by
  use ∏ i, IsUnifLocDoublingMeasure.doublingConstant (μ i)
  filter_upwards [Filter.eventually_all.mpr fun i ↦
      IsUnifLocDoublingMeasure.eventually_measure_le_doublingConstant_mul (μ i),
    eventually_mem_nhdsWithin] with r hr (hr₀ : 0 < r) x
  simpa (disch := positivity) [Finset.prod_mul_distrib, closedBall_pi, pi_pi]
    using Fintype.prod_mono' fun i ↦ hr i (x i)
/-
**MeasureTheory.Measure.IsUnifLocDoublingMeasure.volume_pi** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.IsUnifLocDoublingMeasure`。
形式化陈述：∀ {ι : Type u_4} [inst : Fintype ι] {X : ι → Type u_5} [inst_1 : (i : ι) →
 PseudoMetricSpace (X i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace (X i)
] [∀ (i : ι), MeasureTheory.SigmaFinite MeasureTheory.volume]   [∀ (i : ι), IsUn
ifLocDoublingMeasure MeasureTheory.volume], IsUnifLocDoublingMeasure MeasureTheo
ry.volume
参数：i : ι；X i；i : ι；X i；i : ι；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnifLocDoublingMeasure.pi`：∀ {ι : Type u_4} [inst : Fintype ι] {X : ι 
→ Type u_5} [inst_1 : (i : ι) → PseudoMetricSpace (X i)]   [inst_2 : (i : ι) → M
easurableSpace (X…
-/
instance IsUnifLocDoublingMeasure.volume_pi {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] [∀ i, MeasureSpace (X i)]
    [∀ i, SigmaFinite (volume : Measure (X i))]
    [∀ i, IsUnifLocDoublingMeasure (volume : Measure (X i))] :
    IsUnifLocDoublingMeasure (volume : Measure (∀ i, X i)) :=
  .pi _

variable (μ)

@[to_additive]
/-
**MeasureTheory.Measure.pi.isMulLeftInvariant** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [∀ (i : ι)
, MeasureTheory.SigmaFinite (μ i)]   [inst_3 : (i : ι) → Group (α i)] [∀ (i : ι)
, MeasurableMul (α i)] [∀ (i : ι), (μ i).IsMulLeftInvariant],   (MeasureTheory.M
easure.pi μ).IsMulLeftInvariant
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；i : ι；α i；i : ι
；α i；i : ι；μ i；MeasureTheory.Measure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasureTheory.measure_preimage_mul`：measure_preimage_mul (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) (A : Set G) : μ ((fun h => g * h) ⁻¹' A) = μ A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance pi.isMulLeftInvariant [∀ i, Group (α i)] [∀ i, MeasurableMul (α i)]
    [∀ i, IsMulLeftInvariant (μ i)] : IsMulLeftInvariant (Measure.pi μ) := by
  refine ⟨fun v => (pi_eq fun s hs => ?_).symm⟩
  rw [map_apply (measurable_const_mul _) (MeasurableSet.univ_pi hs),
    show (v * ·) ⁻¹' univ.pi s = univ.pi fun i => (v i * ·) ⁻¹' s i by rfl, pi_pi]
  simp_rw [measure_preimage_mul]

@[to_additive]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : ι → Type*} [∀ i, Group (G i)] [∀ i, MeasureSpace (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, SigmaFinite (volume : Measure (G i))] [∀ i, IsMulLeftInvariant (volume : Measure (G i))] :
    IsMulLeftInvariant (volume : Measure (∀ i, G i)) :=
  pi.isMulLeftInvariant _

@[to_additive]
/-
**MeasureTheory.Measure.pi.isMulRightInvariant** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [∀ (i : ι)
, MeasureTheory.SigmaFinite (μ i)]   [inst_3 : (i : ι) → Group (α i)] [∀ (i : ι)
, MeasurableMul (α i)] [∀ (i : ι), (μ i).IsMulRightInvariant],   (MeasureTheory.
Measure.pi μ).IsMulRightInvariant
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；i : ι；α i；i : ι
；α i；i : ι；μ i；MeasureTheory.Measure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasureTheory.measure_preimage_mul_right`：measure_preimage_mul_right (μ 
: Measure G) [IsMulRightInvariant μ] (g : G) (A : Set G) : μ ((fun h => h * g) ⁻
¹' A) = μ A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance pi.isMulRightInvariant [∀ i, Group (α i)] [∀ i, MeasurableMul (α i)]
    [∀ i, IsMulRightInvariant (μ i)] : IsMulRightInvariant (Measure.pi μ) := by
  refine ⟨fun v => (pi_eq fun s hs => ?_).symm⟩
  rw [map_apply (measurable_mul_const _) (MeasurableSet.univ_pi hs),
    show (· * v) ⁻¹' univ.pi s = univ.pi fun i => (· * v i) ⁻¹' s i by rfl, pi_pi]
  simp_rw [measure_preimage_mul_right]

@[to_additive]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : ι → Type*} [∀ i, Group (G i)] [∀ i, MeasureSpace (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, SigmaFinite (volume : Measure (G i))]
    [∀ i, IsMulRightInvariant (volume : Measure (G i))] :
    IsMulRightInvariant (volume : Measure (∀ i, G i)) :=
  pi.isMulRightInvariant _

@[to_additive]
/-
**MeasureTheory.Measure.pi.isInvInvariant** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure.pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [∀ (i : ι)
, MeasureTheory.SigmaFinite (μ i)]   [inst_3 : (i : ι) → Group (α i)] [∀ (i : ι)
, MeasurableInv (α i)] [∀ (i : ι), (μ i).IsInvInvariant],   (MeasureTheory.Measu
re.pi μ).IsInvInvariant
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；i : ι；α i；i : ι
；α i；i : ι；μ i；MeasureTheory.Measure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.inv_pi`：inv_pi (s : Set ι) (t : forall i, Set (α i)) : (s.pi t)⁻¹ = 
s.pi fun i => (t i)⁻¹
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasureTheory.Measure.measure_preimage_inv`：measure_preimage_inv (μ : Me
asure G) [IsInvInvariant μ] (A : Set G) : μ (Inv.inv ⁻¹' A) = μ A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance pi.isInvInvariant [∀ i, Group (α i)] [∀ i, MeasurableInv (α i)]
    [∀ i, IsInvInvariant (μ i)] : IsInvInvariant (Measure.pi μ) := by
  refine ⟨(Measure.pi_eq fun s hs => ?_).symm⟩
  have A : Inv.inv ⁻¹' pi univ s = Set.pi univ fun i => Inv.inv ⁻¹' s i := by ext; simp
  simp_rw [Measure.inv, Measure.map_apply measurable_inv (MeasurableSet.univ_pi hs), A, pi_pi,
    measure_preimage_inv]

@[to_additive]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : ι → Type*} [∀ i, Group (G i)] [∀ i, MeasureSpace (G i)] [∀ i, MeasurableInv (G i)]
    [∀ i, SigmaFinite (volume : Measure (G i))] [∀ i, IsInvInvariant (volume : Measure (G i))] :
    IsInvInvariant (volume : Measure (∀ i, G i)) :=
  pi.isInvInvariant _
/-
**MeasureTheory.Measure.pi.isOpenPosMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [∀ (i : ι)
, MeasureTheory.SigmaFinite (μ i)]   [inst_3 : (i : ι) → TopologicalSpace (α i)]
 [∀ (i : ι), (μ i).IsOpenPosMeasure],   (MeasureTheory.Measure.pi μ).IsOpenPosMe
asure
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；i : ι；α i；i : ι
；μ i；MeasureTheory.Measure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_pi_iff'`：isOpen_pi_iff' [Finite ι] {s : Set (forall a, A a)} : Is
Open s ↔ forall f, f in s -> exists u : forall a, Set (A a), (forall a, IsOpen (
u a)…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `CanonicallyOrderedAdd.prod_pos`：∀ {ι : Type u_1} {R : Type u_2} [inst : 
CommSemiring R] [inst_1 : PartialOrder R] [CanonicallyOrderedAdd R] {f : ι → R} 
  {s : Finset ι} [No…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
instance pi.isOpenPosMeasure [∀ i, TopologicalSpace (α i)] [∀ i, IsOpenPosMeasure (μ i)] :
    IsOpenPosMeasure (MeasureTheory.Measure.pi μ) := by
  constructor
  rintro U U_open ⟨a, ha⟩
  obtain ⟨s, ⟨hs, hsU⟩⟩ := isOpen_pi_iff'.1 U_open a ha
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsU))
  simp only [pi_pi]
  rw [CanonicallyOrderedAdd.prod_pos]
  intro i _
  apply (hs i).1.measure_pos (μ i) ⟨a i, (hs i).2⟩
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MeasureSpace (X i)]
    [∀ i, IsOpenPosMeasure (volume : Measure (X i))] [∀ i, SigmaFinite (volume : Measure (X i))] :
    IsOpenPosMeasure (volume : Measure (∀ i, X i)) :=
  pi.isOpenPosMeasure _
/-
**MeasureTheory.Measure.pi.isFiniteMeasureOnCompacts** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [∀ (i : ι)
, MeasureTheory.SigmaFinite (μ i)]   [inst_3 : (i : ι) → TopologicalSpace (α i)]
 [∀ (i : ι), MeasureTheory.IsFiniteMeasureOnCompacts (μ i)],   MeasureTheory.IsF
initeMeasureOnCompacts (MeasureTheory.Measure.pi μ)
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；i : ι；α i；i : ι
；μ i；MeasureTheory.Measure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用引理 `WithTop.prod_lt_top`：prod_lt_top [LT M₀] (h : forall i in s, f i < ⊤) : 
∏ i in s, f i < ⊤
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_pi_eval_image`：subset_pi_eval_image (s : Set ι) (u : Set (for
all i, α i)) : u subseteq pi s fun i => eval i '' u
-/
instance pi.isFiniteMeasureOnCompacts [∀ i, TopologicalSpace (α i)]
    [∀ i, IsFiniteMeasureOnCompacts (μ i)] :
    IsFiniteMeasureOnCompacts (MeasureTheory.Measure.pi μ) := by
  constructor
  intro K hK
  suffices Measure.pi μ (Set.univ.pi fun j => Function.eval j '' K) < ⊤ by
    exact lt_of_le_of_lt (measure_mono (univ.subset_pi_eval_image K)) this
  rw [Measure.pi_pi]
  refine WithTop.prod_lt_top ?_
  exact fun i _ => IsCompact.measure_lt_top (IsCompact.image hK (continuous_apply i))
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : ι → Type*} [∀ i, MeasureSpace (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, SigmaFinite (volume : Measure (X i))]
    [∀ i, IsFiniteMeasureOnCompacts (volume : Measure (X i))] :
    IsFiniteMeasureOnCompacts (volume : Measure (∀ i, X i)) :=
  pi.isFiniteMeasureOnCompacts _

@[to_additive]
/-
**MeasureTheory.Measure.pi.isHaarMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure.pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) →
 MeasurableSpace (α i)]   (μ : (i : ι) → MeasureTheory.Measure (α i)) [∀ (i : ι)
, MeasureTheory.SigmaFinite (μ i)]   [inst_3 : (i : ι) → Group (α i)] [inst_4 : 
(i : ι) → TopologicalSpace (α i)] [∀ (i : ι), (μ i).IsHaarMeasure]   [∀ (i : ι),
 MeasurableMul (α i)], (MeasureTheory.Measure.pi μ).IsHaarMeasure
参数：i : ι；α i；μ : (i : ι) → MeasureTheory.Measure (α i)；i : ι；μ i；i : ι；α i；i : ι
；α i；i : ι；μ i；i : ι；α i；MeasureTheory.Measure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi.isFiniteMeasureOnCompacts`：∀ {ι : Type u_1} {α 
: ι → Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   
(μ : (i : ι) → MeasureTheory.Measure (α …
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.pi.isMulLeftInvariant`：∀ {ι : Type u_1} {α : ι → T
ype u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i
 : ι) → MeasureTheory.Measure (α …
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.pi.isOpenPosMeasure`：∀ {ι : Type u_1} {α : ι → Typ
e u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i :
 ι) → MeasureTheory.Measure (α …
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
-/
instance pi.isHaarMeasure [∀ i, Group (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, IsHaarMeasure (μ i)] [∀ i, MeasurableMul (α i)] : IsHaarMeasure (Measure.pi μ) where

@[to_additive]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : ι → Type*} [∀ i, Group (G i)] [∀ i, MeasureSpace (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, SigmaFinite (volume : Measure (G i))]
    [∀ i, IsHaarMeasure (volume : Measure (G i))] : IsHaarMeasure (volume : Measure (∀ i, G i)) :=
  pi.isHaarMeasure _

end Measure

/-
**MeasureTheory.volume_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：volume_pi [forall i, MeasureSpace (α i)] : (volume : Measure (forall i, α 
i)) = Measure.pi fun _ => volume
参数：α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem volume_pi [∀ i, MeasureSpace (α i)] :
    (volume : Measure (∀ i, α i)) = Measure.pi fun _ => volume :=
  rfl
/-
**MeasureTheory.volume_pi_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：volume_pi_pi [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume
 : Measure (α i))] (s : forall i, Set (α i)) : volume (pi univ s) = ∏ i, volume 
(s i)
参数：α i；volume : Measure (α i)；s : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
-/
theorem volume_pi_pi [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))]
    (s : ∀ i, Set (α i)) : volume (pi univ s) = ∏ i, volume (s i) :=
  Measure.pi_pi (fun _ => volume) s
/-
**MeasureTheory.volume_pi_ball** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：volume_pi_ball [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volu
me : Measure (α i))] [forall i, MetricSpace (α i)] (x : forall i, α i) {r : Real
} (hr : 0 < r) : volume (Metric.ball x r) = ∏ i, volume (Metric.ball (x i) r)
参数：α i；volume : Measure (α i)；α i；x : forall i, α i；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi_ball`：pi_ball [forall i, MetricSpace (α i)] (x 
: forall i, α i) {r : Real} (hr : 0 < r) : Measure.pi μ (Metric.ball x r) = ∏ i,
 μ i (Metric.ball (…
-/
theorem volume_pi_ball [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))]
    [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball x r) = ∏ i, volume (Metric.ball (x i) r) :=
  Measure.pi_ball _ _ hr
/-
**MeasureTheory.volume_pi_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：volume_pi_closedBall [forall i, MeasureSpace (α i)] [forall i, SigmaFinite
 (volume : Measure (α i))] [forall i, MetricSpace (α i)] (x : forall i, α i) {r 
: Real} (hr : 0 <= r) : volume (Metric.closedBall x r) = ∏ i, volume (Metric.clo
sedBall (x i) r)
参数：α i；volume : Measure (α i)；α i；x : forall i, α i；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi_closedBall`：pi_closedBall [forall i, MetricSpac
e (α i)] (x : forall i, α i) {r : Real} (hr : 0 <= r) : Measure.pi μ (Metric.clo
sedBall x r) = ∏ i, μ i (…
-/
theorem volume_pi_closedBall [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))]
    [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall x r) = ∏ i, volume (Metric.closedBall (x i) r) :=
  Measure.pi_closedBall _ _ hr

open Measure

/-- We intentionally restrict this only to the nondependent function space, since type-class
inference cannot find an instance for `ι → ℝ` when this is stated for dependent function spaces. -/
@[to_additive /-- We intentionally restrict this only to the nondependent function space, since
type-class inference cannot find an instance for `ι → ℝ` when this is stated for dependent function
spaces. -/]
/-
**MeasureTheory.Pi.isMulLeftInvariant_volume** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Pi`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] {α : Type u_4} [inst_1 : Group α] [ins
t_2 : MeasureTheory.MeasureSpace α]   [MeasureTheory.SigmaFinite MeasureTheory.v
olume] [MeasurableMul α] [MeasureTheory.volume.IsMulLeftInvariant],   MeasureThe
ory.volume.IsMulLeftInvariant
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi.isMulLeftInvariant`：∀ {ι : Type u_1} {α : ι → T
ype u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i
 : ι) → MeasureTheory.Measure (α …
-/
instance Pi.isMulLeftInvariant_volume {α} [Group α] [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] [MeasurableMul α] [IsMulLeftInvariant (volume : Measure α)] :
    IsMulLeftInvariant (volume : Measure (ι → α)) :=
  pi.isMulLeftInvariant _

/-- We intentionally restrict this only to the nondependent function space, since type-class
inference cannot find an instance for `ι → ℝ` when this is stated for dependent function spaces. -/
@[to_additive /-- We intentionally restrict this only to the nondependent function space, since
type-class inference cannot find an instance for `ι → ℝ` when this is stated for dependent function
spaces. -/]
/-
**MeasureTheory.Pi.isInvInvariant_volume** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Pi`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] {α : Type u_4} [inst_1 : Group α] [ins
t_2 : MeasureTheory.MeasureSpace α]   [MeasureTheory.SigmaFinite MeasureTheory.v
olume] [MeasurableInv α] [MeasureTheory.volume.IsInvInvariant],   MeasureTheory.
volume.IsInvInvariant
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pi.isInvInvariant`：∀ {ι : Type u_1} {α : ι → Type 
u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι
) → MeasureTheory.Measure (α …
-/
instance Pi.isInvInvariant_volume {α} [Group α] [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    [MeasurableInv α] [IsInvInvariant (volume : Measure α)] :
    IsInvInvariant (volume : Measure (ι → α)) :=
  pi.isInvInvariant _

/-!
### Measure-preserving equivalences

In this section we prove that some measurable equivalences (e.g., between `Fin 1 → α` and `α` or
between `Fin 2 → α` and `α × α`) preserve measure or volume. These lemmas can be used to prove that
measures of corresponding sets (images or preimages) have equal measures and functions `f ∘ e` and
`f` have equal integrals, see lemmas in the `MeasureTheory.measurePreserving` prefix.
-/


section MeasurePreserving

variable {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
variable [Fintype ι']

/-
**MeasureTheory.measurePreserving_piEquivPiSubtypeProd** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：measurePreserving_piEquivPiSubtypeProd (p : ι -> Prop) [DecidablePred p] :
 MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p) (Measure.pi μ) ((M
easure.pi fun i : Subtype p => μ i).prod (Measure.pi fun i => μ i))
参数：p : ι -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `Equiv.preimage_piEquivPiSubtypeProd_symm_pi`：preimage_piEquivPiSubtypePr
od_symm_pi {α : Type*} {β : α -> Type*} (p : α -> Prop) [DecidablePred p] (s : f
orall i, Set (β i)) : (piEquivPiS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.pi.sigmaFinite`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `Fintype.prod_subtype_mul_prod_subtype`：prod_subtype_mul_prod_subtype (p 
: ι -> Prop) (f : ι -> M) [DecidablePred p] : (∏ i : { x // p x }, f i) * ∏ i : 
{ x // ¬p x }, f i = ∏ i, f…
-/
theorem measurePreserving_piEquivPiSubtypeProd (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p) (Measure.pi μ)
      ((Measure.pi fun i : Subtype p => μ i).prod (Measure.pi fun i => μ i)) := by
  set e := (MeasurableEquiv.piEquivPiSubtypeProd α p).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s _ => ?_).symm⟩
  have : e ⁻¹' pi univ s =
      (pi univ fun i : { i // p i } => s i) ×ˢ pi univ fun i : { i // ¬p i } => s i :=
    Equiv.preimage_piEquivPiSubtypeProd_symm_pi p s
  rw [e.map_apply, this, prod_prod, pi_pi, pi_pi]
  exact Fintype.prod_subtype_mul_prod_subtype p fun i => μ i (s i)
/-
**MeasureTheory.volume_preserving_piEquivPiSubtypeProd** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：volume_preserving_piEquivPiSubtypeProd (α : ι -> Type*) [forall i, Measure
Space (α i)] [forall i, SigmaFinite (volume : Measure (α i))] (p : ι -> Prop) [D
ecidablePred p] : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p)
参数：α : ι -> Type*；α i；volume : Measure (α i)；p : ι -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_piEquivPiSubtypeProd`：measurePreserving_
piEquivPiSubtypeProd (p : ι -> Prop) [DecidablePred p] : MeasurePreserving (Meas
urableEquiv.piEquivPiSubtypeProd α p) (Mea…
-/
theorem volume_preserving_piEquivPiSubtypeProd (α : ι → Type*)
    [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] (p : ι → Prop)
    [DecidablePred p] : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p) :=
  measurePreserving_piEquivPiSubtypeProd (fun _ => volume) p
/-
**MeasureTheory.measurePreserving_piCongrLeft** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measurePreserving_piCongrLeft (f : ι' ≃ ι) : MeasurePreserving (Measurable
Equiv.piCongrLeft α f) (Measure.pi fun i' => μ (f i')) (Measure.pi μ) where meas
urable
参数：f : ι' ≃ ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `MeasurableEquiv.coe_piCongrLeft`：coe_piCongrLeft (f : δ ≃ δ') : ⇑(Measur
ableEquiv.piCongrLeft π f) = f.piCongrLeft π
· 使用定理 `Equiv.piCongrLeft_preimage_univ_pi`：piCongrLeft_preimage_univ_pi (f : ι'
 ≃ ι) (t : forall i, Set (α i)) : f.piCongrLeft α ⁻¹' univ.pi t = univ.pi fun i 
=> t (f i)
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
-/
theorem measurePreserving_piCongrLeft (f : ι' ≃ ι) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft α f)
      (Measure.pi fun i' => μ (f i')) (Measure.pi μ) where
  measurable := (MeasurableEquiv.piCongrLeft α f).measurable
  map_eq := by
    refine (pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_piCongrLeft f,
      Equiv.piCongrLeft_preimage_univ_pi, pi_pi _ _, f.prod_comp (fun i => μ i (s i))]
/-
**MeasureTheory.volume_measurePreserving_piCongrLeft** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：volume_measurePreserving_piCongrLeft (α : ι -> Type*) (f : ι' ≃ ι) [forall
 i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))] : Measu
rePreserving (MeasurableEquiv.piCongrLeft α f) volume volume
参数：α : ι -> Type*；f : ι' ≃ ι；α i；volume : Measure (α i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_piCongrLeft`：measurePreserving_piCongrLe
ft (f : ι' ≃ ι) : MeasurePreserving (MeasurableEquiv.piCongrLeft α f) (Measure.p
i fun i' => μ (f i')) (Measure.pi…
-/
theorem volume_measurePreserving_piCongrLeft (α : ι → Type*) (f : ι' ≃ ι)
    [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piCongrLeft α f) volume volume :=
  measurePreserving_piCongrLeft (fun _ ↦ volume) f
/-
**MeasureTheory.Measure.pi_map_piCongrLeft** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} [inst : Fintype ι] [inst_1 : Fintype ι'] 
(e : ι ≃ ι') {β : ι' → Type u_4}   [inst_2 : (i : ι') → MeasurableSpace (β i)] (
μ : (i : ι') → MeasureTheory.Measure (β i))   [∀ (i : ι'), MeasureTheory.SigmaFi
nite (μ i)],   MeasureTheory.Measure.map (⇑(MeasurableEquiv.piCongrLeft (fun i =
> β i) e))       (MeasureTheory.Measure.pi fun i => μ (e i)) =     MeasureTheory
.Measure.pi μ
参数：e : ι ≃ ι'；i : ι'；β i；μ : (i : ι') → MeasureTheory.Measure (β i)；i : ι'；μ i；⇑
(MeasurableEquiv.piCongrLeft (fun i => β i) e)；MeasureTheory.Measure.pi fun i =>
 μ (e i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.measurePreserving_piCongrLeft`：measurePreserving_piCongrLe
ft (f : ι' ≃ ι) : MeasurePreserving (MeasurableEquiv.piCongrLeft α f) (Measure.p
i fun i' => μ (f i')) (Measure.pi…
-/
lemma Measure.pi_map_piCongrLeft (e : ι ≃ ι') {β : ι' → Type*} [∀ i, MeasurableSpace (β i)]
    (μ : (i : ι') → Measure (β i)) [∀ i, SigmaFinite (μ i)] :
    (Measure.pi fun i ↦ μ (e i)).map (MeasurableEquiv.piCongrLeft (fun i ↦ β i) e) =
      Measure.pi μ :=
  (measurePreserving_piCongrLeft (α := fun i ↦ β i) μ e).map_eq
/-
**MeasureTheory.measurePreserving_arrowProdEquivProdArrow** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：measurePreserving_arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace
 α] [MeasurableSpace β] [Fintype γ] (μ : γ -> Measure α) (ν : γ -> Measure β) [f
orall i, SigmaFinite (μ i)] [forall i, SigmaFinite (ν i)] : MeasurePreserving (M
easurableEquiv.arrowProdEquivProdArrow α β γ) (.pi fun i => (μ i).prod (ν i)) ((
Measure.pi fun i => μ i).prod (Measure.pi fun i => ν i)) where measurable
参数：α β γ : Type*；μ : γ -> Measure α；ν : γ -> Measure β；μ i；ν i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.ext`：∀ {α : Type u_1} {m0 : M
easurableSpace α} {μ ν : MeasureTheory.Measure α} {C : Set (Set α)},   m0 = Meas
urableSpace.generateFrom C → IsPiSys…
· 使用定理 `generateFrom_eq_prod`：generateFrom_eq_prod {C : Set (Set α)} {D : Set (S
et β)} (hC : generateFrom C = ‹_›) (hD : generateFrom D = ‹_›) (h2C : IsCountabl
ySpanning …
· 使用定理 `generateFrom_pi`：generateFrom_pi [forall i, MeasurableSpace (α i)] : gen
erateFrom (pi univ '' pi univ fun i => { s : Set (α i) | MeasurableSet s }) = Me
asura…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.isCountablySpanning`：∀ {α : T
ype u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)
}   (h : μ.FiniteSpanningSetsIn C), IsCountablySpann…
· 使用引理 `IsPiSystem.prod`：IsPiSystem.prod {C : Set (Set α)} {D : Set (Set β)} (hC
 : IsPiSystem C) (hD : IsPiSystem D) : IsPiSystem (image2 (· ×ˢ ·) C D)
· 使用定理 `isPiSystem_pi`：isPiSystem_pi [forall i, MeasurableSpace (α i)] : IsPiSys
tem (pi univ '' pi univ fun i => { s : Set (α i) | MeasurableSet s })
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `MeasurableEquiv.arrowProdEquivProdArrow.eq_1`：∀ (α : Type u_8) (β : Type
 u_9) (γ : Type u_10) [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β],  
 MeasurableEquiv.arrowProdEquivPro…
· 使用定理 `MeasurableEquiv.coe_mk`：coe_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Mea
surable e.symm) : ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α -> β) = e
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.arrowProdEquivProdArrow_apply`：∀ (α : Type u_9) (β : α → Type u_10
) (γ : α → Type u_11) (f : (i : α) → β i × γ i),   (Equiv.arrowProdEquivProdArro
w α β γ) f = (fun c => (f…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `MeasureTheory.Measure.prod.instSigmaFinite`：∀ {α : Type u_4} {β : Type u
_5} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFi
nite μ]   {x_1 : MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.pi.sigmaFinite`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
（共 31 条，此处仅展示前 30 条）
-/
theorem measurePreserving_arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace α]
    [MeasurableSpace β] [Fintype γ] (μ : γ → Measure α) (ν : γ → Measure β) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow α β γ)
      (.pi fun i ↦ (μ i).prod (ν i))
        ((Measure.pi fun i ↦ μ i).prod (Measure.pi fun i ↦ ν i)) where
  measurable := (MeasurableEquiv.arrowProdEquivProdArrow α β γ).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi (fun i ↦ (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply, MeasurableEquiv.arrowProdEquivProdArrow,
        MeasurableEquiv.coe_mk]
      rw [show Equiv.arrowProdEquivProdArrow γ _ _ ⁻¹' (univ.pi s ×ˢ univ.pi t) =
          (univ.pi fun i ↦ s i ×ˢ t i) by
          ext; simp [Set.mem_pi, forall_and]]
      simp_rw [pi_pi, prod_prod, pi_pi, Finset.prod_mul_distrib]
/-
**MeasureTheory.volume_measurePreserving_arrowProdEquivProdArrow** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：volume_measurePreserving_arrowProdEquivProdArrow (α β γ : Type*) [MeasureS
pace α] [MeasureSpace β] [Fintype γ] [SigmaFinite (volume : Measure α)] [SigmaFi
nite (volume : Measure β)] : MeasurePreserving (MeasurableEquiv.arrowProdEquivPr
odArrow α β γ)
参数：α β γ : Type*；volume : Measure α；volume : Measure β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_arrowProdEquivProdArrow`：measurePreservi
ng_arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace 
β] [Fintype γ] (μ : γ -> Measure α) (ν : γ ->…
-/
theorem volume_measurePreserving_arrowProdEquivProdArrow (α β γ : Type*) [MeasureSpace α]
    [MeasureSpace β] [Fintype γ] [SigmaFinite (volume : Measure α)]
    [SigmaFinite (volume : Measure β)] :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow α β γ) :=
  measurePreserving_arrowProdEquivProdArrow α β γ (fun _ ↦ volume) (fun _ ↦ volume)
/-
**MeasureTheory.measurePreserving_sumPiEquivProdPi_symm** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：measurePreserving_sumPiEquivProdPi_symm {X : ι oplus ι' -> Type*} {m : for
all i, MeasurableSpace (X i)} (μ : forall i, Measure (X i)) [forall i, SigmaFini
te (μ i)] : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm ((Measur
e.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) (Measure.pi μ) 
where measurable
参数：X i；μ : forall i, Measure (X i)；μ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MeasurableEquiv.coe_sumPiEquivProdPi_symm`：coe_sumPiEquivProdPi_symm (α 
: δ oplus δ' -> Type*) [forall i, MeasurableSpace (α i)] : ⇑(MeasurableEquiv.sum
PiEquivProdPi α).symm = (Equiv.…
· 使用定理 `Equiv.sumPiEquivProdPi_symm_preimage_univ_pi`：sumPiEquivProdPi_symm_prei
mage_univ_pi (π : ι oplus ι' -> Type*) (t : forall i, Set (π i)) : (sumPiEquivPr
odPi π).symm ⁻¹' univ.pi t = univ.…
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.pi.sigmaFinite`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.prod_sum_type`：Fintype.prod_sum_type (f : α₁ oplus α₂ -> M) : ∏ 
x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measurePreserving_sumPiEquivProdPi_symm {X : ι ⊕ ι' → Type*}
    {m : ∀ i, MeasurableSpace (X i)} (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm
      ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) (Measure.pi μ) where
  measurable := (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
  map_eq := by
    refine (pi_eq fun s _ => ?_).symm
    simp_rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
      Equiv.sumPiEquivProdPi_symm_preimage_univ_pi, Measure.prod_prod, Measure.pi_pi,
      Fintype.prod_sum_type]
/-
**MeasureTheory.volume_measurePreserving_sumPiEquivProdPi_symm** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：volume_measurePreserving_sumPiEquivProdPi_symm (X : ι oplus ι' -> Type*) [
forall i, MeasureSpace (X i)] [forall i, SigmaFinite (volume : Measure (X i))] :
 MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm volume volume
参数：X : ι oplus ι' -> Type*；X i；volume : Measure (X i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_sumPiEquivProdPi_symm`：measurePreserving
_sumPiEquivProdPi_symm {X : ι oplus ι' -> Type*} {m : forall i, MeasurableSpace 
(X i)} (μ : forall i, Measure (X i)) [foral…
-/
theorem volume_measurePreserving_sumPiEquivProdPi_symm (X : ι ⊕ ι' → Type*)
    [∀ i, MeasureSpace (X i)] [∀ i, SigmaFinite (volume : Measure (X i))] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm volume volume :=
  measurePreserving_sumPiEquivProdPi_symm (fun _ ↦ volume)
/-
**MeasureTheory.measurePreserving_sumPiEquivProdPi** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：measurePreserving_sumPiEquivProdPi {X : ι oplus ι' -> Type*} {_m : forall 
i, MeasurableSpace (X i)} (μ : forall i, Measure (X i)) [forall i, SigmaFinite (
μ i)] : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X) (Measure.pi μ) ((
Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i)))
参数：X i；μ : forall i, Measure (X i)；μ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.measurePreserving_sumPiEquivProdPi_symm`：measurePreserving
_sumPiEquivProdPi_symm {X : ι oplus ι' -> Type*} {m : forall i, MeasurableSpace 
(X i)} (μ : forall i, Measure (X i)) [foral…
-/
theorem measurePreserving_sumPiEquivProdPi {X : ι ⊕ ι' → Type*} {_m : ∀ i, MeasurableSpace (X i)}
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X)
      (Measure.pi μ) ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) :=
  measurePreserving_sumPiEquivProdPi_symm μ |>.symm
/-
**MeasureTheory.volume_measurePreserving_sumPiEquivProdPi** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：volume_measurePreserving_sumPiEquivProdPi (X : ι oplus ι' -> Type*) [foral
l i, MeasureSpace (X i)] [forall i, SigmaFinite (volume : Measure (X i))] : Meas
urePreserving (MeasurableEquiv.sumPiEquivProdPi X) volume volume
参数：X : ι oplus ι' -> Type*；X i；volume : Measure (X i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_sumPiEquivProdPi`：measurePreserving_sumP
iEquivProdPi {X : ι oplus ι' -> Type*} {_m : forall i, MeasurableSpace (X i)} (μ
 : forall i, Measure (X i)) [forall i,…
-/
theorem volume_measurePreserving_sumPiEquivProdPi (X : ι ⊕ ι' → Type*)
    [∀ i, MeasureSpace (X i)] [∀ i, SigmaFinite (volume : Measure (X i))] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X) volume volume :=
  measurePreserving_sumPiEquivProdPi (fun _ ↦ volume)
/-
**MeasureTheory.measurePreserving_piFinSuccAbove** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：measurePreserving_piFinSuccAbove {n : Nat} {α : Fin (n + 1) -> Type u} {m 
: forall i, MeasurableSpace (α i)} (μ : forall i, Measure (α i)) [forall i, Sigm
aFinite (μ i)] (i : Fin (n + 1)) : MeasurePreserving (MeasurableEquiv.piFinSuccA
bove α i) (Measure.pi μ) ((μ i).prod <| Measure.pi fun j => μ (i.succAbove j))
参数：n + 1；α i；μ : forall i, Measure (α i)；μ i；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `Fin.prod_univ_succAbove`：prod_univ_succAbove (f : Fin (n + 1) -> M) (x :
 Fin (n + 1)) : ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.pi.sigmaFinite`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableEquiv.piFinSuccAbove_symm_apply`：∀ {n : ℕ} (α : Fin (n + 1) → 
Type u_8) [inst : (i : Fin (n + 1)) → MeasurableSpace (α i)] (i : Fin (n + 1)), 
  ⇑(MeasurableEquiv.piFinSuccAb…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Fin.insertNthEquiv_apply`：∀ {n : ℕ} (α : Fin (n + 1) → Type u) (p : Fin 
(n + 1)) (f : α p × ((i : Fin n) → α (p.succAbove i))) (j : Fin (n + 1)),   (Fin
.insertNthEqui…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Fin.forall_iff_succAbove`：forall_iff_succAbove {P : Fin (n + 1) -> Prop}
 (p : Fin (n + 1)) : (forall i, P i) ↔ P p ∧ forall i, P (p.succAbove i)
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem measurePreserving_piFinSuccAbove {n : ℕ} {α : Fin (n + 1) → Type u}
    {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i) (Measure.pi μ)
      ((μ i).prod <| Measure.pi fun j => μ (i.succAbove j)) := by
  set e := (MeasurableEquiv.piFinSuccAbove α i).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s _ => ?_).symm⟩
  rw [e.map_apply, i.prod_univ_succAbove _, ← pi_pi, ← prod_prod]
  congr 1 with ⟨x, f⟩
  simp [e, i.forall_iff_succAbove]
/-
**MeasureTheory.volume_preserving_piFinSuccAbove** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：volume_preserving_piFinSuccAbove {n : Nat} (α : Fin (n + 1) -> Type u) [fo
rall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))] (i 
: Fin (n + 1)) : MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i)
参数：α : Fin (n + 1) -> Type u；α i；volume : Measure (α i)；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_piFinSuccAbove`：measurePreserving_piFinS
uccAbove {n : Nat} {α : Fin (n + 1) -> Type u} {m : forall i, MeasurableSpace (α
 i)} (μ : forall i, Measure (α i)) […
-/
theorem volume_preserving_piFinSuccAbove {n : ℕ} (α : Fin (n + 1) → Type u)
    [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i) :=
  measurePreserving_piFinSuccAbove (fun _ => volume) i
/-
**MeasureTheory.measurePreserving_piUnique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measurePreserving_piUnique {X : ι -> Type*} [Unique ι] {m : forall i, Meas
urableSpace (X i)} (μ : forall i, Measure (X i)) : MeasurePreserving (Measurable
Equiv.piUnique X) (Measure.pi μ) (μ default) where measurable
参数：X i；μ : forall i, Measure (X i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.piPremeasure.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_3} [in
st : Fintype ι] (m : (i : ι) → MeasureTheory.OuterMeasure (α i))   (s : Set ((i 
: ι) → α i)), Measure…
· 使用定理 `Fintype.prod_unique`：prod_unique [Unique ι] (f : ι -> M) : ∏ x : ι, f x 
= f default
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `MeasureTheory.Measure.coe_toOuterMeasure`：∀ {α : Type u_1} [inst : Measu
rableSpace α] (μ : MeasureTheory.Measure α), ⇑μ.toOuterMeasure = ⇑μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `MeasureTheory.Measure.pi_caratheodory`：pi_caratheodory : MeasurableSpace
.pi <= (OuterMeasure.pi fun i => (μ i).toOuterMeasure).caratheodory
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.pi_def`：∀ {ι : Type u_4} {α : ι → Type u_5} [inst 
: Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) → Measure
Theory.Measure (α …
· 使用定理 `MeasureTheory.OuterMeasure.toMeasure.congr_simp`：∀ {α : Type u_1} [ms : 
MeasurableSpace α] (m m_1 : MeasureTheory.OuterMeasure α) (e_m : m = m_1)   (h :
 ms ≤ m.caratheodory), m.toMeasure h …
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_eq_self`：boundedBy_eq_self (m : Out
erMeasure α) : boundedBy m = m
· 使用定理 `MeasureTheory.toOuterMeasure_toMeasure`：toOuterMeasure_toMeasure {μ : Me
asure α} : μ.toOuterMeasure.toMeasure (le_toOuterMeasure_caratheodory _) = μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasurableEquiv.map_map_symm`：map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm)
.map e = ν
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measurePreserving_piUnique {X : ι → Type*} [Unique ι] {m : ∀ i, MeasurableSpace (X i)}
    (μ : ∀ i, Measure (X i)) :
    MeasurePreserving (MeasurableEquiv.piUnique X) (Measure.pi μ) (μ default) where
  measurable := (MeasurableEquiv.piUnique X).measurable
  map_eq := by
    set e := MeasurableEquiv.piUnique X
    have : (piPremeasure fun i => (μ i).toOuterMeasure) = Measure.map e.symm (μ default) := by
      ext1 s
      rw [piPremeasure, Fintype.prod_unique, e.symm.map_apply, coe_toOuterMeasure]
      congr 1; exact e.toEquiv.image_eq_preimage_symm s
    simp_rw [Measure.pi, OuterMeasure.pi, this, ← coe_toOuterMeasure, boundedBy_eq_self,
      toOuterMeasure_toMeasure, MeasurableEquiv.map_map_symm]
/-
**MeasureTheory.volume_preserving_piUnique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：volume_preserving_piUnique (X : ι -> Type*) [Unique ι] [forall i, MeasureS
pace (X i)] : MeasurePreserving (MeasurableEquiv.piUnique X) volume volume
参数：X : ι -> Type*；X i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_piUnique`：measurePreserving_piUnique {X 
: ι -> Type*} [Unique ι] {m : forall i, MeasurableSpace (X i)} (μ : forall i, Me
asure (X i)) : MeasurePreservi…
-/
theorem volume_preserving_piUnique (X : ι → Type*) [Unique ι] [∀ i, MeasureSpace (X i)] :
    MeasurePreserving (MeasurableEquiv.piUnique X) volume volume :=
  measurePreserving_piUnique _
/-
**MeasureTheory.measurePreserving_funUnique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measurePreserving_funUnique {β : Type u} {_m : MeasurableSpace β} (μ : Mea
sure β) (α : Type v) [Unique α] : MeasurePreserving (MeasurableEquiv.funUnique α
 β) (Measure.pi fun _ : α => μ) μ
参数：μ : Measure β；α : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_piUnique`：measurePreserving_piUnique {X 
: ι -> Type*} [Unique ι] {m : forall i, MeasurableSpace (X i)} (μ : forall i, Me
asure (X i)) : MeasurePreservi…
-/
theorem measurePreserving_funUnique {β : Type u} {_m : MeasurableSpace β} (μ : Measure β)
    (α : Type v) [Unique α] :
    MeasurePreserving (MeasurableEquiv.funUnique α β) (Measure.pi fun _ : α => μ) μ :=
  measurePreserving_piUnique _
/-
**MeasureTheory.volume_preserving_funUnique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：volume_preserving_funUnique (α : Type u) (β : Type v) [Unique α] [MeasureS
pace β] : MeasurePreserving (MeasurableEquiv.funUnique α β) volume volume
参数：α : Type u；β : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_funUnique`：measurePreserving_funUnique {
β : Type u} {_m : MeasurableSpace β} (μ : Measure β) (α : Type v) [Unique α] : M
easurePreserving (MeasurableEqu…
-/
theorem volume_preserving_funUnique (α : Type u) (β : Type v) [Unique α] [MeasureSpace β] :
    MeasurePreserving (MeasurableEquiv.funUnique α β) volume volume :=
  measurePreserving_funUnique volume α
/-
**MeasureTheory.measurePreserving_piFinTwo** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measurePreserving_piFinTwo {α : Fin 2 -> Type u} {m : forall i, Measurable
Space (α i)} (μ : forall i, Measure (α i)) [forall i, SigmaFinite (μ i)] : Measu
rePreserving (MeasurableEquiv.piFinTwo α) (Measure.pi μ) ((μ 0).prod (μ 1))
参数：α i；μ : forall i, Measure (α i)；μ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `MeasurableEquiv.piFinTwo_apply`：∀ (α : Fin 2 → Type u_8) [inst : (i : Fi
n 2) → MeasurableSpace (α i)],   ⇑(MeasurableEquiv.piFinTwo α) = fun f => (f 0, 
f 1)
· 使用定理 `Fin.preimage_apply_01_prod`：Fin.preimage_apply_01_prod {α : Fin 2 -> Typ
e u} (s : Set (α 0)) (t : Set (α 1)) : (fun f : forall i, α i => (f 0, f 1)) ⁻¹'
 s ×ˢ t = Set.pi…
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
-/
theorem measurePreserving_piFinTwo {α : Fin 2 → Type u} {m : ∀ i, MeasurableSpace (α i)}
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.piFinTwo α) (Measure.pi μ) ((μ 0).prod (μ 1)) := by
  refine ⟨MeasurableEquiv.measurable _, (Measure.prod_eq fun s t _ _ => ?_).symm⟩
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.piFinTwo_apply, Fin.preimage_apply_01_prod,
    Measure.pi_pi, Fin.prod_univ_two]
  rfl
/-
**MeasureTheory.volume_preserving_piFinTwo** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：volume_preserving_piFinTwo (α : Fin 2 -> Type u) [forall i, MeasureSpace (
α i)] [forall i, SigmaFinite (volume : Measure (α i))] : MeasurePreserving (Meas
urableEquiv.piFinTwo α) volume volume
参数：α : Fin 2 -> Type u；α i；volume : Measure (α i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_piFinTwo`：measurePreserving_piFinTwo {α 
: Fin 2 -> Type u} {m : forall i, MeasurableSpace (α i)} (μ : forall i, Measure 
(α i)) [forall i, SigmaFinite …
-/
theorem volume_preserving_piFinTwo (α : Fin 2 → Type u) [∀ i, MeasureSpace (α i)]
    [∀ i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piFinTwo α) volume volume :=
  measurePreserving_piFinTwo _
/-
**MeasureTheory.measurePreserving_finTwoArrow_vec** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：measurePreserving_finTwoArrow_vec {α : Type u} {_ : MeasurableSpace α} (μ 
ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] : MeasurePreserving MeasurableEqu
iv.finTwoArrow (Measure.pi ![μ, ν]) (μ.prod ν)
参数：μ ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_piFinTwo`：measurePreserving_piFinTwo {α 
: Fin 2 -> Type u} {m : forall i, MeasurableSpace (α i)} (μ : forall i, Measure 
(α i)) [forall i, SigmaFinite …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.forall_fin_two`：∀ {p : Fin 2 → Prop}, (∀ (i : Fin 2), p i) ↔ p 0 ∧ p
 1
-/
theorem measurePreserving_finTwoArrow_vec {α : Type u} {_ : MeasurableSpace α} (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] :
    MeasurePreserving MeasurableEquiv.finTwoArrow (Measure.pi ![μ, ν]) (μ.prod ν) :=
  haveI : ∀ i, SigmaFinite (![μ, ν] i) := Fin.forall_fin_two.2 ⟨‹_›, ‹_›⟩
  measurePreserving_piFinTwo _
/-
**MeasureTheory.measurePreserving_finTwoArrow** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measurePreserving_finTwoArrow {α : Type u} {m : MeasurableSpace α} (μ : Me
asure α) [SigmaFinite μ] : MeasurePreserving MeasurableEquiv.finTwoArrow (Measur
e.pi fun _ => μ) (μ.prod μ)
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.vec_single_eq_const`：vec_single_eq_const (a : α) : ![a] = fun _ =
> a
· 使用定理 `Matrix.vecCons_const`：vecCons_const (a : α) : (vecCons a fun _ : Fin n =
> a) = fun _ => a
· 使用定理 `MeasureTheory.measurePreserving_finTwoArrow_vec`：measurePreserving_finTw
oArrow_vec {α : Type u} {_ : MeasurableSpace α} (μ ν : Measure α) [SigmaFinite μ
] [SigmaFinite ν] : MeasurePreserving…
-/
theorem measurePreserving_finTwoArrow {α : Type u} {m : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] :
    MeasurePreserving MeasurableEquiv.finTwoArrow (Measure.pi fun _ => μ) (μ.prod μ) := by
  simpa only [Matrix.vec_single_eq_const, Matrix.vecCons_const] using
    measurePreserving_finTwoArrow_vec μ μ
/-
**MeasureTheory.volume_preserving_finTwoArrow** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：volume_preserving_finTwoArrow (α : Type u) [MeasureSpace α] [SigmaFinite (
volume : Measure α)] : MeasurePreserving (@MeasurableEquiv.finTwoArrow α _) volu
me volume
参数：α : Type u；volume : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_finTwoArrow`：measurePreserving_finTwoArr
ow {α : Type u} {m : MeasurableSpace α} (μ : Measure α) [SigmaFinite μ] : Measur
ePreserving MeasurableEquiv.finTw…
-/
theorem volume_preserving_finTwoArrow (α : Type u) [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] :
    MeasurePreserving (@MeasurableEquiv.finTwoArrow α _) volume volume :=
  measurePreserving_finTwoArrow volume
/-
**MeasureTheory.measurePreserving_pi_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measurePreserving_pi_empty {ι : Type u} {α : ι -> Type v} [Fintype ι] [IsE
mpty ι] {m : forall i, MeasurableSpace (α i)} (μ : forall i, Measure (α i)) : Me
asurePreserving (MeasurableEquiv.ofUniqueOfUnique (forall i, α i) Unit) (Measure
.pi μ) (Measure.dirac ())
参数：α i；μ : forall i, Measure (α i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `MeasureTheory.Measure.pi_of_empty`：pi_of_empty {α : Type*} [Fintype α] [
IsEmpty α] {β : α -> Type*} {m : forall a, MeasurableSpace (β a)} (μ : forall a 
: α, Measure (β a)) (x …
· 使用定理 `MeasureTheory.Measure.map_dirac'`：map_dirac' {f : α -> β} (hf : Measurab
le f) (a : α) : (dirac a).map f = dirac (f a)
-/
theorem measurePreserving_pi_empty {ι : Type u} {α : ι → Type v} [Fintype ι] [IsEmpty ι]
    {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) :
    MeasurePreserving (MeasurableEquiv.ofUniqueOfUnique (∀ i, α i) Unit) (Measure.pi μ)
      (Measure.dirac ()) := by
  set e := MeasurableEquiv.ofUniqueOfUnique (∀ i, α i) Unit
  refine ⟨e.measurable, ?_⟩
  rw [Measure.pi_of_empty, Measure.map_dirac' e.measurable]
/-
**MeasureTheory.volume_preserving_pi_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：volume_preserving_pi_empty {ι : Type u} (α : ι -> Type v) [Fintype ι] [IsE
mpty ι] [forall i, MeasureSpace (α i)] : MeasurePreserving (MeasurableEquiv.ofUn
iqueOfUnique (forall i, α i) Unit) volume volume
参数：α : ι -> Type v；α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_pi_empty`：measurePreserving_pi_empty {ι 
: Type u} {α : ι -> Type v} [Fintype ι] [IsEmpty ι] {m : forall i, MeasurableSpa
ce (α i)} (μ : forall i, Measu…
-/
theorem volume_preserving_pi_empty {ι : Type u} (α : ι → Type v) [Fintype ι] [IsEmpty ι]
    [∀ i, MeasureSpace (α i)] :
    MeasurePreserving (MeasurableEquiv.ofUniqueOfUnique (∀ i, α i) Unit) volume volume :=
  measurePreserving_pi_empty fun _ => volume
/-
**MeasureTheory.measurePreserving_piFinsetUnion** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measurePreserving_piFinsetUnion {ι : Type*} {α : ι -> Type*} {_ : forall i
, MeasurableSpace (α i)} [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t) (μ 
: forall i, Measure (α i)) [forall i, SigmaFinite (μ i)] : MeasurePreserving (Me
asurableEquiv.piFinsetUnion α h) ((Measure.pi fun i : s => μ i).prod (Measure.pi
 fun i : t => μ i)) (Measure.pi fun i : ↥(s union t) => μ i)
参数：α i；h : Disjoint s t；μ : forall i, Measure (α i)；μ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_piCongrLeft`：measurePreserving_piCongrLe
ft (f : ι' ≃ ι) : MeasurePreserving (MeasurableEquiv.piCongrLeft α f) (Measure.p
i fun i' => μ (f i')) (Measure.pi…
· 使用定理 `MeasureTheory.measurePreserving_sumPiEquivProdPi_symm`：measurePreserving
_sumPiEquivProdPi_symm {X : ι oplus ι' -> Type*} {m : forall i, MeasurableSpace 
(X i)} (μ : forall i, Measure (X i)) [foral…
-/
theorem measurePreserving_piFinsetUnion {ι : Type*} {α : ι → Type*}
    {_ : ∀ i, MeasurableSpace (α i)} [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t)
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.piFinsetUnion α h)
      ((Measure.pi fun i : s ↦ μ i).prod (Measure.pi fun i : t ↦ μ i))
      (Measure.pi fun i : ↥(s ∪ t) ↦ μ i) :=
  let e := Equiv.Finset.union s t h
  measurePreserving_piCongrLeft (fun i : ↥(s ∪ t) ↦ μ i) e |>.comp <|
    measurePreserving_sumPiEquivProdPi_symm fun b ↦ μ (e b)
/-
**MeasureTheory.volume_preserving_piFinsetUnion** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：volume_preserving_piFinsetUnion {ι : Type*} [DecidableEq ι] (α : ι -> Type
*) {s t : Finset ι} (h : Disjoint s t) [forall i, MeasureSpace (α i)] [forall i,
 SigmaFinite (volume : Measure (α i))] : MeasurePreserving (MeasurableEquiv.piFi
nsetUnion α h) volume volume
参数：α : ι -> Type*；h : Disjoint s t；α i；volume : Measure (α i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_piFinsetUnion`：measurePreserving_piFinse
tUnion {ι : Type*} {α : ι -> Type*} {_ : forall i, MeasurableSpace (α i)} [Decid
ableEq ι] {s t : Finset ι} (h : Dis…
-/
theorem volume_preserving_piFinsetUnion {ι : Type*} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι}
    (h : Disjoint s t) [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piFinsetUnion α h) volume volume :=
  measurePreserving_piFinsetUnion h (fun _ ↦ volume)
/-
**MeasureTheory.measurePreserving_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measurePreserving_pi {ι : Type*} [Fintype ι] {α : ι -> Type v} {β : ι -> T
ype*} [forall i, MeasurableSpace (α i)] [forall i, MeasurableSpace (β i)] (μ : (
i : ι) -> Measure (α i)) (ν : (i : ι) -> Measure (β i)) {f : (i : ι) -> (α i) ->
 (β i)} [hν : forall i, SigmaFinite (ν i)] (hf : forall i, MeasurePreserving (f 
i) (μ i) (ν i)) : MeasurePreserving (fun a i => f i (a i)) (Measure.pi μ) (Measu
re.pi ν) where measurable
参数：α i；β i；μ : (i : ι) -> Measure (α i)；ν : (i : ι) -> Measure (β i)；i : ι；α i；β
 i；ν i；hf : forall i, MeasurePreserving (f i) (μ i) (ν i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.pi_map_pi`：pi_map_pi {X Y : ι -> Type*} {mX : fora
ll i, MeasurableSpace (X i)} {μ : (i : ι) -> Measure (X i)} [forall i, Measurabl
eSpace (Y i)] {f : (i…
· 使用定理 `MeasureTheory.MeasurePreserving.aemeasurable`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : MeasureTheor
y.Measure α}   {μb : MeasureTheory…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem measurePreserving_pi {ι : Type*} [Fintype ι] {α : ι → Type v} {β : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
    (μ : (i : ι) → Measure (α i)) (ν : (i : ι) → Measure (β i))
    {f : (i : ι) → (α i) → (β i)} [hν : ∀ i, SigmaFinite (ν i)]
    (hf : ∀ i, MeasurePreserving (f i) (μ i) (ν i)) :
    MeasurePreserving (fun a i ↦ f i (a i)) (Measure.pi μ) (Measure.pi ν) where
  measurable :=
    measurable_pi_iff.mpr <| fun i ↦ (hf i).measurable.comp (measurable_pi_apply i)
  map_eq := by
    have (i : ι) : SigmaFinite ((μ i).map (f i)) := (hf i).map_eq ▸ hν i
    rw [pi_map_pi (fun i ↦ (hf i).aemeasurable)]
    exact congrArg _ <| funext fun i ↦ (hf i).map_eq
/-
**MeasureTheory.volume_preserving_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：volume_preserving_pi {α' β' : ι -> Type*} [forall i, MeasureSpace (α' i)] 
[forall i, MeasureSpace (β' i)] [forall i, SigmaFinite (volume : Measure (β' i))
] {f : (i : ι) -> (α' i) -> (β' i)} (hf : forall i, MeasurePreserving (f i)) : M
easurePreserving (fun (a : (i : ι) -> α' i) (i : ι) => (f i) (a i))
参数：α' i；β' i；volume : Measure (β' i)；i : ι；α' i；β' i；hf : forall i, MeasurePrese
rving (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_pi`：measurePreserving_pi {ι : Type*} [Fi
ntype ι] {α : ι -> Type v} {β : ι -> Type*} [forall i, MeasurableSpace (α i)] [f
orall i, MeasurableSpace…
-/
theorem volume_preserving_pi {α' β' : ι → Type*} [∀ i, MeasureSpace (α' i)]
    [∀ i, MeasureSpace (β' i)] [∀ i, SigmaFinite (volume : Measure (β' i))]
    {f : (i : ι) → (α' i) → (β' i)} (hf : ∀ i, MeasurePreserving (f i)) :
    MeasurePreserving (fun (a : (i : ι) → α' i) (i : ι) ↦ (f i) (a i)) :=
  measurePreserving_pi _ _ hf

set_option backward.isDefEq.respectTransparency.types false in
/-- The measurable equiv `(α₁ → β₁) ≃ᵐ (α₂ → β₂)` induced by `α₁ ≃ α₂` and `β₁ ≃ᵐ β₂` is
measure preserving. -/
/-
**MeasureTheory.measurePreserving_arrowCongr'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measurePreserving_arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype 
α₂] [MeasurableSpace β₁] [MeasurableSpace β₂] (μ : α₁ -> Measure β₁) (ν : α₂ -> 
Measure β₂) [forall i, SigmaFinite (ν i)] (eα : α₁ ≃ α₂) (eβ : β₁ ≃ᵐ β₂) (hm : f
orall i, MeasurePreserving eβ (μ i) (ν (eα i))) : MeasurePreserving (MeasurableE
quiv.arrowCongr' eα eβ) (Measure.pi fun i => μ i) (Measure.pi fun i => ν i)
参数：μ : α₁ -> Measure β₁；ν : α₂ -> Measure β₂；ν i；eα : α₁ ≃ α₂；eβ : β₁ ≃ᵐ β₂；hm :
 forall i, MeasurePreserving eβ (μ i) (ν (eα i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `MeasurableEquiv.mk.congr_simp`：∀ {α : Type u_6} {β : Type u_7} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] (toEquiv toEquiv_1 : α ≃ β)   (e_
toEquiv : toEquiv =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_piCongrLeft`：measurePreserving_piCongrLe
ft (f : ι' ≃ ι) : MeasurePreserving (MeasurableEquiv.piCongrLeft α f) (Measure.p
i fun i' => μ (f i')) (Measure.pi…
· 使用定理 `MeasureTheory.measurePreserving_pi`：measurePreserving_pi {ι : Type*} [Fi
ntype ι] {α : ι -> Type v} {β : ι -> Type*} [forall i, MeasurableSpace (α i)] [f
orall i, MeasurableSpace…

--- 原说明 ---
The measurable equiv `(α₁ → β₁) ≃ᵐ (α₂ → β₂)` induced by `α₁ ≃ α₂` and `β₁ ≃ᵐ β₂
` is
measure preserving.
-/
theorem measurePreserving_arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂]
    [MeasurableSpace β₁] [MeasurableSpace β₂] (μ : α₁ → Measure β₁) (ν : α₂ → Measure β₂)
    [∀ i, SigmaFinite (ν i)] (eα : α₁ ≃ α₂) (eβ : β₁ ≃ᵐ β₂)
    (hm : ∀ i, MeasurePreserving eβ (μ i) (ν (eα i))) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' eα eβ) (Measure.pi fun i ↦ μ i)
      (Measure.pi fun i ↦ ν i) := by
  convert!
    (measurePreserving_piCongrLeft (fun i : α₂ ↦ ν i) eα).comp
      (measurePreserving_pi μ (fun i : α₁ ↦ ν (eα i)) hm)
  simp only [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr, EquivLike.coe_coe,
    comp_def, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.symm_symm, Equiv.piCongrLeft', eq_rec_constant, Equiv.coe_fn_symm_mk]

/-- The measurable equiv `(α₁ → β₁) ≃ᵐ (α₂ → β₂)` induced by `α₁ ≃ α₂` and `β₁ ≃ᵐ β₂` is
volume preserving. -/
/-
**MeasureTheory.volume_preserving_arrowCongr'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：volume_preserving_arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype 
α₂] [MeasureSpace β₁] [MeasureSpace β₂] [SigmaFinite (volume : Measure β₂)] (hα 
: α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂) (hm : MeasurePreserving hβ) : MeasurePreserving (Meas
urableEquiv.arrowCongr' hα hβ)
参数：volume : Measure β₂；hα : α₁ ≃ α₂；hβ : β₁ ≃ᵐ β₂；hm : MeasurePreserving hβ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_arrowCongr'`：measurePreserving_arrowCong
r' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂] [MeasurableSpace β₁] [Measura
bleSpace β₂] (μ : α₁ -> Measure β…

--- 原说明 ---
The measurable equiv `(α₁ → β₁) ≃ᵐ (α₂ → β₂)` induced by `α₁ ≃ α₂` and `β₁ ≃ᵐ β₂
` is
volume preserving.
-/
theorem volume_preserving_arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂]
    [MeasureSpace β₁] [MeasureSpace β₂] [SigmaFinite (volume : Measure β₂)]
    (hα : α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂) (hm : MeasurePreserving hβ) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' hα hβ) :=
  measurePreserving_arrowCongr' (fun _ ↦ volume) (fun _ ↦ volume) hα hβ (fun _ ↦ hm)

end MeasurePreserving

end MeasureTheory

