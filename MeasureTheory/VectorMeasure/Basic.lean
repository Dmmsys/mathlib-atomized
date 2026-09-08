/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!

# Vector-valued measures

This file defines vector-valued measures, which are σ-additive functions from a set to an
additive monoid `M` such that it maps the empty set and non-measurable sets to zero. In the case
that `M = ℝ`, we called the vector measure a signed measure and write `SignedMeasure α`.
Similarly, when `M = ℂ`, we call the measure a complex measure and write `ComplexMeasure α`
(defined in `MeasureTheory/Measure/Complex`).

## Main definitions

* `MeasureTheory.VectorMeasure` is a vector-valued, σ-additive function that maps the empty
  and non-measurable sets to zero.
* `MeasureTheory.VectorMeasure.map` is the pushforward of a vector measure along a function.
* `MeasureTheory.VectorMeasure.restrict` is the restriction of a vector measure on some set.

## Notation

* `v ≤[i] w` means that the vector measure `v` restricted on the set `i` is less than or equal
  to the vector measure `w` restricted on `i`, i.e. `v.restrict i ≤ w.restrict i`.

## Implementation notes

We require all non-measurable sets to be mapped to zero in order for the extensionality lemma
to only compare the underlying functions for measurable sets.

We use `HasSum` instead of `tsum` in the definition of vector measures in comparison to `Measure`
since this provides summability.

## Tags

vector measure, signed measure, complex measure
-/

@[expose] public section


noncomputable section

open NNReal ENNReal Filter

open scoped Topology Function -- required for scoped `on` notation
namespace MeasureTheory

variable {α β : Type*} {m : MeasurableSpace α}

/-- A vector measure on a measurable space `α` is a σ-additive `M`-valued function (for some `M`
an additive monoid) such that the empty set and non-measurable sets are mapped to zero. -/
/-
**MeasureTheory.VectorMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：(α : Type u_3) → [MeasurableSpace α] → (M : Type u_4) → [AddCommMonoid M] 
→ [TopologicalSpace M] → Type (max u_3 u_4)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vector measure on a measurable space `α` is a σ-additive `M`-valued function (
for some `M`
an additive monoid) such that the empty set and non-measurable sets are mapped t
o zero.
-/
structure VectorMeasure (α : Type*) [MeasurableSpace α] (M : Type*) [AddCommMonoid M]
    [TopologicalSpace M] where
  /-- The measure of sets -/
  measureOf' : Set α → M
  /-- The empty set has measure zero -/
  empty' : measureOf' ∅ = 0
  /-- Non-measurable sets have measure zero -/
  not_measurable' ⦃i : Set α⦄ : ¬MeasurableSet i → measureOf' i = 0
  /-- The measure is σ-additive -/
  m_iUnion' ⦃f : ℕ → Set α⦄ : (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
    HasSum (fun i => measureOf' (f i)) (measureOf' (⋃ i, f i))

/-- A `SignedMeasure` is an `ℝ`-vector measure. -/
/-
**MeasureTheory.SignedMeasure** 是 Mathlib 中的一个缩写定义，位于命名空间 `MeasureTheory`。
形式化陈述：SignedMeasure (α : Type*) [MeasurableSpace α]
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SignedMeasure` is an `ℝ`-vector measure.
-/
abbrev SignedMeasure (α : Type*) [MeasurableSpace α] :=
  VectorMeasure α ℝ

open Set

namespace VectorMeasure

section

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (VectorMeasure α M) (Set α) M where
  coe := VectorMeasure.measureOf'
  coe_injective v w h := by
    cases v; cases w; congr

@[simp]
/-
**MeasureTheory.VectorMeasure.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ve
ctorMeasure`。
形式化陈述：coe_mk (v : Set α -> M) (h₁) (h₂) (h₃) : (mk v h₁ h₂ h₃ : VectorMeasure α 
M) = v
参数：v : Set α -> M；h₁；h₂；h₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (v : Set α → M) (h₁) (h₂) (h₃) : (mk v h₁ h₂ h₃ : VectorMeasure α M) = v := rfl

initialize_simps_projections VectorMeasure (measureOf' → apply)

@[simp]
/-
**MeasureTheory.VectorMeasure.empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Vec
torMeasure`。
形式化陈述：empty (v : VectorMeasure α M) : v ∅ = 0
参数：v : VectorMeasure α M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.empty'`：∀ {α : Type u_3} [inst : MeasurableS
pace α] {M : Type u_4} [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M] 
  (self : MeasureTheory.…
-/
theorem empty (v : VectorMeasure α M) : v ∅ = 0 :=
  v.empty'

@[simp]
/-
**MeasureTheory.VectorMeasure.not_measurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：not_measurable (v : VectorMeasure α M) {i : Set α} (hi : ¬MeasurableSet i)
 : v i = 0
参数：v : VectorMeasure α M；hi : ¬MeasurableSet i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable'`：∀ {α : Type u_3} [inst : Me
asurableSpace α] {M : Type u_4} [inst_1 : AddCommMonoid M] [inst_2 : Topological
Space M]   (self : MeasureTheory.…
-/
theorem not_measurable (v : VectorMeasure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0 :=
  v.not_measurable' hi
/-
**MeasureTheory.VectorMeasure.m_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：m_iUnion (v : VectorMeasure α M) {f : Nat -> Set α} (hf₁ : forall i, Measu
rableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) : HasSum (fun i => v (f i)) (v 
(⋃ i, f i))
参数：v : VectorMeasure α M；hf₁ : forall i, MeasurableSet (f i)；hf₂ : Pairwise (Dis
joint on f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.m_iUnion'`：∀ {α : Type u_3} [inst : Measurab
leSpace α] {M : Type u_4} [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace 
M]   (self : MeasureTheory.…
-/
theorem m_iUnion (v : VectorMeasure α M) {f : ℕ → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) : HasSum (fun i => v (f i)) (v (⋃ i, f i)) :=
  v.m_iUnion' hf₁ hf₂

@[deprecated (since := "2026-06-10")] alias coe_injective := DFunLike.coe_injective

@[deprecated (since := "2026-06-10")] alias ext_iff' := DFunLike.ext_iff
/-
**MeasureTheory.VectorMeasure.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.V
ectorMeasure`。
形式化陈述：ext_iff (v w : VectorMeasure α M) : v = w ↔ forall i : Set α, MeasurableSe
t i -> v i = w i
参数：v w : VectorMeasure α M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ext_iff (v w : VectorMeasure α M) : v = w ↔ ∀ i : Set α, MeasurableSet i → v i = w i := by
  constructor
  · rintro rfl _ _
    rfl
  · rw [DFunLike.ext_iff]
    intro h i
    by_cases hi : MeasurableSet i
    · exact h i hi
    · simp_rw [not_measurable _ hi]

@[ext]
/-
**MeasureTheory.VectorMeasure.ext** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Vecto
rMeasure`。
形式化陈述：ext {s t : VectorMeasure α M} (h : forall i : Set α, MeasurableSet i -> s 
i = t i) : s = t
参数：h : forall i : Set α, MeasurableSet i -> s i = t i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.VectorMeasure.ext_iff`：ext_iff (v w : VectorMeasure α M) :
 v = w ↔ forall i : Set α, MeasurableSet i -> v i = w i
-/
theorem ext {s t : VectorMeasure α M} (h : ∀ i : Set α, MeasurableSet i → s i = t i) : s = t :=
  (ext_iff s t).2 h

variable [Countable β] {v : VectorMeasure α M} {f : β → Set α}
/-
**MeasureTheory.VectorMeasure.hasSum_of_disjoint_iUnion** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.VectorMeasure`。
形式化陈述：hasSum_of_disjoint_iUnion (hm : forall i, MeasurableSet (f i)) (hd : Pairw
ise (Disjoint on f)) : HasSum (fun i => v (f i)) (v (⋃ i, f i))
参数：hm : forall i, MeasurableSet (f i)；hd : Pairwise (Disjoint on f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Countable.exists_injective_nat`：Countable.exists_injective_nat (α : Sort
 u) [Countable α] : exists f : α -> Nat, Injective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasSum_extend_zero`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {g : β →
 γ}, Fun…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Function.apply_extend`：apply_extend {δ} {g : α -> γ} (F : γ -> δ) (f : α
 -> β) (e' : β -> γ) (b : β) : F (extend f g e' b) = extend f (F ∘ g) (F ∘ e') b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iSup_extend_bot`：iSup_extend_bot {e : ι -> β} (he : Injective e) (f : ι 
-> α) : ⨆ j, extend e f ⊥ j = ⨆ i, f i
· 使用定理 `MeasureTheory.VectorMeasure.m_iUnion`：m_iUnion (v : VectorMeasure α M) {
f : Nat -> Set α} (hf₁ : forall i, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoin
t on f)) : HasSum (fun i =…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Function.extend_const`：extend_const (f : α -> β) (c : γ) : extend f (fun
 _ => c) (fun _ => c) = fun _ => c
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Pairwise.disjoint_extend_bot`：Pairwise.disjoint_extend_bot [PartialOrder
 γ] [OrderBot γ] {e : α -> β} {f : α -> γ} (hf : Pairwise (Disjoint on f)) (he :
 FactorsThrough f …
· 使用定理 `Function.Injective.factorsThrough`：∀ {α : Sort u_1} {β : Sort u_2} {γ : 
Sort u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ), Function.FactorsT
hrough g f
-/
theorem hasSum_of_disjoint_iUnion (hm : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    HasSum (fun i => v (f i)) (v (⋃ i, f i)) := by
  rcases Countable.exists_injective_nat β with ⟨e, he⟩
  rw [← hasSum_extend_zero he]
  convert! m_iUnion v (f := Function.extend e f fun _ ↦ ∅) _ _
  · simp only [Pi.zero_def, Function.apply_extend v, Function.comp_def, empty]
  · exact (iSup_extend_bot he _).symm
  · simp [Function.apply_extend MeasurableSet, Function.comp_def, hm]
  · exact hd.disjoint_extend_bot (he.factorsThrough _)
/-
**MeasureTheory.VectorMeasure.of_if** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Vec
torMeasure`。
形式化陈述：of_if {ι : Type*} {x : ι} {B : Set ι} {A : Set α} [Decidable (x in B)] : v
 (if x in B then A else ∅) = indicator B (fun _ => v A) x
参数：x in B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem of_if {ι : Type*} {x : ι} {B : Set ι} {A : Set α} [Decidable (x ∈ B)] :
    v (if x ∈ B then A else ∅) = indicator B (fun _ => v A) x := by
  split_ifs with h <;> simp [h]

variable [T2Space M]
/-
**MeasureTheory.VectorMeasure.of_disjoint_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：of_disjoint_iUnion (hm : forall i, MeasurableSet (f i)) (hd : Pairwise (Di
sjoint on f)) : v (⋃ i, f i) = ∑' i, v (f i)
参数：hm : forall i, MeasurableSet (f i)；hd : Pairwise (Disjoint on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `MeasureTheory.VectorMeasure.hasSum_of_disjoint_iUnion`：hasSum_of_disjoin
t_iUnion (hm : forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : 
HasSum (fun i => v (f i)) (v (⋃ i, f i))
-/
theorem of_disjoint_iUnion (hm : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    v (⋃ i, f i) = ∑' i, v (f i) :=
  (hasSum_of_disjoint_iUnion hm hd).tsum_eq.symm
/-
**MeasureTheory.VectorMeasure.of_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.VectorMeasure`。
形式化陈述：of_biUnion {ι : Type*} {s : Set ι} {f : ι -> Set α} (hs : s.Countable) (hd
 : s.Pairwise (Disjoint on f)) (h : forall b in s, MeasurableSet (f b)) : v (⋃ b
 in s, f b) = ∑' p : s, v (f p)
参数：hs : s.Countable；hd : s.Pairwise (Disjoint on f)；h : forall b in s, Measurabl
eSet (f b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.Pairwise.on_injective`：∀ {α : Type u_1} {ι : Type u_3} {r : α → α → 
Prop} {f : ι → α} {s : Set α},   s.Pairwise r → Function.Injective f → (∀ (x : ι
), f x ∈ s) → P…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem of_biUnion {ι : Type*} {s : Set ι} {f : ι → Set α} (hs : s.Countable)
    (hd : s.Pairwise (Disjoint on f)) (h : ∀ b ∈ s, MeasurableSet (f b)) :
    v (⋃ b ∈ s, f b) = ∑' p : s, v (f p) := by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]
  apply of_disjoint_iUnion
  · exact fun x ↦ h x x.2
  · exact hd.on_injective Subtype.coe_injective fun x => x.2
/-
**MeasureTheory.VectorMeasure.of_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：of_biUnion_finset {ι : Type*} {s : Finset ι} {f : ι -> Set α} (hd : Pairwi
seDisjoint (↑s) f) (hm : forall b in s, MeasurableSet (f b)) : v (⋃ b in s, f b)
 = ∑ p in s, v (f p)
参数：hd : PairwiseDisjoint (↑s) f；hm : forall b in s, MeasurableSet (f b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Finset.attach_eq_univ`：Finset.attach_eq_univ {s : Finset α} : s.attach =
 Finset.univ
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `MeasureTheory.VectorMeasure.of_biUnion`：of_biUnion {ι : Type*} {s : Set 
ι} {f : ι -> Set α} (hs : s.Countable) (hd : s.Pairwise (Disjoint on f)) (h : fo
rall b in s, MeasurableSet (…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
-/
theorem of_biUnion_finset {ι : Type*} {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) : v (⋃ b ∈ s, f b) = ∑ p ∈ s, v (f p) := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype (L := .unconditional s)]
  exact of_biUnion s.countable_toSet hd hm
/-
**MeasureTheory.VectorMeasure.of_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：of_union {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : Mea
surableSet B) : v (A union B) = v A + v B
参数：h : Disjoint A B；hA : MeasurableSet A；hB : MeasurableSet B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pairwise_disjoint_on_bool`：pairwise_disjoint_on_bool [PartialOrder α] [O
rderBot α] {a b : α} : Pairwise (Disjoint on fun c => cond c a b) ↔ Disjoint a b
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Fintype.sum_bool`：∀ {α : Type u_1} [inst : AddCommMonoid α] (f : Bool → 
α), ∑ b, f b = f true + f false
· 使用定理 `cond.eq_1`：∀ {α : Sort u} (x y : α), (bif true then x else y) = x
· 使用定理 `cond.eq_2`：∀ {α : Sort u} (x y : α), (bif false then x else y) = y
-/
theorem of_union {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    v (A ∪ B) = v A + v B := by
  rw [Set.union_eq_iUnion, of_disjoint_iUnion, tsum_fintype, Fintype.sum_bool, cond, cond]
  exacts [fun b => Bool.casesOn b hB hA, pairwise_disjoint_on_bool.2 h]
/-
**MeasureTheory.VectorMeasure.of_add_of_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.VectorMeasure`。
形式化陈述：of_add_of_sdiff {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B
) (h : A subseteq B) : v A + v (B \ A) = v B
参数：hA : MeasurableSet A；hB : MeasurableSet B；h : A subseteq B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
-/
theorem of_add_of_sdiff {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A ⊆ B) :
    v A + v (B \ A) = v B := by
  rw [← of_union (@Set.disjoint_sdiff_right _ A B) hA (hB.diff hA), Set.union_sdiff_cancel h]

@[deprecated (since := "2026-06-03")] alias of_add_of_diff := of_add_of_sdiff
/-
**MeasureTheory.VectorMeasure.of_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：of_sdiff {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M] {v 
: VectorMeasure α M} {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
 (h : A subseteq B) : v (B \ A) = v B - v A
参数：hA : MeasurableSet A；hB : MeasurableSet B；h : A subseteq B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.of_add_of_sdiff`：of_add_of_sdiff {A B : Set 
α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A subseteq B) : v A + v (B
 \ A) = v B
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
theorem of_sdiff {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    {v : VectorMeasure α M} {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : A ⊆ B) : v (B \ A) = v B - v A := by
  rw [← of_add_of_sdiff hA hB h, add_sub_cancel_left]

@[deprecated (since := "2026-06-03")] alias of_diff := of_sdiff
/-
**MeasureTheory.VectorMeasure.of_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：of_compl {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M] {v 
: VectorMeasure α M} {A : Set α} (hA : MeasurableSet A) : v Aᶜ = v univ - v A
参数：hA : MeasurableSet A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `MeasureTheory.VectorMeasure.of_sdiff`：of_sdiff {M : Type*} [AddCommGroup
 M] [TopologicalSpace M] [T2Space M] {v : VectorMeasure α M} {A B : Set α} (hA :
 MeasurableSet A) (hB : Me…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem of_compl {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    {v : VectorMeasure α M} {A : Set α} (hA : MeasurableSet A) :
    v Aᶜ = v univ - v A := by
  simpa [compl_eq_univ_sdiff] using of_sdiff hA .univ (v := v) (subset_univ _)
/-
**MeasureTheory.VectorMeasure.of_sdiff_of_sdiff_eq_zero** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.VectorMeasure`。
形式化陈述：of_sdiff_of_sdiff_eq_zero {A B : Set α} (hA : MeasurableSet A) (hB : Measu
rableSet B) (h' : v (B \ A) = 0) : v (A \ B) + v B = v A
参数：hA : MeasurableSet A；hB : MeasurableSet B；h' : v (B \ A) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem of_sdiff_of_sdiff_eq_zero {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h' : v (B \ A) = 0) : v (A \ B) + v B = v A := by
  symm
  calc
    v A = v (A \ B ∪ A ∩ B) := by simp only [Set.sdiff_union_inter]
    _ = v (A \ B) + v (A ∩ B) := by
      rw [of_union]
      · rw [disjoint_comm]
        exact Set.disjoint_of_subset_left A.inter_subset_right disjoint_sdiff_self_right
      · exact hA.diff hB
      · exact hA.inter hB
    _ = v (A \ B) + v (A ∩ B ∪ B \ A) := by
      rw [of_union, h', add_zero]
      · exact Set.disjoint_of_subset_left A.inter_subset_left disjoint_sdiff_self_right
      · exact hA.inter hB
      · exact hB.diff hA
    _ = v (A \ B) + v B := by rw [Set.union_comm, Set.inter_comm, Set.sdiff_union_inter]

@[deprecated (since := "2026-06-03")] alias of_diff_of_diff_eq_zero := of_sdiff_of_sdiff_eq_zero
/-
**MeasureTheory.VectorMeasure.of_iUnion_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：of_iUnion_nonneg {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Parti
alOrder M] [IsOrderedAddMonoid M] [OrderClosedTopology M] {v : VectorMeasure α M
} (hf₁ : forall i, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) (hf₃ : 
forall i, 0 <= v (f i)) : 0 <= v (⋃ i, f i)
参数：hf₁ : forall i, MeasurableSet (f i)；hf₂ : Pairwise (Disjoint on f)；hf₃ : fora
ll i, 0 <= v (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
-/
theorem of_iUnion_nonneg {M : Type*} [TopologicalSpace M]
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [OrderClosedTopology M] {v : VectorMeasure α M} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) (hf₃ : ∀ i, 0 ≤ v (f i)) : 0 ≤ v (⋃ i, f i) :=
  (v.of_disjoint_iUnion hf₁ hf₂).symm ▸ tsum_nonneg hf₃
/-
**MeasureTheory.VectorMeasure.of_iUnion_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：of_iUnion_nonpos {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Parti
alOrder M] [IsOrderedAddMonoid M] [OrderClosedTopology M] {v : VectorMeasure α M
} (hf₁ : forall i, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) (hf₃ : 
forall i, v (f i) <= 0) : v (⋃ i, f i) <= 0
参数：hf₁ : forall i, MeasurableSet (f i)；hf₂ : Pairwise (Disjoint on f)；hf₃ : fora
ll i, v (f i) <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_nonpos`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
-/
theorem of_iUnion_nonpos {M : Type*} [TopologicalSpace M]
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [OrderClosedTopology M] {v : VectorMeasure α M} (hf₁ : ∀ i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) (hf₃ : ∀ i, v (f i) ≤ 0) : v (⋃ i, f i) ≤ 0 :=
  (v.of_disjoint_iUnion hf₁ hf₂).symm ▸ tsum_nonpos hf₃
/-
**MeasureTheory.VectorMeasure.of_nonneg_disjoint_union_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：of_nonneg_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : 
Disjoint A B) (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : 0 <= s A) (
hB₂ : 0 <= s B) (hAB : s (A union B) = 0) : s A = 0
参数：h : Disjoint A B；hA₁ : MeasurableSet A；hB₁ : MeasurableSet B；hA₂ : 0 <= s A；h
B₂ : 0 <= s B；hAB : s (A union B) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_le_of_neg`：add_lt_of_le_of_neg [IsStri
ctOrderedRing α] {a b c : α} (hbc : b <= c) (ha : a < 0) : b + a < c
· 使用定理 `Mathlib.Tactic.Linarith.sub_nonpos_of_le`：sub_nonpos_of_le [IsOrderedRin
g α] {a b : α} : a <= b -> a - b <= 0
· 使用定理 `Mathlib.Tactic.Linarith.sub_neg_of_lt`：sub_neg_of_lt [IsOrderedRing α] {
a b : α} : a < b -> a - b < 0
（共 36 条，此处仅展示前 30 条）
-/
theorem of_nonneg_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
    (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : 0 ≤ s A) (hB₂ : 0 ≤ s B)
    (hAB : s (A ∪ B) = 0) : s A = 0 := by
  rw [of_union h hA₁ hB₁] at hAB
  linarith
/-
**MeasureTheory.VectorMeasure.of_nonpos_disjoint_union_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：of_nonpos_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : 
Disjoint A B) (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : s A <= 0) (
hB₂ : s B <= 0) (hAB : s (A union B) = 0) : s A = 0
参数：h : Disjoint A B；hA₁ : MeasurableSet A；hB₁ : MeasurableSet B；hA₂ : s A <= 0；h
B₂ : s B <= 0；hAB : s (A union B) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_le_of_neg`：add_lt_of_le_of_neg [IsStri
ctOrderedRing α] {a b c : α} (hbc : b <= c) (ha : a < 0) : b + a < c
（共 39 条，此处仅展示前 30 条）
-/
theorem of_nonpos_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
    (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : s A ≤ 0) (hB₂ : s B ≤ 0)
    (hAB : s (A ∪ B) = 0) : s A = 0 := by
  rw [of_union h hA₁ hB₁] at hAB
  linarith
/-
**MeasureTheory.VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：tendsto_vectorMeasure_iUnion_atTop_nat {s : Nat -> Set α} (hm : Monotone s
) (hs : forall i, MeasurableSet (s i)) : Tendsto (fun n => v (s n)) atTop (𝓝 (v 
(⋃ n, s n)))
参数：hm : Monotone s；hs : forall i, MeasurableSet (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用定理 `MeasureTheory.VectorMeasure.m_iUnion`：m_iUnion (v : VectorMeasure α M) {
f : Nat -> Set α} (hf₁ : forall i, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoin
t on f)) : HasSum (fun i =…
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.VectorMeasure.of_biUnion_finset`：of_biUnion_finset {ι : Ty
pe*} {s : Finset ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f) (hm : forall
 b in s, MeasurableSet (f b)) : v (…
· 使用引理 `biUnion_range_succ_disjointed`：biUnion_range_succ_disjointed {α : Type*}
 (f : Nat -> Set α) (n : Nat) : (⋃ i in Finset.range (n + 1), disjointed f i) = 
partialSups f n
· 使用定理 `Monotone.partialSups_eq`：Monotone.partialSups_eq {f : ι -> α} (hf : Mono
tone f) : partialSups f = f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `Filter.tendsto_add_atTop_nat`：tendsto_add_atTop_nat (k : Nat) : Tendsto 
(fun a => a + k) atTop atTop
-/
theorem tendsto_vectorMeasure_iUnion_atTop_nat
    {s : ℕ → Set α} (hm : Monotone s) (hs : ∀ i, MeasurableSet (s i)) :
    Tendsto (fun n ↦ v (s n)) atTop (𝓝 (v (⋃ n, s n))) := by
  set t : ℕ → Set α := disjointed s
  have ht n : MeasurableSet (t n) := .disjointed (fun n ↦ hs n) n
  have : HasSum (fun n ↦ v (t n)) (v (⋃ n, s n)) := by
    rw [← iUnion_disjointed]
    apply m_iUnion _ ht (disjoint_disjointed _)
  convert! (HasSum.tendsto_sum_nat this).comp (tendsto_add_atTop_nat 1) with n
  dsimp
  rw [← of_biUnion_finset]
  · rw [biUnion_range_succ_disjointed, Monotone.partialSups_eq hm]
  · exact fun i hi j hj hij ↦ disjoint_disjointed _ hij
  · exact fun b hb ↦ ht _
/-
**MeasureTheory.VectorMeasure.tendsto_vectorMeasure_iInter_atTop_nat** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：tendsto_vectorMeasure_iInter_atTop_nat {M : Type*} [AddCommGroup M] [Topol
ogicalSpace M] [T2Space M] [ContinuousSub M] {v : VectorMeasure α M} {s : Nat ->
 Set α} (hm : Antitone s) (hs : forall i, MeasurableSet (s i)) : Tendsto (fun n 
=> v (s n)) atTop (𝓝 (v (⋂ n, s n)))
参数：hm : Antitone s；hs : forall i, MeasurableSet (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.of_compl`：of_compl {M : Type*} [AddCommGroup
 M] [TopologicalSpace M] [T2Space M] {v : VectorMeasure α M} {A : Set α} (hA : M
easurableSet A) : v Aᶜ = v…
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `MeasureTheory.VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat`：tend
sto_vectorMeasure_iUnion_atTop_nat {s : Nat -> Set α} (hm : Monotone s) (hs : fo
rall i, MeasurableSet (s i)) : Tendsto (fun n => v (s n)…
-/
theorem tendsto_vectorMeasure_iInter_atTop_nat
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M] [ContinuousSub M]
    {v : VectorMeasure α M} {s : ℕ → Set α} (hm : Antitone s) (hs : ∀ i, MeasurableSet (s i)) :
    Tendsto (fun n ↦ v (s n)) atTop (𝓝 (v (⋂ n, s n))) := by
  have I n : v (s n) = v univ - v (s n)ᶜ := by simp [of_compl (hs n)]
  have J : v (⋂ n, s n) = v univ - v (⋃ n, (s n)ᶜ) := by
    rw [← of_compl (MeasurableSet.iUnion (fun n ↦ (hs n).compl))]
    simp
  simp_rw [I, J]
  apply tendsto_const_nhds.sub
  exact tendsto_vectorMeasure_iUnion_atTop_nat (fun i j hij ↦ by simpa using hm hij)
    (fun i ↦ (hs i).compl)

/-- If two vector measures give the same mass to the whole space and coincide on a
generating π-system, then they coincide. -/
/-
**MeasureTheory.VectorMeasure.ext_of_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.VectorMeasure`。
形式化陈述：ext_of_generateFrom {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2S
pace M] {X : Type*} {mX : MeasurableSpace X} {μ ν : VectorMeasure X M} (C : Set 
(Set X)) (hμν : forall s in C, μ s = ν s) (hA : mX = MeasurableSpace.generateFro
m C) (hC : IsPiSystem C) (h_univ : μ Set.univ = ν Set.univ) : μ = ν
参数：C : Set (Set X)；hμν : forall s in C, μ s = ν s；hA : mX = MeasurableSpace.gene
rateFrom C；hC : IsPiSystem C；h_univ : μ Set.univ = ν Set.univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.of_compl`：of_compl {M : Type*} [AddCommGroup
 M] [TopologicalSpace M] [T2Space M] {v : VectorMeasure α M} {A : Set α} (hA : M
easurableSet A) : v Aᶜ = v…
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
If two vector measures give the same mass to the whole space and coincide on a
generating π-system, then they coincide.
-/
theorem ext_of_generateFrom {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    {X : Type*} {mX : MeasurableSpace X} {μ ν : VectorMeasure X M}
    (C : Set (Set X)) (hμν : ∀ s ∈ C, μ s = ν s)
    (hA : mX = MeasurableSpace.generateFrom C) (hC : IsPiSystem C)
    (h_univ : μ Set.univ = ν Set.univ) : μ = ν := by
  ext s hs
  induction s, hs using MeasurableSpace.induction_on_inter hA hC with
  | empty => simp
  | basic t ht => exact hμν t ht
  | compl t htm iht =>
    simp [of_compl, iht, htm, h_univ]
  | iUnion f hfd hfm ihf =>
    simp [of_disjoint_iUnion, hfm, hfd, ihf]

end

section SMul

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

/-- Given a scalar `r` and a vector measure `v`, `smul r v` is the vector measure corresponding to
the set function `s : Set α => r • (v s)`. -/
@[instance_reducible]
/-
**MeasureTheory.VectorMeasure.smul** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vect
orMeasure`。
形式化陈述：smul (r : R) (v : VectorMeasure α M) : VectorMeasure α M where measureOf'
参数：r : R；v : VectorMeasure α M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a scalar `r` and a vector measure `v`, `smul r v` is the vector measure co
rresponding to
the set function `s : Set α => r • (v s)`.
-/
def smul (r : R) (v : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := r • ⇑v
  empty' := by rw [Pi.smul_apply, empty, smul_zero]
  not_measurable' _ hi := by rw [Pi.smul_apply, v.not_measurable hi, smul_zero]
  m_iUnion' _ hf₁ hf₂ := by exact HasSum.const_smul _ (v.m_iUnion hf₁ hf₂)
/-
**MeasureTheory.VectorMeasure.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：instSMul : SMul R (VectorMeasure α M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul R (VectorMeasure α M) :=
  ⟨smul⟩
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply R (VectorMeasure α M) (Set α) M where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

end SMul

section AddCommMonoid

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

/-
**MeasureTheory.VectorMeasure.instZero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：instZero : Zero (VectorMeasure α M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (VectorMeasure α M) :=
  ⟨⟨0, rfl, fun _ _ => rfl, fun _ _ _ => hasSum_zero⟩⟩
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (VectorMeasure α M) (Set α) M where
  zero_apply _ := rfl
/-
**MeasureTheory.VectorMeasure.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：instInhabited : Inhabited (VectorMeasure α M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (VectorMeasure α M) :=
  ⟨0⟩

@[nontriviality]
/-
**MeasureTheory.VectorMeasure.apply_eq_zero_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：apply_eq_zero_of_isEmpty [IsEmpty α] (μ : VectorMeasure α M) (s : Set α) :
 μ s = 0
参数：μ : VectorMeasure α M；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma apply_eq_zero_of_isEmpty [IsEmpty α] (μ : VectorMeasure α M) (s : Set α) :
    μ s = 0 := by
  simp [eq_empty_of_isEmpty s]
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Subsingleton (VectorMeasure α M) :=
  ⟨fun μ ν => by ext; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩
/-
**MeasureTheory.VectorMeasure.eq_zero_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：eq_zero_of_isEmpty [IsEmpty α] (μ : VectorMeasure α M) : μ = 0
参数：μ : VectorMeasure α M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `MeasureTheory.VectorMeasure.instSubsingletonOfIsEmpty`：∀ {α : Type u_1} 
{m : MeasurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : Topolo
gicalSpace M]   [IsEmpty α], Subsingleton (…
-/
theorem eq_zero_of_isEmpty [IsEmpty α] (μ : VectorMeasure α M) : μ = 0 :=
  Subsingleton.elim μ 0

@[deprecated (since := "2026-06-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

variable [ContinuousAdd M]

/-- The sum of two vector measure is a vector measure. -/
/-
**MeasureTheory.VectorMeasure.add** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vecto
rMeasure`。
形式化陈述：add (v w : VectorMeasure α M) : VectorMeasure α M where measureOf'
参数：v w : VectorMeasure α M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two vector measure is a vector measure.
-/
def add (v w : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := v + w
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.add_apply, v.not_measurable hi, w.not_measurable hi, add_zero]
  m_iUnion' _ hf₁ hf₂ := HasSum.add (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)
/-
**MeasureTheory.VectorMeasure.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.V
ectorMeasure`。
形式化陈述：instAdd : Add (VectorMeasure α M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (VectorMeasure α M) :=
  ⟨add⟩
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (VectorMeasure α M) (Set α) M where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply
/-
**MeasureTheory.VectorMeasure.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：instAddCommMonoid : AddCommMonoid (VectorMeasure α M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid : AddCommMonoid (VectorMeasure α M) :=
  fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-06-10")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-10")] alias coe_finsetSum := FunLike.coe_sum

end AddCommMonoid

section AddCommGroup

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The negative of a vector measure is a vector measure. -/
/-
**MeasureTheory.VectorMeasure.neg** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vecto
rMeasure`。
形式化陈述：neg (v : VectorMeasure α M) : VectorMeasure α M where measureOf'
参数：v : VectorMeasure α M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The negative of a vector measure is a vector measure.
-/
def neg (v : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := -v
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.neg_apply, neg_eq_zero, v.not_measurable hi]
  m_iUnion' _ hf₁ hf₂ := HasSum.neg <| v.m_iUnion hf₁ hf₂
/-
**MeasureTheory.VectorMeasure.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.V
ectorMeasure`。
形式化陈述：instNeg : Neg (VectorMeasure α M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg (VectorMeasure α M) :=
  ⟨neg⟩
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply (VectorMeasure α M) (Set α) M where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

/-- The difference of two vector measure is a vector measure. -/
/-
**MeasureTheory.VectorMeasure.sub** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vecto
rMeasure`。
形式化陈述：sub (v w : VectorMeasure α M) : VectorMeasure α M where measureOf'
参数：v w : VectorMeasure α M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The difference of two vector measure is a vector measure.
-/
def sub (v w : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := v - w
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.sub_apply, v.not_measurable hi, w.not_measurable hi, sub_zero]
  m_iUnion' _ hf₁ hf₂ := HasSum.sub (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)
/-
**MeasureTheory.VectorMeasure.instSub** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.V
ectorMeasure`。
形式化陈述：instSub : Sub (VectorMeasure α M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub (VectorMeasure α M) :=
  ⟨sub⟩
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply (VectorMeasure α M) (Set α) M where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply
/-
**MeasureTheory.VectorMeasure.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：instAddCommGroup : AddCommGroup (VectorMeasure α M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup : AddCommGroup (VectorMeasure α M) := fast_instance% FunLike.addCommGroup

end AddCommGroup

section DistribMulAction

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

/-
**MeasureTheory.VectorMeasure.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Me
asureTheory.VectorMeasure`。
形式化陈述：instDistribMulAction [ContinuousAdd M] : DistribMulAction R (VectorMeasure
 α M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [ContinuousAdd M] : DistribMulAction R (VectorMeasure α M) :=
  fast_instance% FunLike.distribMulAction

end DistribMulAction

section Module

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [Module R M] [ContinuousConstSMul R M]

/-
**MeasureTheory.VectorMeasure.instModule** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.VectorMeasure`。
形式化陈述：instModule [ContinuousAdd M] : Module R (VectorMeasure α M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [ContinuousAdd M] : Module R (VectorMeasure α M) :=
  fast_instance% FunLike.module

end Module

section Dirac

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [MeasurableSpace β]
  {x : β} {v : M} {s : Set β}

open scoped Classical in
/-- The Dirac vector measure with mass `v` at a point `x`. It gives mass `v` to measurable sets
containing `x`, and `0` otherwise. -/
/-
**MeasureTheory.VectorMeasure.dirac** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vec
torMeasure`。
形式化陈述：dirac (x : β) (v : M) : VectorMeasure β M where measureOf' s
参数：x : β；v : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Dirac vector measure with mass `v` at a point `x`. It gives mass `v` to meas
urable sets
containing `x`, and `0` otherwise.
-/
def dirac (x : β) (v : M) : VectorMeasure β M where
  measureOf' s := if MeasurableSet s ∧ x ∈ s then v else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    by_cases hx : x ∈ ⋃ i, f i; swap
    · simp only [mem_iUnion, not_exists] at hx
      simp [hx, hasSum_zero]
    have : MeasurableSet (⋃ i, f i) := by
      apply MeasurableSet.iUnion f_meas
    simp only [f_meas, true_and, MeasurableSet.iUnion f_meas, hx, and_self, ↓reduceIte]
    obtain ⟨j, hj⟩ : ∃ j, x ∈ f j := by simpa using hx
    nth_rewrite 2 [show v = if x ∈ f j then v else 0 by simp [hj]]
    apply hasSum_single
    intro i hi
    have : Disjoint (f i) (f j) := f_disj hi
    grind
/-
**MeasureTheory.VectorMeasure.dirac_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：∀ {β : Type u_2} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : Topolog
icalSpace M] [inst_2 : MeasurableSpace β]   {x : β} {v : M} {s : Set β}, Measura
bleSet s → x ∈ s → (MeasureTheory.VectorMeasure.dirac x v) s = v
参数：MeasureTheory.VectorMeasure.dirac x v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
@[simp] lemma dirac_apply_of_mem (hs : MeasurableSet s) (hx : x ∈ s) : dirac x v s = v :=
  if_pos (And.intro hs hx)
/-
**MeasureTheory.VectorMeasure.dirac_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：∀ {β : Type u_2} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : Topolog
icalSpace M] [inst_2 : MeasurableSpace β]   {x : β} {v : M} {s : Set β}, x ∉ s →
 (MeasureTheory.VectorMeasure.dirac x v) s = 0
参数：MeasureTheory.VectorMeasure.dirac x v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dirac_apply_of_notMem (hx : x ∉ s) : dirac x v s = 0 := by
  simp [dirac, hx]
/-
**MeasureTheory.VectorMeasure.dirac_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.VectorMeasure`。
形式化陈述：∀ {β : Type u_2} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : Topolog
icalSpace M] [inst_2 : MeasurableSpace β]   {x : β}, MeasureTheory.VectorMeasure
.dirac x 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `MeasureTheory.VectorMeasure.mk.congr_simp`：∀ {α : Type u_3} [inst : Meas
urableSpace α] {M : Type u_4} [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSp
ace M]   (measureOf' measureOf'…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dirac_zero : dirac x (0 : M) = 0 := by
  ext s hs
  simp [dirac]

end Dirac

end VectorMeasure

namespace Measure

open scoped Classical in
/-- A finite measure coerced into a real function is a signed measure. -/
/-
**MeasureTheory.Measure.toSignedMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：toSignedMeasure (μ : Measure α) [hμ : IsFiniteMeasure μ] : SignedMeasure α
 where measureOf' s
参数：μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite measure coerced into a real function is a signed measure.
-/
def toSignedMeasure (μ : Measure α) [hμ : IsFiniteMeasure μ] : SignedMeasure α where
  measureOf' s := if MeasurableSet s then μ.real s else 0
  empty' := by simp
  not_measurable' _ hi := if_neg hi
  m_iUnion' f hf₁ hf₂ := by
    simp only [*, MeasurableSet.iUnion hf₁, if_true, measure_iUnion hf₂ hf₁, measureReal_def]
    rw [ENNReal.tsum_toReal_eq]
    exacts [(summable_measure_toReal hf₁ hf₂).hasSum, fun _ ↦ measure_ne_top _ _]

open scoped Classical in
@[simp]
/-
**MeasureTheory.Measure.toSignedMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：toSignedMeasure_apply (μ : Measure α) [hμ : IsFiniteMeasure μ] (i : Set α)
 : μ.toSignedMeasure i = if MeasurableSet i then μ.real i else 0
参数：μ : Measure α；i : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSignedMeasure_apply (μ : Measure α) [hμ : IsFiniteMeasure μ] (i : Set α) :
    μ.toSignedMeasure i = if MeasurableSet i then μ.real i else 0 := rfl
/-
**MeasureTheory.Measure.toSignedMeasure_apply_measurable** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：toSignedMeasure_apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : 
Set α} (hi : MeasurableSet i) : μ.toSignedMeasure i = μ.real i
参数：hi : MeasurableSet i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem toSignedMeasure_apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α}
    (hi : MeasurableSet i) : μ.toSignedMeasure i = μ.real i :=
  if_pos hi

-- Without this lemma, `singularPart_neg` in
-- `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` is extremely slow
/-
**MeasureTheory.Measure.toSignedMeasure_congr** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：toSignedMeasure_congr {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasu
re ν] (h : μ = ν) : μ.toSignedMeasure = ν.toSignedMeasure
参数：h : μ = ν。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSignedMeasure_congr {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ = ν) : μ.toSignedMeasure = ν.toSignedMeasure := by
  congr
/-
**MeasureTheory.Measure.toSignedMeasure_eq_toSignedMeasure_iff** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：toSignedMeasure_eq_toSignedMeasure_iff {μ ν : Measure α} [IsFiniteMeasure 
μ] [IsFiniteMeasure ν] : μ.toSignedMeasure = ν.toSignedMeasure ↔ μ = ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_eq_measureReal_iff`：measureReal_eq_measureReal
_iff {m : MeasurableSpace β} {ν : Measure β} {t : Set β} (h₁ : μ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_apply_measurable`：toSignedMeasure_
apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α} (hi : Measurabl
eSet i) : μ.toSignedMeasure i = μ.real i
-/
theorem toSignedMeasure_eq_toSignedMeasure_iff {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : μ.toSignedMeasure = ν.toSignedMeasure ↔ μ = ν := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext1 i hi
    have : μ.toSignedMeasure i = ν.toSignedMeasure i := by rw [h]
    rwa [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi,
        measureReal_eq_measureReal_iff] at this
  · congr

@[simp]
/-
**MeasureTheory.Measure.toSignedMeasure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：toSignedMeasure_zero : (0 : Measure α).toSignedMeasure = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSignedMeasure_zero : (0 : Measure α).toSignedMeasure = 0 := by
  ext i hi
  simp [hi]

@[simp]
/-
**MeasureTheory.Measure.toSignedMeasure_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：toSignedMeasure_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure
 ν] : (μ + ν).toSignedMeasure = μ.toSignedMeasure + ν.toSignedMeasure
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_apply_measurable`：toSignedMeasure_
apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α} (hi : Measurabl
eSet i) : μ.toSignedMeasure i = μ.real i
· 使用定理 `MeasureTheory.measureReal_add_apply`：measureReal_add_apply {μ₁ μ₂ : Meas
ure α} (h₁ : μ₁ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
-/
theorem toSignedMeasure_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ + ν).toSignedMeasure = μ.toSignedMeasure + ν.toSignedMeasure := by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi, measureReal_add_apply,
    _root_.add_apply, toSignedMeasure_apply_measurable hi,
    toSignedMeasure_apply_measurable hi]

@[simp]
/-
**MeasureTheory.Measure.toSignedMeasure_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：toSignedMeasure_smul (μ : Measure α) [IsFiniteMeasure μ] (r : Real>=0) : (
r • μ).toSignedMeasure = r • μ.toSignedMeasure
参数：μ : Measure α；r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_apply_measurable`：toSignedMeasure_
apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α} (hi : Measurabl
eSet i) : μ.toSignedMeasure i = μ.real i
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSMulApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M]   {R : Type u_4} [inst_2 : Se…
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.measureReal_nnreal_smul_apply`：∀ {α : Type u_1} {x : Measu
rableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} (c : NNReal),   (c • μ).
real s = ↑c * μ.real s
-/
theorem toSignedMeasure_smul (μ : Measure α) [IsFiniteMeasure μ] (r : ℝ≥0) :
    (r • μ).toSignedMeasure = r • μ.toSignedMeasure := by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi, _root_.smul_apply,
    toSignedMeasure_apply_measurable hi, measureReal_nnreal_smul_apply]
  rfl

open scoped Classical in
/-- A measure is a vector measure over `ℝ≥0∞`. -/
/-
**MeasureTheory.Measure.toENNRealVectorMeasure** 是 Mathlib 中的一个定义，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：toENNRealVectorMeasure (μ : Measure α) : VectorMeasure α Real>=0∞ where me
asureOf' i
参数：μ : Measure α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is a vector measure over `ℝ≥0∞`.
-/
def toENNRealVectorMeasure (μ : Measure α) : VectorMeasure α ℝ≥0∞ where
  measureOf' i := if MeasurableSet i then μ i else 0
  empty' := by simp
  not_measurable' _ hi := if_neg hi
  m_iUnion' _ hf₁ hf₂ := by
    rw [Summable.hasSum_iff ENNReal.summable, if_pos (MeasurableSet.iUnion hf₁),
      MeasureTheory.measure_iUnion hf₂ hf₁]
    exact tsum_congr fun n => if_pos (hf₁ n)

open scoped Classical in
@[simp]
/-
**MeasureTheory.Measure.toENNRealVectorMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：toENNRealVectorMeasure_apply (μ : Measure α) (i : Set α) : μ.toENNRealVect
orMeasure i = if MeasurableSet i then μ i else 0
参数：μ : Measure α；i : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toENNRealVectorMeasure_apply (μ : Measure α) (i : Set α) :
    μ.toENNRealVectorMeasure i = if MeasurableSet i then μ i else 0 := rfl
/-
**MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：toENNRealVectorMeasure_apply_measurable {μ : Measure α} {i : Set α} (hi : 
MeasurableSet i) : μ.toENNRealVectorMeasure i = μ i
参数：hi : MeasurableSet i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem toENNRealVectorMeasure_apply_measurable {μ : Measure α} {i : Set α} (hi : MeasurableSet i) :
    μ.toENNRealVectorMeasure i = μ i :=
  if_pos hi

@[simp]
/-
**MeasureTheory.Measure.toENNRealVectorMeasure_zero** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：toENNRealVectorMeasure_zero : (0 : Measure α).toENNRealVectorMeasure = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toENNRealVectorMeasure_zero : (0 : Measure α).toENNRealVectorMeasure = 0 := by
  ext i
  simp

@[simp]
/-
**MeasureTheory.Measure.toENNRealVectorMeasure_add** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：toENNRealVectorMeasure_add (μ ν : Measure α) : (μ + ν).toENNRealVectorMeas
ure = μ.toENNRealVectorMeasure + ν.toENNRealVectorMeasure
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable`：toENNReal
VectorMeasure_apply_measurable {μ : Measure α} {i : Set α} (hi : MeasurableSet i
) : μ.toENNRealVectorMeasure i = μ i
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
-/
theorem toENNRealVectorMeasure_add (μ ν : Measure α) :
    (μ + ν).toENNRealVectorMeasure = μ.toENNRealVectorMeasure + ν.toENNRealVectorMeasure := by
  refine MeasureTheory.VectorMeasure.ext fun i hi => ?_
  rw [toENNRealVectorMeasure_apply_measurable hi, add_apply, _root_.add_apply,
    toENNRealVectorMeasure_apply_measurable hi, toENNRealVectorMeasure_apply_measurable hi]
/-
**MeasureTheory.Measure.toSignedMeasure_sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：toSignedMeasure_sub_apply {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteM
easure ν] {i : Set α} (hi : MeasurableSet i) : (μ.toSignedMeasure - ν.toSignedMe
asure) i = μ.real i - ν.real i
参数：hi : MeasurableSet i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSubApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_apply_measurable`：toSignedMeasure_
apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α} (hi : Measurabl
eSet i) : μ.toSignedMeasure i = μ.real i
-/
theorem toSignedMeasure_sub_apply {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {i : Set α} (hi : MeasurableSet i) :
    (μ.toSignedMeasure - ν.toSignedMeasure) i = μ.real i - ν.real i := by
  rw [_root_.sub_apply, toSignedMeasure_apply_measurable hi,
    Measure.toSignedMeasure_apply_measurable hi]

end Measure

namespace VectorMeasure

open Measure

section

/-- A vector measure over `ℝ≥0∞` is a measure. -/
/-
**MeasureTheory.VectorMeasure.ennrealToMeasure** 是 Mathlib 中的一个定义，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：ennrealToMeasure {_ : MeasurableSpace α} (v : VectorMeasure α Real>=0∞) : 
Measure α
参数：v : VectorMeasure α Real>=0∞。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal

--- 原说明 ---
A vector measure over `ℝ≥0∞` is a measure.
-/
def ennrealToMeasure {_ : MeasurableSpace α} (v : VectorMeasure α ℝ≥0∞) : Measure α :=
  ofMeasurable (fun s _ => v s) v.empty fun _ hf₁ hf₂ => v.of_disjoint_iUnion hf₁ hf₂
/-
**MeasureTheory.VectorMeasure.ennrealToMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.VectorMeasure`。
形式化陈述：ennrealToMeasure_apply {m : MeasurableSpace α} {v : VectorMeasure α Real>=
0∞} {s : Set α} (hs : MeasurableSet s) : ennrealToMeasure v s = v s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure.eq_1`：∀ {α : Type u_1} {x :
 MeasurableSpace α} (v : MeasureTheory.VectorMeasure α ENNReal),   v.ennrealToMe
asure = MeasureTheory.Measure.ofMeasura…
· 使用定理 `MeasureTheory.Measure.ofMeasurable_apply`：ofMeasurable_apply {m : forall
 s : Set α, MeasurableSet s -> Real>=0∞} {m0 : m ∅ MeasurableSet.empty = 0} {mU 
: forall ⦃f : Nat -> Set α⦄ (h…
-/
theorem ennrealToMeasure_apply {m : MeasurableSpace α} {v : VectorMeasure α ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet s) : ennrealToMeasure v s = v s := by
  rw [ennrealToMeasure, ofMeasurable_apply _ hs]

@[simp]
/-
**MeasureTheory.VectorMeasure.ennrealToMeasure_zero** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：ennrealToMeasure_zero : ennrealToMeasure (0 : VectorMeasure α Real>=0∞) = 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasureTheory.Measure.ofMeasurable.congr_simp`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] (m m_1 : (s : Set α) → MeasurableSet s → ENNReal) (e_m : m = 
m_1)   (m0 : m ∅ ⋯ = 0)   (mU :    …
· 使用定理 `MeasureTheory.Measure.ofMeasurable_zero`：ofMeasurable_zero : ofMeasurabl
e (α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ennrealToMeasure_zero : ennrealToMeasure (0 : VectorMeasure α ℝ≥0∞) = 0 := by
  simp [ennrealToMeasure]

@[simp]
/-
**MeasureTheory.VectorMeasure._root_.MeasureTheory.Measure.toENNRealVectorMeasur
e_ennrealToMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Measure.toENNRealVectorMeasure_ennrealToMeasure
    (μ : VectorMeasure α ℝ≥0∞) :
    toENNRealVectorMeasure (ennrealToMeasure μ) = μ := ext fun s hs => by
  rw [toENNRealVectorMeasure_apply_measurable hs, ennrealToMeasure_apply hs]

@[simp]
/-
**MeasureTheory.VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：ennrealToMeasure_toENNRealVectorMeasure (μ : Measure α) : ennrealToMeasure
 (toENNRealVectorMeasure μ) = μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_apply`：ennrealToMeasure_app
ly {m : MeasurableSpace α} {v : VectorMeasure α Real>=0∞} {s : Set α} (hs : Meas
urableSet s) : ennrealToMeasure v s = v …
· 使用定理 `MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable`：toENNReal
VectorMeasure_apply_measurable {μ : Measure α} {i : Set α} (hi : MeasurableSet i
) : μ.toENNRealVectorMeasure i = μ i
-/
theorem ennrealToMeasure_toENNRealVectorMeasure (μ : Measure α) :
    ennrealToMeasure (toENNRealVectorMeasure μ) = μ := Measure.ext fun s hs => by
  rw [ennrealToMeasure_apply hs, toENNRealVectorMeasure_apply_measurable hs]

/-- The equiv between `VectorMeasure α ℝ≥0∞` and `Measure α` formed by
`MeasureTheory.VectorMeasure.ennrealToMeasure` and
`MeasureTheory.Measure.toENNRealVectorMeasure`. -/
@[simps]
/-
**MeasureTheory.VectorMeasure.equivMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：equivMeasure [MeasurableSpace α] : VectorMeasure α Real>=0∞ ≃ Measure α wh
ere toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.toENNRealVectorMeasure_ennrealToMeasure`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} (μ : MeasureTheory.VectorMeasure α ENNReal),   μ
.ennrealToMeasure.toENNRealVectorMeasure = μ
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure`：enn
realToMeasure_toENNRealVectorMeasure (μ : Measure α) : ennrealToMeasure (toENNRe
alVectorMeasure μ) = μ

--- 原说明 ---
The equiv between `VectorMeasure α ℝ≥0∞` and `Measure α` formed by
`MeasureTheory.VectorMeasure.ennrealToMeasure` and
`MeasureTheory.Measure.toENNRealVectorMeasure`.
-/
def equivMeasure [MeasurableSpace α] : VectorMeasure α ℝ≥0∞ ≃ Measure α where
  toFun := ennrealToMeasure
  invFun := toENNRealVectorMeasure
  left_inv := toENNRealVectorMeasure_ennrealToMeasure
  right_inv := ennrealToMeasure_toENNRealVectorMeasure

end

section

variable {mα : MeasurableSpace α} [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable (v : VectorMeasure α M)

open scoped Classical in
/-- The pushforward of a vector measure along a function. -/
/-
**MeasureTheory.VectorMeasure.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vecto
rMeasure`。
形式化陈述：map (v : VectorMeasure α M) (f : α -> β) : VectorMeasure β M
参数：v : VectorMeasure α M；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward of a vector measure along a function.
-/
def map (v : VectorMeasure α M) (f : α → β) : VectorMeasure β M :=
  if hf : Measurable f then
    { measureOf' := fun s => if MeasurableSet s then v (f ⁻¹' s) else 0
      empty' := by simp
      not_measurable' := fun _ hi => if_neg hi
      m_iUnion' := by
        intro g hg₁ hg₂
        convert! v.m_iUnion (fun i => hf (hg₁ i)) fun i j hij => (hg₂ hij).preimage _
        · rw [if_pos (hg₁ _)]
        · rw [Set.preimage_iUnion, if_pos (MeasurableSet.iUnion hg₁)] }
  else 0
/-
**MeasureTheory.VectorMeasure.map_not_measurable** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：map_not_measurable {f : α -> β} (hf : ¬Measurable f) : v.map f = 0
参数：hf : ¬Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem map_not_measurable {f : α → β} (hf : ¬Measurable f) : v.map f = 0 :=
  dif_neg hf
/-
**MeasureTheory.VectorMeasure.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.VectorMeasure`。
形式化陈述：map_apply {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet
 s) : v.map f s = v (f ⁻¹' s)
参数：hf : Measurable f；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.map.eq_1`：∀ {α : Type u_1} {β : Type u_2} {m
α : MeasurableSpace α} [inst : MeasurableSpace β] {M : Type u_3}   [inst_1 : Add
CommMonoid M] [inst_2 : To…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem map_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    v.map f s = v (f ⁻¹' s) := by
  rw [map, dif_pos hf]
  exact if_pos hs

@[simp]
/-
**MeasureTheory.VectorMeasure.map_id** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ve
ctorMeasure`。
形式化陈述：map_id : v.map id = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.map_apply`：map_apply {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : v.map f s = v (f ⁻¹' s)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `Set.preimage_id`：preimage_id {s : Set α} : id ⁻¹' s = s
-/
theorem map_id : v.map id = v :=
  ext fun i hi => by rw [map_apply v measurable_id hi, Set.preimage_id]

@[simp]
/-
**MeasureTheory.VectorMeasure.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：map_zero (f : α -> β) : (0 : VectorMeasure α M).map f = 0
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.map_apply`：map_apply {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : v.map f s = v (f ⁻¹' s)
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem map_zero (f : α → β) : (0 : VectorMeasure α M).map f = 0 := by
  by_cases hf : Measurable f
  · ext i hi
    rw [map_apply _ hf hi, zero_apply, zero_apply]
  · exact dif_neg hf

section

variable {N : Type*} [AddCommMonoid N] [TopologicalSpace N]

/-- Given a vector measure `v` on `M` and a continuous `AddMonoidHom` `f : M → N`, `f ∘ v` is a
vector measure on `N`. -/
/-
**MeasureTheory.VectorMeasure.mapRange** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：mapRange (v : VectorMeasure α M) (f : M ->+ N) (hf : Continuous f) : Vecto
rMeasure α N where measureOf' s
参数：v : VectorMeasure α M；f : M ->+ N；hf : Continuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a vector measure `v` on `M` and a continuous `AddMonoidHom` `f : M → N`, `
f ∘ v` is a
vector measure on `N`.
-/
def mapRange (v : VectorMeasure α M) (f : M →+ N) (hf : Continuous f) : VectorMeasure α N where
  measureOf' s := f (v s)
  empty' := by rw [empty, AddMonoidHom.map_zero]
  not_measurable' i hi := by rw [not_measurable v hi, AddMonoidHom.map_zero]
  m_iUnion' _ hg₁ hg₂ := HasSum.map (v.m_iUnion hg₁ hg₂) f hf

@[simp]
/-
**MeasureTheory.VectorMeasure.mapRange_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：mapRange_apply {f : M ->+ N} (hf : Continuous f) {s : Set α} : v.mapRange 
f hf s = f (v s)
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapRange_apply {f : M →+ N} (hf : Continuous f) {s : Set α} : v.mapRange f hf s = f (v s) :=
  rfl

@[simp]
/-
**MeasureTheory.VectorMeasure.mapRange_id** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.VectorMeasure`。
形式化陈述：mapRange_id : v.mapRange (AddMonoidHom.id M) continuous_id = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem mapRange_id : v.mapRange (AddMonoidHom.id M) continuous_id = v := by
  ext
  rfl

@[simp]
/-
**MeasureTheory.VectorMeasure.mapRange_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：mapRange_zero {f : M ->+ N} (hf : Continuous f) : mapRange (0 : VectorMeas
ure α M) f hf = 0
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange_zero {f : M →+ N} (hf : Continuous f) :
    mapRange (0 : VectorMeasure α M) f hf = 0 := by
  ext
  simp

section ContinuousAdd

variable [ContinuousAdd M] [ContinuousAdd N]

@[simp]
/-
**MeasureTheory.VectorMeasure.mapRange_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：mapRange_add {v w : VectorMeasure α M} {f : M ->+ N} (hf : Continuous f) :
 (v + w).mapRange f hf = v.mapRange f hf + w.mapRange f hf
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange_add {v w : VectorMeasure α M} {f : M →+ N} (hf : Continuous f) :
    (v + w).mapRange f hf = v.mapRange f hf + w.mapRange f hf := by
  ext
  simp

/-- Given a continuous `AddMonoidHom` `f : M → N`, `mapRangeHom` is the `AddMonoidHom` mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
/-
**MeasureTheory.VectorMeasure.mapRangeHom** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.VectorMeasure`。
形式化陈述：mapRangeHom {α : Type*} [MeasurableSpace α] (f : M ->+ N) (hf : Continuous
 f) : VectorMeasure α M ->+ VectorMeasure α N where toFun v
参数：f : M ->+ N；hf : Continuous f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.mapRange_zero`：mapRange_zero {f : M ->+ N} (
hf : Continuous f) : mapRange (0 : VectorMeasure α M) f hf = 0
· 使用定理 `MeasureTheory.VectorMeasure.mapRange_add`：mapRange_add {v w : VectorMeas
ure α M} {f : M ->+ N} (hf : Continuous f) : (v + w).mapRange f hf = v.mapRange 
f hf + w.mapRange f hf

--- 原说明 ---
Given a continuous `AddMonoidHom` `f : M → N`, `mapRangeHom` is the `AddMonoidHo
m` mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`.
-/
def mapRangeHom {α : Type*} [MeasurableSpace α] (f : M →+ N) (hf : Continuous f) :
    VectorMeasure α M →+ VectorMeasure α N where
  toFun v := v.mapRange f hf
  map_zero' := mapRange_zero hf
  map_add' _ _ := mapRange_add hf

end ContinuousAdd

section Module

variable {R : Type*} [Semiring R] [Module R M] [Module R N]

variable [ContinuousConstSMul R M] [ContinuousConstSMul R N]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MeasureTheory.VectorMeasure.mapRange_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：mapRange_smul {v : VectorMeasure α M} {f : M ->ₗ[R] N} (hf : Continuous f)
 {c : R} : (c • v).mapRange f.toAddMonoidHom hf = c • (v.mapRange f.toAddMonoidH
om hf)
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSMulApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M]   {R : Type u_4} [inst_2 : Se…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange_smul {v : VectorMeasure α M} {f : M →ₗ[R] N} (hf : Continuous f) {c : R} :
    (c • v).mapRange f.toAddMonoidHom hf = c • (v.mapRange f.toAddMonoidHom hf) := by
  ext; simp

variable [ContinuousAdd M] [ContinuousAdd N]

set_option backward.isDefEq.respectTransparency false in
/-- Given a continuous linear map `f : M → N`, `mapRangeₗ` is the linear map mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
/-
**MeasureTheory.VectorMeasure.mapRange** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：mapRange (v : VectorMeasure α M) (f : M ->+ N) (hf : Continuous f) : Vecto
rMeasure α N where measureOf' s
参数：v : VectorMeasure α M；f : M ->+ N；hf : Continuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous linear map `f : M → N`, `mapRangeₗ` is the linear map mapping
 the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`.
-/
def mapRangeₗ {α : Type*} [MeasurableSpace α] (f : M →ₗ[R] N) (hf : Continuous f) :
    VectorMeasure α M →ₗ[R] VectorMeasure α N where
  toFun v := v.mapRange f.toAddMonoidHom hf
  map_add' _ _ := mapRange_add hf
  map_smul' _ _ := mapRange_smul hf

end Module

end

open scoped Classical in
/-- The restriction of a vector measure on some set. -/
/-
**MeasureTheory.VectorMeasure.restrict** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：{α : Type u_1} →   {mα : MeasurableSpace α} →     {M : Type u_3} →       [
inst : AddCommMonoid M] →         [inst_1 : TopologicalSpace M] → MeasureTheory.
VectorMeasure α M → Set α → MeasureTheory.VectorMeasure α M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a vector measure on some set.
-/
@[no_expose] def restrict (v : VectorMeasure α M) (i : Set α) : VectorMeasure α M :=
  if hi : MeasurableSet i then
    { measureOf' := fun s => if MeasurableSet s then v (s ∩ i) else 0
      empty' := by simp
      not_measurable' := fun _ hi => if_neg hi
      m_iUnion' := by
        intro f hf₁ hf₂
        convert!
          v.m_iUnion (fun n => (hf₁ n).inter hi)
            (hf₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left)
        · rw [if_pos (hf₁ _)]
        · rw [Set.iUnion_inter, if_pos (MeasurableSet.iUnion hf₁)] }
  else 0
/-
**MeasureTheory.VectorMeasure.restrict_not_measurable** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.VectorMeasure`。
形式化陈述：restrict_not_measurable {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i
 = 0
参数：hi : ¬MeasurableSet i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem restrict_not_measurable {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0 :=
  dif_neg hi
/-
**MeasureTheory.VectorMeasure.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：restrict_apply {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : Measur
ableSet j) : v.restrict i j = v (j inter i)
参数：hi : MeasurableSet i；hj : MeasurableSet j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Basic.0.MeasureTheory.Vecto
rMeasure.restrict.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace α} {M : Type u_3}
 [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   (v : MeasureTheory.Vec
torM…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem restrict_apply {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) :
    v.restrict i j = v (j ∩ i) := by
  rw [restrict, dif_pos hi]
  exact if_pos hj
/-
**MeasureTheory.VectorMeasure.restrict_apply_univ** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.VectorMeasure`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : TopologicalSpace M]   (v : MeasureTheory.VectorMeasure α M) {i
 : Set α}, (v.restrict i) Set.univ = v i
参数：v : MeasureTheory.VectorMeasure α M；v.restrict i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
-/
@[simp] theorem restrict_apply_univ {i : Set α} :
    v.restrict i univ = v i := by
  by_cases hi : MeasurableSet i
  · simp [restrict_apply, hi]
  · simp [restrict_not_measurable, hi]
/-
**MeasureTheory.VectorMeasure.restrict_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：restrict_eq_self {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : Meas
urableSet j) (hij : j subseteq i) : v.restrict i j = v j
参数：hi : MeasurableSet i；hj : MeasurableSet j；hij : j subseteq i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
-/
theorem restrict_eq_self {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j)
    (hij : j ⊆ i) : v.restrict i j = v j := by
  rw [restrict_apply v hi hj, Set.inter_eq_left.2 hij]

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：restrict_empty : v.restrict ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
-/
theorem restrict_empty : v.restrict ∅ = 0 :=
  ext fun i hi => by
    rw [restrict_apply v MeasurableSet.empty hi, Set.inter_empty, v.empty, zero_apply]

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：restrict_univ : v.restrict Set.univ = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem restrict_univ : v.restrict Set.univ = v :=
  ext fun i hi => by rw [restrict_apply v MeasurableSet.univ hi, Set.inter_univ]

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：restrict_zero {i : Set α} : (0 : VectorMeasure α M).restrict i = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem restrict_zero {i : Set α} : (0 : VectorMeasure α M).restrict i = 0 := by
  by_cases hi : MeasurableSet i
  · ext j hj
    rw [restrict_apply 0 hi hj, zero_apply, zero_apply]
  · exact dif_neg hi
/-
**MeasureTheory.VectorMeasure.restrict_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：restrict_dirac {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) [Decidab
le (x in s)] : (dirac x m).restrict s = if x in s then dirac x m else 0
参数：hs : MeasurableSet s；x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
-/
theorem restrict_dirac {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) [Decidable (x ∈ s)] :
    (dirac x m).restrict s = if x ∈ s then dirac x m else 0 := by
  classical
  ext t ht
  simp only [hs, ht, restrict_apply]
  split_ifs with has <;> simp [dirac, ht, ht.inter hs, has]

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_dirac_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：restrict_dirac_of_mem {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) (
hx : x in s) : (dirac x m).restrict s = dirac x m
参数：hs : MeasurableSet s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_dirac`：restrict_dirac {s : Set α} {
x : α} {m : M} (hs : MeasurableSet s) [Decidable (x in s)] : (dirac x m).restric
t s = if x in s then dirac x m e…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_dirac_of_mem {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) (hx : x ∈ s) :
    (dirac x m).restrict s = dirac x m := by
  classical
  simp [restrict_dirac, hs, hx]

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_dirac_of_notMem** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_dirac_of_notMem {s : Set α} {x : α} {m : M} (hx : x ∉ s) : (dirac
 x m).restrict s = 0
参数：hx : x ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_dirac`：restrict_dirac {s : Set α} {
x : α} {m : M} (hs : MeasurableSet s) [Decidable (x in s)] : (dirac x m).restric
t s = if x in s then dirac x m e…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
theorem restrict_dirac_of_notMem {s : Set α} {x : α} {m : M} (hx : x ∉ s) :
    (dirac x m).restrict s = 0 := by
  classical
  by_cases hs : MeasurableSet s
  · simp [restrict_dirac, hs, hx]
  · simp [restrict, hs]

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：restrict_singleton {a : α} : v.restrict {a} = dirac a (v {a})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `Set.inter_singleton_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s 
→ s ∩ {a} = {a}
· 使用定理 `MeasureTheory.VectorMeasure.dirac_apply_of_mem`：∀ {β : Type u_2} {M : Ty
pe u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] [inst_2 : Measura
bleSpace β]   {x : β} {v : M} {s : S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.inter_singleton_of_notMem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∉
 s → s ∩ {a} = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `MeasureTheory.VectorMeasure.dirac_apply_of_notMem`：∀ {β : Type u_2} {M :
 Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] [inst_2 : Meas
urableSpace β]   {x : β} {v : M} {s : S…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `MeasureTheory.VectorMeasure.dirac_zero`：∀ {β : Type u_2} {M : Type u_3} 
[inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] [inst_2 : MeasurableSpace
 β]   {x : β}, MeasureTheory…
-/
theorem restrict_singleton {a : α} : v.restrict {a} = dirac a (v {a}) := by
  by_cases h : MeasurableSet {a}
  · ext s hs
    by_cases ha : a ∈ s <;> simp [*, restrict_apply]
  · simp [restrict, h]
/-
**MeasureTheory.VectorMeasure.restrict_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：restrict_restrict {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet
 t) : (v.restrict t).restrict s = v.restrict (s inter t)
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_restrict {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (v.restrict t).restrict s = v.restrict (s ∩ t) := by
  ext u hu
  simp [restrict_apply, hs, hu, ht, Set.inter_assoc]
/-
**MeasureTheory.VectorMeasure.restrict_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：restrict_map {f : α -> β} (hf : Measurable f) {s : Set β} (hs : Measurable
Set s) : (v.map f).restrict s = (v.restrict (f ⁻¹' s)).map f
参数：hf : Measurable f；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `MeasureTheory.VectorMeasure.map_apply`：map_apply {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : v.map f s = v (f ⁻¹' s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_map {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (v.map f).restrict s = (v.restrict (f ⁻¹' s)).map f := by
  ext t ht
  simp [map_apply, hs, hf hs, restrict_apply, ht, hf, hf ht]
/-
**MeasureTheory.VectorMeasure.restrict_toSignedMeasure** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_toSignedMeasure {μ : Measure α} [IsFiniteMeasure μ] {s : Set α} (
hs : MeasurableSet s) : μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMe
asure
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_apply_measurable`：toSignedMeasure_
apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α} (hi : Measurabl
eSet i) : μ.toSignedMeasure i = μ.real i
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
-/
theorem restrict_toSignedMeasure {μ : Measure α} [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) :
    μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure := by
  ext t ht
  rw [restrict_apply _ hs ht, Measure.toSignedMeasure_apply_measurable (ht.inter hs),
    Measure.toSignedMeasure_apply_measurable ht, measureReal_restrict_apply ht]

section ContinuousAdd

variable [ContinuousAdd M]

/-
**MeasureTheory.VectorMeasure.map_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.V
ectorMeasure`。
形式化陈述：map_add (v w : VectorMeasure α M) (f : α -> β) : (v + w).map f = v.map f +
 w.map f
参数：v w : VectorMeasure α M；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.map_apply`：map_apply {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : v.map f s = v (f ⁻¹' s)
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `MeasureTheory.VectorMeasure.mk.congr_simp`：∀ {α : Type u_3} [inst : Meas
urableSpace α] {M : Type u_4} [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSp
ace M]   (measureOf' measureOf'…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem map_add (v w : VectorMeasure α M) (f : α → β) : (v + w).map f = v.map f + w.map f := by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp [map, dif_neg hf]

/-- `VectorMeasure.map` as an additive monoid homomorphism. -/
@[simps]
/-
**MeasureTheory.VectorMeasure.mapGm** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vec
torMeasure`。
形式化陈述：mapGm {α : Type*} [MeasurableSpace α] (f : α -> β) : VectorMeasure α M ->+
 VectorMeasure β M where toFun v
参数：f : α -> β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.map_zero`：map_zero (f : α -> β) : (0 : Vecto
rMeasure α M).map f = 0
· 使用定理 `MeasureTheory.VectorMeasure.map_add`：map_add (v w : VectorMeasure α M) (
f : α -> β) : (v + w).map f = v.map f + w.map f

--- 原说明 ---
`VectorMeasure.map` as an additive monoid homomorphism.
-/
def mapGm {α : Type*} [MeasurableSpace α] (f : α → β) : VectorMeasure α M →+ VectorMeasure β M where
  toFun v := v.map f
  map_zero' := map_zero f
  map_add' _ _ := map_add _ _ f

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：restrict_add (v w : VectorMeasure α M) (i : Set α) : (v + w).restrict i = 
v.restrict i + w.restrict i
参数：v w : VectorMeasure α M；i : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem restrict_add (v w : VectorMeasure α M) (i : Set α) :
    (v + w).restrict i = v.restrict i + w.restrict i := by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

/-- `VectorMeasure.restrict` as an additive monoid homomorphism. -/
@[simps]
/-
**MeasureTheory.VectorMeasure.restrictGm** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.VectorMeasure`。
形式化陈述：restrictGm {α : Type*} [MeasurableSpace α] (i : Set α) : VectorMeasure α M
 ->+ VectorMeasure α M where toFun v
参数：i : Set α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.restrict_zero`：restrict_zero {i : Set α} : (
0 : VectorMeasure α M).restrict i = 0
· 使用定理 `MeasureTheory.VectorMeasure.restrict_add`：restrict_add (v w : VectorMeas
ure α M) (i : Set α) : (v + w).restrict i = v.restrict i + w.restrict i

--- 原说明 ---
`VectorMeasure.restrict` as an additive monoid homomorphism.
-/
def restrictGm {α : Type*} [MeasurableSpace α] (i : Set α) :
    VectorMeasure α M →+ VectorMeasure α M where
  toFun v := v.restrict i
  map_zero' := restrict_zero
  map_add' _ _ := restrict_add _ _ i

end ContinuousAdd

section Partition

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [T2Space M] [ContinuousAdd M]
variable {v : VectorMeasure α M} {i s t : Set α}

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_add_restrict_compl** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_add_restrict_compl (hi : MeasurableSet i) : v.restrict i + v.rest
rict iᶜ = v
参数：hi : MeasurableSet i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `Disjoint.inter_left'`：inter_left' (u : Set α) (h : Disjoint s t) : Disjo
int (u inter s) t
· 使用定理 `Disjoint.inter_right'`：inter_right' (u : Set α) (h : Disjoint s t) : Dis
joint s (u inter t)
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_add_restrict_compl (hi : MeasurableSet i) :
    v.restrict i + v.restrict iᶜ = v := by
  ext A hA
  rw [_root_.add_apply, restrict_apply _ hi hA, restrict_apply _ hi.compl hA,
    ← of_union _ (hA.inter hi) (hA.inter hi.compl)]
  · simp
  · exact disjoint_compl_right.inter_right' A |>.inter_left' A
/-
**MeasureTheory.VectorMeasure.restrict_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_inter_add_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t) : v
.restrict (s inter t) + v.restrict (s \ t) = v.restrict s
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem restrict_inter_add_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s ∩ t) + v.restrict (s \ t) = v.restrict s := by
  ext u hu
  simp only [_root_.add_apply, restrict_apply, hs, hu, hs.inter ht, hs.diff ht]
  rw [← of_union (by grind) (hu.inter (hs.inter ht)) (hu.inter (hs.diff ht))]
  congr
  grind

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff
/-
**MeasureTheory.VectorMeasure.restrict_union_add_inter** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_union_add_inter (hs : MeasurableSet s) (ht : MeasurableSet t) : v
.restrict (s union t) + v.restrict (s inter t) = v.restrict s + v.restrict t
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_inter_add_sdiff`：restrict_inter_add
_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t) : v.restrict (s inter t) + 
v.restrict (s \ t) = v.restrict s
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `Set.union_inter_cancel_right`：union_inter_cancel_right {s t : Set α} : (
s union t) inter t = t
· 使用定理 `Set.union_sdiff_right`：union_sdiff_right {s t : Set α} : (s union t) \ t
 = s \ t
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
-/
theorem restrict_union_add_inter (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s ∪ t) + v.restrict (s ∩ t) = v.restrict s + v.restrict t := by
  rw [← v.restrict_inter_add_sdiff (hs.union ht) ht, union_inter_cancel_right, union_sdiff_right,
    ← v.restrict_inter_add_sdiff hs ht, add_comm, ← add_assoc, add_right_comm]
/-
**MeasureTheory.VectorMeasure.restrict_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：restrict_union (h : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableS
et t) : v.restrict (s union t) = v.restrict s + v.restrict t
参数：h : Disjoint s t；hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_union_add_inter`：restrict_union_add
_inter (hs : MeasurableSet s) (ht : MeasurableSet t) : v.restrict (s union t) + 
v.restrict (s inter t) = v.restrict s + v.…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `MeasureTheory.VectorMeasure.restrict_empty`：restrict_empty : v.restrict 
∅ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_union (h : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s ∪ t) = v.restrict s + v.restrict t := by
  simp [← v.restrict_union_add_inter hs ht, disjoint_iff_inter_eq_empty.mp h]

end Partition

section Sub

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：restrict_neg (v : VectorMeasure α M) (i : Set α) : (-v).restrict i = -(v.r
estrict i)
参数：v : VectorMeasure α M；i : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem restrict_neg (v : VectorMeasure α M) (i : Set α) :
    (-v).restrict i = -(v.restrict i) := by
  by_cases hi : MeasurableSet i
  · ext j hj; simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：restrict_sub (v w : VectorMeasure α M) (i : Set α) : (v - w).restrict i = 
v.restrict i - w.restrict i
参数：v w : VectorMeasure α M；i : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.VectorMeasure.restrict_add`：restrict_add (v w : VectorMeas
ure α M) (i : Set α) : (v + w).restrict i = v.restrict i + w.restrict i
· 使用定理 `MeasureTheory.VectorMeasure.restrict_neg`：restrict_neg (v : VectorMeasur
e α M) (i : Set α) : (-v).restrict i = -(v.restrict i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_sub (v w : VectorMeasure α M) (i : Set α) :
    (v - w).restrict i = v.restrict i - w.restrict i := by
  simp [sub_eq_add_neg, restrict_add, restrict_neg]

end Sub

end

section

variable [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

@[simp]
/-
**MeasureTheory.VectorMeasure.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：map_smul {v : VectorMeasure α M} {f : α -> β} (c : R) : (c • v).map f = c 
• v.map f
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.map_apply`：map_apply {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : v.map f s = v (f ⁻¹' s)
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSMulApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M]   {R : Type u_4} [inst_2 : Se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem map_smul {v : VectorMeasure α M} {f : α → β} (c : R) : (c • v).map f = c • v.map f := by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp only [map, dif_neg hf]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext i
    simp

@[simp]
/-
**MeasureTheory.VectorMeasure.restrict_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：restrict_smul {v : VectorMeasure α M} {i : Set α} (c : R) : (c • v).restri
ct i = c • v.restrict i
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSMulApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M]   {R : Type u_4} [inst_2 : Se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem restrict_smul {v : VectorMeasure α M} {i : Set α} (c : R) :
    (c • v).restrict i = c • v.restrict i := by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp only [restrict_not_measurable _ hi]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext j
    simp

end

section

variable [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [Module R M] [ContinuousConstSMul R M] [ContinuousAdd M]

/-- `VectorMeasure.map` as a linear map. -/
@[simps]
/-
**MeasureTheory.VectorMeasure.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vecto
rMeasure`。
形式化陈述：map (v : VectorMeasure α M) (f : α -> β) : VectorMeasure β M
参数：v : VectorMeasure α M；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`VectorMeasure.map` as a linear map.
-/
def mapₗ (f : α → β) : VectorMeasure α M →ₗ[R] VectorMeasure β M where
  toFun v := v.map f
  map_add' _ _ := map_add _ _ f
  map_smul' _ _ := map_smul _

/-- `VectorMeasure.restrict` as an additive monoid homomorphism. -/
@[simps]
/-
**MeasureTheory.VectorMeasure.restrict** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：{α : Type u_1} →   {mα : MeasurableSpace α} →     {M : Type u_3} →       [
inst : AddCommMonoid M] →         [inst_1 : TopologicalSpace M] → MeasureTheory.
VectorMeasure α M → Set α → MeasureTheory.VectorMeasure α M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`VectorMeasure.restrict` as an additive monoid homomorphism.
-/
def restrictₗ (i : Set α) : VectorMeasure α M →ₗ[R] VectorMeasure α M where
  toFun v := v.restrict i
  map_add' _ _ := restrict_add _ _ i
  map_smul' _ _ := restrict_smul _

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]

/-- Vector measures over a partially ordered monoid is partially ordered.

This definition is consistent with `Measure.instPartialOrder`. -/
/-
**MeasureTheory.VectorMeasure.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：instPartialOrder : PartialOrder (VectorMeasure α M) where le v w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vector measures over a partially ordered monoid is partially ordered.

This definition is consistent with `Measure.instPartialOrder`.
-/
instance instPartialOrder : PartialOrder (VectorMeasure α M) where
  le v w := ∀ i, MeasurableSet i → v i ≤ w i
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ i hi := le_trans (h₁ i hi) (h₂ i hi)
  le_antisymm _ _ h₁ h₂ := ext fun i hi => le_antisymm (h₁ i hi) (h₂ i hi)

variable {v w : VectorMeasure α M}
/-
**MeasureTheory.VectorMeasure.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ve
ctorMeasure`。
形式化陈述：le_iff : v <= w ↔ forall i, MeasurableSet i -> v i <= w i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_iff : v ≤ w ↔ ∀ i, MeasurableSet i → v i ≤ w i := Iff.rfl
/-
**MeasureTheory.VectorMeasure.le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.V
ectorMeasure`。
形式化陈述：le_iff' : v <= w ↔ forall i, v i <= w i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem le_iff' : v ≤ w ↔ ∀ i, v i ≤ w i := by
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : MeasurableSet i
  · exact h i hi
  · rw [v.not_measurable hi, w.not_measurable hi]

end

/-- `v ≤[i] w` is notation for `v.restrict i ≤ w.restrict i`. -/
scoped[MeasureTheory]
  notation3:50 v " ≤[" i:50 "] " w:50 =>
    MeasureTheory.VectorMeasure.restrict v i ≤ MeasureTheory.VectorMeasure.restrict w i

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
variable (v w : VectorMeasure α M)

/-
**MeasureTheory.VectorMeasure.restrict_le_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_le_restrict_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ 
forall ⦃j⦄, MeasurableSet j -> j subseteq i -> v j <= w j
参数：hi : MeasurableSet i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.restrict_eq_self`：restrict_eq_self {i : Set 
α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) (hij : j subseteq i
) : v.restrict i j = v j
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.VectorMeasure.le_iff`：le_iff : v <= w ↔ forall i, Measurab
leSet i -> v i <= w i
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
-/
theorem restrict_le_restrict_iff {i : Set α} (hi : MeasurableSet i) :
    v ≤[i] w ↔ ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j :=
  ⟨fun h j hj₁ hj₂ => restrict_eq_self v hi hj₁ hj₂ ▸ restrict_eq_self w hi hj₁ hj₂ ▸ h j hj₁,
    fun h => le_iff.1 fun _ hj =>
      (restrict_apply v hi hj).symm ▸ (restrict_apply w hi hj).symm ▸
      h (hj.inter hi) Set.inter_subset_right⟩
/-
**MeasureTheory.VectorMeasure.subset_le_of_restrict_le_restrict** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：subset_le_of_restrict_le_restrict {i : Set α} (hi : MeasurableSet i) (hi₂ 
: v <=[i] w) {j : Set α} (hj : j subseteq i) : v j <= w j
参数：hi : MeasurableSet i；hi₂ : v <=[i] w；hj : j subseteq i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iff`：restrict_le_restri
ct_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ forall ⦃j⦄, MeasurableSe
t j -> j subseteq i -> v j <= w j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem subset_le_of_restrict_le_restrict {i : Set α} (hi : MeasurableSet i) (hi₂ : v ≤[i] w)
    {j : Set α} (hj : j ⊆ i) : v j ≤ w j := by
  by_cases hj₁ : MeasurableSet j
  · exact (restrict_le_restrict_iff _ _ hi).1 hi₂ hj₁ hj
  · rw [v.not_measurable hj₁, w.not_measurable hj₁]
/-
**MeasureTheory.VectorMeasure.restrict_le_restrict_of_subset_le** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_le_restrict_of_subset_le {i : Set α} (h : forall ⦃j⦄, MeasurableS
et j -> j subseteq i -> v j <= w j) : v <=[i] w
参数：h : forall ⦃j⦄, MeasurableSet j -> j subseteq i -> v j <= w j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iff`：restrict_le_restri
ct_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ forall ⦃j⦄, MeasurableSe
t j -> j subseteq i -> v j <= w j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem restrict_le_restrict_of_subset_le {i : Set α}
    (h : ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j) : v ≤[i] w := by
  by_cases hi : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi).2 h
  · rw [restrict_not_measurable v hi, restrict_not_measurable w hi]
/-
**MeasureTheory.VectorMeasure.restrict_le_restrict_subset** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_le_restrict_subset {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v
 <=[i] w) (hij : j subseteq i) : v <=[j] w
参数：hi₁ : MeasurableSet i；hi₂ : v <=[i] w；hij : j subseteq i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_of_subset_le`：restrict_
le_restrict_of_subset_le {i : Set α} (h : forall ⦃j⦄, MeasurableSet j -> j subse
teq i -> v j <= w j) : v <=[i] w
· 使用定理 `MeasureTheory.VectorMeasure.subset_le_of_restrict_le_restrict`：subset_le
_of_restrict_le_restrict {i : Set α} (hi : MeasurableSet i) (hi₂ : v <=[i] w) {j
 : Set α} (hj : j subseteq i) : v j <= w j
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
theorem restrict_le_restrict_subset {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w)
    (hij : j ⊆ i) : v ≤[j] w :=
  restrict_le_restrict_of_subset_le v w fun _ _ hk₂ =>
    subset_le_of_restrict_le_restrict v w hi₁ hi₂ (Set.Subset.trans hk₂ hij)
/-
**MeasureTheory.VectorMeasure.le_restrict_empty** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：le_restrict_empty : v <=[∅] w
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_empty`：restrict_empty : v.restrict 
∅ = 0
-/
theorem le_restrict_empty : v ≤[∅] w := by
  simp
/-
**MeasureTheory.VectorMeasure.le_restrict_univ_iff_le** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.VectorMeasure`。
形式化陈述：le_restrict_univ_iff_le : v <=[Set.univ] w ↔ v <= w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_univ`：restrict_univ : v.restrict Se
t.univ = v
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_restrict_univ_iff_le : v ≤[Set.univ] w ↔ v ≤ w := by
  simp

end

section

variable {M : Type*} [TopologicalSpace M]
  [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M] [IsTopologicalAddGroup M]
variable (v w : VectorMeasure α M)

nonrec theorem neg_le_neg {i : Set α} (hi : MeasurableSet i) (h : v ≤[i] w) : -w ≤[i] -v := by
  intro j hj₁
  rw [restrict_apply _ hi hj₁, restrict_apply _ hi hj₁, neg_apply, neg_apply]
  refine neg_le_neg ?_
  rw [← restrict_apply _ hi hj₁, ← restrict_apply _ hi hj₁]
  exact h j hj₁

/-
**MeasureTheory.VectorMeasure.neg_le_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：neg_le_neg_iff {i : Set α} (hi : MeasurableSet i) : -w <=[i] -v ↔ v <=[i] 
w
参数：hi : MeasurableSet i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg`：∀ {α : Type u_1} {m : Measurable
Space α} {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : AddCommGroup M]   
[inst_2 : PartialOrder M] [I…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neg_le_neg_iff {i : Set α} (hi : MeasurableSet i) : -w ≤[i] -v ↔ v ≤[i] w :=
  ⟨fun h => neg_neg v ▸ neg_neg w ▸ neg_le_neg _ _ hi h, fun h => neg_le_neg _ _ hi h⟩

end

section

variable {M : Type*} [TopologicalSpace M]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M] [OrderClosedTopology M]
variable (v w : VectorMeasure α M) {i j : Set α}

/-
**MeasureTheory.VectorMeasure.restrict_le_restrict_iUnion** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_le_restrict_iUnion {f : Nat -> Set α} (hf₁ : forall n, Measurable
Set (f n)) (hf₂ : forall n, v <=[f n] w) : v <=[⋃ n, f n] w
参数：hf₁ : forall n, MeasurableSet (f n)；hf₂ : forall n, v <=[f n] w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_of_subset_le`：restrict_
le_restrict_of_subset_le {i : Set α} (h : forall ⦃j⦄, MeasurableSet j -> j subse
teq i -> v j <= w j) : v <=[i] w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iff`：restrict_le_restri
ct_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ forall ⦃j⦄, MeasurableSe
t j -> j subseteq i -> v j <= w j
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `disjointed_subset`：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> Set α) (i : ι) : disjointed f i subseteq f i
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `MeasureTheory.VectorMeasure.m_iUnion`：m_iUnion (v : VectorMeasure α M) {
f : Nat -> Set α} (hf₁ : forall i, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoin
t on f)) : HasSum (fun i =…
-/
theorem restrict_le_restrict_iUnion {f : ℕ → Set α} (hf₁ : ∀ n, MeasurableSet (f n))
    (hf₂ : ∀ n, v ≤[f n] w) : v ≤[⋃ n, f n] w := by
  refine restrict_le_restrict_of_subset_le v w fun a ha₁ ha₂ => ?_
  have ha₃ : ⋃ n, a ∩ disjointed f n = a := by
    rwa [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left]
  have ha₄ : Pairwise (Disjoint on fun n => a ∩ disjointed f n) :=
    (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  rw [← ha₃, v.of_disjoint_iUnion _ ha₄, w.of_disjoint_iUnion _ ha₄]
  · refine Summable.tsum_le_tsum (fun n => (restrict_le_restrict_iff v w (hf₁ n)).1 (hf₂ n) ?_ ?_)
      ?_ ?_
    · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
    · exact Set.Subset.trans Set.inter_subset_right (disjointed_subset _ _)
    · refine (v.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
    · refine (w.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  · intro n
    exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
  · exact fun n => ha₁.inter (MeasurableSet.disjointed hf₁ n)
/-
**MeasureTheory.VectorMeasure.restrict_le_restrict_countable_iUnion** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_le_restrict_countable_iUnion [Countable β] {f : β -> Set α} (hf₁ 
: forall b, MeasurableSet (f b)) (hf₂ : forall b, v <=[f b] w) : v <=[⋃ b, f b] 
w
参数：hf₁ : forall b, MeasurableSet (f b)；hf₂ : forall b, v <=[f b] w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_encodable`：nonempty_encodable (α : Type*) [Countable α] : Nonem
pty (Encodable α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Encodable.iUnion_decode₂`：iUnion_decode₂ (f : β -> Set α) : ⋃ (i : Nat) 
(b in decode₂ β i), f b = ⋃ b, f b
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iUnion`：restrict_le_res
trict_iUnion {f : Nat -> Set α} (hf₁ : forall n, MeasurableSet (f n)) (hf₂ : for
all n, v <=[f n] w) : v <=[⋃ n, f n] w
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `MeasureTheory.VectorMeasure.restrict_empty`：restrict_empty : v.restrict 
∅ = 0
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
-/
theorem restrict_le_restrict_countable_iUnion [Countable β] {f : β → Set α}
    (hf₁ : ∀ b, MeasurableSet (f b)) (hf₂ : ∀ b, v ≤[f b] w) : v ≤[⋃ b, f b] w := by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]
  refine restrict_le_restrict_iUnion v w ?_ ?_
  · intro n
    measurability
  · intro n
    rcases Encodable.decode₂ β n with - | b
    · simp
    · simp [hf₂ b]
/-
**MeasureTheory.VectorMeasure.restrict_le_restrict_union** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_le_restrict_union (hi₁ : MeasurableSet i) (hi₂ : v <=[i] w) (hj₁ 
: MeasurableSet j) (hj₂ : v <=[j] w) : v <=[i union j] w
参数：hi₁ : MeasurableSet i；hi₂ : v <=[i] w；hj₁ : MeasurableSet j；hj₂ : v <=[j] w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_countable_iUnion`：restr
ict_le_restrict_countable_iUnion [Countable β] {f : β -> Set α} (hf₁ : forall b,
 MeasurableSet (f b)) (hf₂ : forall b, v <=[f b] w) : v…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem restrict_le_restrict_union (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w) (hj₁ : MeasurableSet j)
    (hj₂ : v ≤[j] w) : v ≤[i ∪ j] w := by
  rw [Set.union_eq_iUnion]
  refine restrict_le_restrict_countable_iUnion v w ?_ ?_
  · measurability
  · rintro (_ | _) <;> simpa

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
variable (v w : VectorMeasure α M) {i j : Set α}

/-
**MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：nonneg_of_zero_le_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
参数：hi₂ : 0 <=[i] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iff`：restrict_le_restri
ct_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ forall ⦃j⦄, MeasurableSe
t j -> j subseteq i -> v j <= w j
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem nonneg_of_zero_le_restrict (hi₂ : 0 ≤[i] v) : 0 ≤ v i := by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]
/-
**MeasureTheory.VectorMeasure.nonpos_of_restrict_le_zero** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：nonpos_of_restrict_le_zero (hi₂ : v <=[i] 0) : v i <= 0
参数：hi₂ : v <=[i] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iff`：restrict_le_restri
ct_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ forall ⦃j⦄, MeasurableSe
t j -> j subseteq i -> v j <= w j
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem nonpos_of_restrict_le_zero (hi₂ : v ≤[i] 0) : v i ≤ 0 := by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]
/-
**MeasureTheory.VectorMeasure.zero_le_restrict_not_measurable** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：zero_le_restrict_not_measurable (hi : ¬MeasurableSet i) : 0 <=[i] v
参数：hi : ¬MeasurableSet i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_zero`：restrict_zero {i : Set α} : (
0 : VectorMeasure α M).restrict i = 0
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem zero_le_restrict_not_measurable (hi : ¬MeasurableSet i) : 0 ≤[i] v := by
  rw [restrict_zero, restrict_not_measurable _ hi]
/-
**MeasureTheory.VectorMeasure.restrict_le_zero_of_not_measurable** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：restrict_le_zero_of_not_measurable (hi : ¬MeasurableSet i) : v <=[i] 0
参数：hi : ¬MeasurableSet i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_zero`：restrict_zero {i : Set α} : (
0 : VectorMeasure α M).restrict i = 0
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem restrict_le_zero_of_not_measurable (hi : ¬MeasurableSet i) : v ≤[i] 0 := by
  rw [restrict_zero, restrict_not_measurable _ hi]
/-
**MeasureTheory.VectorMeasure.measurable_of_not_zero_le_restrict** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：measurable_of_not_zero_le_restrict (hi : ¬0 <=[i] v) : MeasurableSet i
参数：hi : ¬0 <=[i] v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_not_measurable`：zero_le_res
trict_not_measurable (hi : ¬MeasurableSet i) : 0 <=[i] v
-/
theorem measurable_of_not_zero_le_restrict (hi : ¬0 ≤[i] v) : MeasurableSet i :=
  Not.imp_symm (zero_le_restrict_not_measurable _) hi
/-
**MeasureTheory.VectorMeasure.measurable_of_not_restrict_le_zero** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：measurable_of_not_restrict_le_zero (hi : ¬v <=[i] 0) : MeasurableSet i
参数：hi : ¬v <=[i] 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_zero_of_not_measurable`：restrict
_le_zero_of_not_measurable (hi : ¬MeasurableSet i) : v <=[i] 0
-/
theorem measurable_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) : MeasurableSet i :=
  Not.imp_symm (restrict_le_zero_of_not_measurable _) hi
/-
**MeasureTheory.VectorMeasure.zero_le_restrict_subset** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.VectorMeasure`。
形式化陈述：zero_le_restrict_subset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ 
: 0 <=[i] v) : 0 <=[j] v
参数：hi₁ : MeasurableSet i；hij : j subseteq i；hi₂ : 0 <=[i] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_of_subset_le`：restrict_
le_restrict_of_subset_le {i : Set α} (h : forall ⦃j⦄, MeasurableSet j -> j subse
teq i -> v j <= w j) : v <=[i] w
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iff`：restrict_le_restri
ct_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ forall ⦃j⦄, MeasurableSe
t j -> j subseteq i -> v j <= w j
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
theorem zero_le_restrict_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : 0 ≤[i] v) : 0 ≤[j] v :=
  restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)
/-
**MeasureTheory.VectorMeasure.restrict_le_zero_subset** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.VectorMeasure`。
形式化陈述：restrict_le_zero_subset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ 
: v <=[i] 0) : v <=[j] 0
参数：hi₁ : MeasurableSet i；hij : j subseteq i；hi₂ : v <=[i] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_of_subset_le`：restrict_
le_restrict_of_subset_le {i : Set α} (h : forall ⦃j⦄, MeasurableSet j -> j subse
teq i -> v j <= w j) : v <=[i] w
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iff`：restrict_le_restri
ct_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ forall ⦃j⦄, MeasurableSe
t j -> j subseteq i -> v j <= w j
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
theorem restrict_le_zero_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : v ≤[i] 0) : v ≤[j] 0 :=
  restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [LinearOrder M]
variable (v w : VectorMeasure α M) {i j : Set α}

/-
**MeasureTheory.VectorMeasure.exists_pos_measure_of_not_restrict_le_zero** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：exists_pos_measure_of_not_restrict_le_zero (hi : ¬v <=[i] 0) : exists j : 
Set α, MeasurableSet j ∧ j subseteq i ∧ 0 < v j
参数：hi : ¬v <=[i] 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.measurable_of_not_restrict_le_zero`：measurab
le_of_not_restrict_le_zero (hi : ¬v <=[i] 0) : MeasurableSet i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iff`：restrict_le_restri
ct_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ forall ⦃j⦄, MeasurableSe
t j -> j subseteq i -> v j <= w j
-/
theorem exists_pos_measure_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ 0 < v j := by
  have hi₁ : MeasurableSet i := measurable_of_not_restrict_le_zero _ hi
  rw [restrict_le_restrict_iff _ _ hi₁] at hi
  push Not at hi
  exact hi

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
  [AddLeftMono M] [ContinuousAdd M]

/-
**MeasureTheory.VectorMeasure.instAddLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `Measure
Theory.VectorMeasure`。
形式化陈述：instAddLeftMono : AddLeftMono (VectorMeasure α M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
instance instAddLeftMono : AddLeftMono (VectorMeasure α M) :=
  ⟨fun _ _ _ h i hi => by simp only [_root_.add_apply]; grw [h i hi]⟩

end

section

variable {L M N : Type*}
variable [AddCommMonoid L] [TopologicalSpace L] [AddCommMonoid M] [TopologicalSpace M]
  [AddCommMonoid N] [TopologicalSpace N]

/-- A vector measure `v` is absolutely continuous with respect to a measure `μ` if for all sets
`s`, `μ s = 0`, we have `v s = 0`. -/
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous** 是 Mathlib 中的一个定义，位于命名空间 `Me
asureTheory.VectorMeasure`。
形式化陈述：AbsolutelyContinuous (v : VectorMeasure α M) (w : VectorMeasure α N)
参数：v : VectorMeasure α M；w : VectorMeasure α N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vector measure `v` is absolutely continuous with respect to a measure `μ` if f
or all sets
`s`, `μ s = 0`, we have `v s = 0`.
-/
def AbsolutelyContinuous (v : VectorMeasure α M) (w : VectorMeasure α N) :=
  ∀ ⦃s : Set α⦄, w s = 0 → v s = 0

@[inherit_doc VectorMeasure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ᵥ " => MeasureTheory.VectorMeasure.AbsolutelyContinuous

open MeasureTheory

namespace AbsolutelyContinuous

variable {v : VectorMeasure α M} {w : VectorMeasure α N}

/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.mk** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：mk (h : forall ⦃s : Set α⦄, MeasurableSet s -> w s = 0 -> v s = 0) : v ≪ᵥ 
w
参数：h : forall ⦃s : Set α⦄, MeasurableSet s -> w s = 0 -> v s = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
-/
theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → w s = 0 → v s = 0) : v ≪ᵥ w := by
  intro s hs
  by_cases hmeas : MeasurableSet s
  · exact h hmeas hs
  · exact not_measurable v hmeas
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.eq** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：eq {w : VectorMeasure α M} (h : v = w) : v ≪ᵥ w
参数：h : v = w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq {w : VectorMeasure α M} (h : v = w) : v ≪ᵥ w :=
  fun _ hs => h.symm ▸ hs

@[refl]
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.refl** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：refl (v : VectorMeasure α M) : v ≪ᵥ v
参数：v : VectorMeasure α M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.AbsolutelyContinuous.eq`：eq {w : VectorMeasu
re α M} (h : v = w) : v ≪ᵥ w
-/
theorem refl (v : VectorMeasure α M) : v ≪ᵥ v :=
  eq rfl

@[trans]
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.trans** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：trans {u : VectorMeasure α L} {v : VectorMeasure α M} {w : VectorMeasure α
 N} (huv : u ≪ᵥ v) (hvw : v ≪ᵥ w) : u ≪ᵥ w
参数：huv : u ≪ᵥ v；hvw : v ≪ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans {u : VectorMeasure α L} {v : VectorMeasure α M} {w : VectorMeasure α N} (huv : u ≪ᵥ v)
    (hvw : v ≪ᵥ w) : u ≪ᵥ w :=
  fun _ hs => huv <| hvw hs
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.zero** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：zero (v : VectorMeasure α N) : (0 : VectorMeasure α M) ≪ᵥ v
参数：v : VectorMeasure α N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
-/
theorem zero (v : VectorMeasure α N) : (0 : VectorMeasure α M) ≪ᵥ v :=
  fun s _ => zero_apply s
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.neg_left** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：neg_left {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalA
ddGroup M] {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : -v ≪ᵥ 
w
参数：h : v ≪ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem neg_left {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : -v ≪ᵥ w := by
  intro s hs
  rw [neg_apply, h hs, neg_zero]
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.neg_right** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：neg_right {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopological
AddGroup N] {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : v ≪ᵥ 
-w
参数：h : v ≪ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
-/
theorem neg_right {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : v ≪ᵥ -w := by
  intro s hs
  rw [neg_apply, neg_eq_zero] at hs
  exact h hs
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.add** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：add [ContinuousAdd M] {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} 
(hv₁ : v₁ ≪ᵥ w) (hv₂ : v₂ ≪ᵥ w) : v₁ + v₂ ≪ᵥ w
参数：hv₁ : v₁ ≪ᵥ w；hv₂ : v₂ ≪ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem add [ContinuousAdd M] {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w)
    (hv₂ : v₂ ≪ᵥ w) : v₁ + v₂ ≪ᵥ w := by
  intro s hs
  rw [_root_.add_apply, hv₁ hs, hv₂ hs, zero_add]
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.sub** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：sub {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGro
up M] {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w) (hv₂ :
 v₂ ≪ᵥ w) : v₁ - v₂ ≪ᵥ w
参数：hv₁ : v₁ ≪ᵥ w；hv₂ : v₂ ≪ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSubApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem sub {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w) (hv₂ : v₂ ≪ᵥ w) :
    v₁ - v₂ ≪ᵥ w := by
  intro s hs
  rw [sub_apply, hv₁ hs, hv₂ hs, zero_sub, neg_zero]
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.smul** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：smul {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul 
R M] {r : R} {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : r • 
v ≪ᵥ w
参数：h : v ≪ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSMulApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M]   {R : Type u_4} [inst_2 : Se…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem smul {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] {r : R}
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : r • v ≪ᵥ w := by
  intro s hs
  rw [_root_.smul_apply, h hs, smul_zero]
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.map** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：map [MeasureSpace β] (h : v ≪ᵥ w) (f : α -> β) : v.map f ≪ᵥ w.map f
参数：h : v ≪ᵥ w；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s :
 Set α⦄, MeasurableSet s -> w s = 0 -> v s = 0) : v ≪ᵥ w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.map_apply`：map_apply {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : v.map f s = v (f ⁻¹' s)
· 使用定理 `MeasureTheory.VectorMeasure.map_not_measurable`：map_not_measurable {f : 
α -> β} (hf : ¬Measurable f) : v.map f = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
-/
theorem map [MeasureSpace β] (h : v ≪ᵥ w) (f : α → β) : v.map f ≪ᵥ w.map f := by
  by_cases hf : Measurable f
  · refine mk fun s hs hws => ?_
    rw [map_apply _ hf hs] at hws ⊢
    exact h hws
  · intro s _
    rw [map_not_measurable v hf, zero_apply]
/-
**MeasureTheory.VectorMeasure.AbsolutelyContinuous.ennrealToMeasure** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure.AbsolutelyContinuous`。
形式化陈述：ennrealToMeasure {μ : VectorMeasure α Real>=0∞} : (forall ⦃s : Set α⦄, μ.e
nnrealToMeasure s = 0 -> v s = 0) ↔ v ≪ᵥ μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s :
 Set α⦄, MeasurableSet s -> w s = 0 -> v s = 0) : v ≪ᵥ w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_apply`：ennrealToMeasure_app
ly {m : MeasurableSpace α} {v : VectorMeasure α Real>=0∞} {s : Set α} (hs : Meas
urableSet s) : ennrealToMeasure v s = v …
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
-/
theorem ennrealToMeasure {μ : VectorMeasure α ℝ≥0∞} :
    (∀ ⦃s : Set α⦄, μ.ennrealToMeasure s = 0 → v s = 0) ↔ v ≪ᵥ μ := by
  constructor <;> intro h
  · refine mk fun s hmeas hs => h ?_
    rw [← hs, ennrealToMeasure_apply hmeas]
  · intro s hs
    by_cases hmeas : MeasurableSet s
    · rw [ennrealToMeasure_apply hmeas] at hs
      exact h hs
    · exact not_measurable v hmeas

end AbsolutelyContinuous

/-- Two vector measures `v` and `w` are said to be mutually singular if there exists a measurable
set `s`, such that for all `t ⊆ s`, `v t = 0` and for all `t ⊆ sᶜ`, `w t = 0`.

We note that we do not require the measurability of `t` in the definition since this makes it easier
to use. This is equivalent to the definition which requires measurability. To prove
`MutuallySingular` with the measurability condition, use
`MeasureTheory.VectorMeasure.MutuallySingular.mk`. -/
/-
**MeasureTheory.VectorMeasure.MutuallySingular** 是 Mathlib 中的一个定义，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：MutuallySingular (v : VectorMeasure α M) (w : VectorMeasure α N) : Prop
参数：v : VectorMeasure α M；w : VectorMeasure α N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two vector measures `v` and `w` are said to be mutually singular if there exists
 a measurable
set `s`, such that for all `t ⊆ s`, `v t = 0` and for all `t ⊆ sᶜ`, `w t = 0`.

We note that we do not require the measurability of `t` in the definition since 
this makes it easier
to use. This is equivalent to the definition which requires measurability. To pr
ove
`MutuallySingular` with the measurability condition, use
`MeasureTheory.VectorMeasure.MutuallySingular.mk`.
-/
def MutuallySingular (v : VectorMeasure α M) (w : VectorMeasure α N) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ (∀ t ⊆ s, v t = 0) ∧ ∀ t ⊆ sᶜ, w t = 0

@[inherit_doc VectorMeasure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ᵥ " => MeasureTheory.VectorMeasure.MutuallySingular

namespace MutuallySingular

variable {v v₁ v₂ : VectorMeasure α M} {w w₁ w₂ : VectorMeasure α N}

/-
**MeasureTheory.VectorMeasure.MutuallySingular.mk** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：mk (s : Set α) (hs : MeasurableSet s) (h₁ : forall t subseteq s, Measurabl
eSet t -> v t = 0) (h₂ : forall t subseteq sᶜ, MeasurableSet t -> w t = 0) : v ⟂
ᵥ w
参数：s : Set α；hs : MeasurableSet s；h₁ : forall t subseteq s, MeasurableSet t -> v
 t = 0；h₂ : forall t subseteq sᶜ, MeasurableSet t -> w t = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
-/
theorem mk (s : Set α) (hs : MeasurableSet s) (h₁ : ∀ t ⊆ s, MeasurableSet t → v t = 0)
    (h₂ : ∀ t ⊆ sᶜ, MeasurableSet t → w t = 0) : v ⟂ᵥ w := by
  refine ⟨s, hs, fun t hst => ?_, fun t hst => ?_⟩ <;> by_cases ht : MeasurableSet t
  · exact h₁ t hst ht
  · exact not_measurable v ht
  · exact h₂ t hst ht
  · exact not_measurable w ht
/-
**MeasureTheory.VectorMeasure.MutuallySingular.symm** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：symm (h : v ⟂ᵥ w) : w ⟂ᵥ v
参数：h : v ⟂ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem symm (h : v ⟂ᵥ w) : w ⟂ᵥ v :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨sᶜ, hmeas.compl, hs₂, fun t ht => hs₁ _ (compl_compl s ▸ ht : t ⊆ s)⟩
/-
**MeasureTheory.VectorMeasure.MutuallySingular.zero_right** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：zero_right : v ⟂ᵥ (0 : VectorMeasure α N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
-/
theorem zero_right : v ⟂ᵥ (0 : VectorMeasure α N) :=
  ⟨∅, MeasurableSet.empty, fun _ ht => (Set.subset_empty_iff.1 ht).symm ▸ v.empty,
    fun _ _ => zero_apply _⟩
/-
**MeasureTheory.VectorMeasure.MutuallySingular.zero_left** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：zero_left : (0 : VectorMeasure α M) ⟂ᵥ w
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.symm`：symm (h : v ⟂ᵥ w) : w
 ⟂ᵥ v
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.zero_right`：zero_right : v 
⟂ᵥ (0 : VectorMeasure α N)
-/
theorem zero_left : (0 : VectorMeasure α M) ⟂ᵥ w :=
  zero_right.symm
/-
**MeasureTheory.VectorMeasure.MutuallySingular.add_left** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：add_left [T2Space N] [ContinuousAdd M] (h₁ : v₁ ⟂ᵥ w) (h₂ : v₂ ⟂ᵥ w) : v₁ 
+ v₂ ⟂ᵥ w
参数：h₁ : v₁ ⟂ᵥ w；h₂ : v₂ ⟂ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.mk`：mk (s : Set α) (hs : Me
asurableSet s) (h₁ : forall t subseteq s, MeasurableSet t -> v t = 0) (h₂ : fora
ll t subseteq sᶜ, MeasurableSet t -> …
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem add_left [T2Space N] [ContinuousAdd M] (h₁ : v₁ ⟂ᵥ w) (h₂ : v₂ ⟂ᵥ w) : v₁ + v₂ ⟂ᵥ w := by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h₁
  obtain ⟨v, hmv, hv₁, hv₂⟩ := h₂
  refine mk (u ∩ v) (hmu.inter hmv) (fun t ht _ => ?_) fun t ht hmt => ?_
  · rw [_root_.add_apply, hu₁ _ (Set.subset_inter_iff.1 ht).1, hv₁ _ (Set.subset_inter_iff.1 ht).2,
      zero_add]
  · rw [Set.compl_inter] at ht
    rw [(_ : t = uᶜ ∩ t ∪ vᶜ \ uᶜ ∩ t),
      of_union _ (hmu.compl.inter hmt) ((hmv.compl.diff hmu.compl).inter hmt), hu₂, hv₂, add_zero]
    · exact Set.Subset.trans Set.inter_subset_left sdiff_subset
    · exact Set.inter_subset_left
    · exact disjoint_sdiff_self_right.mono Set.inter_subset_left Set.inter_subset_left
    · apply Set.Subset.antisymm <;> intro x hx
      · by_cases hxu' : x ∈ uᶜ
        · exact Or.inl ⟨hxu', hx⟩
        rcases ht hx with (hxu | hxv)
        exacts [False.elim (hxu' hxu), Or.inr ⟨⟨hxv, hxu'⟩, hx⟩]
      · rcases hx with hx | hx <;> exact hx.2
/-
**MeasureTheory.VectorMeasure.MutuallySingular.add_right** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：add_right [T2Space M] [ContinuousAdd N] (h₁ : v ⟂ᵥ w₁) (h₂ : v ⟂ᵥ w₂) : v 
⟂ᵥ w₁ + w₂
参数：h₁ : v ⟂ᵥ w₁；h₂ : v ⟂ᵥ w₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.symm`：symm (h : v ⟂ᵥ w) : w
 ⟂ᵥ v
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.add_left`：add_left [T2Space
 N] [ContinuousAdd M] (h₁ : v₁ ⟂ᵥ w) (h₂ : v₂ ⟂ᵥ w) : v₁ + v₂ ⟂ᵥ w
-/
theorem add_right [T2Space M] [ContinuousAdd N] (h₁ : v ⟂ᵥ w₁) (h₂ : v ⟂ᵥ w₂) : v ⟂ᵥ w₁ + w₂ :=
  (add_left h₁.symm h₂.symm).symm
/-
**MeasureTheory.VectorMeasure.MutuallySingular.smul_right** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：smul_right {R : Type*} [Semiring R] [DistribMulAction R N] [ContinuousCons
tSMul R N] (r : R) (h : v ⟂ᵥ w) : v ⟂ᵥ r • w
参数：r : R；h : v ⟂ᵥ w。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `MeasureTheory.VectorMeasure.instIsSMulApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M]   {R : Type u_4} [inst_2 : Se…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_right {R : Type*} [Semiring R] [DistribMulAction R N] [ContinuousConstSMul R N]
    (r : R) (h : v ⟂ᵥ w) : v ⟂ᵥ r • w :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨s, hmeas, hs₁, fun t ht => by simp only [_root_.smul_apply, hs₂ t ht, smul_zero]⟩
/-
**MeasureTheory.VectorMeasure.MutuallySingular.smul_left** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：smul_left {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConst
SMul R M] (r : R) (h : v ⟂ᵥ w) : r • v ⟂ᵥ w
参数：r : R；h : v ⟂ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.symm`：symm (h : v ⟂ᵥ w) : w
 ⟂ᵥ v
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.smul_right`：smul_right {R :
 Type*} [Semiring R] [DistribMulAction R N] [ContinuousConstSMul R N] (r : R) (h
 : v ⟂ᵥ w) : v ⟂ᵥ r • w
-/
theorem smul_left {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] (r : R)
    (h : v ⟂ᵥ w) : r • v ⟂ᵥ w :=
  (smul_right r h.symm).symm
/-
**MeasureTheory.VectorMeasure.MutuallySingular.neg_left** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：neg_left {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalA
ddGroup M] {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : -v ⟂ᵥ 
w
参数：h : v ⟂ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
-/
theorem neg_left {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : -v ⟂ᵥ w := by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h
  refine ⟨u, hmu, fun s hs => ?_, hu₂⟩
  rw [neg_apply v s, neg_eq_zero]
  exact hu₁ s hs
/-
**MeasureTheory.VectorMeasure.MutuallySingular.neg_right** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：neg_right {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopological
AddGroup N] {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : v ⟂ᵥ 
-w
参数：h : v ⟂ᵥ w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.symm`：symm (h : v ⟂ᵥ w) : w
 ⟂ᵥ v
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.neg_left`：neg_left {M : Typ
e*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {v : VectorM
easure α M} {w : VectorMeasure α N} (h : v …
-/
theorem neg_right {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : v ⟂ᵥ -w :=
  h.symm.neg_left.symm

@[simp]
/-
**MeasureTheory.VectorMeasure.MutuallySingular.neg_left_iff** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：neg_left_iff {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologi
calAddGroup M] {v : VectorMeasure α M} {w : VectorMeasure α N} : -v ⟂ᵥ w ↔ v ⟂ᵥ 
w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.neg_left`：neg_left {M : Typ
e*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {v : VectorM
easure α M} {w : VectorMeasure α N} (h : v …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neg_left_iff {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} : -v ⟂ᵥ w ↔ v ⟂ᵥ w :=
  ⟨fun h => neg_neg v ▸ h.neg_left, neg_left⟩

@[simp]
/-
**MeasureTheory.VectorMeasure.MutuallySingular.neg_right_iff** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.VectorMeasure.MutuallySingular`。
形式化陈述：neg_right_iff {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopolog
icalAddGroup N] {v : VectorMeasure α M} {w : VectorMeasure α N} : v ⟂ᵥ -w ↔ v ⟂ᵥ
 w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.neg_right`：neg_right {N : T
ype*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N] {v : Vecto
rMeasure α M} {w : VectorMeasure α N} (h : v…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neg_right_iff {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} : v ⟂ᵥ -w ↔ v ⟂ᵥ w :=
  ⟨fun h => neg_neg w ▸ h.neg_right, neg_right⟩

end MutuallySingular

section Trim

open scoped Classical in
/-- Restriction of a vector measure onto a sub-σ-algebra. -/
@[simps]
/-
**MeasureTheory.VectorMeasure.trim** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vect
orMeasure`。
形式化陈述：trim {m n : MeasurableSpace α} (v : VectorMeasure α M) (hle : m <= n) : @V
ectorMeasure α m M _ _
参数：v : VectorMeasure α M；hle : m <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a vector measure onto a sub-σ-algebra.
-/
def trim {m n : MeasurableSpace α} (v : VectorMeasure α M) (hle : m ≤ n) :
    @VectorMeasure α m M _ _ :=
  @VectorMeasure.mk α m M _ _
    (fun i => if MeasurableSet[m] i then v i else 0)
    (by rw [if_pos (@MeasurableSet.empty _ m), v.empty])
    (fun i hi => by rw [if_neg hi])
    (fun f hf₁ hf₂ => by
      have hf₁' : ∀ k, MeasurableSet[n] (f k) := fun k => hle _ (hf₁ k)
      convert! v.m_iUnion hf₁' hf₂ using 1
      · ext n
        rw [if_pos (hf₁ n)]
      · rw [if_pos (@MeasurableSet.iUnion _ _ m _ _ hf₁)])

variable {n : MeasurableSpace α} {v : VectorMeasure α M}
/-
**MeasureTheory.VectorMeasure.trim_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：trim_eq_self : v.trim le_rfl = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem trim_eq_self : v.trim le_rfl = v := by
  ext i hi
  exact if_pos hi

@[simp]
/-
**MeasureTheory.VectorMeasure.zero_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.VectorMeasure`。
形式化陈述：zero_trim (hle : m <= n) : (0 : VectorMeasure α M).trim hle = 0
参数：hle : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem zero_trim (hle : m ≤ n) : (0 : VectorMeasure α M).trim hle = 0 := by
  ext i hi
  exact if_pos hi
/-
**MeasureTheory.VectorMeasure.trim_measurableSet_eq** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：trim_measurableSet_eq (hle : m <= n) {i : Set α} (hi : MeasurableSet[m] i)
 : v.trim hle i = v i
参数：hle : m <= n；hi : MeasurableSet[m] i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem trim_measurableSet_eq (hle : m ≤ n) {i : Set α} (hi : MeasurableSet[m] i) :
    v.trim hle i = v i :=
  if_pos hi
/-
**MeasureTheory.VectorMeasure.restrict_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：restrict_trim (hle : m <= n) {i : Set α} (hi : MeasurableSet[m] i) : @Vect
orMeasure.restrict α m M _ _ (v.trim hle) i = (v.restrict i).trim hle
参数：hle : m <= n；hi : MeasurableSet[m] i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `MeasureTheory.VectorMeasure.trim_measurableSet_eq`：trim_measurableSet_eq
 (hle : m <= n) {i : Set α} (hi : MeasurableSet[m] i) : v.trim hle i = v i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem restrict_trim (hle : m ≤ n) {i : Set α} (hi : MeasurableSet[m] i) :
    @VectorMeasure.restrict α m M _ _ (v.trim hle) i = (v.restrict i).trim hle := by
  ext j hj
  rw [@restrict_apply _ m, trim_measurableSet_eq hle hj, restrict_apply, trim_measurableSet_eq]
  all_goals measurability

end Trim

end

end VectorMeasure

namespace SignedMeasure

open VectorMeasure

open MeasureTheory

/-- The underlying function for `SignedMeasure.toMeasureOfZeroLE`. -/
/-
**MeasureTheory.SignedMeasure.toMeasureOfZeroLE'** 是 Mathlib 中的一个定义，位于命名空间 `Meas
ureTheory.SignedMeasure`。
形式化陈述：toMeasureOfZeroLE' (s : SignedMeasure α) (i : Set α) (hi : 0 <=[i] s) (j :
 Set α) (hj : MeasurableSet j) : Real>=0∞
参数：s : SignedMeasure α；i : Set α；hi : 0 <=[i] s；j : Set α；hj : MeasurableSet j。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying function for `SignedMeasure.toMeasureOfZeroLE`.
-/
def toMeasureOfZeroLE' (s : SignedMeasure α) (i : Set α) (hi : 0 ≤[i] s) (j : Set α)
    (hj : MeasurableSet j) : ℝ≥0∞ :=
  ((↑) : ℝ≥0 → ℝ≥0∞) (.mk (s.restrict i j) (le_trans (by simp) (hi j hj)))

/-- Given a signed measure `s` and a positive measurable set `i`, `toMeasureOfZeroLE`
provides the measure, mapping measurable sets `j` to `s (i ∩ j)`. -/
/-
**MeasureTheory.SignedMeasure.toMeasureOfZeroLE** 是 Mathlib 中的一个定义，位于命名空间 `Measu
reTheory.SignedMeasure`。
形式化陈述：toMeasureOfZeroLE (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i
) (hi₂ : 0 <=[i] s) : Measure α
参数：s : SignedMeasure α；i : Set α；hi₁ : MeasurableSet i；hi₂ : 0 <=[i] s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a signed measure `s` and a positive measurable set `i`, `toMeasureOfZeroLE
`
provides the measure, mapping measurable sets `j` to `s (i ∩ j)`.
-/
def toMeasureOfZeroLE (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : 0 ≤[i] s) :
    Measure α := by
  refine Measure.ofMeasurable (s.toMeasureOfZeroLE' i hi₂) ?_ ?_
  · simp_rw [toMeasureOfZeroLE', s.restrict_apply hi₁ MeasurableSet.empty, Set.empty_inter i,
      s.empty]
    rfl
  · intro f hf₁ hf₂
    have h₁ : ∀ n, MeasurableSet (i ∩ f n) := fun n => hi₁.inter (hf₁ n)
    have h₂ : Pairwise (Disjoint on fun n : ℕ => i ∩ f n) := by
      intro n m hnm
      exact ((hf₂ hnm).inf_left' i).inf_right' i
    simp only [toMeasureOfZeroLE', s.restrict_apply hi₁ (MeasurableSet.iUnion hf₁), Set.inter_comm,
      Set.inter_iUnion, s.of_disjoint_iUnion h₁ h₂]
    have h : ∀ n, 0 ≤ s (i ∩ f n) := fun n =>
      s.nonneg_of_zero_le_restrict (s.zero_le_restrict_subset hi₁ Set.inter_subset_left hi₂)
    rw [NNReal.coe_tsum_of_nonneg h, ENNReal.coe_tsum]
    · refine tsum_congr fun n => ?_
      simp_rw [s.restrict_apply hi₁ (hf₁ n), Set.inter_comm]
    · exact (NNReal.summable_mk h).2 (s.m_iUnion h₁ h₂).summable

variable (s : SignedMeasure α) {i j : Set α}
/-
**MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SignedMeasure`。
形式化陈述：toMeasureOfZeroLE_apply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : Me
asurableSet j) : s.toMeasureOfZeroLE i hi₁ hi j = ((↑) : Real>=0 -> Real>=0∞) (.
mk (s (i inter j)) (nonneg_of_zero_le_restrict s (zero_le_restrict_subset s hi₁ 
Set.inter_subset_left hi)))
参数：hi : 0 <=[i] s；hi₁ : MeasurableSet i；hj₁ : MeasurableSet j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Measure.ofMeasurable_apply`：ofMeasurable_apply {m : forall
 s : Set α, MeasurableSet s -> Real>=0∞} {m0 : m ∅ MeasurableSet.empty = 0} {mU 
: forall ⦃f : Nat -> Set α⦄ (h…
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMeasureOfZeroLE_apply (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfZeroLE i hi₁ hi j = ((↑) : ℝ≥0 → ℝ≥0∞) (.mk (s (i ∩ j)) (nonneg_of_zero_le_restrict
      s (zero_le_restrict_subset s hi₁ Set.inter_subset_left hi))) := by
  simp_rw [toMeasureOfZeroLE, Measure.ofMeasurable_apply _ hj₁, toMeasureOfZeroLE',
    s.restrict_apply hi₁ hj₁, Set.inter_comm]
/-
**MeasureTheory.SignedMeasure.toMeasureOfZeroLE_real_apply** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toMeasureOfZeroLE_real_apply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁
 : MeasurableSet j) : (s.toMeasureOfZeroLE i hi₁ hi).real j = s (i inter j)
参数：hi : 0 <=[i] s；hi₁ : MeasurableSet i；hj₁ : MeasurableSet j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply`：toMeasureOfZeroLE_a
pply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfZeroLE i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMeasureOfZeroLE_real_apply (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i)
    (hj₁ : MeasurableSet j) :
    (s.toMeasureOfZeroLE i hi₁ hi).real j = s (i ∩ j) := by
  simp [measureReal_def, toMeasureOfZeroLE_apply, hj₁]

/-- Given a signed measure `s` and a negative measurable set `i`, `toMeasureOfLEZero`
provides the measure, mapping measurable sets `j` to `-s (i ∩ j)`. -/
/-
**MeasureTheory.SignedMeasure.toMeasureOfLEZero** 是 Mathlib 中的一个定义，位于命名空间 `Measu
reTheory.SignedMeasure`。
形式化陈述：toMeasureOfLEZero (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i
) (hi₂ : s <=[i] 0) : Measure α
参数：s : SignedMeasure α；i : Set α；hi₁ : MeasurableSet i；hi₂ : s <=[i] 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
Given a signed measure `s` and a negative measurable set `i`, `toMeasureOfLEZero
`
provides the measure, mapping measurable sets `j` to `-s (i ∩ j)`.
-/
def toMeasureOfLEZero (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : s ≤[i] 0) :
    Measure α :=
  toMeasureOfZeroLE (-s) i hi₁ <| @neg_zero (VectorMeasure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi₂
/-
**MeasureTheory.SignedMeasure.toMeasureOfLEZero_apply** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SignedMeasure`。
形式化陈述：toMeasureOfLEZero_apply (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁ : Me
asurableSet j) : s.toMeasureOfLEZero i hi₁ hi j = ((↑) : Real>=0 -> Real>=0∞) (N
NReal.mk (-s (i inter j)) (neg_apply s (i inter j) ▸ nonneg_of_zero_le_restrict 
_ (zero_le_restrict_subset _ hi₁ Set.inter_subset_left (@neg_zero (VectorMeasure
 α Real) _ ▸ neg_le_neg _ _ hi₁ hi))))
参数：hi : s <=[i] 0；hi₁ : MeasurableSet i；hj₁ : MeasurableSet j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg`：∀ {α : Type u_1} {m : Measurable
Space α} {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : AddCommGroup M]   
[inst_2 : PartialOrder M] [I…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply`：toMeasureOfZeroLE_a
pply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfZeroLE i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMeasureOfLEZero_apply (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfLEZero i hi₁ hi j =
    ((↑) : ℝ≥0 → ℝ≥0∞) (NNReal.mk (-s (i ∩ j)) (neg_apply s (i ∩ j) ▸
      nonneg_of_zero_le_restrict _ (zero_le_restrict_subset _ hi₁ Set.inter_subset_left
      (@neg_zero (VectorMeasure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi)))) := by
  simp [toMeasureOfLEZero, toMeasureOfZeroLE_apply _ _ _ hj₁]
/-
**MeasureTheory.SignedMeasure.toMeasureOfLEZero_real_apply** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toMeasureOfLEZero_real_apply (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁
 : MeasurableSet j) : (s.toMeasureOfLEZero i hi₁ hi).real j = -s (i inter j)
参数：hi : s <=[i] 0；hi₁ : MeasurableSet i；hj₁ : MeasurableSet j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg`：∀ {α : Type u_1} {m : Measurable
Space α} {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : AddCommGroup M]   
[inst_2 : PartialOrder M] [I…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfLEZero_apply`：toMeasureOfLEZero_a
pply (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfLEZero i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMeasureOfLEZero_real_apply (hi : s ≤[i] 0) (hi₁ : MeasurableSet i)
    (hj₁ : MeasurableSet j) :
    (s.toMeasureOfLEZero i hi₁ hi).real j = -s (i ∩ j) := by
  simp [measureReal_def, toMeasureOfLEZero_apply _ hi hi₁ hj₁]

/-- `SignedMeasure.toMeasureOfZeroLE` is a finite measure. -/
/-
**MeasureTheory.SignedMeasure.toMeasureOfZeroLE_finite** 是 Mathlib 中的一个实例，位于命名空间
 `MeasureTheory.SignedMeasure`。
形式化陈述：toMeasureOfZeroLE_finite (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) : IsFini
teMeasure (s.toMeasureOfZeroLE i hi₁ hi) where measure_univ_lt_top
参数：hi : 0 <=[i] s；hi₁ : MeasurableSet i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply`：toMeasureOfZeroLE_a
pply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfZeroLE i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤

--- 原说明 ---
`SignedMeasure.toMeasureOfZeroLE` is a finite measure.
-/
instance toMeasureOfZeroLE_finite (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) :
    IsFiniteMeasure (s.toMeasureOfZeroLE i hi₁ hi) where
  measure_univ_lt_top := by
    rw [toMeasureOfZeroLE_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

/-- `SignedMeasure.toMeasureOfLEZero` is a finite measure. -/
/-
**MeasureTheory.SignedMeasure.toMeasureOfLEZero_finite** 是 Mathlib 中的一个实例，位于命名空间
 `MeasureTheory.SignedMeasure`。
形式化陈述：toMeasureOfLEZero_finite (hi : s <=[i] 0) (hi₁ : MeasurableSet i) : IsFini
teMeasure (s.toMeasureOfLEZero i hi₁ hi) where measure_univ_lt_top
参数：hi : s <=[i] 0；hi₁ : MeasurableSet i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg`：∀ {α : Type u_1} {m : Measurable
Space α} {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : AddCommGroup M]   
[inst_2 : PartialOrder M] [I…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfLEZero_apply`：toMeasureOfLEZero_a
pply (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfLEZero i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤

--- 原说明 ---
`SignedMeasure.toMeasureOfLEZero` is a finite measure.
-/
instance toMeasureOfLEZero_finite (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) :
    IsFiniteMeasure (s.toMeasureOfLEZero i hi₁ hi) where
  measure_univ_lt_top := by
    rw [toMeasureOfLEZero_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top
/-
**MeasureTheory.SignedMeasure.toMeasureOfZeroLE_toSignedMeasure** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toMeasureOfZeroLE_toSignedMeasure (hs : 0 <=[Set.univ] s) : (s.toMeasureOf
ZeroLE Set.univ MeasurableSet.univ hs).toSignedMeasure = s
参数：hs : 0 <=[Set.univ] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply`：toMeasureOfZeroLE_a
pply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfZeroLE i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMeasureOfZeroLE_toSignedMeasure (hs : 0 ≤[Set.univ] s) :
    (s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs).toSignedMeasure = s := by
  ext i hi
  simp [hi, toMeasureOfZeroLE_apply _ _ _ hi, measureReal_def]
/-
**MeasureTheory.SignedMeasure.toMeasureOfLEZero_toSignedMeasure** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toMeasureOfLEZero_toSignedMeasure (hs : s <=[Set.univ] 0) : (s.toMeasureOf
LEZero Set.univ MeasurableSet.univ hs).toSignedMeasure = -s
参数：hs : s <=[Set.univ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg`：∀ {α : Type u_1} {m : Measurable
Space α} {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : AddCommGroup M]   
[inst_2 : PartialOrder M] [I…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfLEZero_apply`：toMeasureOfLEZero_a
pply (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfLEZero i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMeasureOfLEZero_toSignedMeasure (hs : s ≤[Set.univ] 0) :
    (s.toMeasureOfLEZero Set.univ MeasurableSet.univ hs).toSignedMeasure = -s := by
  ext i hi
  simp [hi, toMeasureOfLEZero_apply _ _ _ hi, measureReal_def]

end SignedMeasure

namespace Measure

open VectorMeasure

variable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Set α)

/-
**MeasureTheory.Measure.zero_le_toSignedMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：zero_le_toSignedMeasure : 0 <= μ.toSignedMeasure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.le_restrict_univ_iff_le`：le_restrict_univ_if
f_le : v <=[Set.univ] w ↔ v <= w
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_of_subset_le`：restrict_
le_restrict_of_subset_le {i : Set α} (h : forall ⦃j⦄, MeasurableSet j -> j subse
teq i -> v j <= w j) : v <=[i] w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem zero_le_toSignedMeasure : 0 ≤ μ.toSignedMeasure := by
  rw [← le_restrict_univ_iff_le]
  refine restrict_le_restrict_of_subset_le _ _ fun j hj₁ _ => ?_
  simp [hj₁]
/-
**MeasureTheory.Measure.toSignedMeasure_toMeasureOfZeroLE** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure`。
形式化陈述：toSignedMeasure_toMeasureOfZeroLE : μ.toSignedMeasure.toMeasureOfZeroLE Se
t.univ MeasurableSet.univ ((le_restrict_univ_iff_le _ _).2 (zero_le_toSignedMeas
ure μ)) = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.VectorMeasure.le_restrict_univ_iff_le`：le_restrict_univ_if
f_le : v <=[Set.univ] w ↔ v <= w
· 使用定理 `MeasureTheory.Measure.zero_le_toSignedMeasure`：zero_le_toSignedMeasure :
 0 <= μ.toSignedMeasure
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply`：toMeasureOfZeroLE_a
pply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfZeroLE i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSignedMeasure_toMeasureOfZeroLE :
    μ.toSignedMeasure.toMeasureOfZeroLE Set.univ MeasurableSet.univ
      ((le_restrict_univ_iff_le _ _).2 (zero_le_toSignedMeasure μ)) = μ := by
  refine Measure.ext fun i hi => ?_
  lift μ i to ℝ≥0 using (measure_lt_top _ _).ne with m hm
  rw [SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hi, ENNReal.coe_inj]
  congr
  simp [hi, ← hm, measureReal_def]
/-
**MeasureTheory.Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：toSignedMeasure_restrict_eq_restrict_toSignedMeasure (hs : MeasurableSet s
) : μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSignedMeasure_restrict_eq_restrict_toSignedMeasure (hs : MeasurableSet s) :
    μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure := by
  ext A hA
  simp [VectorMeasure.restrict_apply, hA, hs]
/-
**MeasureTheory.Measure.toSignedMeasure_le_toSignedMeasure_iff** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：toSignedMeasure_le_toSignedMeasure_iff : μ.toSignedMeasure <= ν.toSignedMe
asure ↔ μ <= ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `MeasureTheory.VectorMeasure.le_iff`：le_iff : v <= w ↔ forall i, Measurab
leSet i -> v i <= w i
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_apply_measurable`：toSignedMeasure_
apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α} (hi : Measurabl
eSet i) : μ.toSignedMeasure i = μ.real i
· 使用定理 `MeasureTheory.Measure.real_def`：∀ {α : Type u_6} {m : MeasurableSpace α}
 (μ : MeasureTheory.Measure α) (s : Set α), μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem toSignedMeasure_le_toSignedMeasure_iff :
    μ.toSignedMeasure ≤ ν.toSignedMeasure ↔ μ ≤ ν := by
  rw [Measure.le_iff, VectorMeasure.le_iff]
  congrm ∀ s, (hs : MeasurableSet s) → ?_
  simp_rw [toSignedMeasure_apply_measurable hs, real_def]
  apply ENNReal.toReal_le_toReal <;> finiteness

end Measure

end MeasureTheory

