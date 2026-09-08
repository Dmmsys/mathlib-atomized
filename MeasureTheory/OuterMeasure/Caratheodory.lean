/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.OfFunction
public import Mathlib.MeasureTheory.PiSystem

/-!
# The Carathéodory σ-algebra of an outer measure

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `MeasureTheory.OuterMeasure.caratheodory` is the Carathéodory-measurable space
  of an outer measure.

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

Carathéodory-measurable, Carathéodory's criterion

-/

@[expose] public section

noncomputable section

open Set Function Filter
open scoped NNReal Topology ENNReal

namespace MeasureTheory
namespace OuterMeasure

section CaratheodoryMeasurable

universe u

variable {α : Type u} (m : OuterMeasure α)

attribute [local simp] Set.inter_comm Set.inter_left_comm Set.inter_assoc

variable {s s₁ s₂ : Set α}

/-- A set `s` is Carathéodory-measurable for an outer measure `m` if for all sets `t` we have
  `m t = m (t ∩ s) + m (t \ s)`. -/
/-
**MeasureTheory.OuterMeasure.IsCaratheodory** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTh
eory.OuterMeasure`。
形式化陈述：IsCaratheodory (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is Carathéodory-measurable for an outer measure `m` if for all sets `t
` we have
  `m t = m (t ∩ s) + m (t \ s)`.
-/
def IsCaratheodory (s : Set α) : Prop :=
  ∀ t, m t = m (t ∩ s) + m (t \ s)
/-
**MeasureTheory.OuterMeasure.isCaratheodory_iff_le'** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_iff_le' {s : Set α} : IsCaratheodory m s ↔ forall t, m (t i
nter s) + m (t \ s) <= m t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `MeasureTheory.measure_le_inter_add_sdiff`：measure_le_inter_add_sdiff (μ 
: F) (s t : Set α) : μ s <= μ (s inter t) + μ (s \ t)
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
-/
theorem isCaratheodory_iff_le' {s : Set α} :
    IsCaratheodory m s ↔ ∀ t, m (t ∩ s) + m (t \ s) ≤ m t :=
  forall_congr' fun _ => le_antisymm_iff.trans <| and_iff_right <| measure_le_inter_add_sdiff _ _ _

@[simp]
/-
**MeasureTheory.OuterMeasure.isCaratheodory_empty** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_empty : IsCaratheodory m ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isCaratheodory_empty : IsCaratheodory m ∅ := by simp [IsCaratheodory, sdiff_empty]
/-
**MeasureTheory.OuterMeasure.isCaratheodory_compl** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_compl : IsCaratheodory m s₁ -> IsCaratheodory m s₁ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem isCaratheodory_compl : IsCaratheodory m s₁ → IsCaratheodory m s₁ᶜ := by
  simp [IsCaratheodory, sdiff_eq, add_comm]

@[simp]
/-
**MeasureTheory.OuterMeasure.isCaratheodory_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_compl_iff : IsCaratheodory m sᶜ ↔ IsCaratheodory m s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_compl`：isCaratheodory_compl : 
IsCaratheodory m s₁ -> IsCaratheodory m s₁ᶜ
-/
theorem isCaratheodory_compl_iff : IsCaratheodory m sᶜ ↔ IsCaratheodory m s :=
  ⟨fun h => by simpa using isCaratheodory_compl m h, isCaratheodory_compl m⟩
/-
**MeasureTheory.OuterMeasure.isCaratheodory_union** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_union (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂)
 : IsCaratheodory m (s₁ union s₂)
参数：h₁ : IsCaratheodory m s₁；h₂ : IsCaratheodory m s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.inter_sdiff_assoc`：inter_sdiff_assoc (a b c : Set α) : (a inter b) \
 c = a inter (b \ c)
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.union_sdiff_left`：union_sdiff_left {s t : Set α} : (s union t) \ s =
 t \ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_left_comm`：inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ inter (s₂ i
nter s₃) = s₂ inter (s₁ inter s₃)
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isCaratheodory_union (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) :
    IsCaratheodory m (s₁ ∪ s₂) := fun t => by
  rw [h₁ t, h₂ (t ∩ s₁), h₂ (t \ s₁), h₁ (t ∩ (s₁ ∪ s₂)), inter_sdiff_assoc _ _ s₁,
    Set.inter_assoc _ _ s₁, inter_eq_self_of_subset_right Set.subset_union_left,
    union_sdiff_left, h₂ (t ∩ s₁)]
  simp [sdiff_eq, add_assoc]

variable {m} in
/-
**MeasureTheory.OuterMeasure.IsCaratheodory.biUnion_of_finite** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.OuterMeasure.IsCaratheodory`。
形式化陈述：∀ {α : Type u} {m : MeasureTheory.OuterMeasure α} {ι : Type u_1} {s : ι → 
Set α} {t : Set ι},   t.Finite → (∀ i ∈ t, m.IsCaratheodory (s i)) → m.IsCarathe
odory (⋃ i ∈ t, s i)
参数：∀ i ∈ t, m.IsCaratheodory (s i)；⋃ i ∈ t, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_union`：isCaratheodory_union (h
₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) : IsCaratheodory m (s₁ union
 s₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma IsCaratheodory.biUnion_of_finite {ι : Type*} {s : ι → Set α} {t : Set ι} (ht : t.Finite)
    (h : ∀ i ∈ t, m.IsCaratheodory (s i)) :
    m.IsCaratheodory (⋃ i ∈ t, s i) := by
  classical
  lift t to Finset ι using ht
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    simp only [Finset.mem_coe, Finset.mem_insert, iUnion_iUnion_eq_or_left] at h ⊢
    exact m.isCaratheodory_union (h _ <| Or.inl rfl) (IH fun _ hj ↦ h _ <| Or.inr hj)
/-
**MeasureTheory.OuterMeasure.measure_inter_union** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.OuterMeasure`。
形式化陈述：measure_inter_union (h : s₁ inter s₂ subseteq ∅) (h₁ : IsCaratheodory m s₁
) {t : Set α} : m (t inter (s₁ union s₂)) = m (t inter s₁) + m (t inter s₂)
参数：h : s₁ inter s₂ subseteq ∅；h₁ : IsCaratheodory m s₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.union_inter_cancel_left`：union_inter_cancel_left {s t : Set α} : (s 
union t) inter s = s
· 使用引理 `Set.inter_sdiff_assoc`：inter_sdiff_assoc (a b c : Set α) : (a inter b) \
 c = a inter (b \ c)
· 使用定理 `Set.union_sdiff_cancel_left`：union_sdiff_cancel_left {s t : Set α} (h : 
s inter t subseteq ∅) : (s union t) \ s = t
-/
theorem measure_inter_union (h : s₁ ∩ s₂ ⊆ ∅) (h₁ : IsCaratheodory m s₁) {t : Set α} :
    m (t ∩ (s₁ ∪ s₂)) = m (t ∩ s₁) + m (t ∩ s₂) := by
  rw [h₁, Set.inter_assoc, Set.union_inter_cancel_left, inter_sdiff_assoc,
    union_sdiff_cancel_left h]
/-
**MeasureTheory.OuterMeasure.isCaratheodory_iUnion_lt** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.OuterMeasure`。
形式化陈述：∀ {α : Type u} (m : MeasureTheory.OuterMeasure α) {s : ℕ → Set α} {n : ℕ},
   (∀ i < n, m.IsCaratheodory (s i)) → m.IsCaratheodory (⋃ i, ⋃ (_ : i < n), s i
)
参数：m : MeasureTheory.OuterMeasure α；∀ i < n, m.IsCaratheodory (s i)；⋃ i, ⋃ (_ : 
i < n), s i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isCaratheodory_iUnion_lt {s : ℕ → Set α} :
    ∀ {n : ℕ}, (∀ i < n, IsCaratheodory m (s i)) → IsCaratheodory m (⋃ i < n, s i)
  | 0, _ => by simp
  | n + 1, h => by
    rw [biUnion_lt_succ]
    exact isCaratheodory_union m
            (isCaratheodory_iUnion_lt fun i hi => h i <| lt_of_lt_of_le hi <| Nat.le_succ _)
            (h n (le_refl (n + 1)))
/-
**MeasureTheory.OuterMeasure.isCaratheodory_inter** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_inter (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂)
 : IsCaratheodory m (s₁ inter s₂)
参数：h₁ : IsCaratheodory m s₁；h₂ : IsCaratheodory m s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_compl_iff`：isCaratheodory_comp
l_iff : IsCaratheodory m sᶜ ↔ IsCaratheodory m s
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_union`：isCaratheodory_union (h
₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) : IsCaratheodory m (s₁ union
 s₂)
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_compl`：isCaratheodory_compl : 
IsCaratheodory m s₁ -> IsCaratheodory m s₁ᶜ
-/
theorem isCaratheodory_inter (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) :
    IsCaratheodory m (s₁ ∩ s₂) := by
  rw [← isCaratheodory_compl_iff, Set.compl_inter]
  exact isCaratheodory_union _ (isCaratheodory_compl _ h₁) (isCaratheodory_compl _ h₂)
/-
**MeasureTheory.OuterMeasure.isCaratheodory_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_sdiff (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂)
 : IsCaratheodory m (s₁ \ s₂)
参数：h₁ : IsCaratheodory m s₁；h₂ : IsCaratheodory m s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_inter`：isCaratheodory_inter (h
₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) : IsCaratheodory m (s₁ inter
 s₂)
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_compl`：isCaratheodory_compl : 
IsCaratheodory m s₁ -> IsCaratheodory m s₁ᶜ
-/
lemma isCaratheodory_sdiff (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) :
    IsCaratheodory m (s₁ \ s₂) := m.isCaratheodory_inter h₁ (m.isCaratheodory_compl h₂)

@[deprecated (since := "2026-06-03")] alias isCaratheodory_diff := isCaratheodory_sdiff
/-
**MeasureTheory.OuterMeasure.isCaratheodory_partialSups** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_partialSups {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot
 ι] {s : ι -> Set α} (h : forall i, m.IsCaratheodory (s i)) (i : ι) : m.IsCarath
eodory (partialSups s i)
参数：h : forall i, m.IsCaratheodory (s i)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `MeasureTheory.OuterMeasure.IsCaratheodory.biUnion_of_finite`：∀ {α : Type
 u} {m : MeasureTheory.OuterMeasure α} {ι : Type u_1} {s : ι → Set α} {t : Set ι
},   t.Finite → (∀ i ∈ t, m.IsCaratheodory (s i))…
· 使用定理 `Set.finite_Iic`：∀ {α : Type u_1} [inst : Preorder α] [LocallyFiniteOrder
Bot α] (a : α), (Set.Iic a).Finite
-/
lemma isCaratheodory_partialSups {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    {s : ι → Set α} (h : ∀ i, m.IsCaratheodory (s i)) (i : ι) :
    m.IsCaratheodory (partialSups s i) := by
  simpa only [partialSups_apply, Finset.sup'_eq_sup, Finset.sup_set_eq_biUnion, ← Finset.mem_coe,
    Finset.coe_Iic] using .biUnion_of_finite (finite_Iic _) (fun j _ ↦ h j)
/-
**MeasureTheory.OuterMeasure.isCaratheodory_disjointed** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_disjointed {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot 
ι] {s : ι -> Set α} (h : forall i, m.IsCaratheodory (s i)) (i : ι) : m.IsCarathe
odory (disjointed s i)
参数：h : forall i, m.IsCaratheodory (s i)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `disjointedRec`：disjointedRec {f : ι -> α} {p : α -> Prop} (hdiff : foral
l ⦃t i⦄, p t -> p (t \ f i)) : forall ⦃i⦄, p (f i) -> p (disjointed f i)
· 使用引理 `MeasureTheory.OuterMeasure.isCaratheodory_sdiff`：isCaratheodory_sdiff (h
₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) : IsCaratheodory m (s₁ \ s₂)
-/
lemma isCaratheodory_disjointed {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    {s : ι → Set α} (h : ∀ i, m.IsCaratheodory (s i)) (i : ι) :
    m.IsCaratheodory (disjointed s i) :=
  disjointedRec (fun _ j ht ↦ m.isCaratheodory_sdiff ht <| h j) (h i)
/-
**MeasureTheory.OuterMeasure.isCaratheodory_sum** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.OuterMeasure`。
形式化陈述：∀ {α : Type u} (m : MeasureTheory.OuterMeasure α) {s : ℕ → Set α},   (∀ (i
 : ℕ), m.IsCaratheodory (s i)) →     Pairwise (Function.onFun Disjoint s) →     
  ∀ {t : Set α} {n : ℕ}, ∑ i ∈ Finset.range n, m (t ∩ s i) = m (t ∩ ⋃ i, ⋃ (_ : 
i < n), s i)
参数：m : MeasureTheory.OuterMeasure α；∀ (i : ℕ), m.IsCaratheodory (s i)；Function.o
nFun Disjoint s；t ∩ s i；t ∩ ⋃ i, ⋃ (_ : i < n), s i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isCaratheodory_sum {s : ℕ → Set α} (h : ∀ i, IsCaratheodory m (s i))
    (hd : Pairwise (Disjoint on s)) {t : Set α} :
    ∀ {n}, (∑ i ∈ Finset.range n, m (t ∩ s i)) = m (t ∩ ⋃ i < n, s i)
  | 0 => by simp
  | Nat.succ n => by
    rw [biUnion_lt_succ, Finset.sum_range_succ, Set.union_comm, isCaratheodory_sum h hd,
      m.measure_inter_union _ (h n), add_comm]
    intro a
    simpa using fun (h₁ : a ∈ s n) i (hi : i < n) h₂ => (hd (ne_of_gt hi)).le_bot ⟨h₁, h₂⟩

/-- Use `isCaratheodory_iUnion` instead, which does not require the disjoint assumption. -/
/-
**MeasureTheory.OuterMeasure.isCaratheodory_iUnion_of_disjoint** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_iUnion_of_disjoint {s : Nat -> Set α} (h : forall i, IsCara
theodory m (s i)) (hd : Pairwise (Disjoint on s)) : IsCaratheodory m (⋃ i, s i)
参数：h : forall i, IsCaratheodory m (s i)；hd : Pairwise (Disjoint on s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_iff_le'`：isCaratheodory_iff_le
' {s : Set α} : IsCaratheodory m s ↔ forall t, m (t inter s) + m (t \ s) <= m t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.tsum_eq_iSup_nat`：∀ {f : ℕ → ENNReal}, ∑' (i : ℕ), f i = ⨆ i, ∑ 
a ∈ Finset.range i, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_sum`：∀ {α : Type u} (m : Measu
reTheory.OuterMeasure α) {s : ℕ → Set α},   (∀ (i : ℕ), m.IsCaratheodory (s i)) 
→     Pairwise (Function.onFun Disj…
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `ENNReal.iSup_add`：iSup_add [Nonempty ι] (f : ι -> Real>=0∞) : (⨆ i, f i)
 + a = ⨆ i, f i + a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_iUnion_lt`：∀ {α : Type u} (m :
 MeasureTheory.OuterMeasure α) {s : ℕ → Set α} {n : ℕ},   (∀ i < n, m.IsCaratheo
dory (s i)) → m.IsCaratheodory (⋃ i, ⋃ (_…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
· 使用定理 `Set.iUnion_mono''`：iUnion_mono'' {s t : ι -> Set α} (h : forall i, s i s
ubseteq t i) : iUnion s subseteq iUnion t
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Use `isCaratheodory_iUnion` instead, which does not require the disjoint assumpt
ion.
-/
theorem isCaratheodory_iUnion_of_disjoint {s : ℕ → Set α} (h : ∀ i, IsCaratheodory m (s i))
    (hd : Pairwise (Disjoint on s)) : IsCaratheodory m (⋃ i, s i) := by
  apply (isCaratheodory_iff_le' m).mpr
  intro t
  have hp : m (t ∩ ⋃ i, s i) ≤ ⨆ n, m (t ∩ ⋃ i < n, s i) := by
    convert! measure_iUnion_le (μ := m) fun i => t ∩ s i using 1
    · simp [inter_iUnion]
    · simp [ENNReal.tsum_eq_iSup_nat, isCaratheodory_sum m h hd]
  grw [hp, ENNReal.iSup_add]
  refine iSup_le fun n => ?_
  rw [isCaratheodory_iUnion_lt _ (fun i _ => h i) t (n := n)]
  gcongr with i
  exact iUnion_subset fun _ => .rfl
/-
**MeasureTheory.OuterMeasure.isCaratheodory_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_iUnion {s : Nat -> Set α} (h : forall i, m.IsCaratheodory (
s i)) : m.IsCaratheodory (⋃ i, s i)
参数：h : forall i, m.IsCaratheodory (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_iUnion_of_disjoint`：isCaratheo
dory_iUnion_of_disjoint {s : Nat -> Set α} (h : forall i, IsCaratheodory m (s i)
) (hd : Pairwise (Disjoint on s)) : IsCaratheodory…
· 使用引理 `MeasureTheory.OuterMeasure.isCaratheodory_disjointed`：isCaratheodory_dis
jointed {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι] {s : ι -> Set α} (h :
 forall i, m.IsCaratheodory (s i)) (i : ι)…
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
-/
lemma isCaratheodory_iUnion {s : ℕ → Set α} (h : ∀ i, m.IsCaratheodory (s i)) :
    m.IsCaratheodory (⋃ i, s i) := by
  rw [← iUnion_disjointed]
  exact m.isCaratheodory_iUnion_of_disjoint (m.isCaratheodory_disjointed h)
    (disjoint_disjointed _)
/-
**MeasureTheory.OuterMeasure.f_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：f_iUnion {s : Nat -> Set α} (h : forall i, IsCaratheodory m (s i)) (hd : P
airwise (Disjoint on s)) : m (⋃ i, s i) = ∑' i, m (s i)
参数：h : forall i, IsCaratheodory m (s i)；hd : Pairwise (Disjoint on s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_eq_iSup_nat`：∀ {f : ℕ → ENNReal}, ∑' (i : ℕ), f i = ⨆ i, ∑ 
a ∈ Finset.range i, f a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_sum`：∀ {α : Type u} (m : Measu
reTheory.OuterMeasure α) {s : ℕ → Set α},   (∀ (i : ℕ), m.IsCaratheodory (s i)) 
→     Pairwise (Function.onFun Disj…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
theorem f_iUnion {s : ℕ → Set α} (h : ∀ i, IsCaratheodory m (s i)) (hd : Pairwise (Disjoint on s)) :
    m (⋃ i, s i) = ∑' i, m (s i) := by
  refine le_antisymm (measure_iUnion_le s) ?_
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have := @isCaratheodory_sum _ m _ h hd univ n
  simp only [inter_comm, inter_univ, univ_inter] at this; simp only [this]
  exact m.mono (iUnion₂_subset fun i _ => subset_iUnion _ i)

/-- The Carathéodory-measurable sets for an outer measure `m` form a Dynkin system. -/
/-
**MeasureTheory.OuterMeasure.caratheodoryDynkin** 是 Mathlib 中的一个定义，位于命名空间 `Measu
reTheory.OuterMeasure`。
形式化陈述：caratheodoryDynkin : MeasurableSpace.DynkinSystem α where Has
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_empty`：isCaratheodory_empty : 
IsCaratheodory m ∅
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_compl`：isCaratheodory_compl : 
IsCaratheodory m s₁ -> IsCaratheodory m s₁ᶜ

--- 原说明 ---
The Carathéodory-measurable sets for an outer measure `m` form a Dynkin system.
-/
def caratheodoryDynkin : MeasurableSpace.DynkinSystem α where
  Has := IsCaratheodory m
  has_empty := isCaratheodory_empty m
  has_compl s := isCaratheodory_compl m s
  has_iUnion_nat _ hf hn := by apply isCaratheodory_iUnion m hf

/-- Given an outer measure `μ`, the Carathéodory-measurable space is
  defined such that `s` is measurable if `∀ t, μ t = μ (t ∩ s) + μ (t \ s)`. -/
@[instance_reducible]
/-
**MeasureTheory.OuterMeasure.caratheodory** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.OuterMeasure`。
形式化陈述：{α : Type u} → MeasureTheory.OuterMeasure α → MeasurableSpace α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_inter`：isCaratheodory_inter (h
₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) : IsCaratheodory m (s₁ inter
 s₂)

--- 原说明 ---
Given an outer measure `μ`, the Carathéodory-measurable space is
  defined such that `s` is measurable if `∀ t, μ t = μ (t ∩ s) + μ (t \ s)`.
-/
protected def caratheodory : MeasurableSpace α := by
  apply MeasurableSpace.DynkinSystem.toMeasurableSpace (caratheodoryDynkin m)
  intro s₁ s₂
  apply isCaratheodory_inter
/-
**MeasureTheory.OuterMeasure.isCaratheodory_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.OuterMeasure`。
形式化陈述：isCaratheodory_iff {s : Set α} : MeasurableSet[OuterMeasure.caratheodory m
] s ↔ forall t, m t = m (t inter s) + m (t \ s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCaratheodory_iff {s : Set α} :
    MeasurableSet[OuterMeasure.caratheodory m] s ↔ ∀ t, m t = m (t ∩ s) + m (t \ s) :=
  Iff.rfl
/-
**MeasureTheory.OuterMeasure.isCaratheodory_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.OuterMeasure`。
形式化陈述：isCaratheodory_iff_le {s : Set α} : MeasurableSet[OuterMeasure.caratheodor
y m] s ↔ forall t, m (t inter s) + m (t \ s) <= m t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_iff_le'`：isCaratheodory_iff_le
' {s : Set α} : IsCaratheodory m s ↔ forall t, m (t inter s) + m (t \ s) <= m t
-/
theorem isCaratheodory_iff_le {s : Set α} :
    MeasurableSet[OuterMeasure.caratheodory m] s ↔ ∀ t, m (t ∩ s) + m (t \ s) ≤ m t :=
  isCaratheodory_iff_le' m
/-
**MeasureTheory.OuterMeasure.iUnion_eq_of_caratheodory** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.OuterMeasure`。
形式化陈述：∀ {α : Type u} (m : MeasureTheory.OuterMeasure α) {s : ℕ → Set α},   (∀ (i
 : ℕ), MeasurableSet (s i)) → Pairwise (Function.onFun Disjoint s) → m (⋃ i, s i
) = ∑' (i : ℕ), m (s i)
参数：m : MeasureTheory.OuterMeasure α；∀ (i : ℕ), MeasurableSet (s i)；Function.onFu
n Disjoint s；⋃ i, s i；i : ℕ；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.f_iUnion`：f_iUnion {s : Nat -> Set α} (h : fo
rall i, IsCaratheodory m (s i)) (hd : Pairwise (Disjoint on s)) : m (⋃ i, s i) =
 ∑' i, m (s i)
-/
protected theorem iUnion_eq_of_caratheodory {s : ℕ → Set α}
    (h : ∀ i, MeasurableSet[OuterMeasure.caratheodory m] (s i)) (hd : Pairwise (Disjoint on s)) :
    m (⋃ i, s i) = ∑' i, m (s i) :=
  f_iUnion m h hd

end CaratheodoryMeasurable

variable {α : Type*}

/-
**MeasureTheory.OuterMeasure.ofFunction_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.OuterMeasure`。
形式化陈述：ofFunction_caratheodory {m : Set α -> Real>=0∞} {s : Set α} {h₀ : m ∅ = 0}
 (hs : forall t, m (t inter s) + m (t \ s) <= m t) : MeasurableSet[(OuterMeasure
.ofFunction m h₀).caratheodory] s
参数：hs : forall t, m (t inter s) + m (t \ s) <= m t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_iff_le`：isCaratheodory_iff_le 
{s : Set α} : MeasurableSet[OuterMeasure.caratheodory m] s ↔ forall t, m (t inte
r s) + m (t \ s) <= m t
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.iUnion_sdiff`：iUnion_sdiff (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 \ s = ⋃ i, t i \ s
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `ENNReal.tsum_add`：∀ {α : Type u_1} {f g : α → ENNReal}, ∑' (a : α), (f a
 + g a) = ∑' (a : α), f a + ∑' (a : α), g a
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
-/
theorem ofFunction_caratheodory {m : Set α → ℝ≥0∞} {s : Set α} {h₀ : m ∅ = 0}
    (hs : ∀ t, m (t ∩ s) + m (t \ s) ≤ m t) :
    MeasurableSet[(OuterMeasure.ofFunction m h₀).caratheodory] s := by
  apply (isCaratheodory_iff_le _).mpr
  refine fun t => le_iInf fun f => le_iInf fun hf => ?_
  refine
    le_trans
      (add_le_add ((iInf_le_of_le fun i => f i ∩ s) <| iInf_le _ ?_)
        ((iInf_le_of_le fun i => f i \ s) <| iInf_le _ ?_))
      ?_
  · rw [← iUnion_inter]
    exact inter_subset_inter_left _ hf
  · rw [← iUnion_sdiff]
    exact sdiff_subset_sdiff_left hf
  · rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun i => hs _
/-
**MeasureTheory.OuterMeasure.boundedBy_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.OuterMeasure`。
形式化陈述：boundedBy_caratheodory {m : Set α -> Real>=0∞} {s : Set α} (hs : forall t,
 m (t inter s) + m (t \ s) <= m t) : MeasurableSet[(boundedBy m).caratheodory] s
参数：hs : forall t, m (t inter s) + m (t \ s) <= m t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_caratheodory`：ofFunction_caratheod
ory {m : Set α -> Real>=0∞} {s : Set α} {h₀ : m ∅ = 0} (hs : forall t, m (t inte
r s) + m (t \ s) <= m t) : MeasurableSet…
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Set.empty_sdiff`：empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iSup_const_le`：iSup_const_le : ⨆ _ : ι, a <= a
-/
theorem boundedBy_caratheodory {m : Set α → ℝ≥0∞} {s : Set α}
    (hs : ∀ t, m (t ∩ s) + m (t \ s) ≤ m t) : MeasurableSet[(boundedBy m).caratheodory] s := by
  apply ofFunction_caratheodory; intro t
  rcases t.eq_empty_or_nonempty with rfl | h
  · simp [Set.not_nonempty_empty]
  · convert! le_trans _ (hs t)
    · simp [h]
    exact add_le_add iSup_const_le iSup_const_le

@[simp]
/-
**MeasureTheory.OuterMeasure.zero_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.OuterMeasure`。
形式化陈述：zero_caratheodory : (0 : OuterMeasure α).caratheodory = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem zero_caratheodory : (0 : OuterMeasure α).caratheodory = ⊤ :=
  top_unique fun _ _ _ => (add_zero _).symm
/-
**MeasureTheory.OuterMeasure.top_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.OuterMeasure`。
形式化陈述：top_caratheodory : (⊤ : OuterMeasure α).caratheodory = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_iff_le`：isCaratheodory_iff_le 
{s : Set α} : MeasurableSet[OuterMeasure.caratheodory m] s ↔ forall t, m (t inte
r s) + m (t \ s) <= m t
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `Set.empty_sdiff`：empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.OuterMeasure.top_apply`：top_apply {s : Set α} (h : s.Nonem
pty) : (⊤ : OuterMeasure α) s = ∞
-/
theorem top_caratheodory : (⊤ : OuterMeasure α).caratheodory = ⊤ :=
  top_unique fun s _ =>
    (isCaratheodory_iff_le _).2 fun t =>
      t.eq_empty_or_nonempty.elim (fun ht => by simp [ht]) fun ht => by
        simp only [ht, top_apply, le_top]
/-
**MeasureTheory.OuterMeasure.le_add_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.OuterMeasure`。
形式化陈述：le_add_caratheodory (m₁ m₂ : OuterMeasure α) : m₁.caratheodory ⊓ m₂.carath
eodory <= (m₁ + m₂ : OuterMeasure α).caratheodory
参数：m₁ m₂ : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.OuterMeasure.instIsAddApplySetENNReal`：∀ {α : Type u_1}, I
sAddApply (MeasureTheory.OuterMeasure α) (Set α) ENNReal
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_add_caratheodory (m₁ m₂ : OuterMeasure α) :
    m₁.caratheodory ⊓ m₂.caratheodory ≤ (m₁ + m₂ : OuterMeasure α).caratheodory :=
  fun s ⟨hs₁, hs₂⟩ t => by simp [hs₁ t, hs₂ t, add_left_comm, add_assoc]
/-
**MeasureTheory.OuterMeasure.le_sum_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.OuterMeasure`。
形式化陈述：le_sum_caratheodory {ι} (m : ι -> OuterMeasure α) : ⨅ i, (m i).caratheodor
y <= (sum m).caratheodory
参数：m : ι -> OuterMeasure α。
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasurableSpace.measurableSet_iInf`：measurableSet_iInf {ι} {m : ι -> Mea
surableSpace α} {s : Set α} : MeasurableSet[iInf m] s ↔ forall i, MeasurableSet[
m i] s
· 使用定理 `ENNReal.tsum_add`：∀ {α : Type u_1} {f g : α → ENNReal}, ∑' (a : α), (f a
 + g a) = ∑' (a : α), f a + ∑' (a : α), g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_sum_caratheodory {ι} (m : ι → OuterMeasure α) :
    ⨅ i, (m i).caratheodory ≤ (sum m).caratheodory := fun s h t => by
  simp [fun i => MeasurableSpace.measurableSet_iInf.1 h i t, ENNReal.tsum_add]
/-
**MeasureTheory.OuterMeasure.le_smul_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.OuterMeasure`。
形式化陈述：le_smul_caratheodory (a : Real>=0∞) (m : OuterMeasure α) : m.caratheodory 
<= (a • m).caratheodory
参数：a : Real>=0∞；m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.OuterMeasure.instIsSMulApplySetENNReal`：∀ {α : Type u_1} {
R : Type u_3} [inst : SMul R ENNReal] [inst_1 : IsScalarTower R ENNReal ENNReal]
,   IsSMulApply R (MeasureTheory.OuterMeas…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.OuterMeasure.isCaratheodory_iff`：isCaratheodory_iff {s : S
et α} : MeasurableSet[OuterMeasure.caratheodory m] s ↔ forall t, m t = m (t inte
r s) + m (t \ s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_smul_caratheodory (a : ℝ≥0∞) (m : OuterMeasure α) :
    m.caratheodory ≤ (a • m).caratheodory := fun s h t => by
      simp only [smul_apply, smul_eq_mul]
      rw [(isCaratheodory_iff m).mp h t]
      simp [mul_add]

@[simp]
/-
**MeasureTheory.OuterMeasure.dirac_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.OuterMeasure`。
形式化陈述：dirac_caratheodory (a : α) : (dirac a).caratheodory = ⊤
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem dirac_caratheodory (a : α) : (dirac a).caratheodory = ⊤ :=
  top_unique fun s _ t => by
    by_cases ht : a ∈ t; swap; · simp [ht]
    by_cases hs : a ∈ s <;> simp [*]

end OuterMeasure

end MeasureTheory

