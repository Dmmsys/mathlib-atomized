/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.Data.ENat.Lattice

/-!
# Stopping times, stopped processes and stopped values

Definition and properties of stopping times.

## Main definitions

* `MeasureTheory.IsStoppingTime`: a stopping time with respect to some filtration `f` on a
  measurable space `Ω` is a function `τ : Ω → WithTop ι` such that for all `i : ι`,
  the preimage of `{j | j ≤ i}` along `τ` is `f i`-measurable
* `MeasureTheory.IsStoppingTime.measurableSpace`: the σ-algebra associated with a stopping time

## Main results

* `IsStronglyProgressive.stoppedProcess`: the stopped process of a progressively measurable process
  is progressively measurable.
* `memLp_stoppedProcess`: if a process belongs to `ℒp` at every time in `ℕ`, then its stopped
  process belongs to `ℒp` as well.

## Implementation notes

For a filtration on a type `ι`, we define stopping times as functions from the measurable space `Ω`
to `WithTop ι`, which allows stopping times that can take an infinite value, represented by
`⊤ : WithTop ι`.

This means that if we have a process `X : ι → Ω → β` and a stopping time `τ : Ω → WithTop ι`, then
to consider the value of `X` at the stopping time `τ ω`, we need to write `X (τ ω).untopA ω`,
in which `(τ ω).untopA` is the value of `τ ω` in `ι` if `τ ω ≠ ⊤` and some arbitrary value if
`τ ω = ⊤`.

While indexing would be more convenient if we defined stopping times as functions from `Ω` to `ι`,
this would prevent us from using stopping times as in standard mathematical literature, where a
typical example of stopping time is the first time an event occurs, which may never happen.
Consider for example the first time a coin lands heads when flipping it infinitely many times:
this is almost surely finite, but possibly infinite. We could also not use a function `Ω → ι` with
arbitrary value for the infinite case, because this would be incompatible with the stopping time
property.

## Tags

stopping time, stochastic process

-/

@[expose] public section

open Filter Order TopologicalSpace WithTop

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

/-! ### Stopping times -/


/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
/-
**MeasureTheory.IsStoppingTime** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：IsStoppingTime [Preorder ι] (f : Filtration ι m) (τ : Ω -> WithTop ι)
参数：f : Filtration ι m；τ : Ω -> WithTop ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at tim
e
`i`, we may determine it with the information we have at time `i`.
-/
def IsStoppingTime [Preorder ι] (f : Filtration ι m) (τ : Ω → WithTop ι) :=
  ∀ i : ι, MeasurableSet[f i] <| {ω | τ ω ≤ i}
/-
**MeasureTheory.isStoppingTime_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：isStoppingTime_const [Preorder ι] (f : Filtration ι m) (i : ι) : IsStoppin
gTime f fun _ => i
参数：f : Filtration ι m；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem isStoppingTime_const [Preorder ι] (f : Filtration ι m) (i : ι) :
    IsStoppingTime f fun _ => i := fun j => by simp only [MeasurableSet.const]

section MeasurableSet

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}

/-
**MeasureTheory.IsStoppingTime.measurableSet_le** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι}, MeasureTheory.IsStop
pingTime f τ → ∀ (i : ι), MeasurableSet {ω | τ ω ≤ ↑i}
参数：i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsStoppingTime.measurableSet_le (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω ≤ i} :=
  hτ i
/-
**MeasureTheory.IsStoppingTime.measurableSet_lt_of_pred** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [PredOrder ι], Measur
eTheory.IsStoppingTime f τ → ∀ (i : ι), MeasurableSet {ω | τ ω < ↑i}
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isMin_iff_forall_not_lt`：isMin_iff_forall_not_lt : IsMin a ↔ forall b, ¬
b < a
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Order.le_pred_iff_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] [in
st_1 : PredOrder α] {a b : α}, ¬IsMin a → (b ≤ Order.pred a ↔ b < a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `Order.pred_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrder 
α] (a : α), Order.pred a ≤ a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration
 ι m}   {τ : Ω → WithTop ι}, Measur…
-/
theorem IsStoppingTime.measurableSet_lt_of_pred [PredOrder ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} := by
  by_cases hi_min : IsMin i
  · suffices {ω : Ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rw [isMin_iff_forall_not_lt] at hi_min
    cases τ ω with
    | top => simp
    | coe t => exact mod_cast hi_min t
  have : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iic (pred i : ι) := by
    ext ω
    push _ ∈ _
    cases τ ω with
    | top => simp
    | coe t =>
      simp only [coe_lt_coe, coe_le_coe]
      rw [le_pred_iff_of_not_isMin hi_min]
  rw [this]
  exact f.mono (pred_le i) _ (hτ.measurableSet_le <| pred i)

end Preorder

section CountableStoppingTime

namespace IsStoppingTime

variable [PartialOrder ι] {τ : Ω → WithTop ι} {f : Filtration ι m}

/-
**MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : PartialOrd
er ι] {τ : Ω → WithTop ι}   {f : MeasureTheory.Filtration ι m},   MeasureTheory.
IsStoppingTime f τ → (Set.range τ).Countable → ∀ (i : ι), MeasurableSet {ω | τ ω
 = ↑i}
参数：Set.range τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration
 ι m}   {τ : Ω → WithTop ι}, Measur…
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
· 使用定理 `Set.iUnion_eq_if`：iUnion_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋃ 
_ : p, s = if p then s else ∅
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
（共 31 条，此处仅展示前 30 条）
-/
protected theorem measurableSet_eq_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) : MeasurableSet[f i] {ω | τ ω = i} := by
  have : {ω | τ ω = i} = {ω | τ ω ≤ i} \ ⋃ (j ∈ Set.range τ) (_ : j < i), {ω | τ ω ≤ j} := by
    ext1 a
    simp only [Set.mem_ofPred_eq, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]
    constructor <;> intro h
    · simp only [h, lt_iff_le_not_ge, le_refl, and_imp, imp_self, imp_true_iff, and_self_iff]
    · exact h.1.eq_or_lt.resolve_right fun h_lt => h.2 a h_lt le_rfl
  rw [this]
  refine (hτ.measurableSet_le i).diff ?_
  refine MeasurableSet.biUnion h_countable fun j _ => ?_
  classical
  rw [Set.iUnion_eq_if]
  split_ifs with hji
  · lift j to ι using (ne_top_of_lt hji)
    exact f.mono (mod_cast hji.le) _ (hτ.measurableSet_le j)
  · exact @MeasurableSet.empty _ (f i)
/-
**MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : PartialOrd
er ι] {τ : Ω → WithTop ι}   {f : MeasureTheory.Filtration ι m} [Countable ι],   
MeasureTheory.IsStoppingTime f τ → ∀ (i : ι), MeasurableSet {ω | τ ω = ↑i}
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range`：∀ {Ω :
 Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : PartialOrder ι] {τ : Ω
 → WithTop ι}   {f : MeasureTheory.Filtration ι m},   …
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
protected theorem measurableSet_eq_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω = i} :=
  hτ.measurableSet_eq_of_countable_range (Set.to_countable _) i
/-
**MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable_range** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : PartialOrd
er ι] {τ : Ω → WithTop ι}   {f : MeasureTheory.Filtration ι m},   MeasureTheory.
IsStoppingTime f τ → (Set.range τ).Countable → ∀ (i : ι), MeasurableSet {ω | τ ω
 < ↑i}
参数：Set.range τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration
 ι m}   {τ : Ω → WithTop ι}, Measur…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range`：∀ {Ω :
 Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : PartialOrder ι] {τ : Ω
 → WithTop ι}   {f : MeasureTheory.Filtration ι m},   …
-/
protected theorem measurableSet_lt_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) : MeasurableSet[f i] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i} := by ext1 ω; simp [lt_iff_le_and_ne]
  rw [this]
  exact (hτ.measurableSet_le i).diff (hτ.measurableSet_eq_of_countable_range h_countable i)
/-
**MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : PartialOrd
er ι] {τ : Ω → WithTop ι}   {f : MeasureTheory.Filtration ι m} [Countable ι],   
MeasureTheory.IsStoppingTime f τ → ∀ (i : ι), MeasurableSet {ω | τ ω < ↑i}
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable_range`：∀ {Ω :
 Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : PartialOrder ι] {τ : Ω
 → WithTop ι}   {f : MeasureTheory.Filtration ι m},   …
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
protected theorem measurableSet_lt_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} :=
  hτ.measurableSet_lt_of_countable_range (Set.to_countable _) i
/-
**MeasureTheory.IsStoppingTime.measurableSet_ge_of_countable_range** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} {ι : Type u_4} [inst : LinearOrde
r ι] {τ : Ω → WithTop ι}   {f : MeasureTheory.Filtration ι m},   MeasureTheory.I
sStoppingTime f τ → (Set.range τ).Countable → ∀ (i : ι), MeasurableSet {ω | ↑i ≤
 τ ω}
参数：Set.range τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable_range`：∀ {Ω :
 Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : PartialOrder ι] {τ : Ω
 → WithTop ι}   {f : MeasureTheory.Filtration ι m},   …
-/
protected theorem measurableSet_ge_of_countable_range {ι} [LinearOrder ι] {τ : Ω → WithTop ι}
    {f : Filtration ι m} (hτ : IsStoppingTime f τ) (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt_of_countable_range h_countable i).compl
/-
**MeasureTheory.IsStoppingTime.measurableSet_ge_of_countable** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} {ι : Type u_4} [inst : LinearOrde
r ι] {τ : Ω → WithTop ι}   {f : MeasureTheory.Filtration ι m} [Countable ι],   M
easureTheory.IsStoppingTime f τ → ∀ (i : ι), MeasurableSet {ω | ↑i ≤ τ ω}
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_ge_of_countable_range`：∀ {Ω :
 Type u_1} {m : MeasurableSpace Ω} {ι : Type u_4} [inst : LinearOrder ι] {τ : Ω 
→ WithTop ι}   {f : MeasureTheory.Filtration ι m},   M…
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
protected theorem measurableSet_ge_of_countable {ι} [LinearOrder ι] {τ : Ω → WithTop ι}
    {f : Filtration ι m} [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} :=
  hτ.measurableSet_ge_of_countable_range (Set.to_countable _) i

end IsStoppingTime

end CountableStoppingTime

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}

/-
**MeasureTheory.IsStoppingTime.measurableSet_gt** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι}, MeasureTheory.IsS
toppingTime f τ → ∀ (i : ι), MeasurableSet {ω | ↑i < τ ω}
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration
 ι m}   {τ : Ω → WithTop ι}, Measur…
-/
theorem IsStoppingTime.measurableSet_gt (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i < τ ω} := by
  have : {ω | i < τ ω} = {ω | τ ω ≤ i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  rw [this]
  exact (hτ.measurableSet_le i).compl

section TopologicalSpace

variable [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]

/-- Auxiliary lemma for `MeasureTheory.IsStoppingTime.measurableSet_lt`. -/
/-
**MeasureTheory.IsStoppingTime.measurableSet_lt_of_isLUB** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [FirstCountableTopology ι],   MeasureTheory.IsStop
pingTime f τ → ∀ (i : ι), IsLUB (Set.Iio i) i → MeasurableSet {ω | τ ω < ↑i}
参数：i : ι；Set.Iio i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isMin_iff_forall_not_lt`：isMin_iff_forall_not_lt : IsMin a ↔ forall b, ¬
b < a
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `IsLUB.exists_seq_monotone_tendsto`：IsLUB.exists_seq_monotone_tendsto {t 
: Set α} {x : α} [IsCountablyGenerated (𝓝 x)] (htx : IsLUB t x) (ht : t.Nonempty
) : exists u : Nat -> α…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `not_isMin_iff`：not_isMin_iff : ¬IsMin a ↔ exists b, b < a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.Ioi_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ici b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.tendsto_atTop'`：tendsto_atTop' : Tendsto f atTop l ↔ forall s in 
l, exists a, forall b, a <= b -> f b in s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `MeasureTheory.IsStoppingTime.measurableSet_lt`.
-/
theorem IsStoppingTime.measurableSet_lt_of_isLUB (hτ : IsStoppingTime f τ) (i : ι)
    (h_lub : IsLUB (Set.Iio i) i) : MeasurableSet[f i] {ω | τ ω < i} := by
  by_cases hi_min : IsMin i
  · suffices {ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    cases τ ω with
    | top => simp
    | coe t => norm_cast; exact isMin_iff_forall_not_lt.mp hi_min t
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ :
      ∃ seq : ℕ → ι, Monotone seq ∧ (∀ j, seq j ≤ i) ∧ Tendsto seq atTop (𝓝 i) ∧ ∀ j, seq j < i :=
    h_lub.exists_seq_monotone_tendsto (not_isMin_iff.mp hi_min)
  have h_Iio_eq_Union : Set.Iio (i : WithTop ι) = ⋃ j, {k : WithTop ι | k ≤ seq j} := by
    ext1 k
    push _ ∈ _
    refine ⟨fun hk_lt_i => ?_, fun h_exists_k_le_seq => ?_⟩
    · rw [tendsto_atTop'] at h_tendsto
      cases k with
      | top => simp at hk_lt_i
      | coe k =>
        norm_cast at hk_lt_i ⊢
        have h_nhds : Set.Ici k ∈ 𝓝 i :=
          mem_nhds_iff.mpr ⟨Set.Ioi k, Set.Ioi_subset_Ici le_rfl, isOpen_Ioi, hk_lt_i⟩
        obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ b : ℕ, b ≥ a → k ≤ seq b := h_tendsto (Set.Ici k) h_nhds
        exact ⟨a, ha a le_rfl⟩
    · obtain ⟨j, hk_seq_j⟩ := h_exists_k_le_seq
      exact hk_seq_j.trans_lt (mod_cast h_bound j)
  have h_lt_eq_preimage : {ω | τ ω < i} = τ ⁻¹' Set.Iio i := by
    ext1 ω; push _ ∈ _; rfl
  rw [h_lt_eq_preimage, h_Iio_eq_Union]
  simp only [Set.preimage_iUnion, Set.preimage_ofPred_eq]
  exact MeasurableSet.iUnion fun n => f.mono (h_bound n).le _ (hτ.measurableSet_le (seq n))
/-
**MeasureTheory.IsStoppingTime.measurableSet_lt** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [FirstCountableTopology ι],   MeasureTheory.IsStop
pingTime f τ → ∀ (i : ι), MeasurableSet {ω | τ ω < ↑i}
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lub_Iio`：exists_lub_Iio (i : γ) : exists j, IsLUB (Iio i) j
· 使用定理 `lub_Iio_eq_self_or_Iio_eq_Iic`：lub_Iio_eq_self_or_Iio_eq_Iic [PartialOrd
er γ] {j : γ} (i : γ) (hj : IsLUB (Iio i) j) : j = i ∨ Iio i = Iic j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_lt_of_isLUB`：∀ {Ω : Type u_1}
 {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheor
y.Filtration ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `WithTop.image_coe_Iio`：image_coe_Iio : (some : α -> WithTop α) '' Iio a 
= Iio (a : WithTop α)
· 使用定理 `WithTop.image_coe_Iic`：image_coe_Iic : (some : α -> WithTop α) '' Iic a 
= Iic (a : WithTop α)
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `le_of_isLUB_Iio`：le_of_isLUB_Iio (a : α) (hb : IsLUB (Iio a) b) : b <= a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration
 ι m}   {τ : Ω → WithTop ι}, Measur…
-/
theorem IsStoppingTime.measurableSet_lt (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} := by
  obtain ⟨i', hi'_lub⟩ : ∃ i', IsLUB (Set.Iio i) i' := exists_lub_Iio i
  rcases lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i | h_Iio_eq_Iic
  · rw [← hi'_eq_i] at hi'_lub ⊢
    exact hτ.measurableSet_lt_of_isLUB i' hi'_lub
  · have h_lt_eq_preimage : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iio i := rfl
    have h_Iio_eq_Iic' : Set.Iio (i : WithTop ι) = Set.Iic (i' : WithTop ι) := by
      rw [← image_coe_Iio, ← image_coe_Iic, h_Iio_eq_Iic]
    rw [h_lt_eq_preimage, h_Iio_eq_Iic']
    exact f.mono (le_of_isLUB_Iio i hi'_lub) _ (hτ.measurableSet_le i')
/-
**MeasureTheory.IsStoppingTime.measurableSet_ge** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [FirstCountableTopology ι],   MeasureTheory.IsStop
pingTime f τ → ∀ (i : ι), MeasurableSet {ω | ↑i ≤ τ ω}
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_lt`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
-/
theorem IsStoppingTime.measurableSet_ge (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt i).compl
/-
**MeasureTheory.IsStoppingTime.measurableSet_eq** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [FirstCountableTopology ι],   MeasureTheory.IsStop
pingTime f τ → ∀ (i : ι), MeasurableSet {ω | τ ω = ↑i}
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration
 ι m}   {τ : Ω → WithTop ι}, Measur…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_ge`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
-/
theorem IsStoppingTime.measurableSet_eq (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω = i} := by
  have : {ω | τ ω = i} = {ω | τ ω ≤ i} ∩ {ω | τ ω ≥ i} := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, le_antisymm_iff]
  rw [this]
  exact (hτ.measurableSet_le i).inter (hτ.measurableSet_ge i)
/-
**MeasureTheory.IsStoppingTime.measurableSet_eq_le** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [FirstCountableTopology ι],   MeasureTheory.IsStop
pingTime f τ → ∀ {i j : ι}, i ≤ j → MeasurableSet {ω | τ ω = ↑i}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
-/
theorem IsStoppingTime.measurableSet_eq_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    MeasurableSet[f j] {ω | τ ω = i} :=
  f.mono hle _ <| hτ.measurableSet_eq i
/-
**MeasureTheory.IsStoppingTime.measurableSet_lt_le** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [FirstCountableTopology ι],   MeasureTheory.IsStop
pingTime f τ → ∀ {i j : ι}, i ≤ j → MeasurableSet {ω | τ ω < ↑i}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_lt`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
-/
theorem IsStoppingTime.measurableSet_lt_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    MeasurableSet[f j] {ω | τ ω < i} :=
  f.mono hle _ <| hτ.measurableSet_lt i

end TopologicalSpace

end LinearOrder

section Countable

/-
**MeasureTheory.isStoppingTime_of_measurableSet_eq** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：isStoppingTime_of_measurableSet_eq [Preorder ι] [Countable ι] {f : Filtrat
ion ι m} {τ : Ω -> WithTop ι} (hτ : forall i, MeasurableSet[f i] {ω | τ ω = i}) 
: IsStoppingTime f τ
参数：hτ : forall i, MeasurableSet[f i] {ω | τ ω = i}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
-/
theorem isStoppingTime_of_measurableSet_eq [Preorder ι] [Countable ι] {f : Filtration ι m}
    {τ : Ω → WithTop ι} (hτ : ∀ i, MeasurableSet[f i] {ω | τ ω = i}) : IsStoppingTime f τ := by
  intro i
  have h_eq_iUnion : {ω | τ ω ≤ i} = ⋃ k ≤ i, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp
  rw [h_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun k hk => ?_
  exact f.mono hk _ (hτ k)

end Countable

section IsRightContinuous

open Filtration

variable [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] {f : Filtration ι m} {τ : Ω → WithTop ι}

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous'** 是 Mat
hlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：isStoppingTime_of_measurableSet_lt_of_isRightContinuous' [hf : f.IsRightCo
ntinuous] (hτ1 : forall i, MeasurableSet[f i] {ω | τ ω < i}) (hτ2 : forall i, 𝓝[
>] i = ⊥ -> MeasurableSet[f i] {ω | τ ω = i}) : IsStoppingTime f τ
参数：hτ1 : forall i, MeasurableSet[f i] {ω | τ ω < i}；hτ2 : forall i, 𝓝[>] i = ⊥ -
> MeasurableSet[f i] {ω | τ ω = i}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
· 使用定理 `Filter.exists_seq_forall_of_frequently`：exists_seq_forall_of_frequently 
{ι : Type*} {l : Filter ι} {p : ι -> Prop} [l.IsCountablyGenerated] (h : existsᶠ
 n in l, p n) : exists ns : …
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually_lt_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用引理 `WithTop.continuous_coe`：continuous_coe : Continuous ((↑) : ι -> WithTop 
ι)
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `MeasureTheory.Filtration.IsRightContinuous.eq`：∀ {Ω : Type u_1} {ι : Typ
e u_2} {m : MeasurableSpace Ω} [inst : PartialOrder ι] {𝓕 : MeasureTheory.Filtra
tion ι m}   [h : 𝓕.IsRightContinuou…
· 使用引理 `MeasureTheory.Filtration.rightCont_eq_of_neBot_nhdsGT`：rightCont_eq_of_n
eBot_nhdsGT [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtrat
ion ι m) (i : ι) [(𝓝[>] i).NeBot] : 𝓕₊ i = …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
（共 45 条，此处仅展示前 30 条）
-/
lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous' [hf : f.IsRightContinuous]
    (hτ1 : ∀ i, MeasurableSet[f i] {ω | τ ω < i})
    (hτ2 : ∀ i, 𝓝[>] i = ⊥ → MeasurableSet[f i] {ω | τ ω = i}) :
    IsStoppingTime f τ := by
  intro t
  by_cases ht : 𝓝[>] t = ⊥
  · have h_eq : {ω | τ ω ≤ t} = {ω | τ ω < t} ∪ {ω | τ ω = t} := by ext; grind
    rw [h_eq]
    exact (hτ1 t).union (hτ2 t ht)
  have : (𝓝[>] t).NeBot := ⟨ht⟩
  -- now `t` is a limit point on the right
  obtain ⟨s, hs_gt, hs_tendsto⟩ : ∃ s : ℕ → ι, (∀ n, t < s n) ∧ Tendsto s atTop (𝓝 t) := by
    have h_freq : ∃ᶠ x in 𝓝[>] t, t < x :=
      Eventually.frequently <| eventually_nhdsWithin_of_forall fun _ hx ↦ hx
    have := exists_seq_forall_of_frequently h_freq
    simp_rw [tendsto_nhdsWithin_iff] at this
    obtain ⟨s, ⟨hs_tendsto, _⟩, hs_gt⟩ := this
    exact ⟨s, hs_gt, hs_tendsto⟩
  have h_exists_lt (u : ι) (hu : t < u) : ∃ i, s i < u :=
    Eventually.exists (f := atTop) (hs_tendsto.eventually_lt_const hu)
  have h_exists_lt' (u : WithTop ι) (hu : t < u) : ∃ i, s i < u := by
    refine Eventually.exists (f := atTop) ?_
    have hs_tendsto' : Tendsto (fun n ↦ (s n : WithTop ι)) atTop (𝓝 (t : WithTop ι)) :=
      WithTop.continuous_coe.continuousAt.tendsto.comp hs_tendsto
    exact hs_tendsto'.eventually_lt_const hu
  -- we write `{τ ≤ t}` as a countable intersection of `{τ < s n}`
  have h_eq_iInter : {ω | τ ω ≤ t} = ⋂ m, {ω | τ ω < s m} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun h_le m ↦ h_le.trans_lt (mod_cast (hs_gt m)), fun h_lt ↦ ?_⟩
    refine le_of_forall_gt fun u hu ↦ ?_
    obtain ⟨i, hi⟩ : ∃ i, s i < u := h_exists_lt' u hu
    exact (h_lt i).trans hi
  rw [h_eq_iInter]
  have h𝓕_eq_iInf : f t = ⨅ m, f (s m) := by
    nth_rw 1 [← hf.eq, Filtration.rightCont_eq_of_neBot_nhdsGT]
    refine le_antisymm ?_ ?_
    · simp only [gt_iff_lt, le_iInf_iff]
      exact fun i ↦ iInf₂_le (s i) (hs_gt i)
    · simp only [gt_iff_lt, le_iInf_iff]
      intro i hti
      obtain ⟨m, hm⟩ := h_exists_lt i hti
      exact (iInf_le _ m).trans (f.mono hm.le)
  rw [h𝓕_eq_iInf]
  simp only [MeasurableSpace.measurableSet_sInf, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff]
  intro k
  have h_eq_k : ⋂ m, {ω | τ ω < s m} = ⋂ (m) (hm : s m ≤ s k), {ω | τ ω < s m} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h m _ ↦ h m, fun h m ↦ ?_⟩
    rcases le_total (s m) (s k) with hmk | hkm
    · exact h m hmk
    · exact (h k le_rfl).trans_le (mod_cast hkm)
  rw [h_eq_k]
  exact MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun hm ↦ f.mono hm _ (hτ1 (s m))
/-
**MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：isStoppingTime_of_measurableSet_lt_of_isRightContinuous [DenselyOrdered ι]
 [NoMaxOrder ι] {τ : Ω -> WithTop ι} [f.IsRightContinuous] (hτ : forall i, Measu
rableSet[f i] {ω | τ ω < i}) : IsStoppingTime f τ
参数：hτ : forall i, MeasurableSet[f i] {ω | τ ω < i}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous'`：
isStoppingTime_of_measurableSet_lt_of_isRightContinuous' [hf : f.IsRightContinuo
us] (hτ1 : forall i, MeasurableSet[f i] {ω | τ ω < i}) (hτ2 …
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
-/
lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous [DenselyOrdered ι] [NoMaxOrder ι]
    {τ : Ω → WithTop ι} [f.IsRightContinuous] (hτ : ∀ i, MeasurableSet[f i] {ω | τ ω < i}) :
    IsStoppingTime f τ :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous' hτ
    <| fun _ hi ↦ absurd hi (NeBot.ne inferInstance)

end IsRightContinuous

end MeasurableSet

namespace IsStoppingTime

/-
**MeasureTheory.IsStoppingTime.max** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsSt
oppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ π : Ω → WithTop ι},   MeasureTheory
.IsStoppingTime f τ →     MeasureTheory.IsStoppingTime f π → MeasureTheory.IsSto
ppingTime f fun ω => max (τ ω) (π ω)
参数：τ ω；π ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
protected theorem max [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun ω => max (τ ω) (π ω) := by
  intro i
  simp_rw [max_le_iff, Set.ofPred_and]
  exact (hτ i).inter (hπ i)
/-
**MeasureTheory.IsStoppingTime.max_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι},   MeasureTheory.I
sStoppingTime f τ → ∀ (i : ι), MeasureTheory.IsStoppingTime f fun ω => max (τ ω)
 ↑i
参数：i : ι；τ ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.max`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
-/
protected theorem max_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => max (τ ω) i :=
  hτ.max (isStoppingTime_const f i)
/-
**MeasureTheory.IsStoppingTime.min** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsSt
oppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ π : Ω → WithTop ι},   MeasureTheory
.IsStoppingTime f τ →     MeasureTheory.IsStoppingTime f π → MeasureTheory.IsSto
ppingTime f fun ω => min (τ ω) (π ω)
参数：τ ω；π ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
-/
protected theorem min [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f fun ω => min (τ ω) (π ω) := by
  intro i
  simp_rw [min_le_iff, Set.ofPred_or]
  exact (hτ i).union (hπ i)
/-
**MeasureTheory.IsStoppingTime.min_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι},   MeasureTheory.I
sStoppingTime f τ → ∀ (i : ι), MeasureTheory.IsStoppingTime f fun ω => min (τ ω)
 ↑i
参数：i : ι；τ ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
-/
protected theorem min_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => min (τ ω) i :=
  hτ.min (isStoppingTime_const f i)
/-
**MeasureTheory.IsStoppingTime.biInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Is
StoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Conditiona
llyCompleteLinearOrderBot ι]   [inst_1 : TopologicalSpace ι] [OrderTopology ι] [
DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]   {κ : Type u_4} {f 
: MeasureTheory.Filtration ι m} {τ : κ → Ω → WithTop ι} {s : Set κ},   s.Countab
le →     ∀ [f.IsRightContinuous],       (∀ n ∈ s, MeasureTheory.IsStoppingTime f
 (τ n)) → MeasureTheory.IsStoppingTime f fun ω => ⨅ n ∈ s, τ n ω
参数：∀ n ∈ s, MeasureTheory.IsStoppingTime f (τ n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous`：i
sStoppingTime_of_measurableSet_lt_of_isRightContinuous [DenselyOrdered ι] [NoMax
Order ι] {τ : Ω -> WithTop ι} [f.IsRightContinuous] (hτ : f…
· 使用定理 `MeasurableSet.of_compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpac
e α}, MeasurableSet sᶜ → MeasurableSet s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_ge`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
-/
protected lemma biInf [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
    {κ : Type*} {f : Filtration ι m} {τ : κ → Ω → WithTop ι} {s : Set κ} (hs : s.Countable)
    [f.IsRightContinuous] (hτ : ∀ n ∈ s, IsStoppingTime f (τ n)) :
    IsStoppingTime f (fun ω ↦ ⨅ n ∈ s, τ n ω) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous <|
    fun i ↦ MeasurableSet.of_compl ?_
  rw [(_ : {ω | ⨅ n ∈ s, τ n ω < i}ᶜ = ⋂ n ∈ s, {ω | i ≤ τ n ω})]
  · exact MeasurableSet.biInter hs <| fun n hn ↦ (hτ n hn).measurableSet_ge i
  · ext ω
    simp
/-
**MeasureTheory.IsStoppingTime.iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsS
toppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Conditiona
llyCompleteLinearOrderBot ι]   [inst_1 : TopologicalSpace ι] [OrderTopology ι] [
DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]   {κ : Type u_4} [Co
untable κ] {f : MeasureTheory.Filtration ι m} {τ : κ → Ω → WithTop ι} [f.IsRight
Continuous],   (∀ (n : κ), MeasureTheory.IsStoppingTime f (τ n)) → MeasureTheory
.IsStoppingTime f fun ω => ⨅ n, τ n ω
参数：∀ (n : κ), MeasureTheory.IsStoppingTime f (τ n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.IsStoppingTime.biInf`：∀ {Ω : Type u_1} {ι : Type u_3} {m :
 MeasurableSpace Ω} [inst : ConditionallyCompleteLinearOrderBot ι]   [inst_1 : T
opologicalSpace ι] [Orde…
· 使用定理 `Set.countable_univ`：countable_univ [Countable α] : (univ : Set α).Counta
ble
-/
protected lemma iInf [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
    {κ : Type*} [Countable κ] {f : Filtration ι m} {τ : κ → Ω → WithTop ι}
    [f.IsRightContinuous] (hτ : ∀ n, IsStoppingTime f (τ n)) :
    IsStoppingTime f (fun ω ↦ ⨅ n, τ n ω) := by
  convert! IsStoppingTime.biInf (κ := κ) Set.countable_univ (fun n _ => hτ n) using 2
  simp
/-
**MeasureTheory.IsStoppingTime.add_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IsStoppingTime`。
形式化陈述：add_const [AddGroup ι] [Preorder ι] [AddRightMono ι] [AddLeftMono ι] {f : 
Filtration ι m} {τ : Ω -> WithTop ι} (hτ : IsStoppingTime f τ) {i : ι} (hi : 0 <
= i) : IsStoppingTime f fun ω => τ ω + i
参数：hτ : IsStoppingTime f τ；hi : 0 <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `sub_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeft
Mono α] (a : α) {b : α}, 0 ≤ b → a - b ≤ a
-/
theorem add_const [AddGroup ι] [Preorder ι] [AddRightMono ι]
    [AddLeftMono ι] {f : Filtration ι m} {τ : Ω → WithTop ι} (hτ : IsStoppingTime f τ)
    {i : ι} (hi : 0 ≤ i) : IsStoppingTime f fun ω => τ ω + i := by
  intro j
  simp only
  have h_eq : {ω | τ ω + i ≤ j} = {ω | τ ω ≤ j - i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, coe_sub]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp_rw [← le_sub_iff_add_le]
  rw [h_eq]
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))
/-
**MeasureTheory.IsStoppingTime.add_const'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IsStoppingTime`。
形式化陈述：add_const' [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
 [TopologicalSpace ι] [OrderTopology ι] {f : Filtration ι m} {τ : Ω -> WithTop ι
} (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => τ ω + i
参数：hτ : IsStoppingTime f τ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_le`：∀ {Ω : Type u_1} {ι : 
Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filt
ration ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_firstCountableTopology`：∀ (α
 : Type u) [t : TopologicalSpace α] [SecondCountableTopology α], FirstCountableT
opology α
· 使用定理 `instSecondCountableTopologyOfOrderTopologyOfCountable`：∀ {α : Type u} [t
s : TopologicalSpace α] [inst : Preorder α] [OrderTopology α] [Countable α], Sec
ondCountableTopology α
· 使用定理 `le_of_add_le_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [
CanonicallyOrderedAdd α] {a b c : α}, a + b ≤ c → a ≤ c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem add_const' [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
    [TopologicalSpace ι] [OrderTopology ι]
    {f : Filtration ι m} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) :
    IsStoppingTime f fun ω => τ ω + i := by
  intro j
  have h : {ω | τ ω + i ≤ j} = ⋃ k : {k | k + i ≤ j}, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    cases τ ω with
    | top => simp
    | coe a => simp; norm_cast
  exact h ▸ MeasurableSet.iUnion fun k => hτ.measurableSet_eq_le (le_of_add_le_left k.2)
/-
**MeasureTheory.IsStoppingTime.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsSt
oppingTime`。
形式化陈述：add [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι] [Topol
ogicalSpace ι] [OrderTopology ι] {f : Filtration ι m} {τ π : Ω -> WithTop ι} (hτ
 : IsStoppingTime f τ) (hπ : IsStoppingTime f π) : IsStoppingTime f (τ + π)
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `le_of_add_le_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] 
[CanonicallyOrderedAdd α] {a b c : α}, a + b ≤ c → b ≤ c
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_le`：∀ {Ω : Type u_1} {ι : 
Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filt
ration ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_firstCountableTopology`：∀ (α
 : Type u) [t : TopologicalSpace α] [SecondCountableTopology α], FirstCountableT
opology α
· 使用定理 `instSecondCountableTopologyOfOrderTopologyOfCountable`：∀ {α : Type u} [t
s : TopologicalSpace α] [inst : Preorder α] [OrderTopology α] [Countable α], Sec
ondCountableTopology α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MeasureTheory.IsStoppingTime.add_const'`：add_const' [Add ι] [LinearOrder
 ι] [CanonicallyOrderedAdd ι] [Countable ι] [TopologicalSpace ι] [OrderTopology 
ι] {f : Filtration ι m} {τ : …
-/
theorem add [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
    [TopologicalSpace ι] [OrderTopology ι]
    {f : Filtration ι m} {τ π : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f (τ + π) := by
  intro j
  have h : {ω | (τ + π) ω ≤ j} = ⋃ k : Set.Iic j, {ω | π ω = k} ∩ {ω | τ ω + k ≤ j} := by
    ext ω
    simp only [Pi.add_apply, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    cases τ ω with
    | top => simp
    | coe a =>
      cases π ω with
      | top => simp
      | coe b => norm_cast; simpa using le_of_add_le_right
  exact h ▸ MeasurableSet.iUnion fun k => (hπ.measurableSet_eq_le k.2).inter (hτ.add_const' k.1 j)

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}

/-- The associated σ-algebra with a stopping time. -/
@[instance_reducible]
/-
**MeasureTheory.IsStoppingTime.measurableSpace** 是 Mathlib 中的一个定义，位于命名空间 `Measur
eTheory.IsStoppingTime`。
形式化陈述：{Ω : Type u_1} →   {ι : Type u_3} →     {m : MeasurableSpace Ω} →       [i
nst : Preorder ι] →         {f : MeasureTheory.Filtration ι m} → {τ : Ω → WithTo
p ι} → MeasureTheory.IsStoppingTime f τ → MeasurableSpace Ω
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associated σ-algebra with a stopping time.
-/
protected def measurableSpace (hτ : IsStoppingTime f τ) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[⨆ t, f t] s ∧ ∀ i : ι, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i})
  measurableSet_empty := by simp
  measurableSet_compl s hs := by
    refine ⟨hs.1.compl, fun i ↦ ?_⟩
    rw [(_ : sᶜ ∩ {ω | τ ω ≤ i} = (sᶜ ∪ {ω | τ ω ≤ i}ᶜ) ∩ {ω | τ ω ≤ i})]
    · refine MeasurableSet.inter ?_ ?_
      · rw [← Set.compl_inter]
        exact (hs.2 i).compl
      · exact hτ i
    · rw [Set.union_inter_distrib_right]
      simp only [Set.compl_inter_self, Set.union_empty]
  measurableSet_iUnion s hs := by
    refine ⟨MeasurableSet.iUnion fun i ↦ (hs i).1, fun i ↦ ?_⟩
    replace hs := fun i ↦ (hs i).2
    rw [forall_comm] at hs
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion (hs i)
/-
**MeasureTheory.IsStoppingTime.measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ : MeasureTheory.I
sStoppingTime f τ) (s : Set Ω),   MeasurableSet s ↔ MeasurableSet s ∧ ∀ (i : ι),
 MeasurableSet (s ∩ {ω | τ ω ≤ ↑i})
参数：hτ : MeasureTheory.IsStoppingTime f τ；s : Set Ω；i : ι；s ∩ {ω | τ ω ≤ ↑i}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem measurableSet (hτ : IsStoppingTime f τ) (s : Set Ω) :
    MeasurableSet[hτ.measurableSpace] s
      ↔ MeasurableSet[⨆ t, f t] s ∧ ∀ i : ι, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i}) :=
  Iff.rfl
/-
**MeasureTheory.IsStoppingTime.measurableSpace_mono** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.IsStoppingTime`。
形式化陈述：measurableSpace_mono (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (
hle : τ <= π) : hτ.measurableSpace <= hπ.measurableSpace
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π；hle : τ <= π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem measurableSpace_mono (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ ≤ π) :
    hτ.measurableSpace ≤ hπ.measurableSpace := by
  refine fun s hs ↦ ⟨hs.1, fun i ↦ ?_⟩
  rw [(_ : s ∩ {ω | π ω ≤ i} = s ∩ {ω | τ ω ≤ i} ∩ {ω | π ω ≤ i})]
  · exact (hs.2 i).inter (hπ i)
  · ext
    simp only [Set.mem_inter_iff, iff_self_and, and_congr_left_iff, Set.mem_ofPred_eq]
    intro hle' _
    exact le_trans (hle _) hle'
/-
**MeasureTheory.IsStoppingTime.measurableSpace_le'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.IsStoppingTime`。
形式化陈述：measurableSpace_le' (hτ : IsStoppingTime f τ) : hτ.measurableSpace <= ⨆ t,
 f t
参数：hτ : IsStoppingTime f τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem measurableSpace_le' (hτ : IsStoppingTime f τ) :
    hτ.measurableSpace ≤ ⨆ t, f t := fun _ hs ↦ hs.1
/-
**MeasureTheory.IsStoppingTime.measurableSpace_le** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.IsStoppingTime`。
形式化陈述：measurableSpace_le (hτ : IsStoppingTime f τ) : hτ.measurableSpace <= m
参数：hτ : IsStoppingTime f τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le'`：measurableSpace_le' (h
τ : IsStoppingTime f τ) : hτ.measurableSpace <= ⨆ t, f t
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
-/
theorem measurableSpace_le (hτ : IsStoppingTime f τ) : hτ.measurableSpace ≤ m :=
  hτ.measurableSpace_le'.trans (iSup_le f.le)

@[simp]
/-
**MeasureTheory.IsStoppingTime.measurableSpace_const** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSpace_const (f : Filtration ι m) (i : ι) : (isStoppingTime_const
 f i).measurableSpace = f i
参数：f : Filtration ι m；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.ext`：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h 
: forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet`：∀ {Ω : Type u_1} {ι : Type u
_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι 
m}   {τ : Ω → WithTop ι} (hτ : M…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
-/
theorem measurableSpace_const (f : Filtration ι m) (i : ι) :
    (isStoppingTime_const f i).measurableSpace = f i := by
  ext1 s
  rw [IsStoppingTime.measurableSet]
  constructor <;> intro h
  · have h' := h.2 i
    simpa only [le_refl, Set.ofPred_true, Set.inter_univ] using h'
  · refine ⟨le_iSup f i s h, fun j ↦ ?_⟩
    by_cases hij : i ≤ j
    · norm_cast
      simp only [hij, Set.ofPred_true, Set.inter_univ]
      exact f.mono hij _ h
    · norm_cast
      simp only [hij, Set.ofPred_false, Set.inter_empty, @MeasurableSet.empty _ (f.1 j)]
/-
**MeasureTheory.IsStoppingTime.measurableSet_inter_eq_iff** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_inter_eq_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) :
 MeasurableSet[hτ.measurableSpace] (s inter {ω | τ ω = i}) ↔ MeasurableSet[f i] 
(s inter {ω | τ ω = i})
参数：hτ : IsStoppingTime f τ；s : Set Ω；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
-/
theorem measurableSet_inter_eq_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) :
    MeasurableSet[hτ.measurableSpace] (s ∩ {ω | τ ω = i}) ↔
      MeasurableSet[f i] (s ∩ {ω | τ ω = i}) := by
  have : ∀ j, {ω : Ω | τ ω = i} ∩ {ω : Ω | τ ω ≤ j} = {ω : Ω | τ ω = i} ∩ {_ω | i ≤ j} := by
    intro j
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_congr_right_iff]
    intro hxi
    rw [hxi]
  constructor <;> intro h
  · simpa [Set.inter_assoc, this] using h.2 i
  · refine ⟨le_iSup f i _ h, fun j ↦ ?_⟩
    rw [Set.inter_assoc, this]
    by_cases hij : i ≤ j
    · norm_cast
      simp only [hij, Set.ofPred_true, Set.inter_univ]
      exact f.mono hij _ h
    · simp [hij]
/-
**MeasureTheory.IsStoppingTime.measurableSpace_le_of_le_const** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSpace_le_of_le_const (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : 
forall ω, τ ω <= i) : hτ.measurableSpace <= f i
参数：hτ : IsStoppingTime f τ；hτ_le : forall ω, τ ω <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_mono`：measurableSpace_mono 
(hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ <= π) : hτ.measurab
leSpace <= hπ.measurableSpace
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_const`：measurableSpace_cons
t (f : Filtration ι m) (i : ι) : (isStoppingTime_const f i).measurableSpace = f 
i
-/
theorem measurableSpace_le_of_le_const (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ ω, τ ω ≤ i) :
    hτ.measurableSpace ≤ f i :=
  (measurableSpace_mono hτ _ hτ_le).trans (measurableSpace_const _ _).le
/-
**MeasureTheory.IsStoppingTime.measurableSpace_le_of_le** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSpace_le_of_le (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : forall
 ω, τ ω <= n) : hτ.measurableSpace <= m
参数：hτ : IsStoppingTime f τ；hτ_le : forall ω, τ ω <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le_of_le_const`：measurableS
pace_le_of_le_const (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : forall ω, τ ω <= 
i) : hτ.measurableSpace <= f i
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
-/
theorem measurableSpace_le_of_le (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) :
    hτ.measurableSpace ≤ m :=
  (hτ.measurableSpace_le_of_le_const hτ_le).trans (f.le n)
/-
**MeasureTheory.IsStoppingTime.le_measurableSpace_of_const_le** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：le_measurableSpace_of_const_le (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : 
forall ω, i <= τ ω) : f i <= hτ.measurableSpace
参数：hτ : IsStoppingTime f τ；hτ_le : forall ω, i <= τ ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_const`：measurableSpace_cons
t (f : Filtration ι m) (i : ι) : (isStoppingTime_const f i).measurableSpace = f 
i
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_mono`：measurableSpace_mono 
(hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ <= π) : hτ.measurab
leSpace <= hπ.measurableSpace
-/
theorem le_measurableSpace_of_const_le (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ ω, i ≤ τ ω) :
    f i ≤ hτ.measurableSpace :=
  (measurableSpace_const _ _).symm.le.trans (measurableSpace_mono _ hτ hτ_le)

end Preorder

/-
**MeasureTheory.IsStoppingTime.sigmaFinite_stopping_time** 是 Mathlib 中的一个实例，位于命名
空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：sigmaFinite_stopping_time {ι} [SemilatticeSup ι] [OrderBot ι] {μ : Measure
 Ω} {f : Filtration ι m} {τ : Ω -> WithTop ι} [SigmaFiniteFiltration μ f] (hτ : 
IsStoppingTime f τ) : SigmaFinite (μ.trim hτ.measurableSpace_le)
参数：hτ : IsStoppingTime f τ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.sigmaFiniteTrim_mono`：sigmaFiniteTrim_mono {m m₂ m0 : Meas
urableSpace α} {μ : Measure α} (hm : m <= m0) (hm₂ : m₂ <= m) [SigmaFinite (μ.tr
im (hm₂.trans hm))] : Si…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le`：measurableSpace_le (hτ 
: IsStoppingTime f τ) : hτ.measurableSpace <= m
· 使用定理 `MeasureTheory.IsStoppingTime.le_measurableSpace_of_const_le`：le_measurab
leSpace_of_const_le (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : forall ω, i <= τ 
ω) : f i <= hτ.measurableSpace
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
instance sigmaFinite_stopping_time {ι} [SemilatticeSup ι] [OrderBot ι]
    {μ : Measure Ω} {f : Filtration ι m}
    {τ : Ω → WithTop ι} [SigmaFiniteFiltration μ f] (hτ : IsStoppingTime f τ) :
    SigmaFinite (μ.trim hτ.measurableSpace_le) := by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance
/-
**MeasureTheory.IsStoppingTime.sigmaFinite_stopping_time_of_le** 是 Mathlib 中的一个实
例，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：sigmaFinite_stopping_time_of_le {ι} [SemilatticeSup ι] [OrderBot ι] {μ : M
easure Ω} {f : Filtration ι m} {τ : Ω -> WithTop ι} [SigmaFiniteFiltration μ f] 
(hτ : IsStoppingTime f τ) {n : ι} (hτ_le : forall ω, τ ω <= n) : SigmaFinite (μ.
trim (hτ.measurableSpace_le_of_le hτ_le))
参数：hτ : IsStoppingTime f τ；hτ_le : forall ω, τ ω <= n。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.sigmaFiniteTrim_mono`：sigmaFiniteTrim_mono {m m₂ m0 : Meas
urableSpace α} {μ : Measure α} (hm : m <= m0) (hm₂ : m₂ <= m) [SigmaFinite (μ.tr
im (hm₂.trans hm))] : Si…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le_of_le`：measurableSpace_l
e_of_le (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : forall ω, τ ω <= n) : hτ.meas
urableSpace <= m
· 使用定理 `MeasureTheory.IsStoppingTime.le_measurableSpace_of_const_le`：le_measurab
leSpace_of_const_le (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : forall ω, i <= τ 
ω) : f i <= hτ.measurableSpace
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
instance sigmaFinite_stopping_time_of_le {ι} [SemilatticeSup ι] [OrderBot ι] {μ : Measure Ω}
    {f : Filtration ι m} {τ : Ω → WithTop ι} [SigmaFiniteFiltration μ f]
    (hτ : IsStoppingTime f τ) {n : ι}
    (hτ_le : ∀ ω, τ ω ≤ n) : SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le)) := by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}

/-
**MeasureTheory.IsStoppingTime.measurableSet_le'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ : MeasureTheor
y.IsStoppingTime f τ) (i : ι), MeasurableSet {ω | τ ω ≤ ↑i}
参数：hτ : MeasureTheory.IsStoppingTime f τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
protected theorem measurableSet_le' (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ i} := by
  refine ⟨le_iSup f i _ (hτ i), fun j ↦ ?_⟩
  have : {ω : Ω | τ ω ≤ i} ∩ {ω : Ω | τ ω ≤ j} = {ω : Ω | τ ω ≤ min i j} := by
    ext1 ω
    simp [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [this]
  exact f.mono (min_le_right i j) _ (hτ _)
/-
**MeasureTheory.IsStoppingTime.measurableSet_gt'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ : MeasureTheor
y.IsStoppingTime f τ) (i : ι), MeasurableSet {ω | ↑i < τ ω}
参数：hτ : MeasureTheory.IsStoppingTime f τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le'`：∀ {Ω : Type u_1} {ι : Ty
pe u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtra
tion ι m}   {τ : Ω → WithTop ι} (hτ …
-/
protected theorem measurableSet_gt' (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i < τ ω} := by
  have : {ω : Ω | i < τ ω} = {ω : Ω | τ ω ≤ i}ᶜ := by ext1 ω; simp
  rw [this]
  exact (hτ.measurableSet_le' i).compl
/-
**MeasureTheory.IsStoppingTime.measurableSet_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [FirstCountableTopology ι]   (hτ : MeasureTheory.I
sStoppingTime f τ) (i : ι), MeasurableSet {ω | τ ω = ↑i}
参数：hτ : MeasureTheory.IsStoppingTime f τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_inter_eq_iff`：measurableSet_i
nter_eq_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) : MeasurableSet[hτ.mea
surableSpace] (s inter {ω | τ ω = i}) ↔ Measu…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
-/
protected theorem measurableSet_eq' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} := by
  rw [← Set.univ_inter {ω | τ ω = i}, measurableSet_inter_eq_iff, Set.univ_inter]
  exact hτ.measurableSet_eq i
/-
**MeasureTheory.IsStoppingTime.measurableSet_ge'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [FirstCountableTopology ι]   (hτ : MeasureTheory.I
sStoppingTime f τ) (i : ι), MeasurableSet {ω | ↑i ≤ τ ω}
参数：hτ : MeasureTheory.IsStoppingTime f τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq'`：∀ {Ω : Type u_1} {ι : Ty
pe u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtra
tion ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_gt'`：∀ {Ω : Type u_1} {ι : Ty
pe u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtra
tion ι m}   {τ : Ω → WithTop ι} (hτ …
-/
protected theorem measurableSet_ge' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω = i} ∪ {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_ofPred_eq, Set.mem_union]
    cases τ ω with
    | top => simp
    | coe a =>
      norm_cast
      rw [@eq_comm _ i, or_comm]
  rw [this]
  exact (hτ.measurableSet_eq' i).union (hτ.measurableSet_gt' i)
/-
**MeasureTheory.IsStoppingTime.measurableSet_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [FirstCountableTopology ι]   (hτ : MeasureTheory.I
sStoppingTime f τ) (i : ι), MeasurableSet {ω | τ ω < ↑i}
参数：hτ : MeasureTheory.IsStoppingTime f τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le'`：∀ {Ω : Type u_1} {ι : Ty
pe u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtra
tion ι m}   {τ : Ω → WithTop ι} (hτ …
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq'`：∀ {Ω : Type u_1} {ι : Ty
pe u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtra
tion ι m}   {τ : Ω → WithTop ι} [ins…
-/
protected theorem measurableSet_lt' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_ofPred_eq, Set.mem_sdiff]
  rw [this]
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq' i)

section Countable

/-
**MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range'** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ : MeasureTheor
y.IsStoppingTime f τ),   (Set.range τ).Countable → ∀ (i : ι), MeasurableSet {ω |
 τ ω = ↑i}
参数：hτ : MeasureTheory.IsStoppingTime f τ；Set.range τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_inter_eq_iff`：measurableSet_i
nter_eq_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) : MeasurableSet[hτ.mea
surableSpace] (s inter {ω | τ ω = i}) ↔ Measu…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range`：∀ {Ω :
 Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : PartialOrder ι] {τ : Ω
 → WithTop ι}   {f : MeasureTheory.Filtration ι m},   …
-/
protected theorem measurableSet_eq_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} := by
  rw [← Set.univ_inter {ω | τ ω = i}, measurableSet_inter_eq_iff, Set.univ_inter]
  exact hτ.measurableSet_eq_of_countable_range h_countable i
/-
**MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable'** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [Countable ι] (hτ 
: MeasureTheory.IsStoppingTime f τ) (i : ι), MeasurableSet {ω | τ ω = ↑i}
参数：hτ : MeasureTheory.IsStoppingTime f τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range'`：∀ {Ω 
: Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : M
easureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ …
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
protected theorem measurableSet_eq_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} :=
  hτ.measurableSet_eq_of_countable_range' (Set.to_countable _) i
/-
**MeasureTheory.IsStoppingTime.measurableSet_ge_of_countable_range'** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ : MeasureTheor
y.IsStoppingTime f τ),   (Set.range τ).Countable → ∀ (i : ι), MeasurableSet {ω |
 ↑i ≤ τ ω}
参数：hτ : MeasureTheory.IsStoppingTime f τ；Set.range τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range'`：∀ {Ω 
: Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : M
easureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ …
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_gt'`：∀ {Ω : Type u_1} {ι : Ty
pe u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtra
tion ι m}   {τ : Ω → WithTop ι} (hτ …
-/
protected theorem measurableSet_ge_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω = i} ∪ {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_ofPred_eq, Set.mem_union]
    cases τ ω with
    | top => simp
    | coe a =>
      norm_cast
      rw [@eq_comm _ i, or_comm]
  rw [this]
  exact (hτ.measurableSet_eq_of_countable_range' h_countable i).union (hτ.measurableSet_gt' i)
/-
**MeasureTheory.IsStoppingTime.measurableSet_ge_of_countable'** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [Countable ι] (hτ 
: MeasureTheory.IsStoppingTime f τ) (i : ι), MeasurableSet {ω | ↑i ≤ τ ω}
参数：hτ : MeasureTheory.IsStoppingTime f τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_ge_of_countable_range'`：∀ {Ω 
: Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : M
easureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ …
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
protected theorem measurableSet_ge_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i ≤ τ ω} :=
  hτ.measurableSet_ge_of_countable_range' (Set.to_countable _) i
/-
**MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable_range'** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ : MeasureTheor
y.IsStoppingTime f τ),   (Set.range τ).Countable → ∀ (i : ι), MeasurableSet {ω |
 τ ω < ↑i}
参数：hτ : MeasureTheory.IsStoppingTime f τ；Set.range τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le'`：∀ {Ω : Type u_1} {ι : Ty
pe u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtra
tion ι m}   {τ : Ω → WithTop ι} (hτ …
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range'`：∀ {Ω 
: Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : M
easureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ …
-/
protected theorem measurableSet_lt_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_ofPred_eq, Set.mem_sdiff]
  rw [this]
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq_of_countable_range' h_countable i)
/-
**MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable'** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [Countable ι] (hτ 
: MeasureTheory.IsStoppingTime f τ) (i : ι), MeasurableSet {ω | τ ω < ↑i}
参数：hτ : MeasureTheory.IsStoppingTime f τ；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable_range'`：∀ {Ω 
: Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : M
easureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ …
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
protected theorem measurableSet_lt_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} :=
  hτ.measurableSet_lt_of_countable_range' (Set.to_countable _) i

end Countable

/-
**MeasureTheory.IsStoppingTime.measurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [inst_2 : OrderTopology ι] [SecondCountableTopology ι]   (hτ : Measu
reTheory.IsStoppingTime f τ), Measurable τ
参数：hτ : MeasureTheory.IsStoppingTime f τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_Iic`：measurable_of_Iic {f : δ -> α} (hf : forall x, Measur
ableSet (f ⁻¹' Iic x)) : Measurable f
· 使用定理 `WithTop.instBorelSpace`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 
: TopologicalSpace ι] [inst_2 : OrderTopology ι], BorelSpace (WithTop ι)
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `TopologicalSpace.instSecondCountableTopologyWithTop`：∀ {ι : Type u_1} [i
nst : Preorder ι] [ts : TopologicalSpace ι] [ht : OrderTopology ι] [SecondCounta
bleTopology ι],   SecondCountableTopology…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iic_top`：Iic_top : Iic (⊤ : α) = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le'`：∀ {Ω : Type u_1} {ι : Ty
pe u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtra
tion ι m}   {τ : Ω → WithTop ι} (hτ …
-/
protected theorem measurable [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] τ := by
  refine measurable_of_Iic fun i ↦ ?_
  cases i with
  | top => simp
  | coe i => exact hτ.measurableSet_le' i
/-
**MeasureTheory.IsStoppingTime.measurable'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [inst_2 : OrderTopology ι] [SecondCountableTopology ι],   MeasureThe
ory.IsStoppingTime f τ → Measurable τ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `MeasureTheory.IsStoppingTime.measurable`：∀ {Ω : Type u_1} {ι : Type u_3}
 {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι 
m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le`：measurableSpace_le (hτ 
: IsStoppingTime f τ) : hτ.measurableSpace <= m
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected theorem measurable' [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    Measurable τ := hτ.measurable.mono (measurableSpace_le hτ) le_rfl
/-
**MeasureTheory.IsStoppingTime.measurable_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [inst_2 : OrderTopology ι] [SecondCountableTopology ι],   MeasureThe
ory.IsStoppingTime f τ → Measurable τ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `MeasureTheory.IsStoppingTime.measurable`：∀ {Ω : Type u_1} {ι : Type u_3}
 {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι 
m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le'`：measurableSpace_le' (h
τ : IsStoppingTime f τ) : hτ.measurableSpace <= ⨆ t, f t
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected theorem measurable_iSup [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    Measurable[⨆ t, f t] τ := hτ.measurable.mono (measurableSpace_le' hτ) le_rfl
/-
**MeasureTheory.IsStoppingTime.measurableSet_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [SecondCountableTopology ι],   MeasureTheory.IsSto
ppingTime f τ → MeasurableSet {ω | τ ω = ⊤}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `WithTop.instBorelSpace`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 
: TopologicalSpace ι] [inst_2 : OrderTopology ι], BorelSpace (WithTop ι)
· 使用定理 `TopologicalSpace.instSecondCountableTopologyWithTop`：∀ {ι : Type u_1} [i
nst : Preorder ι] [ts : TopologicalSpace ι] [ht : OrderTopology ι] [SecondCounta
bleTopology ι],   SecondCountableTopology…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `MeasureTheory.IsStoppingTime.measurable'`：∀ {Ω : Type u_1} {ι : Type u_3
} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι
 m}   {τ : Ω → WithTop ι} [ins…
-/
protected lemma measurableSet_eq_top [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    MeasurableSet {ω | τ ω = ⊤} :=
  (measurableSet_singleton _).preimage hτ.measurable'
/-
**MeasureTheory.IsStoppingTime.measurableSet_eq_top'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [OrderTopology ι] [SecondCountableTopology ι],   MeasureTheory.IsSto
ppingTime f τ → MeasurableSet {ω | τ ω = ⊤}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `WithTop.instBorelSpace`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 
: TopologicalSpace ι] [inst_2 : OrderTopology ι], BorelSpace (WithTop ι)
· 使用定理 `TopologicalSpace.instSecondCountableTopologyWithTop`：∀ {ι : Type u_1} [i
nst : Preorder ι] [ts : TopologicalSpace ι] [ht : OrderTopology ι] [SecondCounta
bleTopology ι],   SecondCountableTopology…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `MeasureTheory.IsStoppingTime.measurable_iSup`：∀ {Ω : Type u_1} {ι : Type
 u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrati
on ι m}   {τ : Ω → WithTop ι} [ins…
-/
protected lemma measurableSet_eq_top' [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    MeasurableSet[⨆ t, f t] {ω | τ ω = ⊤} :=
  (measurableSet_singleton _).preimage hτ.measurable_iSup
/-
**MeasureTheory.IsStoppingTime.measurable_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] {f : MeasureTheory.Filtration ι m}   {τ : Ω → WithTop ι} [inst_1 : Topologi
calSpace ι] [inst_2 : OrderTopology ι] [SecondCountableTopology ι],   MeasureThe
ory.IsStoppingTime f τ → ∀ {i : ι}, (∀ (ω : Ω), τ ω ≤ ↑i) → Measurable τ
参数：∀ (ω : Ω), τ ω ≤ ↑i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `MeasureTheory.IsStoppingTime.measurable`：∀ {Ω : Type u_1} {ι : Type u_3}
 {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι 
m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le_of_le_const`：measurableS
pace_le_of_le_const (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : forall ω, τ ω <= 
i) : hτ.measurableSpace <= f i
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected theorem measurable_of_le [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) {i : ι}
    (hτ_le : ∀ ω, τ ω ≤ i) : Measurable[f i] τ :=
  hτ.measurable.mono (measurableSpace_le_of_le_const _ hτ_le) le_rfl
/-
**MeasureTheory.IsStoppingTime.measurableSpace_min** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.IsStoppingTime`。
形式化陈述：measurableSpace_min (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) : 
(hτ.min hπ).measurableSpace = hτ.measurableSpace ⊓ hπ.measurableSpace
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_mono`：measurableSpace_mono 
(hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ <= π) : hτ.measurab
leSpace <= hπ.measurableSpace
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem measurableSpace_min (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    (hτ.min hπ).measurableSpace = hτ.measurableSpace ⊓ hπ.measurableSpace := by
  refine le_antisymm ?_ ?_
  · exact le_inf (measurableSpace_mono _ hτ fun _ => min_le_left _ _)
      (measurableSpace_mono _ hπ fun _ => min_le_right _ _)
  · intro s
    change MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s →
      MeasurableSet[(hτ.min hπ).measurableSpace] s
    simp_rw [IsStoppingTime.measurableSet]
    have : ∀ i, {ω | min (τ ω) (π ω) ≤ i} = {ω | τ ω ≤ i} ∪ {ω | π ω ≤ i} := by
      intro i; ext1 ω; simp
    simp_rw [this, Set.inter_union_distrib_left]
    exact fun h ↦ ⟨h.1.1, fun i ↦ (h.left.2 i).union (h.right.2 i)⟩
/-
**MeasureTheory.IsStoppingTime.measurableSet_min_iff** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_min_iff (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) 
(s : Set Ω) : MeasurableSet[(hτ.min hπ).measurableSpace] s ↔ MeasurableSet[hτ.me
asurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π；s : Set Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_min`：measurableSpace_min (h
τ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) : (hτ.min hπ).measurableSpace 
= hτ.measurableSpace ⊓ hπ.measurableSp…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurableSet_min_iff (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) :
    MeasurableSet[(hτ.min hπ).measurableSpace] s ↔
      MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s := by
  rw [measurableSpace_min hτ hπ]; rfl
/-
**MeasureTheory.IsStoppingTime.measurableSpace_min_const** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSpace_min_const (hτ : IsStoppingTime f τ) {i : ι} : (hτ.min_cons
t i).measurableSpace = hτ.measurableSpace ⊓ f i
参数：hτ : IsStoppingTime f τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min_const`：∀ {Ω : Type u_1} {ι : Type u_3} 
{m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m
}   {τ : Ω → WithTop ι},   M…
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_min`：measurableSpace_min (h
τ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) : (hτ.min hπ).measurableSpace 
= hτ.measurableSpace ⊓ hπ.measurableSp…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_const`：measurableSpace_cons
t (f : Filtration ι m) (i : ι) : (isStoppingTime_const f i).measurableSpace = f 
i
-/
theorem measurableSpace_min_const (hτ : IsStoppingTime f τ) {i : ι} :
    (hτ.min_const i).measurableSpace = hτ.measurableSpace ⊓ f i := by
  rw [hτ.measurableSpace_min (isStoppingTime_const _ i), measurableSpace_const]
/-
**MeasureTheory.IsStoppingTime.measurableSet_min_const_iff** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_min_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) {i : ι} 
: MeasurableSet[(hτ.min_const i).measurableSpace] s ↔ MeasurableSet[hτ.measurabl
eSpace] s ∧ MeasurableSet[f i] s
参数：hτ : IsStoppingTime f τ；s : Set Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min_const`：∀ {Ω : Type u_1} {ι : Type u_3} 
{m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m
}   {τ : Ω → WithTop ι},   M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_min_const`：measurableSpace_
min_const (hτ : IsStoppingTime f τ) {i : ι} : (hτ.min_const i).measurableSpace =
 hτ.measurableSpace ⊓ f i
· 使用定理 `MeasurableSpace.measurableSet_inf`：measurableSet_inf {m₂ m₁ : Measurable
Space α} {s : Set α} : MeasurableSet[m₁ ⊓ m₂] s ↔ MeasurableSet[m₁] s ∧ Measurab
leSet[m₂] s
-/
theorem measurableSet_min_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) {i : ι} :
    MeasurableSet[(hτ.min_const i).measurableSpace] s ↔
      MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[f i] s := by
  rw [measurableSpace_min_const hτ]; apply MeasurableSpace.measurableSet_inf
/-
**MeasureTheory.IsStoppingTime.measurableSet_inter_le** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_inter_le [TopologicalSpace ι] [SecondCountableTopology ι] [O
rderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) 
(hs : MeasurableSet[hτ.measurableSpace] s) : MeasurableSet[(hτ.min hπ).measurabl
eSpace] (s inter {ω | τ ω <= π ω})
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π；s : Set Ω；hs : MeasurableSet[
hτ.measurableSpace] s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `WithTop.instBorelSpace`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 
: TopologicalSpace ι] [inst_2 : OrderTopology ι], BorelSpace (WithTop ι)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `TopologicalSpace.instSecondCountableTopologyWithTop`：∀ {ι : Type u_1} [i
nst : Preorder ι] [ts : TopologicalSpace ι] [ht : OrderTopology ι] [SecondCounta
bleTopology ι],   SecondCountableTopology…
· 使用定理 `MeasureTheory.IsStoppingTime.measurable_iSup`：∀ {Ω : Type u_1} {ι : Type
 u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrati
on ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.IsStoppingTime.measurable_of_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `MeasureTheory.IsStoppingTime.min_const`：∀ {Ω : Type u_1} {ι : Type u_3} 
{m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m
}   {τ : Ω → WithTop ι},   M…
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
theorem measurableSet_inter_le [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π)
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    MeasurableSet[(hτ.min hπ).measurableSpace] (s ∩ {ω | τ ω ≤ π ω}) := by
  simp_rw [IsStoppingTime.measurableSet] at hs ⊢
  have h_eq i : s ∩ {ω | τ ω ≤ π ω} ∩ {ω | min (τ ω) (π ω) ≤ i} =
      s ∩ {ω | τ ω ≤ i} ∩ {ω | min (τ ω) (π ω) ≤ i} ∩
        {ω | min (τ ω) i ≤ min (min (τ ω) (π ω)) i} := by
    ext ω
    by_cases hτi : τ ω ≤ i <;> grind
  simp_rw [h_eq]
  refine ⟨hs.1.inter (measurableSet_le hτ.measurable_iSup hπ.measurable_iSup), fun i ↦ ?_⟩
  refine ((hs.2 i).inter ((hτ.min hπ) i)).inter ?_
  apply @measurableSet_le _ _ _ _ _ (Filtration.seq f i) _ _ _ _ _ ?_ ?_
  · exact (hτ.min_const i).measurable_of_le fun _ => min_le_right _ _
  · exact ((hτ.min hπ).min_const i).measurable_of_le fun _ => min_le_right _ _
/-
**MeasureTheory.IsStoppingTime.measurableSet_inter_le_iff** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_inter_le_iff [TopologicalSpace ι] [SecondCountableTopology ι
] [OrderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set
 Ω) : MeasurableSet[hτ.measurableSpace] (s inter {ω | τ ω <= π ω}) ↔ MeasurableS
et[(hτ.min hπ).measurableSpace] (s inter {ω | τ ω <= π ω})
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π；s : Set Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_inter_le`：measurableSet_inter
_le [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] (hτ : IsS
toppingTime f τ) (hπ : IsStoppingTime f π…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_min_iff`：measurableSet_min_if
f (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) : MeasurableSe
t[(hτ.min hπ).measurableSpace] s ↔ Measu…
-/
theorem measurableSet_inter_le_iff [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) (s : Set Ω) :
    MeasurableSet[hτ.measurableSpace] (s ∩ {ω | τ ω ≤ π ω}) ↔
      MeasurableSet[(hτ.min hπ).measurableSpace] (s ∩ {ω | τ ω ≤ π ω}) := by
  constructor <;> intro h
  · have : s ∩ {ω | τ ω ≤ π ω} = s ∩ {ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ π ω} := by
      rw [Set.inter_assoc, Set.inter_self]
    rw [this]
    exact measurableSet_inter_le _ hπ _ h
  · rw [measurableSet_min_iff hτ hπ] at h
    exact h.1
/-
**MeasureTheory.IsStoppingTime.measurableSet_inter_le_const_iff** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_inter_le_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i 
: ι) : MeasurableSet[hτ.measurableSpace] (s inter {ω | τ ω <= i}) ↔ MeasurableSe
t[(hτ.min_const i).measurableSpace] (s inter {ω | τ ω <= i})
参数：hτ : IsStoppingTime f τ；s : Set Ω；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min_const`：∀ {Ω : Type u_1} {ι : Type u_3} 
{m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m
}   {τ : Ω → WithTop ι},   M…
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_min_iff`：measurableSet_min_if
f (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) : MeasurableSe
t[(hτ.min hπ).measurableSpace] s ↔ Measu…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_const`：measurableSpace_cons
t (f : Filtration ι m) (i : ι) : (isStoppingTime_const f i).measurableSpace = f 
i
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet`：∀ {Ω : Type u_1} {ι : Type u
_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι 
m}   {τ : Ω → WithTop ι} (hτ : M…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem measurableSet_inter_le_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) :
    MeasurableSet[hτ.measurableSpace] (s ∩ {ω | τ ω ≤ i}) ↔
      MeasurableSet[(hτ.min_const i).measurableSpace] (s ∩ {ω | τ ω ≤ i}) := by
  rw [IsStoppingTime.measurableSet_min_iff hτ (isStoppingTime_const _ i),
    IsStoppingTime.measurableSpace_const, IsStoppingTime.measurableSet]
  refine ⟨fun h => ⟨h, ?_⟩, fun h ↦ h.1⟩
  have h' := h.2 i
  rwa [Set.inter_assoc, Set.inter_self] at h'
/-
**MeasureTheory.IsStoppingTime.measurableSet_le_stopping_time** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_le_stopping_time [TopologicalSpace ι] [SecondCountableTopolo
gy ι] [OrderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) : Me
asurableSet[hτ.measurableSpace] {ω | τ ω <= π ω}
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet`：∀ {Ω : Type u_1} {ι : Type u
_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι 
m}   {τ : Ω → WithTop ι} (hτ : M…
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `WithTop.instBorelSpace`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 
: TopologicalSpace ι] [inst_2 : OrderTopology ι], BorelSpace (WithTop ι)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `TopologicalSpace.instSecondCountableTopologyWithTop`：∀ {ι : Type u_1} [i
nst : Preorder ι] [ts : TopologicalSpace ι] [ht : OrderTopology ι] [SecondCounta
bleTopology ι],   SecondCountableTopology…
· 使用定理 `MeasureTheory.IsStoppingTime.measurable_iSup`：∀ {Ω : Type u_1} {ι : Type
 u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrati
on ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Std.IsPreorder.le_trans`：∀ {α : Type u} {inst : LE α} [self : Std.IsPreo
rder α] (a b c : α), a ≤ b → b ≤ c → a ≤ c
· 使用定理 `instIsPreorder_mathlib`：∀ {α : Type u_1} [inst : Preorder α], Std.IsPreo
rder α
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.IsStoppingTime.measurable_of_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `MeasureTheory.IsStoppingTime.min_const`：∀ {Ω : Type u_1} {ι : Type u_3} 
{m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m
}   {τ : Ω → WithTop ι},   M…
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration
 ι m}   {τ : Ω → WithTop ι}, Measur…
-/
theorem measurableSet_le_stopping_time [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ π ω} := by
  rw [hτ.measurableSet]
  refine ⟨measurableSet_le hτ.measurable_iSup hπ.measurable_iSup, fun j ↦ ?_⟩
  have : {ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ j} = {ω | min (τ ω) j ≤ min (π ω) j} ∩ {ω | τ ω ≤ j} := by
    ext
    simpa using fun a b ↦ Std.IsPreorder.le_trans _ _ _ a b
  rw [this]
  refine MeasurableSet.inter ?_ (hτ.measurableSet_le j)
  apply @measurableSet_le _ _ _ _ _ (Filtration.seq f j) _ _ _ _ _ ?_ ?_
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_right _ _
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_right _ _
/-
**MeasureTheory.IsStoppingTime.measurableSet_stopping_time_le_min** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_stopping_time_le_min [TopologicalSpace ι] [SecondCountableTo
pology ι] [OrderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) 
: MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω <= π ω}
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_inter_le_iff`：measurableSet_i
nter_le_iff [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] (
hτ : IsStoppingTime f τ) (hπ : IsStoppingTime…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le_stopping_time`：measurableS
et_le_stopping_time [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopol
ogy ι] (hτ : IsStoppingTime f τ) (hπ : IsStopping…
-/
theorem measurableSet_stopping_time_le_min [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω ≤ π ω} := by
  rw [← Set.univ_inter {ω : Ω | τ ω ≤ π ω}, ← hτ.measurableSet_inter_le_iff hπ, Set.univ_inter]
  exact measurableSet_le_stopping_time hτ hπ
/-
**MeasureTheory.IsStoppingTime.measurableSet_stopping_time_le** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_stopping_time_le [TopologicalSpace ι] [SecondCountableTopolo
gy ι] [OrderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) : Me
asurableSet[hπ.measurableSpace] {ω | τ ω <= π ω}
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_stopping_time_le_min`：measura
bleSet_stopping_time_le_min [TopologicalSpace ι] [SecondCountableTopology ι] [Or
derTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStop…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_min_iff`：measurableSet_min_if
f (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) : MeasurableSe
t[(hτ.min hπ).measurableSpace] s ↔ Measu…
-/
theorem measurableSet_stopping_time_le [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[hπ.measurableSpace] {ω | τ ω ≤ π ω} := by
  have : MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω ≤ π ω} :=
    measurableSet_stopping_time_le_min hτ hπ
  rw [measurableSet_min_iff hτ hπ] at this; exact this.2
/-
**MeasureTheory.IsStoppingTime.measurableSet_eq_stopping_time_min** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_eq_stopping_time_min [TopologicalSpace ι] [OrderTopology ι] 
[SecondCountableTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) 
: MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω = π ω}
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_stopping_time_le_min`：measura
bleSet_stopping_time_le_min [TopologicalSpace ι] [SecondCountableTopology ι] [Or
derTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStop…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
-/
theorem measurableSet_eq_stopping_time_min [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω = π ω} := by
  have : {ω | τ ω = π ω} = {ω | τ ω ≤ π ω} ∩ {ω | π ω ≤ τ ω} := by
    ext; simp only [Set.mem_ofPred_eq, le_antisymm_iff, Set.mem_inter_iff]
  rw [this]
  refine MeasurableSet.inter (measurableSet_stopping_time_le_min hτ hπ) ?_
  convert! (measurableSet_stopping_time_le_min hπ hτ) using 3
  rw [min_comm]
/-
**MeasureTheory.IsStoppingTime.measurableSet_eq_stopping_time** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.IsStoppingTime`。
形式化陈述：measurableSet_eq_stopping_time [TopologicalSpace ι] [OrderTopology ι] [Sec
ondCountableTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) : Me
asurableSet[hτ.measurableSpace] {ω | τ ω = π ω}
参数：hτ : IsStoppingTime f τ；hπ : IsStoppingTime f π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_stopping_time_min`：measura
bleSet_eq_stopping_time_min [TopologicalSpace ι] [OrderTopology ι] [SecondCounta
bleTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStop…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_min_iff`：measurableSet_min_if
f (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) : MeasurableSe
t[(hτ.min hπ).measurableSpace] s ↔ Measu…
-/
theorem measurableSet_eq_stopping_time [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = π ω} := by
  have h := measurableSet_eq_stopping_time_min hτ hπ
  rw [measurableSet_min_iff hτ hπ] at h
  exact h.1

end LinearOrder

end IsStoppingTime

section LinearOrder

/-! ## Stopped value and stopped process -/

variable [Nonempty ι] {u v : ι → Ω → β} {τ σ : Ω → WithTop ι}

/-- Given a map `u : ι → Ω → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ ω) ω`. -/
noncomputable
/-
**MeasureTheory.stoppedValue** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedValue (u : ι -> Ω -> β) (τ : Ω -> WithTop ι) : Ω -> β
参数：u : ι -> Ω -> β；τ : Ω -> WithTop ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def stoppedValue (u : ι → Ω → β) (τ : Ω → WithTop ι) : Ω → β := fun ω => u (τ ω).untopA ω

@[simp]
/-
**MeasureTheory.stoppedValue_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedValue_const (u : ι -> Ω -> β) (i : ι) : (stoppedValue u fun _ => i)
 = u i
参数：u : ι -> Ω -> β；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stoppedValue_const (u : ι → Ω → β) (i : ι) : (stoppedValue u fun _ => i) = u i := rfl
/-
**MeasureTheory.stoppedValue_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : Nonempty ι] {u : ι 
→ Ω → β} {τ : Ω → WithTop ι} {γ : Type u_4}   (f : β → γ), MeasureTheory.stopped
Value (fun t ω => f (u t ω)) τ = fun ω => f (MeasureTheory.stoppedValue u τ ω)
参数：f : β → γ；fun t ω => f (u t ω)；MeasureTheory.stoppedValue u τ ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma stoppedValue_comp {γ : Type*} (f : β → γ) :
    stoppedValue (fun t ω ↦ f (u t ω)) τ = fun ω ↦ f (stoppedValue u τ ω) := rfl
/-
**MeasureTheory.stoppedValue_norm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedValue_norm [SeminormedAddCommGroup β] : stoppedValue (fun t ω => ‖u
 t ω‖) τ = fun ω => ‖stoppedValue u τ ω‖
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stoppedValue_norm [SeminormedAddCommGroup β] :
    stoppedValue (fun t ω ↦ ‖u t ω‖) τ = fun ω ↦ ‖stoppedValue u τ ω‖ := rfl

@[to_additive (attr := simp)]
/-
**MeasureTheory.stoppedValue_inv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedValue_inv [Inv β] : stoppedValue (u⁻¹) τ = (stoppedValue u τ)⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stoppedValue_inv [Inv β] : stoppedValue (u⁻¹) τ = (stoppedValue u τ)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**MeasureTheory.stoppedValue_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedValue_mul [Mul β] : stoppedValue (u * v) τ = stoppedValue u τ * sto
ppedValue v τ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stoppedValue_mul [Mul β] :
    stoppedValue (u * v) τ = stoppedValue u τ * stoppedValue v τ := rfl

@[to_additive (attr := simp)]
/-
**MeasureTheory.stoppedValue_div** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedValue_div [Div β] : stoppedValue (u / v) τ = stoppedValue u τ / sto
ppedValue v τ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stoppedValue_div [Div β] :
    stoppedValue (u / v) τ = stoppedValue u τ / stoppedValue v τ := rfl
/-
**MeasureTheory.stoppedValue_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : Nonempty ι] {u : ι 
→ Ω → β} {τ : Ω → WithTop ι} {𝕜 : Type u_4}   [inst_1 : SMul 𝕜 β] (c : 𝕜), Measu
reTheory.stoppedValue (c • u) τ = c • MeasureTheory.stoppedValue u τ
参数：c : 𝕜；c • u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma stoppedValue_const_smul {𝕜 : Type*} [SMul 𝕜 β] (c : 𝕜) :
    stoppedValue (c • u) τ = c • stoppedValue u τ := rfl
/-
**MeasureTheory.stoppedValue_const_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : Nonempty ι] {u : ι 
→ Ω → β} [inst_1 : Bot ι],   (MeasureTheory.stoppedValue u fun x => ⊥) = u ⊥
参数：MeasureTheory.stoppedValue u fun x => ⊥。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma stoppedValue_const_bot [Bot ι] :
    stoppedValue u (fun _ ↦ ⊥) = u ⊥ := by
  ext; simp [stoppedValue, ← WithTop.coe_bot]

variable [LinearOrder ι]

/-- Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if
`i ≤ τ ω`, and `u (τ ω) ω` otherwise.

Intuitively, the stopped process stops evolving once the stopping time has occurred. -/
noncomputable
/-
**MeasureTheory.stoppedProcess** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedProcess (u : ι -> Ω -> β) (τ : Ω -> WithTop ι) : ι -> Ω -> β
参数：u : ι -> Ω -> β；τ : Ω -> WithTop ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def stoppedProcess (u : ι → Ω → β) (τ : Ω → WithTop ι) : ι → Ω → β :=
  fun i ω => u (min (i : WithTop ι) (τ ω)).untopA ω
/-
**MeasureTheory.stoppedProcess_eq_stoppedValue** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：stoppedProcess_eq_stoppedValue : stoppedProcess u τ = fun i : ι => stopped
Value u fun ω => min i (τ ω)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stoppedProcess_eq_stoppedValue :
    stoppedProcess u τ = fun i : ι => stoppedValue u fun ω => min i (τ ω) := rfl
/-
**MeasureTheory.stoppedProcess_eq_stoppedValue_apply** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：stoppedProcess_eq_stoppedValue_apply (i : ι) (ω : Ω) : stoppedProcess u τ 
i ω = stoppedValue u (fun ω => min i (τ ω)) ω
参数：i : ι；ω : Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stoppedProcess_eq_stoppedValue_apply (i : ι) (ω : Ω) :
    stoppedProcess u τ i ω = stoppedValue u (fun ω ↦ min i (τ ω)) ω := rfl
/-
**MeasureTheory.stoppedProcess_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : Nonempty ι] {τ : Ω 
→ WithTop ι} [inst_1 : LinearOrder ι]   {u₀ : Ω → β}, MeasureTheory.stoppedProce
ss (fun x => u₀) τ = fun x => u₀
参数：fun x => u₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma stoppedProcess_const {u₀ : Ω → β} :
    stoppedProcess (fun _ ↦ u₀) τ = fun _ ↦ u₀ := rfl
/-
**MeasureTheory.stoppedProcess_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : Nonempty ι] {u : ι 
→ Ω → β} {τ : Ω → WithTop ι}   [inst_1 : LinearOrder ι] {γ : Type u_4} (f : β → 
γ),   MeasureTheory.stoppedProcess (fun t ω => f (u t ω)) τ = fun i ω => f (Meas
ureTheory.stoppedProcess u τ i ω)
参数：f : β → γ；fun t ω => f (u t ω)；MeasureTheory.stoppedProcess u τ i ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma stoppedProcess_comp {γ : Type*} (f : β → γ) :
    stoppedProcess (fun t ω ↦ f (u t ω)) τ = fun i ω ↦ f (stoppedProcess u τ i ω) := rfl
/-
**MeasureTheory.stoppedProcess_norm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedProcess_norm [SeminormedAddCommGroup β] : stoppedProcess (fun t ω =
> ‖u t ω‖) τ = fun i ω => ‖stoppedProcess u τ i ω‖
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stoppedProcess_norm [SeminormedAddCommGroup β] :
    stoppedProcess (fun t ω ↦ ‖u t ω‖) τ = fun i ω ↦ ‖stoppedProcess u τ i ω‖ := rfl

@[to_additive (attr := simp)]
/-
**MeasureTheory.stoppedProcess_inv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedProcess_inv [Inv β] : stoppedProcess (u⁻¹) τ = (stoppedProcess u τ)
⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stoppedProcess_inv [Inv β] : stoppedProcess (u⁻¹) τ = (stoppedProcess u τ)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**MeasureTheory.stoppedProcess_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedProcess_mul [Mul β] : stoppedProcess (u * v) τ = stoppedProcess u τ
 * stoppedProcess v τ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stoppedProcess_mul [Mul β] :
    stoppedProcess (u * v) τ = stoppedProcess u τ * stoppedProcess v τ := rfl

@[to_additive (attr := simp)]
/-
**MeasureTheory.stoppedProcess_div** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedProcess_div [Div β] : stoppedProcess (u / v) τ = stoppedProcess u τ
 / stoppedProcess v τ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stoppedProcess_div [Div β] :
    stoppedProcess (u / v) τ = stoppedProcess u τ / stoppedProcess v τ := rfl
/-
**MeasureTheory.stoppedProcess_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : Nonempty ι] {u : ι 
→ Ω → β} {τ : Ω → WithTop ι}   [inst_1 : LinearOrder ι] {𝕜 : Type u_4} [inst_2 :
 SMul 𝕜 β] (c : 𝕜),   MeasureTheory.stoppedProcess (c • u) τ = c • MeasureTheory
.stoppedProcess u τ
参数：c : 𝕜；c • u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma stoppedProcess_const_smul {𝕜 : Type*} [SMul 𝕜 β] (c : 𝕜) :
    stoppedProcess (c • u) τ = c • stoppedProcess u τ := rfl
/-
**MeasureTheory.stoppedProcess_const_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : Nonempty ι] {u : ι 
→ Ω → β} [inst_1 : LinearOrder ι]   [inst_2 : OrderBot ι], (MeasureTheory.stoppe
dProcess u fun x => ⊥) = fun x => u ⊥
参数：MeasureTheory.stoppedProcess u fun x => ⊥。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma stoppedProcess_const_bot [OrderBot ι] :
    stoppedProcess u (fun _ ↦ ⊥) = fun _ ↦ u ⊥ := by
  ext; simp [stoppedProcess, ← WithTop.coe_bot]
/-
**MeasureTheory.stoppedProcess_const_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} [inst : Nonempty ι] {u : ι 
→ Ω → β} [inst_1 : LinearOrder ι],   (MeasureTheory.stoppedProcess u fun x => ⊤)
 = u
参数：MeasureTheory.stoppedProcess u fun x => ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma stoppedProcess_const_top : stoppedProcess u (fun _ ↦ ⊤) = u := by
  ext; simp [stoppedProcess]
/-
**MeasureTheory.stoppedValue_stoppedProcess** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：stoppedValue_stoppedProcess : stoppedValue (stoppedProcess u τ) σ = fun ω 
=> if σ ω != ⊤ then stoppedValue u (fun ω => min (σ ω) (τ ω)) ω else stoppedValu
e u (fun ω => min (Classical.arbitrary ι) (τ ω)) ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem stoppedValue_stoppedProcess :
    stoppedValue (stoppedProcess u τ) σ =
      fun ω ↦ if σ ω ≠ ⊤ then stoppedValue u (fun ω ↦ min (σ ω) (τ ω)) ω
      else stoppedValue u (fun ω ↦ min (Classical.arbitrary ι) (τ ω)) ω := by
  ext ω
  simp only [stoppedValue, stoppedProcess, ne_eq, ite_not]
  cases σ ω <;> cases τ ω <;> simp
/-
**MeasureTheory.stoppedValue_stoppedProcess_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：stoppedValue_stoppedProcess_apply {ω : Ω} (hω : σ ω != ⊤) : stoppedValue (
stoppedProcess u τ) σ ω = stoppedValue u (fun ω => min (σ ω) (τ ω)) ω
参数：hω : σ ω != ⊤。
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
· 使用定理 `MeasureTheory.stoppedValue_stoppedProcess`：stoppedValue_stoppedProcess :
 stoppedValue (stoppedProcess u τ) σ = fun ω => if σ ω != ⊤ then stoppedValue u 
(fun ω => min (σ ω) (τ ω)) ω el…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stoppedValue_stoppedProcess_apply {ω : Ω} (hω : σ ω ≠ ⊤) :
    stoppedValue (stoppedProcess u τ) σ ω = stoppedValue u (fun ω ↦ min (σ ω) (τ ω)) ω := by
  simp [stoppedValue_stoppedProcess, hω]
/-
**MeasureTheory.stoppedValue_stoppedProcess_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：stoppedValue_stoppedProcess_ae_eq {μ : Measure Ω} (hσ : forallᵐ ω ∂μ, σ ω 
!= ⊤) : stoppedValue (stoppedProcess u τ) σ =ᵐ[μ] stoppedValue u (fun ω => min (
σ ω) (τ ω))
参数：hσ : forallᵐ ω ∂μ, σ ω != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.stoppedValue_stoppedProcess`：stoppedValue_stoppedProcess :
 stoppedValue (stoppedProcess u τ) σ = fun ω => if σ ω != ⊤ then stoppedValue u 
(fun ω => min (σ ω) (τ ω)) ω el…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stoppedValue_stoppedProcess_ae_eq {μ : Measure Ω}
    (hσ : ∀ᵐ ω ∂μ, σ ω ≠ ⊤) :
    stoppedValue (stoppedProcess u τ) σ =ᵐ[μ] stoppedValue u (fun ω ↦ min (σ ω) (τ ω)) := by
  filter_upwards [hσ] with ω hσ using by simp [stoppedValue_stoppedProcess, hσ]
/-
**MeasureTheory.stoppedProcess_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：stoppedProcess_eq_of_le {i : ι} {ω : Ω} (h : i <= τ ω) : stoppedProcess u 
τ i ω = u i ω
参数：h : i <= τ ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stoppedProcess_eq_of_le {i : ι} {ω : Ω} (h : i ≤ τ ω) :
    stoppedProcess u τ i ω = u i ω := by simp [stoppedProcess, min_eq_left h]
/-
**MeasureTheory.stoppedProcess_eq_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：stoppedProcess_eq_of_ge {i : ι} {ω : Ω} (h : τ ω <= i) : stoppedProcess u 
τ i ω = u (τ ω).untopA ω
参数：h : τ ω <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stoppedProcess_eq_of_ge {i : ι} {ω : Ω} (h : τ ω ≤ i) :
    stoppedProcess u τ i ω = u (τ ω).untopA ω := by simp [stoppedProcess, min_eq_right h]
/-
**MeasureTheory.stoppedProcess_indicator_comm** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：stoppedProcess_indicator_comm [Zero β] {s : Set Ω} (i : ι) : stoppedProces
s (fun i => s.indicator (u i)) τ i = s.indicator (stoppedProcess u τ i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma stoppedProcess_indicator_comm [Zero β] {s : Set Ω} (i : ι) :
    stoppedProcess (fun i ↦ s.indicator (u i)) τ i = s.indicator (stoppedProcess u τ i) := by
  ext ω
  by_cases hω : ω ∈ s <;> simp [stoppedProcess, hω]
/-
**MeasureTheory.stoppedProcess_indicator_comm'** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：stoppedProcess_indicator_comm' [Zero β] {s : Set Ω} : stoppedProcess (fun 
i => s.indicator (u i)) τ = fun i => s.indicator (stoppedProcess u τ i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.stoppedProcess_indicator_comm`：stoppedProcess_indicator_co
mm [Zero β] {s : Set Ω} (i : ι) : stoppedProcess (fun i => s.indicator (u i)) τ 
i = s.indicator (stoppedProcess u…
-/
lemma stoppedProcess_indicator_comm' [Zero β] {s : Set Ω} :
    stoppedProcess (fun i ↦ s.indicator (u i)) τ = fun i ↦ s.indicator (stoppedProcess u τ i) := by
  ext i ω
  rw [stoppedProcess_indicator_comm]

@[simp]
/-
**MeasureTheory.stoppedProcess_stoppedProcess** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：stoppedProcess_stoppedProcess : stoppedProcess (stoppedProcess u τ) σ = st
oppedProcess u (σ ⊓ τ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `WithTop.untopA_eq_untop`：∀ {α : Type u_1} [inst : Nonempty α] {a : WithT
op α} (ha : a ≠ ⊤), a.untopA = a.untop ha
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
· 使用定理 `WithTop.coe_ne_top`：∀ {α : Type u_1} {a : α}, ↑a ≠ ⊤
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用引理 `min_assoc`：min_assoc (a b c : α) : min (min a b) c = min a (min b c)
· 使用定理 `Pi.inf_apply`：∀ {ι : Type u_1} {α' : ι → Type u_2} [inst : (i : ι) → Min
 (α' i)] (f g : (i : ι) → α' i) (i : ι), (f ⊓ g) i = f i ⊓ g i
-/
theorem stoppedProcess_stoppedProcess :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (σ ⊓ τ) := by
  ext i ω
  simp_rw [stoppedProcess]
  by_cases hτ : τ ω = ⊤
  · simp [hτ]
  by_cases hσ : σ ω = ⊤
  · simp [hσ]
  by_cases hστ : σ ω ≤ τ ω
  · rw [min_eq_left, untopA_eq_untop coe_ne_top]
    · simp [hστ]
    · refine le_trans ?_ hστ
      simp [untopA_eq_untop]
  · nth_rewrite 2 [untopA_eq_untop]
    · rw [coe_untop, min_assoc, Pi.inf_apply]
    · exact (lt_of_le_of_lt (min_le_right _ _) <| lt_top_iff_ne_top.2 hσ).ne
/-
**MeasureTheory.stoppedProcess_stoppedProcess'** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：stoppedProcess_stoppedProcess' : stoppedProcess (stoppedProcess u τ) σ = s
toppedProcess u (fun ω => min (σ ω) (τ ω))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.stoppedProcess_stoppedProcess`：stoppedProcess_stoppedProce
ss : stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (σ ⊓ τ)
-/
theorem stoppedProcess_stoppedProcess' :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (fun ω ↦ min (σ ω) (τ ω)) := by
  rw [stoppedProcess_stoppedProcess]; rfl
/-
**MeasureTheory.stoppedProcess_stoppedProcess_of_le_right** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：stoppedProcess_stoppedProcess_of_le_right (h : σ <= τ) : stoppedProcess (s
toppedProcess u τ) σ = stoppedProcess u σ
参数：h : σ <= τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.stoppedProcess_stoppedProcess`：stoppedProcess_stoppedProce
ss : stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (σ ⊓ τ)
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stoppedProcess_stoppedProcess_of_le_right (h : σ ≤ τ) :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u σ := by simp [h]
/-
**MeasureTheory.stoppedProcess_stoppedProcess_of_le_left** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：stoppedProcess_stoppedProcess_of_le_left (h : τ <= σ) : stoppedProcess (st
oppedProcess u τ) σ = stoppedProcess u τ
参数：h : τ <= σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.stoppedProcess_stoppedProcess`：stoppedProcess_stoppedProce
ss : stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (σ ⊓ τ)
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stoppedProcess_stoppedProcess_of_le_left (h : τ ≤ σ) :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u τ := by simp [h]

section Progressive

variable [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [BorelSpace ι] [TopologicalSpace β] {f : Filtration ι m}

/-
**MeasureTheory.isStronglyProgressive_min_stopping_time** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：isStronglyProgressive_min_stopping_time [PseudoMetrizableSpace ι] (hτ : Is
StoppingTime f τ) : IsStronglyProgressive f fun i ω => (min (i : WithTop ι) (τ ω
)).untopA
参数：hτ : IsStoppingTime f τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.untopA`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 : Top
ologicalSpace ι] [inst_2 : OrderTopology ι]   [inst_3 : MeasurableSpace ι] [Bore
lSpace …
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `Measurable.subtype_val`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableS
pace α} {mβ : MeasurableSpace β} {p : β → Prop} {f : α → Subtype p},   Measurabl
e f → Measur…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `measurable_of_restrict_of_restrict_compl`：measurable_of_restrict_of_rest
rict_compl {f : α -> β} {s : Set α} (hs : MeasurableSet s) (h₁ : Measurable (s.d
omRestrict f)) (h₂ : Measurabl…
· 使用定理 `Measurable.min`：Measurable.min {f g : δ -> α} (hf : Measurable f) (hg : 
Measurable g) : Measurable fun a => min (f a) (g a)
· 使用定理 `WithTop.instBorelSpace`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 
: TopologicalSpace ι] [inst_2 : OrderTopology ι], BorelSpace (WithTop ι)
· 使用定理 `TopologicalSpace.instSecondCountableTopologyWithTop`：∀ {ι : Type u_1} [i
nst : Preorder ι] [ts : TopologicalSpace ι] [ht : OrderTopology ι] [SecondCounta
bleTopology ι],   SecondCountableTopology…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `Measurable.withTop_coe`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 
: TopologicalSpace ι] [inst_2 : OrderTopology ι]   [inst_3 : MeasurableSpace ι] 
[BorelSpace …
· 使用定理 `measurable_of_Iic`：measurable_of_Iic {f : δ -> α} (hf : forall x, Measur
ableSet (f ⁻¹' Iic x)) : Measurable f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iic_top`：Iic_top : Iic (⊤ : α) = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration
 ι m}   {τ : Ω → WithTop ι}, Measur…
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
（共 35 条，此处仅展示前 30 条）
-/
theorem isStronglyProgressive_min_stopping_time [PseudoMetrizableSpace ι]
    (hτ : IsStoppingTime f τ) :
    IsStronglyProgressive f fun i ω ↦ (min (i : WithTop ι) (τ ω)).untopA := by
  refine fun i ↦ (Measurable.untopA ?_).stronglyMeasurable
  let m_prod : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (f i)
  let m_set : ∀ t : Set (Set.Iic i × Ω), MeasurableSpace t := fun _ =>
    @Subtype.instMeasurableSpace (Set.Iic i × Ω) _ m_prod
  let s := {p : Set.Iic i × Ω | τ p.2 ≤ i}
  have hs : MeasurableSet[m_prod] s := @measurable_snd (Set.Iic i) Ω _ (f i) _ (hτ i)
  have h_meas_fst : ∀ t : Set (Set.Iic i × Ω),
      Measurable[m_set t] fun x : t => ((x : Set.Iic i × Ω).fst : ι) :=
    fun t => (@measurable_subtype_coe (Set.Iic i × Ω) m_prod _).fst.subtype_val
  refine measurable_of_restrict_of_restrict_compl hs ?_ ?_
  · refine Measurable.min (h_meas_fst s).withTop_coe ?_
    refine measurable_of_Iic fun j ↦ ?_
    cases j with
    | top => simp
    | coe j =>
      have h_set_eq : (fun x : s => τ (x : Set.Iic i × Ω).snd) ⁻¹' Set.Iic j =
          (fun x : s => (x : Set.Iic i × Ω).snd) ⁻¹' {ω | τ ω ≤ min i j} := by
        ext1 ω
        simp only [Set.mem_preimage, Set.mem_Iic, coe_min, le_inf_iff,
          Set.preimage_ofPred_eq, Set.mem_ofPred_eq, iff_and_self]
        exact fun _ => ω.prop
      rw [h_set_eq]
      suffices h_meas : @Measurable _ _ (m_set s) (f i) fun x : s ↦ (x : Set.Iic i × Ω).snd from
        h_meas (f.mono (min_le_left _ _) _ (hτ.measurableSet_le (min i j)))
      exact measurable_snd.comp (@measurable_subtype_coe _ m_prod _)
  · let sc := sᶜ
    suffices h_min_eq_left :
      (fun x : sc => min (↑(x : Set.Iic i × Ω).fst) (τ (x : Set.Iic i × Ω).snd)) = fun x : sc =>
        ↑(x : Set.Iic i × Ω).fst by
      simp +unfoldPartialApp only [sc, Set.domRestrict, h_min_eq_left]
      exact (h_meas_fst _).withTop_coe
    ext1 ω
    rw [min_eq_left]
    have hx_fst_le : ↑(ω : Set.Iic i × Ω).fst ≤ i := (ω : Set.Iic i × Ω).fst.prop
    by_cases h : τ (ω : Set.Iic i × Ω).2 = ⊤
    · simp [h]
    · lift τ (ω : Set.Iic i × Ω).2 to ι using h with t ht
      norm_cast
      refine hx_fst_le.trans (le_of_lt ?_)
      convert! ω.prop
      simp only [sc, s, not_le, Set.mem_compl_iff, Set.mem_ofPred_eq, ← ht]
      norm_cast

@[deprecated (since := "2026-04-24")]
alias progMeasurable_min_stopping_time := isStronglyProgressive_min_stopping_time
/-
**MeasureTheory.IsStronglyProgressive.stoppedProcess** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [in
st : Nonempty ι] {u : ι → Ω → β}   {τ : Ω → WithTop ι} [inst_1 : LinearOrder ι] 
[inst_2 : MeasurableSpace ι] [inst_3 : TopologicalSpace ι]   [OrderTopology ι] [
SecondCountableTopology ι] [BorelSpace ι] [inst_7 : TopologicalSpace β]   {f : M
easureTheory.Filtration ι m} [TopologicalSpace.PseudoMetrizableSpace ι],   Measu
reTheory.IsStronglyProgressive f u →     MeasureTheory.IsStoppingTime f τ → Meas
ureTheory.IsStronglyProgressive f (MeasureTheory.stoppedProcess u τ)
参数：MeasureTheory.stoppedProcess u τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isStronglyProgressive_min_stopping_time`：isStronglyProgres
sive_min_stopping_time [PseudoMetrizableSpace ι] (hτ : IsStoppingTime f τ) : IsS
tronglyProgressive f fun i ω => (min (i : W…
· 使用定理 `MeasureTheory.IsStronglyProgressive.comp`：∀ {Ω : Type u_1} {ι : Type u_2
} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}
   {β : Type u_3} [inst_1 : To…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
theorem IsStronglyProgressive.stoppedProcess [PseudoMetrizableSpace ι]
    (h : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) :
    IsStronglyProgressive f (stoppedProcess u τ) := by
  have h_meas := isStronglyProgressive_min_stopping_time hτ
  refine h.comp h_meas fun i ω ↦ ?_
  cases τ ω with
  | top => simp
  | coe t =>
    rcases le_total i t with h_it | h_ti
    · simp [(mod_cast h_it : (i : WithTop ι) ≤ t)]
    · simpa [(mod_cast h_ti : t ≤ (i : WithTop ι))]

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.stoppedProcess := IsStronglyProgressive.stoppedProcess
/-
**MeasureTheory.IsStronglyProgressive.stronglyAdapted_stoppedProcess** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [in
st : Nonempty ι] {u : ι → Ω → β}   {τ : Ω → WithTop ι} [inst_1 : LinearOrder ι] 
[inst_2 : MeasurableSpace ι] [inst_3 : TopologicalSpace ι]   [OrderTopology ι] [
SecondCountableTopology ι] [BorelSpace ι] [inst_7 : TopologicalSpace β]   {f : M
easureTheory.Filtration ι m} [TopologicalSpace.PseudoMetrizableSpace ι],   Measu
reTheory.IsStronglyProgressive f u →     MeasureTheory.IsStoppingTime f τ → Meas
ureTheory.StronglyAdapted f (MeasureTheory.stoppedProcess u τ)
参数：MeasureTheory.stoppedProcess u τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStronglyProgressive.stronglyAdapted`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filt
ration ι m}   {β : Type u_3} [inst_1 : To…
· 使用定理 `MeasureTheory.IsStronglyProgressive.stoppedProcess`：∀ {Ω : Type u_1} {β 
: Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Nonempty ι] {u : ι → 
Ω → β}   {τ : Ω → WithTop ι} [inst_1 : L…
-/
theorem IsStronglyProgressive.stronglyAdapted_stoppedProcess [PseudoMetrizableSpace ι]
    (h : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) :
    StronglyAdapted f (MeasureTheory.stoppedProcess u τ) :=
  (h.stoppedProcess hτ).stronglyAdapted

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.stronglyAdapted_stoppedProcess :=
  IsStronglyProgressive.stronglyAdapted_stoppedProcess
/-
**MeasureTheory.IsStronglyProgressive.stronglyMeasurable_stoppedProcess** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [in
st : Nonempty ι] {u : ι → Ω → β}   {τ : Ω → WithTop ι} [inst_1 : LinearOrder ι] 
[inst_2 : MeasurableSpace ι] [inst_3 : TopologicalSpace ι]   [OrderTopology ι] [
SecondCountableTopology ι] [BorelSpace ι] [inst_7 : TopologicalSpace β]   {f : M
easureTheory.Filtration ι m} [TopologicalSpace.PseudoMetrizableSpace ι],   Measu
reTheory.IsStronglyProgressive f u →     MeasureTheory.IsStoppingTime f τ → ∀ (i
 : ι), MeasureTheory.StronglyMeasurable (MeasureTheory.stoppedProcess u τ i)
参数：i : ι；MeasureTheory.stoppedProcess u τ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.IsStronglyProgressive.stronglyAdapted_stoppedProcess`：∀ {Ω
 : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Nonem
pty ι] {u : ι → Ω → β}   {τ : Ω → WithTop ι} [inst_1 : L…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
-/
theorem IsStronglyProgressive.stronglyMeasurable_stoppedProcess [PseudoMetrizableSpace ι]
    (hu : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) (i : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ i) :=
  (hu.stronglyAdapted_stoppedProcess hτ i).mono (f.le _)
/-
**MeasureTheory.stronglyMeasurable_stoppedValue_of_le** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：stronglyMeasurable_stoppedValue_of_le (h : IsStronglyProgressive f u) (hτ 
: IsStoppingTime f τ) {n : ι} (hτ_le : forall ω, τ ω <= n) : StronglyMeasurable[
f n] (stoppedValue u τ)
参数：h : IsStronglyProgressive f u；hτ : IsStoppingTime f τ；hτ_le : forall ω, τ ω <
= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.untopA_le`：∀ {α : Type u_1} [inst : PartialOrder α] {y : WithTop
 α} {b : α} [inst_1 : Nonempty α], y ≤ ↑b → y.untopA ≤ b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `Measurable.untopA`：∀ {ι : Type u_1} [inst : LinearOrder ι] [inst_1 : Top
ologicalSpace ι] [inst_2 : OrderTopology ι]   [inst_3 : MeasurableSpace ι] [Bore
lSpace …
· 使用定理 `MeasureTheory.IsStoppingTime.measurable_of_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem stronglyMeasurable_stoppedValue_of_le (h : IsStronglyProgressive f u)
    (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) :
    StronglyMeasurable[f n] (stoppedValue u τ) := by
  have hτ_le' ω : (τ ω).untopA ≤ n := untopA_le (hτ_le ω)
  have : stoppedValue u τ =
      (fun p : Set.Iic n × Ω => u (↑p.fst) p.snd) ∘ fun ω => (⟨(τ ω).untopA, hτ_le' ω⟩, ω) := by
    ext1 ω; simp only [stoppedValue, Function.comp_apply]
  rw [this]
  refine StronglyMeasurable.comp_measurable (h n) ?_
  refine (Measurable.subtype_mk ?_).prodMk measurable_id
  exact (hτ.measurable_of_le hτ_le).untopA
/-
**MeasureTheory.measurableSet_preimage_stoppedValue_inter** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory`。
形式化陈述：measurableSet_preimage_stoppedValue_inter [PseudoMetrizableSpace β] [Measu
rableSpace β] [BorelSpace β] (hf_prog : IsStronglyProgressive f u) (hτ : IsStopp
ingTime f τ) {t : Set β} (ht : MeasurableSet t) (i : ι) : MeasurableSet[f i] (st
oppedValue u τ ⁻¹' t inter {ω | τ ω <= i})
参数：hf_prog : IsStronglyProgressive f u；hτ : IsStoppingTime f τ；ht : MeasurableSe
t t；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_stoppedValue_of_le`：stronglyMeasurable_
stoppedValue_of_le (h : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) {n 
: ι} (hτ_le : forall ω, τ ω <= n) : Stron…
· 使用定理 `MeasureTheory.IsStoppingTime.min_const`：∀ {Ω : Type u_1} {ι : Type u_3} 
{m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m
}   {τ : Ω → WithTop ι},   M…
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration
 ι m}   {τ : Ω → WithTop ι}, Measur…
-/
lemma measurableSet_preimage_stoppedValue_inter [PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β]
    (hf_prog : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ)
    {t : Set β} (ht : MeasurableSet t) (i : ι) :
    MeasurableSet[f i] (stoppedValue u τ ⁻¹' t ∩ {ω | τ ω ≤ i}) := by
  have h_str_meas : ∀ i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  suffices stoppedValue u τ ⁻¹' t ∩ {ω : Ω | τ ω ≤ i} =
      (stoppedValue u fun ω => min (τ ω) i) ⁻¹' t ∩ {ω : Ω | τ ω ≤ i} by
    rw [this]; exact ((h_str_meas i).measurable ht).inter (hτ.measurableSet_le i)
  ext1 ω
  simp only [stoppedValue, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
    and_congr_left_iff]
  intro h
  rw [min_eq_left h]
/-
**MeasureTheory.measurable_stoppedValue** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measurable_stoppedValue [PseudoMetrizableSpace β] [MeasurableSpace β] [Bor
elSpace β] (hf_prog : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) : Mea
surable[hτ.measurableSpace] (stoppedValue u τ)
参数：hf_prog : IsStronglyProgressive f u；hτ : IsStoppingTime f τ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_stoppedValue_of_le`：stronglyMeasurable_
stoppedValue_of_le (h : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) {n 
: ι} (hτ_le : forall ω, τ ω <= n) : Stron…
· 使用定理 `MeasureTheory.IsStoppingTime.min_const`：∀ {Ω : Type u_1} {ι : Type u_3} 
{m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m
}   {τ : Ω → WithTop ι},   M…
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_or_left`：∀ {a b c : Prop}, a ∧ (b ∨ c) ↔ a ∧ b ∨ a ∧ c
· 使用定理 `iff_self_and`：∀ {p q : Prop}, (p ↔ p ∧ q) ↔ p → q
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用引理 `MeasureTheory.measurableSet_preimage_stoppedValue_inter`：measurableSet_p
reimage_stoppedValue_inter [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelS
pace β] (hf_prog : IsStronglyProgressive f u)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
（共 37 条，此处仅展示前 30 条）
-/
theorem measurable_stoppedValue [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf_prog : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] (stoppedValue u τ) := by
  have h_str_meas : ∀ i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  intro t ht
  refine ⟨?_, fun i ↦ measurableSet_preimage_stoppedValue_inter hf_prog hτ ht i⟩
  obtain ⟨seq : ℕ → ι, h_seq_tendsto⟩ := (atTop : Filter ι).exists_seq_tendsto
  have : stoppedValue u τ ⁻¹' t
      = (⋃ n, stoppedValue u τ ⁻¹' t ∩ {ω | τ ω ≤ seq n})
        ∪ (stoppedValue u τ ⁻¹' t ∩ {ω | τ ω = ⊤}) := by
    ext1 ω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq, exists_and_left]
    rw [← and_or_left, iff_self_and]
    intro _
    by_cases h : τ ω = ⊤
    · exact .inr h
    · lift τ ω to ι using h with t
      simp only [coe_le_coe, coe_ne_top, or_false]
      rw [tendsto_atTop] at h_seq_tendsto
      exact (h_seq_tendsto t).exists
  rw [this]
  refine MeasurableSet.union ?_ ?_
  · exact MeasurableSet.iUnion fun i ↦ le_iSup f (seq i) _
      (measurableSet_preimage_stoppedValue_inter hf_prog hτ ht (seq i))
  · have : stoppedValue u τ ⁻¹' t ∩ {ω | τ ω = ⊤}
       = (fun ω ↦ u (Classical.arbitrary ι) ω) ⁻¹' t ∩ {ω | τ ω = ⊤} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, stoppedValue, untopA,
        Set.mem_ofPred_eq, and_congr_left_iff]
      intro h
      simp [h]
    rw [this]
    refine MeasurableSet.inter (ht.preimage ?_) hτ.measurableSet_eq_top'
    exact (hf_prog.stronglyAdapted (Classical.arbitrary ι)).measurable.mono
      (le_iSup f (Classical.arbitrary ι)) le_rfl

end Progressive

end LinearOrder

section StoppedValueOfMemFinset

variable [Nonempty ι] {μ : Measure Ω} {τ : Ω → WithTop ι} {E : Type*} {p : ℝ≥0∞} {u : ι → Ω → E}

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.stoppedValue_eq_of_mem_finset** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：stoppedValue_eq_of_mem_finset [AddCommMonoid E] {s : Finset ι} (hbdd : for
all ω, τ ω in (WithTop.some '' s)) : stoppedValue u τ = ∑ i in s, Set.indicator 
{ω | τ ω = i} (u i)
参数：hbdd : forall ω, τ ω in (WithTop.some '' s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.stoppedValue.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : Ty
pe u_3} [inst : Nonempty ι] (u : ι → Ω → β) (τ : Ω → WithTop ι) (ω : Ω),   Measu
reTheory.stoppedValue…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_indicator_eq_sum_filter`：∀ {ι : Type u_1} {κ : Type u_2} {β :
 Type u_4} [inst : AddCommMonoid β] (s : Finset ι) (f : ι → κ → β) (t : ι → Set 
κ)   (g : ι → κ) [inst_1…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
-/
theorem stoppedValue_eq_of_mem_finset [AddCommMonoid E] {s : Finset ι}
   (hbdd : ∀ ω, τ ω ∈ (WithTop.some '' s)) :
    stoppedValue u τ = ∑ i ∈ s, Set.indicator {ω | τ ω = i} (u i) := by
  ext y
  classical
  rw [stoppedValue, Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  suffices {i ∈ s | y ∈ {ω : Ω | τ ω = (i : ι)}} = ({(τ y).untopA} : Finset ι) by
    rw [this, Finset.sum_singleton]
  ext1 ω
  simp only [Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_singleton]
  constructor <;> intro h
  · simp [h.2]
  · simp only [h]
    specialize hbdd y
    have : τ y ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
    lift τ y to ι using this with i hi
    simpa using hbdd
/-
**MeasureTheory.stoppedValue_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedValue_eq' [Preorder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] 
{N : ι} (hbdd : forall ω, τ ω <= N) : stoppedValue u τ = ∑ i in Finset.Iic N, Se
t.indicator {ω | τ ω = i} (u i)
参数：hbdd : forall ω, τ ω <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stoppedValue_eq_of_mem_finset`：stoppedValue_eq_of_mem_fins
et [AddCommMonoid E] {s : Finset ι} (hbdd : forall ω, τ ω in (WithTop.some '' s)
) : stoppedValue u τ = ∑ i in s, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem stoppedValue_eq' [Preorder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] {N : ι}
    (hbdd : ∀ ω, τ ω ≤ N) :
    stoppedValue u τ = ∑ i ∈ Finset.Iic N, Set.indicator {ω | τ ω = i} (u i) := by
  refine stoppedValue_eq_of_mem_finset fun ω ↦ ?_
  simp only [Finset.coe_Iic, Set.mem_image]
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩
/-
**MeasureTheory.stoppedProcess_eq_of_mem_finset** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：stoppedProcess_eq_of_mem_finset [LinearOrder ι] [AddCommMonoid E] {s : Fin
set ι} (n : ι) (hbdd : forall ω, τ ω < n -> τ ω in WithTop.some '' s) : stoppedP
rocess u τ n = Set.indicator {a | n <= τ a} (u n) + ∑ i in s with i < n, Set.ind
icator {ω | τ ω = i} (u i)
参数：n : ι；hbdd : forall ω, τ ω < n -> τ ω in WithTop.some '' s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `MeasureTheory.stoppedProcess_eq_of_le`：stoppedProcess_eq_of_le {i : ι} {
ω : Ω} (h : i <= τ ω) : stoppedProcess u τ i ω = u i ω
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.stoppedProcess_eq_of_ge`：stoppedProcess_eq_of_ge {i : ι} {
ω : Ω} (h : τ ω <= i) : stoppedProcess u τ i ω = u (τ ω).untopA ω
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem stoppedProcess_eq_of_mem_finset [LinearOrder ι] [AddCommMonoid E] {s : Finset ι} (n : ι)
    (hbdd : ∀ ω, τ ω < n → τ ω ∈ WithTop.some '' s) :
    stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
      ∑ i ∈ s with i < n, Set.indicator {ω | τ ω = i} (u i) := by
  ext ω
  rw [Pi.add_apply, Finset.sum_apply]
  rcases le_or_gt (n : WithTop ι) (τ ω) with h | h
  · rw [stoppedProcess_eq_of_le h, Set.indicator_of_mem, Finset.sum_eq_zero, add_zero]
    · intro m hm
      refine Set.indicator_of_notMem ?_ _
      rw [Finset.mem_filter] at hm
      simp only [Set.mem_ofPred_eq]
      refine (lt_of_lt_of_le ?_ h).ne'
      exact mod_cast hm.2
    · exact h
  · rw [stoppedProcess_eq_of_ge (le_of_lt h)]
    have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at h
    specialize hbdd ω h
    lift τ ω to ι using h_top with i hi
    rw [Finset.sum_eq_single_of_mem i]
    · simp only [untopD_coe]
      rw [Set.indicator_of_notMem, zero_add, Set.indicator_of_mem] <;> rw [Set.mem_ofPred]
      · exact hi.symm
      · rw [← hi]
        exact not_le.2 h
    · rw [Finset.mem_filter]
      simp only [Set.mem_image, Finset.mem_coe, coe_eq_coe, exists_eq_right] at hbdd
      exact ⟨hbdd, mod_cast h⟩
    · intro b _ hneq
      rw [Set.indicator_of_notMem]
      rw [Set.mem_ofPred, ← hi]
      exact mod_cast hneq.symm
/-
**MeasureTheory.stoppedProcess_eq''** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedProcess_eq'' [LinearOrder ι] [LocallyFiniteOrderBot ι] [AddCommMono
id E] (n : ι) : stoppedProcess u τ n = Set.indicator {a | n <= τ a} (u n) + ∑ i 
in Finset.Iio n, Set.indicator {ω | τ ω = i} (u i)
参数：n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.stoppedProcess_eq_of_mem_finset`：stoppedProcess_eq_of_mem_
finset [LinearOrder ι] [AddCommMonoid E] {s : Finset ι} (n : ι) (hbdd : forall ω
, τ ω < n -> τ ω in WithTop.some ''…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.Iio_filter_lt`：Iio_filter_lt {α} [LinearOrder α] [LocallyFiniteOr
derBot α] (a b : α) : {x in Iio a | x < b} = Iio (min a b)
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem stoppedProcess_eq'' [LinearOrder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] (n : ι) :
    stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
      ∑ i ∈ Finset.Iio n, Set.indicator {ω | τ ω = i} (u i) := by
  have h_mem : ∀ ω, τ ω < n → τ ω ∈ WithTop.some '' (Finset.Iio n) := by
    intro ω h
    simp only [Finset.coe_Iio, Set.mem_image, Set.mem_Iio]
    have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at h
    lift τ ω to ι using h_top with i hi
    exact ⟨i, mod_cast h, rfl⟩
  rw [stoppedProcess_eq_of_mem_finset n h_mem]
  congr with i
  simp

section StoppedValue

variable [PartialOrder ι] {ℱ : Filtration ι m} [NormedAddCommGroup E]

/-
**MeasureTheory.memLp_stoppedValue_of_mem_finset** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：memLp_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : forall n,
 MemLp (u n) p μ) {s : Finset ι} (hbdd : forall ω, τ ω in WithTop.some '' s) : M
emLp (stoppedValue u τ) p μ
参数：hτ : IsStoppingTime ℱ τ；hu : forall n, MemLp (u n) p μ；hbdd : forall ω, τ ω i
n WithTop.some '' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.stoppedValue_eq_of_mem_finset`：stoppedValue_eq_of_mem_fins
et [AddCommMonoid E] {s : Finset ι} (hbdd : forall ω, τ ω in (WithTop.some '' s)
) : stoppedValue u τ = ∑ i in s, …
· 使用定理 `MeasureTheory.memLp_finsetSum'`：memLp_finsetSum' [ContinuousAdd ε'] {ι} 
(s : Finset ι) {f : ι -> α -> ε'} (hf : forall i in s, MemLp (f i) p μ) : MemLp 
(∑ i in s, f i) p μ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.indicator`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topologica
lSpace ε] [inst_1 :…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range`：∀ {Ω :
 Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : PartialOrder ι] {τ : Ω
 → WithTop ι}   {f : MeasureTheory.Filtration ι m},   …
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem memLp_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, MemLp (u n) p μ)
    {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ WithTop.some '' s) :
    MemLp (stoppedValue u τ) p μ := by
  rw [stoppedValue_eq_of_mem_finset hbdd]
  refine memLp_finsetSum' _ fun i _ => MemLp.indicator ?_ (hu i)
  refine ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq_of_countable_range ?_ i)
  have : Set.range τ ⊆ WithTop.some '' s := by
    rintro x ⟨y, rfl⟩
    exact hbdd y
  exact ((Finset.finite_toSet s).image _).subset this |>.countable
/-
**MeasureTheory.memLp_stoppedValue** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ) (hu
 : forall n, MemLp (u n) p μ) {N : ι} (hbdd : forall ω, τ ω <= N) : MemLp (stopp
edValue u τ) p μ
参数：hτ : IsStoppingTime ℱ τ；hu : forall n, MemLp (u n) p μ；hbdd : forall ω, τ ω <
= N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.memLp_stoppedValue_of_mem_finset`：memLp_stoppedValue_of_me
m_finset (hτ : IsStoppingTime ℱ τ) (hu : forall n, MemLp (u n) p μ) {s : Finset 
ι} (hbdd : forall ω, τ ω in WithTop.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem memLp_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, MemLp (u n) p μ) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) : MemLp (stoppedValue u τ) p μ := by
  refine memLp_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩
/-
**MeasureTheory.integrable_stoppedValue_of_mem_finset** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：integrable_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : fora
ll n, Integrable (u n) μ) {s : Finset ι} (hbdd : forall ω, τ ω in WithTop.some '
' s) : Integrable (stoppedValue u τ) μ
参数：hτ : IsStoppingTime ℱ τ；hu : forall n, Integrable (u n) μ；hbdd : forall ω, τ 
ω in WithTop.some '' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.memLp_stoppedValue_of_mem_finset`：memLp_stoppedValue_of_me
m_finset (hτ : IsStoppingTime ℱ τ) (hu : forall n, MemLp (u n) p μ) {s : Finset 
ι} (hbdd : forall ω, τ ω in WithTop.…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem integrable_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ WithTop.some '' s) :
    Integrable (stoppedValue u τ) μ := by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedValue_of_mem_finset hτ hu hbdd

variable (ι)
/-
**MeasureTheory.integrable_stoppedValue** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：integrable_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ
) (hu : forall n, Integrable (u n) μ) {N : ι} (hbdd : forall ω, τ ω <= N) : Inte
grable (stoppedValue u τ) μ
参数：hτ : IsStoppingTime ℱ τ；hu : forall n, Integrable (u n) μ；hbdd : forall ω, τ 
ω <= N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_stoppedValue_of_mem_finset`：integrable_stoppedV
alue_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : forall n, Integrable (u n) μ)
 {s : Finset ι} (hbdd : forall ω, τ ω in …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem integrable_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue u τ) μ := by
  refine integrable_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

end StoppedValue

section StoppedProcess

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
  {ℱ : Filtration ι m} [NormedAddCommGroup E]

/-
**MeasureTheory.memLp_stoppedProcess_of_mem_finset** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：memLp_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : forall 
n, MemLp (u n) p μ) (n : ι) {s : Finset ι} (hbdd : forall ω, τ ω < n -> τ ω in W
ithTop.some '' s) : MemLp (stoppedProcess u τ n) p μ
参数：hτ : IsStoppingTime ℱ τ；hu : forall n, MemLp (u n) p μ；n : ι；hbdd : forall ω,
 τ ω < n -> τ ω in WithTop.some '' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.stoppedProcess_eq_of_mem_finset`：stoppedProcess_eq_of_mem_
finset [LinearOrder ι] [AddCommMonoid E] {s : Finset ι} (n : ι) (hbdd : forall ω
, τ ω < n -> τ ω in WithTop.some ''…
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.indicator`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topologica
lSpace ε] [inst_1 :…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_ge`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `MeasureTheory.memLp_finsetSum`：memLp_finsetSum [ContinuousAdd ε'] {ι} (s
 : Finset ι) {f : ι -> α -> ε'} (hf : forall i in s, MemLp (f i) p μ) : MemLp (f
un a => ∑ i in s, f…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem memLp_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, MemLp (u n) p μ)
    (n : ι) {s : Finset ι} (hbdd : ∀ ω, τ ω < n → τ ω ∈ WithTop.some '' s) :
    MemLp (stoppedProcess u τ n) p μ := by
  rw [stoppedProcess_eq_of_mem_finset n hbdd]
  refine MemLp.add ?_ ?_
  · exact MemLp.indicator (ℱ.le n {a : Ω | n ≤ τ a} (hτ.measurableSet_ge n)) (hu n)
  · suffices MemLp (fun ω => ∑ i ∈ s with i < n, {a : Ω | τ a = i}.indicator (u i) ω) p μ by
      convert! this using 1; ext1 ω; simp only [Finset.sum_apply]
    refine memLp_finsetSum _ fun i _ => MemLp.indicator ?_ (hu i)
    exact ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq i)
/-
**MeasureTheory.memLp_stoppedProcess** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ) (
hu : forall n, MemLp (u n) p μ) (n : ι) : MemLp (stoppedProcess u τ n) p μ
参数：hτ : IsStoppingTime ℱ τ；hu : forall n, MemLp (u n) p μ；n : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.memLp_stoppedProcess_of_mem_finset`：memLp_stoppedProcess_o
f_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : forall n, MemLp (u n) p μ) (n : ι) 
{s : Finset ι} (hbdd : forall ω, τ ω <…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem memLp_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, MemLp (u n) p μ) (n : ι) :
    MemLp (stoppedProcess u τ n) p μ := by
  refine memLp_stoppedProcess_of_mem_finset hτ hu n (s := Finset.Iic n) fun ω h => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at h
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast h.le, rfl⟩
/-
**MeasureTheory.integrable_stoppedProcess_of_mem_finset** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：integrable_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : fo
rall n, Integrable (u n) μ) (n : ι) {s : Finset ι} (hbdd : forall ω, τ ω < n -> 
τ ω in WithTop.some '' s) : Integrable (stoppedProcess u τ n) μ
参数：hτ : IsStoppingTime ℱ τ；hu : forall n, Integrable (u n) μ；n : ι；hbdd : forall
 ω, τ ω < n -> τ ω in WithTop.some '' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.memLp_stoppedProcess_of_mem_finset`：memLp_stoppedProcess_o
f_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : forall n, MemLp (u n) p μ) (n : ι) 
{s : Finset ι} (hbdd : forall ω, τ ω <…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem integrable_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) (n : ι) {s : Finset ι}
    (hbdd : ∀ ω, τ ω < n → τ ω ∈ WithTop.some '' s) :
    Integrable (stoppedProcess u τ n) μ := by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedProcess_of_mem_finset hτ hu n hbdd
/-
**MeasureTheory.integrable_stoppedProcess** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrable_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ
 τ) (hu : forall n, Integrable (u n) μ) (n : ι) : Integrable (stoppedProcess u τ
 n) μ
参数：hτ : IsStoppingTime ℱ τ；hu : forall n, Integrable (u n) μ；n : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_stoppedProcess_of_mem_finset`：integrable_stoppe
dProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : forall n, Integrable (u n
) μ) (n : ι) {s : Finset ι} (hbdd : forall …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem integrable_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) (n : ι) : Integrable (stoppedProcess u τ n) μ := by
  refine integrable_stoppedProcess_of_mem_finset hτ hu n (s := Finset.Iic n) fun ω h => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at h
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast h.le, rfl⟩

end StoppedProcess

end StoppedValueOfMemFinset

section StronglyAdaptedStoppedProcess

variable [TopologicalSpace β] [PseudoMetrizableSpace β] [Nonempty ι] [LinearOrder ι]
  [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
  [MeasurableSpace ι] [BorelSpace ι]
  {f : Filtration ι m} {u : ι → Ω → β} {τ : Ω → WithTop ι}

/-- The stopped process of a strongly adapted process with continuous paths is strongly adapted. -/
/-
**MeasureTheory.StronglyAdapted.stoppedProcess** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [in
st : TopologicalSpace β]   [TopologicalSpace.PseudoMetrizableSpace β] [inst_2 : 
Nonempty ι] [inst_3 : LinearOrder ι]   [inst_4 : TopologicalSpace ι] [SecondCoun
tableTopology ι] [OrderTopology ι] [inst_7 : MeasurableSpace ι]   [BorelSpace ι]
 {f : MeasureTheory.Filtration ι m} {u : ι → Ω → β} {τ : Ω → WithTop ι}   [Topol
ogicalSpace.MetrizableSpace ι],   MeasureTheory.StronglyAdapted f u →     (∀ (ω 
: Ω), Continuous fun i => u i ω) →       MeasureTheory.IsStoppingTime f τ → Meas
ureTheory.StronglyAdapted f (MeasureTheory.stoppedProcess u τ)
参数：∀ (ω : Ω), Continuous fun i => u i ω；MeasureTheory.stoppedProcess u τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStronglyProgressive.stronglyAdapted`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filt
ration ι m}   {β : Type u_3} [inst_1 : To…
· 使用定理 `MeasureTheory.IsStronglyProgressive.stoppedProcess`：∀ {Ω : Type u_1} {β 
: Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Nonempty ι] {u : ι → 
Ω → β}   {τ : Ω → WithTop ι} [inst_1 : L…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous`：∀ {Ω 
: Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : Meas
ureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : To…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α

--- 原说明 ---
The stopped process of a strongly adapted process with continuous paths is stron
gly adapted.
-/
theorem StronglyAdapted.stoppedProcess [MetrizableSpace ι] (hu : StronglyAdapted f u)
    (hu_cont : ∀ ω, Continuous fun i => u i ω) (hτ : IsStoppingTime f τ) :
    StronglyAdapted f (stoppedProcess u τ) :=
  ((hu.isStronglyProgressive_of_continuous hu_cont).stoppedProcess hτ).stronglyAdapted

/-- If the indexing order has the discrete topology, then the stopped process of a strongly adapted
process is strongly adapted. -/
/-
**MeasureTheory.StronglyAdapted.stoppedProcess_of_discrete** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [in
st : TopologicalSpace β]   [TopologicalSpace.PseudoMetrizableSpace β] [inst_2 : 
Nonempty ι] [inst_3 : LinearOrder ι]   [inst_4 : TopologicalSpace ι] [SecondCoun
tableTopology ι] [OrderTopology ι] [inst_7 : MeasurableSpace ι]   [BorelSpace ι]
 {f : MeasureTheory.Filtration ι m} {u : ι → Ω → β} {τ : Ω → WithTop ι} [Discret
eTopology ι],   MeasureTheory.StronglyAdapted f u →     MeasureTheory.IsStopping
Time f τ → MeasureTheory.StronglyAdapted f (MeasureTheory.stoppedProcess u τ)
参数：MeasureTheory.stoppedProcess u τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStronglyProgressive.stronglyAdapted`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filt
ration ι m}   {β : Type u_3} [inst_1 : To…
· 使用定理 `MeasureTheory.IsStronglyProgressive.stoppedProcess`：∀ {Ω : Type u_1} {β 
: Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Nonempty ι] {u : ι → 
Ω → β}   {τ : Ω → WithTop ι} [inst_1 : L…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `TopologicalSpace.DiscreteTopology.metrizableSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] [DiscreteTopology X], TopologicalSpace.MetrizableSpace X
· 使用定理 `MeasureTheory.StronglyAdapted.isStronglyProgressive_of_discrete`：∀ {Ω : 
Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : Measur
eTheory.Filtration ι m}   {β : Type u_3} [inst_1 : To…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α

--- 原说明 ---
If the indexing order has the discrete topology, then the stopped process of a s
trongly adapted
process is strongly adapted.
-/
theorem StronglyAdapted.stoppedProcess_of_discrete [DiscreteTopology ι] (hu : StronglyAdapted f u)
    (hτ : IsStoppingTime f τ) : StronglyAdapted f (MeasureTheory.stoppedProcess u τ) :=
  (hu.isStronglyProgressive_of_discrete.stoppedProcess hτ).stronglyAdapted
/-
**MeasureTheory.StronglyAdapted.stronglyMeasurable_stoppedProcess** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [in
st : TopologicalSpace β]   [TopologicalSpace.PseudoMetrizableSpace β] [inst_2 : 
Nonempty ι] [inst_3 : LinearOrder ι]   [inst_4 : TopologicalSpace ι] [SecondCoun
tableTopology ι] [OrderTopology ι] [inst_7 : MeasurableSpace ι]   [BorelSpace ι]
 {f : MeasureTheory.Filtration ι m} {u : ι → Ω → β} {τ : Ω → WithTop ι}   [Topol
ogicalSpace.MetrizableSpace ι],   MeasureTheory.StronglyAdapted f u →     (∀ (ω 
: Ω), Continuous fun i => u i ω) →       MeasureTheory.IsStoppingTime f τ →     
    ∀ (n : ι), MeasureTheory.StronglyMeasurable (MeasureTheory.stoppedProcess u 
τ n)
参数：∀ (ω : Ω), Continuous fun i => u i ω；n : ι；MeasureTheory.stoppedProcess u τ n
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStronglyProgressive.stronglyMeasurable_stoppedProcess`：∀
 {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : No
nempty ι] {u : ι → Ω → β}   {τ : Ω → WithTop ι} [inst_1 : L…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous`：∀ {Ω 
: Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : Meas
ureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : To…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem StronglyAdapted.stronglyMeasurable_stoppedProcess [MetrizableSpace ι]
    (hu : StronglyAdapted f u) (hu_cont : ∀ ω, Continuous fun i => u i ω) (hτ : IsStoppingTime f τ)
    (n : ι) : StronglyMeasurable (MeasureTheory.stoppedProcess u τ n) :=
  (hu.isStronglyProgressive_of_continuous hu_cont).stronglyMeasurable_stoppedProcess hτ n
/-
**MeasureTheory.StronglyAdapted.stronglyMeasurable_stoppedProcess_of_discrete** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [in
st : TopologicalSpace β]   [TopologicalSpace.PseudoMetrizableSpace β] [inst_2 : 
Nonempty ι] [inst_3 : LinearOrder ι]   [inst_4 : TopologicalSpace ι] [SecondCoun
tableTopology ι] [OrderTopology ι] [inst_7 : MeasurableSpace ι]   [BorelSpace ι]
 {f : MeasureTheory.Filtration ι m} {u : ι → Ω → β} {τ : Ω → WithTop ι} [Discret
eTopology ι],   MeasureTheory.StronglyAdapted f u →     MeasureTheory.IsStopping
Time f τ → ∀ (n : ι), MeasureTheory.StronglyMeasurable (MeasureTheory.stoppedPro
cess u τ n)
参数：n : ι；MeasureTheory.stoppedProcess u τ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStronglyProgressive.stronglyMeasurable_stoppedProcess`：∀
 {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : No
nempty ι] {u : ι → Ω → β}   {τ : Ω → WithTop ι} [inst_1 : L…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `TopologicalSpace.DiscreteTopology.metrizableSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] [DiscreteTopology X], TopologicalSpace.MetrizableSpace X
· 使用定理 `MeasureTheory.StronglyAdapted.isStronglyProgressive_of_discrete`：∀ {Ω : 
Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : Measur
eTheory.Filtration ι m}   {β : Type u_3} [inst_1 : To…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem StronglyAdapted.stronglyMeasurable_stoppedProcess_of_discrete [DiscreteTopology ι]
    (hu : StronglyAdapted f u) (hτ : IsStoppingTime f τ) (n : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ n) :=
  hu.isStronglyProgressive_of_discrete.stronglyMeasurable_stoppedProcess hτ n

end StronglyAdaptedStoppedProcess

section Nat

/-! ### Filtrations indexed by `ℕ` -/


open Filtration

variable {u : ℕ → Ω → β} {τ π : Ω → ℕ∞}

/-
**MeasureTheory.stoppedValue_sub_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：stoppedValue_sub_eq_sum [AddCommGroup β] (hle : τ <= π) (hπ : forall ω, π 
ω != ∞) : stoppedValue u π - stoppedValue u τ = fun ω => (∑ i in Finset.Ico (τ ω
).untopA (π ω).untopA, (u (i + 1) - u i)) ω
参数：hle : τ <= π；hπ : forall ω, π ω != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `WithTop.untopA_mono`：∀ {α : Type u_1} [inst : LE α] {x y : WithTop α} [i
nst_1 : Nonempty α], x ≠ ⊤ → y ≤ x → y.untopA ≤ x.untopA
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_Ico_eq_sub`：∀ {δ : Type u_4} [inst : AddCommGroup δ] (f : ℕ →
 δ) {m n : ℕ},   m ≤ n → ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range n, f k -
 ∑ k ∈ Fins…
· 使用定理 `Finset.sum_range_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (f : ℕ → 
G) (n : ℕ), ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stoppedValue_sub_eq_sum [AddCommGroup β] (hle : τ ≤ π) (hπ : ∀ ω, π ω ≠ ∞) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i ∈ Finset.Ico (τ ω).untopA (π ω).untopA, (u (i + 1) - u i)) ω := by
  ext ω
  have h_le' : (τ ω).untopA ≤ (π ω).untopA := untopA_mono (mod_cast hπ ω) (hle ω)
  rw [Finset.sum_Ico_eq_sub _ h_le', Finset.sum_range_sub, Finset.sum_range_sub]
  simp [stoppedValue]
/-
**MeasureTheory.stoppedValue_sub_eq_sum'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：stoppedValue_sub_eq_sum' [AddCommGroup β] (hle : τ <= π) {N : Nat} (hbdd :
 forall ω, π ω <= N) : stoppedValue u π - stoppedValue u τ = fun ω => (∑ i in Fi
nset.range (N + 1), Set.indicator {ω | τ ω <= i ∧ i < π ω} (u (i + 1) - u i)) ω
参数：hle : τ <= π；hbdd : forall ω, π ω <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.stoppedValue_sub_eq_sum`：stoppedValue_sub_eq_sum [AddCommG
roup β] (hle : τ <= π) (hπ : forall ω, π ω != ∞) : stoppedValue u π - stoppedVal
ue u τ = fun ω => (∑ i in F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_indicator_eq_sum_filter`：∀ {ι : Type u_1} {κ : Type u_2} {β :
 Type u_4} [inst : AddCommMonoid β] (s : Finset ι) (f : ι → κ → β) (t : ι → Set 
κ)   (g : ι → κ) [inst_1…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem stoppedValue_sub_eq_sum' [AddCommGroup β] (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i ∈ Finset.range (N + 1), Set.indicator {ω | τ ω ≤ i ∧ i < π ω} (u (i + 1) - u i)) ω := by
  have hπ_top ω : π ω ≠ ⊤ := fun h ↦ by specialize hbdd ω; simp [h] at hbdd
  have hτ_top ω : τ ω ≠ ⊤ := ne_top_of_le_ne_top (hπ_top ω) (mod_cast hle ω)
  rw [stoppedValue_sub_eq_sum hle]
  swap; · intro ω; exact mod_cast hπ_top ω
  ext ω
  simp only [Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Set.mem_ofPred_eq, Finset.mem_Ico]
  specialize hbdd ω
  lift τ ω to ℕ using hτ_top ω with t ht
  lift π ω to ℕ using hπ_top ω with b hb
  simp only [Nat.cast_le] at hbdd
  simp
  grind

section AddCommMonoid

variable [AddCommMonoid β]

/-
**MeasureTheory.stoppedValue_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedValue_eq {N : Nat} (hbdd : forall ω, τ ω <= N) : stoppedValue u τ =
 fun x => (∑ i in Finset.range (N + 1), Set.indicator {ω | τ ω = i} (u i)) x
参数：hbdd : forall ω, τ ω <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stoppedValue_eq_of_mem_finset`：stoppedValue_eq_of_mem_fins
et [AddCommMonoid E] {s : Finset ι} (hbdd : forall ω, τ ω in (WithTop.some '' s)
) : stoppedValue u τ = ∑ i in s, …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
-/
theorem stoppedValue_eq {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) : stoppedValue u τ = fun x =>
    (∑ i ∈ Finset.range (N + 1), Set.indicator {ω | τ ω = i} (u i)) x := by
  refine stoppedValue_eq_of_mem_finset fun ω ↦ ?_
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ℕ using h_top with t ht
  simp only [Nat.cast_le] at hbdd
  simp only [ENat.some_eq_natCast, Finset.coe_range]
  exact ⟨t, by simpa, Nat.cast_inj.mpr rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.stoppedProcess_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedProcess_eq (n : Nat) : stoppedProcess u τ n = Set.indicator {a | n 
<= τ a} (u n) + ∑ i in Finset.range n, Set.indicator {ω | τ ω = i} (u i)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.stoppedProcess_eq''`：stoppedProcess_eq'' [LinearOrder ι] [
LocallyFiniteOrderBot ι] [AddCommMonoid E] (n : ι) : stoppedProcess u τ n = Set.
indicator {a | n <= τ a…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem stoppedProcess_eq (n : ℕ) : stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
    ∑ i ∈ Finset.range n, Set.indicator {ω | τ ω = i} (u i) := by
  rw [stoppedProcess_eq'' n]
  congr with i
  rw [Finset.mem_Iio, Finset.mem_range]

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.stoppedProcess_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stoppedProcess_eq' (n : Nat) : stoppedProcess u τ n = Set.indicator {a | n
 + 1 <= τ a} (u n) + ∑ i in Finset.range (n + 1), Set.indicator {a | τ a = i} (u
 i)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_union_of_notMem_inter`：∀ {α : Type u_1} {M : Type u_4} [in
st : AddZeroClass M] {s t : Set α} {a : α},   a ∉ s ∩ t → ∀ (f : α → M), (s ∪ t)
.indicator f a = s.indica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.ofPred_or`：ofPred_or {p q : α -> Prop} : { a | p a ∨ q a } = { a | p
 a } union { a | q a }
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.stoppedProcess_eq`：stoppedProcess_eq (n : Nat) : stoppedPr
ocess u τ n = Set.indicator {a | n <= τ a} (u n) + ∑ i in Finset.range n, Set.in
dicator {ω | τ ω = i}…
· 使用定理 `Finset.sum_range_succ_comm`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f
 : ℕ → M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = f n + ∑ x ∈ Finset.range 
n, f x
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem stoppedProcess_eq' (n : ℕ) : stoppedProcess u τ n = Set.indicator {a | n + 1 ≤ τ a} (u n) +
    ∑ i ∈ Finset.range (n + 1), Set.indicator {a | τ a = i} (u i) := by
  have : {a | n ≤ τ a}.indicator (u n) =
      {a | n + 1 ≤ τ a}.indicator (u n) + {a | τ a = n}.indicator (u n) := by
    ext x
    rw [add_comm, Pi.add_apply, ← Set.indicator_union_of_notMem_inter]
    · simp_rw [@eq_comm _ _ (n : WithTop ℕ), @le_iff_eq_or_lt _ _ (n : WithTop ℕ)]
      have : {a | ↑n + 1 ≤ τ a} = {a | ↑n < τ a} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        cases τ ω with
        | top => simp
        | coe t =>
          simp only [Nat.cast_lt]
          norm_cast
      rw [this, Set.ofPred_or]
    · rintro ⟨h₁, h₂⟩
      rw [Set.mem_ofPred] at h₁ h₂
      rw [h₁] at h₂
      norm_cast at h₂
      grind
  rw [stoppedProcess_eq, this, Finset.sum_range_succ_comm, ← add_assoc]

end AddCommMonoid

end Nat

section PiecewiseConst

variable [Preorder ι] {𝒢 : Filtration ι m} {τ η : Ω → WithTop ι} {i j : ι} {s : Set Ω}
  [DecidablePred (· ∈ s)]

/-- Given stopping times `τ` and `η` which are bounded below, `Set.piecewise s τ η` is also
a stopping time with respect to the same filtration. -/
/-
**MeasureTheory.IsStoppingTime.piecewise_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.IsStoppingTime`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Preorder ι
] {𝒢 : MeasureTheory.Filtration ι m}   {τ η : Ω → WithTop ι} {i : ι} {s : Set Ω}
 [inst_1 : DecidablePred fun x => x ∈ s],   MeasureTheory.IsStoppingTime 𝒢 τ →  
   MeasureTheory.IsStoppingTime 𝒢 η →       (∀ (ω : Ω), ↑i ≤ τ ω) → (∀ (ω : Ω), 
↑i ≤ η ω) → MeasurableSet s → MeasureTheory.IsStoppingTime 𝒢 (s.piecewise τ η)
参数：∀ (ω : Ω), ↑i ≤ τ ω；∀ (ω : Ω), ↑i ≤ η ω；s.piecewise τ η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)

--- 原说明 ---
Given stopping times `τ` and `η` which are bounded below, `Set.piecewise s τ η` 
is also
a stopping time with respect to the same filtration.
-/
theorem IsStoppingTime.piecewise_of_le (hτ_st : IsStoppingTime 𝒢 τ) (hη_st : IsStoppingTime 𝒢 η)
    (hτ : ∀ ω, i ≤ τ ω) (hη : ∀ ω, i ≤ η ω) (hs : MeasurableSet[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise τ η) := by
  intro n
  have : {ω | s.piecewise τ η ω ≤ n} = s ∩ {ω | τ ω ≤ n} ∪ sᶜ ∩ {ω | η ω ≤ n} := by
    ext1 ω
    simp only [Set.piecewise, Set.mem_ofPred_eq]
    by_cases hx : ω ∈ s <;> simp [hx]
  rw [this]
  by_cases hin : i ≤ n
  · have hs_n : MeasurableSet[𝒢 n] s := 𝒢.mono hin _ hs
    exact (hs_n.inter (hτ_st n)).union (hs_n.compl.inter (hη_st n))
  · have hτn : ∀ ω, ¬τ ω ≤ n := fun ω hτn => hin (mod_cast (hτ ω).trans hτn)
    have hηn : ∀ ω, ¬η ω ≤ n := fun ω hηn => hin (mod_cast (hη ω).trans hηn)
    simp [hτn, hηn, @MeasurableSet.empty _ _]
/-
**MeasureTheory.isStoppingTime_piecewise_const** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：isStoppingTime_piecewise_const (hij : i <= j) (hs : MeasurableSet[𝒢 i] s) 
: IsStoppingTime 𝒢 (s.piecewise (fun _ => i) fun _ => j)
参数：hij : i <= j；hs : MeasurableSet[𝒢 i] s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.piecewise_of_le`：∀ {Ω : Type u_1} {ι : Type
 u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {𝒢 : MeasureTheory.Filtration 
ι m}   {τ η : Ω → WithTop ι} {i : …
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isStoppingTime_piecewise_const (hij : i ≤ j) (hs : MeasurableSet[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise (fun _ => i) fun _ => j) :=
  (isStoppingTime_const 𝒢 i).piecewise_of_le (isStoppingTime_const 𝒢 j) (fun _ => le_rfl)
    (fun _ => mod_cast hij) hs
/-
**MeasureTheory.stoppedValue_piecewise_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：stoppedValue_piecewise_const {ι' α : Type*} [Nonempty ι'] {i j : ι'} {f : 
ι' -> Ω -> α} : stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.piecewi
se (f i) (f j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.stoppedValue.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : Ty
pe u_3} [inst : Nonempty ι] (u : ι → Ω → β) (τ : Ω → WithTop ι) (ω : Ω),   Measu
reTheory.stoppedValue…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem stoppedValue_piecewise_const {ι' α : Type*} [Nonempty ι'] {i j : ι'} {f : ι' → Ω → α} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.piecewise (f i) (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω ∈ s <;> simp [hx]
/-
**MeasureTheory.stoppedValue_piecewise_const'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：stoppedValue_piecewise_const' {ι' α : Type*} [AddCommGroup α] [Nonempty ι'
] {i j : ι'} {f : ι' -> Ω -> α} : stoppedValue f (s.piecewise (fun _ => i) fun _
 => j) = s.indicator (f i) + sᶜ.indicator (f j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.stoppedValue.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : Ty
pe u_3} [inst : Nonempty ι] (u : ι → Ω → β) (τ : Ω → WithTop ι) (ω : Ω),   Measu
reTheory.stoppedValue…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem stoppedValue_piecewise_const' {ι' α : Type*} [AddCommGroup α]
    [Nonempty ι'] {i j : ι'} {f : ι' → Ω → α} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) =
    s.indicator (f i) + sᶜ.indicator (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω ∈ s <;> simp [hx]

end PiecewiseConst

section Condexp

/-! ### Conditional expectation with respect to the σ-algebra generated by a stopping time -/


variable [LinearOrder ι] {μ : Measure Ω} {ℱ : Filtration ι m} {τ σ : Ω → WithTop ι} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : Ω → E}

/-
**MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable_range** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_stopping_time_ae_eq_restrict_eq_of_countable_range [SigmaFiniteFil
tration μ ℱ] (hτ : IsStoppingTime ℱ τ) (h_countable : (Set.range τ).Countable) [
SigmaFinite (μ.trim (hτ.measurableSpace_le))] (i : ι) : μ[f | hτ.measurableSpace
] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i]
参数：hτ : IsStoppingTime ℱ τ；h_countable : (Set.range τ).Countable；μ.trim (hτ.meas
urableSpace_le)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le`：measurableSpace_le (hτ 
: IsStoppingTime f τ) : hτ.measurableSpace <= m
· 使用定理 `MeasureTheory.condExp_ae_eq_restrict_of_measurableSpace_eq_on`：condExp_a
e_eq_restrict_of_measurableSpace_eq_on {m m₂ m0 : MeasurableSpace α} {μ : Measur
e α} (hm : m <= m0) (hm₂ : m₂ <= m0) [SigmaFinite (…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range'`：∀ {Ω 
: Type u_1} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : M
easureTheory.Filtration ι m}   {τ : Ω → WithTop ι} (hτ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_inter_eq_iff`：measurableSet_i
nter_eq_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) : MeasurableSet[hτ.mea
surableSpace] (s inter {ω | τ ω = i}) ↔ Measu…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem condExp_stopping_time_ae_eq_restrict_eq_of_countable_range [SigmaFiniteFiltration μ ℱ]
    (hτ : IsStoppingTime ℱ τ) (h_countable : (Set.range τ).Countable)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le))] (i : ι) :
    μ[f | hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i] := by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on
    (hτ.measurableSpace_le) (ℱ.le i)
    (hτ.measurableSet_eq_of_countable_range' h_countable i) fun t => ?_
  rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_eq_iff]
/-
**MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_stopping_time_ae_eq_restrict_eq_of_countable [Countable ι] [SigmaF
initeFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ) [SigmaFinite (μ.trim hτ.measurabl
eSpace_le)] (i : ι) : μ[f | hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f
 | ℱ i]
参数：hτ : IsStoppingTime ℱ τ；μ.trim hτ.measurableSpace_le；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le`：measurableSpace_le (hτ 
: IsStoppingTime f τ) : hτ.measurableSpace <= m
· 使用定理 `MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable_range
`：condExp_stopping_time_ae_eq_restrict_eq_of_countable_range [SigmaFiniteFiltrat
ion μ ℱ] (hτ : IsStoppingTime ℱ τ) (h_countable : (Set.range τ…
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
theorem condExp_stopping_time_ae_eq_restrict_eq_of_countable [Countable ι]
    [SigmaFiniteFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ)
    [SigmaFinite (μ.trim hτ.measurableSpace_le)] (i : ι) :
    μ[f | hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i] :=
  condExp_stopping_time_ae_eq_restrict_eq_of_countable_range hτ (Set.to_countable _) i
/-
**MeasureTheory.condExp_min_stopping_time_ae_eq_restrict_le_const** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_min_stopping_time_ae_eq_restrict_le_const (hτ : IsStoppingTime ℱ τ
) (i : ι) [SigmaFinite (μ.trim (hτ.min_const i).measurableSpace_le)] : μ[f | (hτ
.min_const i).measurableSpace] =ᵐ[μ.restrict {x | τ x <= i}] μ[f | hτ.measurable
Space]
参数：hτ : IsStoppingTime ℱ τ；i : ι；μ.trim (hτ.min_const i).measurableSpace_le。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min_const`：∀ {Ω : Type u_1} {ι : Type u_3} 
{m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m
}   {τ : Ω → WithTop ι},   M…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le`：measurableSpace_le (hτ 
: IsStoppingTime f τ) : hτ.measurableSpace <= m
· 使用定理 `MeasureTheory.sigmaFiniteTrim_mono`：sigmaFiniteTrim_mono {m m₂ m0 : Meas
urableSpace α} {μ : Measure α} (hm : m <= m0) (hm₂ : m₂ <= m) [SigmaFinite (μ.tr
im (hm₂.trans hm))] : Si…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_min_const`：measurableSpace_
min_const (hτ : IsStoppingTime f τ) {i : ι} : (hτ.min_const i).measurableSpace =
 hτ.measurableSpace ⊓ f i
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_ae_eq_restrict_of_measurableSpace_eq_on`：condExp_a
e_eq_restrict_of_measurableSpace_eq_on {m m₂ m0 : MeasurableSpace α} {μ : Measur
e α} (hm : m <= m0) (hm₂ : m₂ <= m0) [SigmaFinite (…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le'`：∀ {Ω : Type u_1} {ι : Ty
pe u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtra
tion ι m}   {τ : Ω → WithTop ι} (hτ …
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_inter_le_const_iff`：measurabl
eSet_inter_le_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) : Measurab
leSet[hτ.measurableSpace] (s inter {ω | τ ω <= i}) …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem condExp_min_stopping_time_ae_eq_restrict_le_const (hτ : IsStoppingTime ℱ τ) (i : ι)
    [SigmaFinite (μ.trim (hτ.min_const i).measurableSpace_le)] :
    μ[f | (hτ.min_const i).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ i}]
      μ[f | hτ.measurableSpace] := by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    haveI h_le : (hτ.min_const i).measurableSpace ≤ hτ.measurableSpace := by
      rw [IsStoppingTime.measurableSpace_min_const]
      exact inf_le_left
    sigmaFiniteTrim_mono _ h_le
  refine (condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le
    (hτ.min_const i).measurableSpace_le (hτ.measurableSet_le' i) fun t => ?_).symm
  rw [Set.inter_comm _ t, hτ.measurableSet_inter_le_const_iff]

variable [TopologicalSpace ι] [OrderTopology ι]
/-
**MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：condExp_stopping_time_ae_eq_restrict_eq [FirstCountableTopology ι] [SigmaF
initeFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ) [SigmaFinite (μ.trim hτ.measurabl
eSpace_le)] (i : ι) : μ[f | hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f
 | ℱ i]
参数：hτ : IsStoppingTime ℱ τ；μ.trim hτ.measurableSpace_le；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le`：measurableSpace_le (hτ 
: IsStoppingTime f τ) : hτ.measurableSpace <= m
· 使用定理 `MeasureTheory.condExp_ae_eq_restrict_of_measurableSpace_eq_on`：condExp_a
e_eq_restrict_of_measurableSpace_eq_on {m m₂ m0 : MeasurableSpace α} {μ : Measur
e α} (hm : m <= m0) (hm₂ : m₂ <= m0) [SigmaFinite (…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq'`：∀ {Ω : Type u_1} {ι : Ty
pe u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtra
tion ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_inter_eq_iff`：measurableSet_i
nter_eq_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) : MeasurableSet[hτ.mea
surableSpace] (s inter {ω | τ ω = i}) ↔ Measu…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem condExp_stopping_time_ae_eq_restrict_eq [FirstCountableTopology ι]
    [SigmaFiniteFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ)
    [SigmaFinite (μ.trim hτ.measurableSpace_le)] (i : ι) :
    μ[f | hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i] := by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le (ℱ.le i)
    (hτ.measurableSet_eq' i) fun t => ?_
  rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_eq_iff]
/-
**MeasureTheory.condExp_min_stopping_time_ae_eq_restrict_le** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：condExp_min_stopping_time_ae_eq_restrict_le [SecondCountableTopology ι] (h
τ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) [SigmaFinite (μ.trim (hτ.min h
σ).measurableSpace_le)] : μ[f | (hτ.min hσ).measurableSpace] =ᵐ[μ.restrict {x | 
τ x <= σ x}] μ[f | hτ.measurableSpace]
参数：hτ : IsStoppingTime ℱ τ；hσ : IsStoppingTime ℱ σ；μ.trim (hτ.min hσ).measurable
Space_le。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_le`：measurableSpace_le (hτ 
: IsStoppingTime f τ) : hτ.measurableSpace <= m
· 使用定理 `MeasureTheory.sigmaFiniteTrim_mono`：sigmaFiniteTrim_mono {m m₂ m0 : Meas
urableSpace α} {μ : Measure α} (hm : m <= m0) (hm₂ : m₂ <= m) [SigmaFinite (μ.tr
im (hm₂.trans hm))] : Si…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSpace_min`：measurableSpace_min (h
τ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) : (hτ.min hπ).measurableSpace 
= hτ.measurableSpace ⊓ hπ.measurableSp…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_ae_eq_restrict_of_measurableSpace_eq_on`：condExp_a
e_eq_restrict_of_measurableSpace_eq_on {m m₂ m0 : MeasurableSpace α} {μ : Measur
e α} (hm : m <= m0) (hm₂ : m₂ <= m0) [SigmaFinite (…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_le_stopping_time`：measurableS
et_le_stopping_time [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopol
ogy ι] (hτ : IsStoppingTime f τ) (hπ : IsStopping…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_inter_le_iff`：measurableSet_i
nter_le_iff [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] (
hτ : IsStoppingTime f τ) (hπ : IsStoppingTime…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem condExp_min_stopping_time_ae_eq_restrict_le [SecondCountableTopology ι]
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
    [SigmaFinite (μ.trim (hτ.min hσ).measurableSpace_le)] :
    μ[f | (hτ.min hσ).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ σ x}]
      μ[f | hτ.measurableSpace] := by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    sigmaFiniteTrim_mono _ (hτ.measurableSpace_min hσ ▸ inf_le_left)
  refine (condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le
    (hτ.min hσ).measurableSpace_le (hτ.measurableSet_le_stopping_time hσ) fun t => ?_).symm
  rw [Set.inter_comm _ t, hτ.measurableSet_inter_le_iff hσ]

end Condexp

end MeasureTheory

