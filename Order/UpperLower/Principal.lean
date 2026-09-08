/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Order.Interval.Set.OrderIso
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Principal upper/lower sets

The results in this file all assume that the underlying type is equipped with at least a preorder.

## Main declarations

* `UpperSet.Ici`: Principal upper set. `Set.Ici` as an upper set.
* `UpperSet.Ioi`: Strict principal upper set. `Set.Ioi` as an upper set.
* `LowerSet.Iic`: Principal lower set. `Set.Iic` as a lower set.
* `LowerSet.Iio`: Strict principal lower set. `Set.Iio` as a lower set.
-/

@[expose] public section

open Function Set

variable {α β : Type*} {ι : Sort*} {κ : ι → Sort*}

namespace UpperSet

section Preorder

variable [Preorder α] [Preorder β] {s : UpperSet α} {a b : α}

/-- Principal upper set. `Set.Ici` as an upper set. The smallest upper set containing a given
element. -/
@[to_dual
/-- Principal lower set. `Set.Iic` as a lower set. The smallest lower set containing a given
element. -/]
/-
**UpperSet.Ici** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet`。
形式化陈述：Ici (a : α) : UpperSet α
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_Ici`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsUpperSet
 (Set.Ici a)
-/
def Ici (a : α) : UpperSet α :=
  ⟨Set.Ici a, isUpperSet_Ici a⟩

/-- Strict principal upper set. `Set.Ioi` as an upper set. -/
@[to_dual
/-- Strict principal lower set. `Set.Iio` as a lower set. -/]
/-
**UpperSet.Ioi** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet`。
形式化陈述：Ioi (a : α) : UpperSet α
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_Ioi`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsUpperSet
 (Set.Ioi a)
-/
def Ioi (a : α) : UpperSet α :=
  ⟨Set.Ioi a, isUpperSet_Ioi a⟩

@[to_dual (attr := simp)]
/-
**UpperSet.coe_Ici** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_Ici (a : α) : ↑(Ici a) = Set.Ici a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_Ici (a : α) : ↑(Ici a) = Set.Ici a :=
  rfl

@[to_dual (attr := simp)]
/-
**UpperSet.coe_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_Ioi (a : α) : ↑(Ioi a) = Set.Ioi a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_Ioi (a : α) : ↑(Ioi a) = Set.Ioi a :=
  rfl

@[to_dual (attr := simp)]
/-
**UpperSet.mem_Ici_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_Ici_iff : b in Ici a ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_Ici_iff : b ∈ Ici a ↔ a ≤ b :=
  Iff.rfl

@[to_dual (attr := simp)]
/-
**UpperSet.mem_Ioi_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_Ioi_iff : b in Ioi a ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_Ioi_iff : b ∈ Ioi a ↔ a < b :=
  Iff.rfl

@[to_dual (attr := simp)]
/-
**UpperSet.map_Ici** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：map_Ici (f : α ≃o β) (a : α) : map f (Ici a) = Ici (f a)
参数：f : α ≃o β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderIso.image_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
[inst_1 : Preorder β] (e : α ≃o β) (a : α),   ⇑e '' Set.Ici a = Set.Ici (e a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_Ici (f : α ≃o β) (a : α) : map f (Ici a) = Ici (f a) := by
  ext
  simp

@[to_dual (attr := simp)]
/-
**UpperSet.map_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：map_Ioi (f : α ≃o β) (a : α) : map f (Ioi a) = Ioi (f a)
参数：f : α ≃o β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderIso.image_Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
[inst_1 : Preorder β] (e : α ≃o β) (a : α),   ⇑e '' Set.Ioi a = Set.Ioi (e a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_Ioi (f : α ≃o β) (a : α) : map f (Ioi a) = Ioi (f a) := by
  ext
  simp

@[to_dual Ioi_le_Ici]
/-
**UpperSet.Ici_le_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ici_le_Ioi (a : α) : Ici a <= Ioi a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
-/
theorem Ici_le_Ioi (a : α) : Ici a ≤ Ioi a :=
  Ioi_subset_Ici_self

@[to_dual (attr := simp)]
nonrec theorem Ici_bot [OrderBot α] : Ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot

@[to_dual (attr := simp)]
nonrec theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top

@[to_dual (attr := simp)]
/-
**UpperSet.Ici_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：Ici_ne_top : Ici a != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.coe_ne_coe`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p
 q : A}, ↑p ≠ ↑q ↔ p ≠ q
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.nonempty_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set.Ici
 a).Nonempty
-/
lemma Ici_ne_top : Ici a ≠ ⊤ := SetLike.coe_ne_coe.1 nonempty_Ici.ne_empty

@[to_dual (attr := simp) bot_lt_Iic]
/-
**UpperSet.Ici_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：Ici_lt_top : Ici a < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用引理 `UpperSet.Ici_ne_top`：Ici_ne_top : Ici a != ⊤
-/
lemma Ici_lt_top : Ici a < ⊤ := lt_top_iff_ne_top.2 Ici_ne_top

@[to_dual (attr := simp) Iic_le]
/-
**UpperSet.le_Ici** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：le_Ici : s <= Ici a ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `IsUpperSet.Ici_subset`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 IsUpperSet s → ∀ ⦃a : α⦄, a ∈ s → Set.Ici a ⊆ s
· 使用定理 `UpperSet.upper`：∀ {α : Type u_1} [inst : LE α] (s : UpperSet α), IsUpper
Set ↑s
-/
lemma le_Ici : s ≤ Ici a ↔ a ∈ s := ⟨fun h ↦ h le_rfl, fun ha ↦ s.upper.Ici_subset ha⟩

variable (α) in
@[to_dual]
/-
**UpperSet.Ici_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ici_strictMono : StrictMono (Ici (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_ssubset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set
.Ici a ⊂ Set.Ici b ↔ b < a
-/
theorem Ici_strictMono : StrictMono (Ici (α := α)) := fun _ _ h ↦ (Set.Ici_ssubset_Ici).mpr h

variable (α) in
@[to_dual]
/-
**UpperSet.Ioi_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ioi_strictMono : StrictMono (Ioi (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioi_ssubset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b <
 a → Set.Ioi a ⊂ Set.Ioi b
-/
theorem Ioi_strictMono : StrictMono (Ioi (α := α)) := fun _ _ h ↦ Set.Ioi_ssubset_Ioi h

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

@[to_dual]
/-
**UpperSet.Ici_injective** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：Ici_injective : Injective (Ici : α -> UpperSet α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ici_injective`：∀ {α : Type u_1} [inst : PartialOrder α], Function.In
jective Set.Ici
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma Ici_injective : Injective (Ici : α → UpperSet α) := fun _a _b hab ↦
  Set.Ici_injective <| congr_arg ((↑) : _ → Set α) hab

@[to_dual (attr := simp)]
/-
**UpperSet.Ici_inj** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：Ici_inj : Ici a = Ici b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `UpperSet.Ici_injective`：Ici_injective : Injective (Ici : α -> UpperSet α
)
-/
lemma Ici_inj : Ici a = Ici b ↔ a = b := Ici_injective.eq_iff

@[to_dual]
/-
**UpperSet.Ici_ne_Ici** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：Ici_ne_Ici : Ici a != Ici b ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `UpperSet.Ici_inj`：Ici_inj : Ici a = Ici b ↔ a = b
-/
lemma Ici_ne_Ici : Ici a ≠ Ici b ↔ a ≠ b := Ici_inj.not

@[to_dual (attr := simp)]
/-
**UpperSet.Ioi_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ioi_eq_top [OrderTop α] {a : α} : Ioi a = ⊤ ↔ a = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ioi_eq_top [OrderTop α] {a : α} : Ioi a = ⊤ ↔ a = ⊤ := by
  simp [UpperSet.ext_iff]

end PartialOrder

@[to_dual (attr := simp)]
/-
**UpperSet.Ici_sup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ici_sup [SemilatticeSup α] (a b : α) : Ici (a ⊔ b) = Ici a ⊔ Ici b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_inter_Ici`：∀ {α : Type u_1} [inst : SemilatticeSup α] {a b : α},
 Set.Ici a ∩ Set.Ici b = Set.Ici (a ⊔ b)
-/
theorem Ici_sup [SemilatticeSup α] (a b : α) : Ici (a ⊔ b) = Ici a ⊔ Ici b :=
  ext Ici_inter_Ici.symm

section CompleteLattice

variable [CompleteLattice α]

@[to_dual (attr := simp)]
/-
**UpperSet.Ici_sSup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ici_sSup (S : Set α) : Ici (sSup S) = ⨆ a in S, Ici a
参数：S : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ici_sSup (S : Set α) : Ici (sSup S) = ⨆ a ∈ S, Ici a :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, sSup_le_iff]

@[to_dual (attr := simp)]
/-
**UpperSet.Ici_iSup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ici_iSup (f : ι -> α) : Ici (⨆ i, f i) = ⨆ i, Ici (f i)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ici_iSup (f : ι → α) : Ici (⨆ i, f i) = ⨆ i, Ici (f i) :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, iSup_le_iff]

@[to_dual]
/-
**UpperSet.Ici_iSup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ici_iSup (f : ι -> α) : Ici (⨆ i, f i) = ⨆ i, Ici (f i)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ici_iSup₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⨆ (i) (j), Ici (f i j) := by
  simp

end CompleteLattice

end UpperSet

