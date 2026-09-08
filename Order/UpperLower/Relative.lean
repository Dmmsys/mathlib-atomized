/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.SetNotation

/-!
# Properties of relative upper/lower sets

This file proves results on `IsRelUpperSet` and `IsRelLowerSet`.
-/

public section

open Set

variable {α : Type*} {ι : Sort*} {κ : ι → Sort*} {s t : Set α} {a b : α} {P : α → Prop}

section LE

variable [LE α]

/-
**isRelUpperSet_true_iff_isUpperSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : LE α], (IsRelUpperSet s fun x => True
) ↔ IsUpperSet s
参数：IsRelUpperSet s fun x => True。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma isRelUpperSet_true_iff_isUpperSet :
    IsRelUpperSet s (fun _ ↦ True) ↔ IsUpperSet s := by
  grind [IsUpperSet, IsRelUpperSet]
/-
**isRelLowerSet_true_iff_isLowerSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : LE α], (IsRelLowerSet s fun x => True
) ↔ IsLowerSet s
参数：IsRelLowerSet s fun x => True。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma isRelLowerSet_true_iff_isLowerSet :
    IsRelLowerSet s (fun _ ↦ True) ↔ IsLowerSet s := by
  grind [IsLowerSet, IsRelLowerSet]

variable (P) in
/-
**IsUpperSet.isRelUpperSet_sep** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUpperSet.isRelUpperSet_sep (hs : IsUpperSet s) : IsRelUpperSet {x in s |
 P x} P
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsUpperSet.isRelUpperSet_sep (hs : IsUpperSet s) : IsRelUpperSet {x ∈ s | P x} P :=
  fun _ h => ⟨h.2, fun _ ht hp => ⟨hs ht h.1, hp⟩⟩
variable (P) in
/-
**IsLowerSet.isRelLowerSet_sep** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLowerSet.isRelLowerSet_sep (hs : IsLowerSet s) : IsRelLowerSet {x in s |
 P x} P
参数：hs : IsLowerSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsLowerSet.isRelLowerSet_sep (hs : IsLowerSet s) : IsRelLowerSet {x ∈ s | P x} P :=
  fun _ h => ⟨h.2, fun _ ht hp => ⟨hs ht h.1, hp⟩⟩

/-- A subset that is a lower set is additionally a _relative_ lower set. -/
/-
**IsRelLowerSet.mono_isLowerSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelLowerSet.mono_isLowerSet (ht : IsRelLowerSet t P) (hs : IsLowerSet s)
 (hst : s subseteq t) : IsRelLowerSet s P
参数：ht : IsRelLowerSet t P；hs : IsLowerSet s；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A subset that is a lower set is additionally a _relative_ lower set.
-/
lemma IsRelLowerSet.mono_isLowerSet (ht : IsRelLowerSet t P) (hs : IsLowerSet s) (hst : s ⊆ t) :
    IsRelLowerSet s P :=
  fun _ h => ⟨(ht (hst h)).1, fun _ ht _ => hs ht h⟩

/-- A subset that is an upper set is additionally a _relative_ upper set. -/
/-
**IsRelUpperSet.mono_isUpperSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelUpperSet.mono_isUpperSet (ht : IsRelUpperSet t P) (hs : IsUpperSet s)
 (hst : s subseteq t) : IsRelUpperSet s P
参数：ht : IsRelUpperSet t P；hs : IsUpperSet s；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A subset that is an upper set is additionally a _relative_ upper set.
-/
lemma IsRelUpperSet.mono_isUpperSet (ht : IsRelUpperSet t P) (hs : IsUpperSet s) (hst : s ⊆ t) :
    IsRelUpperSet s P :=
  fun _ h => ⟨(ht (hst h)).1, fun _ ht _ => hs ht h⟩
/-
**IsRelUpperSet.prop_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelUpperSet.prop_of_mem (hs : IsRelUpperSet s P) (h : a in s) : P a
参数：hs : IsRelUpperSet s P；h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsRelUpperSet.prop_of_mem (hs : IsRelUpperSet s P) (h : a ∈ s) : P a := (hs h).1
/-
**IsRelLowerSet.prop_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelLowerSet.prop_of_mem (hs : IsRelLowerSet s P) (h : a in s) : P a
参数：hs : IsRelLowerSet s P；h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsRelLowerSet.prop_of_mem (hs : IsRelLowerSet s P) (h : a ∈ s) : P a := (hs h).1
/-
**IsRelUpperSet.mem_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelUpperSet.mem_of_le (hs : IsRelUpperSet s P) (h : a in s) (h₁ : a <= b
) (h₂ : P b) : b in s
参数：hs : IsRelUpperSet s P；h : a in s；h₁ : a <= b；h₂ : P b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsRelUpperSet.mem_of_le (hs : IsRelUpperSet s P) (h : a ∈ s) (h₁ : a ≤ b) (h₂ : P b) :
    b ∈ s := (hs h).2 h₁ h₂
/-
**IsRelLowerSet.mem_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelLowerSet.mem_of_le (hs : IsRelLowerSet s P) (h : a in s) (h₁ : b <= a
) (h₂ : P b) : b in s
参数：hs : IsRelLowerSet s P；h : a in s；h₁ : b <= a；h₂ : P b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsRelLowerSet.mem_of_le (hs : IsRelLowerSet s P) (h : a ∈ s) (h₁ : b ≤ a) (h₂ : P b) :
    b ∈ s := (hs h).2 h₁ h₂
/-
**isRelUpperSet_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} [inst : LE α], IsRelUpperSet ∅ P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma isRelUpperSet_empty : IsRelUpperSet (∅ : Set α) P := fun _ ↦ False.elim
/-
**isRelLowerSet_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} [inst : LE α], IsRelLowerSet ∅ P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma isRelLowerSet_empty : IsRelLowerSet (∅ : Set α) P := fun _ ↦ False.elim
/-
**isRelUpperSet_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : LE α], IsRelUpperSet s fun x => x ∈ s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma isRelUpperSet_self : IsRelUpperSet s (· ∈ s) := fun _ b ↦ ⟨b, fun _ _ ↦ id⟩
/-
**isRelLowerSet_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : LE α], IsRelLowerSet s fun x => x ∈ s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma isRelLowerSet_self : IsRelLowerSet s (· ∈ s) := fun _ b ↦ ⟨b, fun _ _ ↦ id⟩
/-
**IsRelUpperSet.union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelUpperSet.union (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P) : Is
RelUpperSet (s union t) P
参数：hs : IsRelUpperSet s P；ht : IsRelUpperSet t P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsRelUpperSet.union (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P) :
    IsRelUpperSet (s ∪ t) P := fun b mb ↦ by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y ↦ .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y ↦ .inr ((ht h).2 x y)⟩
/-
**IsRelLowerSet.union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelLowerSet.union (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P) : Is
RelLowerSet (s union t) P
参数：hs : IsRelLowerSet s P；ht : IsRelLowerSet t P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsRelLowerSet.union (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P) :
    IsRelLowerSet (s ∪ t) P := fun b mb ↦ by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y ↦ .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y ↦ .inr ((ht h).2 x y)⟩
/-
**IsRelUpperSet.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelUpperSet.inter (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P) : Is
RelUpperSet (s inter t) P
参数：hs : IsRelUpperSet s P；ht : IsRelUpperSet t P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsRelUpperSet.inter (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P) :
    IsRelUpperSet (s ∩ t) P := fun b ⟨bs, bt⟩ ↦ by
  simp_all only [IsRelUpperSet, true_and]
  exact fun _ x y ↦ ⟨(hs bs).2 x y, (ht bt).2 x y⟩
/-
**IsRelLowerSet.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRelLowerSet.inter (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P) : Is
RelLowerSet (s inter t) P
参数：hs : IsRelLowerSet s P；ht : IsRelLowerSet t P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsRelLowerSet.inter (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P) :
    IsRelLowerSet (s ∩ t) P := fun b ⟨bs, bt⟩ ↦ by
  simp_all only [IsRelLowerSet, true_and]
  exact fun _ x y ↦ ⟨(hs bs).2 x y, (ht bt).2 x y⟩
/-
**IsRelUpperSet.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `IsRelUpperSet`。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S : Set (Set α)}, (∀ s ∈ S,
 IsRelUpperSet s P) → IsRelUpperSet (⋃₀ S) P
参数：Set α；∀ s ∈ S, IsRelUpperSet s P；⋃₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma IsRelUpperSet.sUnion {S : Set (Set α)} (hS : ∀ s ∈ S, IsRelUpperSet s P) :
    IsRelUpperSet (⋃₀ S) P := fun _ ⟨s, ms, mb⟩ ↦
  ⟨(hS s ms mb).1, fun _ x y ↦ ⟨s, ms, (hS s ms mb).2 x y⟩⟩
/-
**IsRelLowerSet.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `IsRelLowerSet`。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S : Set (Set α)}, (∀ s ∈ S,
 IsRelLowerSet s P) → IsRelLowerSet (⋃₀ S) P
参数：Set α；∀ s ∈ S, IsRelLowerSet s P；⋃₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma IsRelLowerSet.sUnion {S : Set (Set α)} (hS : ∀ s ∈ S, IsRelLowerSet s P) :
    IsRelLowerSet (⋃₀ S) P := fun _ ⟨s, ms, mb⟩ ↦
  ⟨(hS s ms mb).1, fun _ x y ↦ ⟨s, ms, (hS s ms mb).2 x y⟩⟩
/-
**IsRelUpperSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `IsRelUpperSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_2} {P : α → Prop} [inst : LE α] {f : ι → Set 
α},   (∀ (i : ι), IsRelUpperSet (f i) P) → IsRelUpperSet (⋃ i, f i) P
参数：∀ (i : ι), IsRelUpperSet (f i) P；⋃ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelUpperSet.sUnion`：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S :
 Set (Set α)}, (∀ s ∈ S, IsRelUpperSet s P) → IsRelUpperSet (⋃₀ S) P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma IsRelUpperSet.iUnion {f : ι → Set α} (hf : ∀ i, IsRelUpperSet (f i) P) :
    IsRelUpperSet (⋃ i, f i) P :=
  .sUnion (forall_mem_range.2 hf)
/-
**IsRelLowerSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `IsRelLowerSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_2} {P : α → Prop} [inst : LE α] {f : ι → Set 
α},   (∀ (i : ι), IsRelLowerSet (f i) P) → IsRelLowerSet (⋃ i, f i) P
参数：∀ (i : ι), IsRelLowerSet (f i) P；⋃ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelLowerSet.sUnion`：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S :
 Set (Set α)}, (∀ s ∈ S, IsRelLowerSet s P) → IsRelLowerSet (⋃₀ S) P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma IsRelLowerSet.iUnion {f : ι → Set α} (hf : ∀ i, IsRelLowerSet (f i) P) :
    IsRelLowerSet (⋃ i, f i) P :=
  .sUnion (forall_mem_range.2 hf)
/-
**IsRelUpperSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `IsRelUpperSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_2} {P : α → Prop} [inst : LE α] {f : ι → Set 
α},   (∀ (i : ι), IsRelUpperSet (f i) P) → IsRelUpperSet (⋃ i, f i) P
参数：∀ (i : ι), IsRelUpperSet (f i) P；⋃ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelUpperSet.sUnion`：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S :
 Set (Set α)}, (∀ s ∈ S, IsRelUpperSet s P) → IsRelUpperSet (⋃₀ S) P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma IsRelUpperSet.iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelUpperSet (f i j) P) :
    IsRelUpperSet (⋃ (i) (j), f i j) P :=
  .iUnion fun i ↦ .iUnion (hf i)
/-
**IsRelLowerSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `IsRelLowerSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_2} {P : α → Prop} [inst : LE α] {f : ι → Set 
α},   (∀ (i : ι), IsRelLowerSet (f i) P) → IsRelLowerSet (⋃ i, f i) P
参数：∀ (i : ι), IsRelLowerSet (f i) P；⋃ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelLowerSet.sUnion`：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S :
 Set (Set α)}, (∀ s ∈ S, IsRelLowerSet s P) → IsRelLowerSet (⋃₀ S) P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma IsRelLowerSet.iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelLowerSet (f i j) P) :
    IsRelLowerSet (⋃ (i) (j), f i j) P :=
  .iUnion fun i ↦ .iUnion (hf i)
/-
**IsRelUpperSet.sInter** 是 Mathlib 中的一个定理，位于命名空间 `IsRelUpperSet`。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S : Set (Set α)},   S.Nonem
pty → (∀ s ∈ S, IsRelUpperSet s P) → IsRelUpperSet (⋂₀ S) P
参数：Set α；∀ s ∈ S, IsRelUpperSet s P；⋂₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma IsRelUpperSet.sInter
    {S : Set (Set α)} (hS : S.Nonempty) (hf : ∀ s ∈ S, IsRelUpperSet s P) :
    IsRelUpperSet (⋂₀ S) P := fun b mb ↦ by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms ↦ (hf s ms (mb s ms)).2 x y⟩
/-
**IsRelLowerSet.sInter** 是 Mathlib 中的一个定理，位于命名空间 `IsRelLowerSet`。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S : Set (Set α)},   S.Nonem
pty → (∀ s ∈ S, IsRelLowerSet s P) → IsRelLowerSet (⋂₀ S) P
参数：Set α；∀ s ∈ S, IsRelLowerSet s P；⋂₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma IsRelLowerSet.sInter
    {S : Set (Set α)} (hS : S.Nonempty) (hf : ∀ s ∈ S, IsRelLowerSet s P) :
    IsRelLowerSet (⋂₀ S) P := fun b mb ↦ by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms ↦ (hf s ms (mb s ms)).2 x y⟩
/-
**IsRelUpperSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `IsRelUpperSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_2} {P : α → Prop} [inst : LE α] [Nonempty ι] 
{f : ι → Set α},   (∀ (i : ι), IsRelUpperSet (f i) P) → IsRelUpperSet (⋂ i, f i)
 P
参数：∀ (i : ι), IsRelUpperSet (f i) P；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelUpperSet.sInter`：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S :
 Set (Set α)},   S.Nonempty → (∀ s ∈ S, IsRelUpperSet s P) → IsRelUpperSet (⋂₀ S
) P
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma IsRelUpperSet.iInter
    [Nonempty ι] {f : ι → Set α} (hf : ∀ i, IsRelUpperSet (f i) P) : IsRelUpperSet (⋂ i, f i) P :=
  .sInter (range_nonempty f) (forall_mem_range.2 hf)
/-
**IsRelLowerSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `IsRelLowerSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_2} {P : α → Prop} [inst : LE α] [Nonempty ι] 
{f : ι → Set α},   (∀ (i : ι), IsRelLowerSet (f i) P) → IsRelLowerSet (⋂ i, f i)
 P
参数：∀ (i : ι), IsRelLowerSet (f i) P；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelLowerSet.sInter`：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S :
 Set (Set α)},   S.Nonempty → (∀ s ∈ S, IsRelLowerSet s P) → IsRelLowerSet (⋂₀ S
) P
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma IsRelLowerSet.iInter
    [Nonempty ι] {f : ι → Set α} (hf : ∀ i, IsRelLowerSet (f i) P) : IsRelLowerSet (⋂ i, f i) P :=
  .sInter (range_nonempty f) (forall_mem_range.2 hf)
/-
**IsRelUpperSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `IsRelUpperSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_2} {P : α → Prop} [inst : LE α] [Nonempty ι] 
{f : ι → Set α},   (∀ (i : ι), IsRelUpperSet (f i) P) → IsRelUpperSet (⋂ i, f i)
 P
参数：∀ (i : ι), IsRelUpperSet (f i) P；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelUpperSet.sInter`：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S :
 Set (Set α)},   S.Nonempty → (∀ s ∈ S, IsRelUpperSet s P) → IsRelUpperSet (⋂₀ S
) P
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma IsRelUpperSet.iInter₂ [Nonempty ι] [∀ i, Nonempty (κ i)]
    {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelUpperSet (f i j) P) :
    IsRelUpperSet (⋂ (i) (j), f i j) P :=
  .iInter fun i ↦ .iInter (hf i)
/-
**IsRelLowerSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `IsRelLowerSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_2} {P : α → Prop} [inst : LE α] [Nonempty ι] 
{f : ι → Set α},   (∀ (i : ι), IsRelLowerSet (f i) P) → IsRelLowerSet (⋂ i, f i)
 P
参数：∀ (i : ι), IsRelLowerSet (f i) P；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelLowerSet.sInter`：∀ {α : Type u_1} {P : α → Prop} [inst : LE α] {S :
 Set (Set α)},   S.Nonempty → (∀ s ∈ S, IsRelLowerSet s P) → IsRelLowerSet (⋂₀ S
) P
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma IsRelLowerSet.iInter₂ [Nonempty ι] [∀ i, Nonempty (κ i)]
    {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelLowerSet (f i j) P) :
    IsRelLowerSet (⋂ (i) (j), f i j) P :=
  .iInter fun i ↦ .iInter (hf i)
/-
**isUpperSet_subtype_iff_isRelUpperSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUpperSet_subtype_iff_isRelUpperSet {s : Set { x // P x }} : IsUpperSet s
 ↔ IsRelUpperSet (Subtype.val '' s) P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isUpperSet_subtype_iff_isRelUpperSet {s : Set { x // P x }} :
    IsUpperSet s ↔ IsRelUpperSet (Subtype.val '' s) P := by
  refine ⟨fun h a x ↦ ?_, fun h a b x y ↦ ?_⟩
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y ↦ by simpa [h (show a ≤ ⟨b, y⟩ by exact x) ma]⟩
  · have ma : a.1 ∈ Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, Subtype.coe_inj, exists_eq_right] using (h ma).2 x b.2
/-
**isLowerSet_subtype_iff_isRelLowerSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLowerSet_subtype_iff_isRelLowerSet {s : Set { x // P x }} : IsLowerSet s
 ↔ IsRelLowerSet (Subtype.val '' s) P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isLowerSet_subtype_iff_isRelLowerSet {s : Set { x // P x }} :
    IsLowerSet s ↔ IsRelLowerSet (Subtype.val '' s) P := by
  refine ⟨fun h a x ↦ ?_, fun h a b x y ↦ ?_⟩
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y ↦ by simpa [h (show ⟨b, y⟩ ≤ a by exact x) ma]⟩
  · have ma : a.1 ∈ Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, Subtype.coe_inj, exists_eq_right] using (h ma).2 x b.2
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (RelUpperSet P) α where
  coe := RelUpperSet.carrier
  coe_injective s t h := by cases s; cases t; congr
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (RelUpperSet P) := .ofSetLike (RelUpperSet P) α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (RelLowerSet P) α where
  coe := RelLowerSet.carrier
  coe_injective s t h := by cases s; cases t; congr
/-
**RelUpperSet.isRelUpperSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RelUpperSet.isRelUpperSet (u : RelUpperSet P) : IsRelUpperSet u P
参数：u : RelUpperSet P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelUpperSet.isRelUpperSet'`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop
} (self : RelUpperSet P), IsRelUpperSet self.carrier P
-/
lemma RelUpperSet.isRelUpperSet (u : RelUpperSet P) : IsRelUpperSet u P := u.isRelUpperSet'
/-
**RelLowerSet.isRelLowerSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RelLowerSet.isRelLowerSet (l : RelLowerSet P) : IsRelLowerSet l P
参数：l : RelLowerSet P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelLowerSet.isRelLowerSet'`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop
} (self : RelLowerSet P), IsRelLowerSet self.carrier P
-/
lemma RelLowerSet.isRelLowerSet (l : RelLowerSet P) : IsRelLowerSet l P := l.isRelLowerSet'

end LE

section Preorder

variable [Preorder α] {c : α}

/-
**isRelUpperSet_Icc_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRelUpperSet_Icc_le : IsRelUpperSet (Icc a c) (· <= c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma isRelUpperSet_Icc_le : IsRelUpperSet (Icc a c) (· ≤ c) := fun _ b ↦ by
  simp_all only [mem_Icc, and_true, true_and]
  exact fun _ x _ ↦ b.1.trans x
/-
**isRelLowerSet_Icc_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRelLowerSet_Icc_ge : IsRelLowerSet (Icc c a) (c <= ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isRelLowerSet_Icc_ge : IsRelLowerSet (Icc c a) (c ≤ ·) := fun _ b ↦ by
  simp_all only [mem_Icc, true_and]
  exact fun _ x _ ↦ x.trans b.2

end Preorder

