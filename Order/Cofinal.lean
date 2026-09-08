/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.WellFounded

import Mathlib.Data.Set.Lattice

/-!
# Cofinal sets

A set `s` in an ordered type `α` is cofinal when for every `a : α` there exists an element of `s`
greater or equal to it. This file provides a basic API for the `IsCofinal` predicate.

For the cofinality of a set as a cardinal, see `Mathlib/SetTheory/Cardinal/Cofinality/Basic.lean`.

## TODO

- Deprecate `Order.Cofinal` in favor of this predicate.
-/

public section

open Set

variable {α β : Type*}

section LE
variable [LE α]

/-
**IsCofinal.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinal.of_isEmpty [IsEmpty α] {s : Set α} : IsCofinal s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsCofinal.of_isEmpty [IsEmpty α] {s : Set α} : IsCofinal s :=
  fun a ↦ isEmptyElim a
/-
**isCofinal_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCofinal_empty_iff : IsCofinal (∅ : Set α) ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `IsCofinal.of_isEmpty`：IsCofinal.of_isEmpty [IsEmpty α] {s : Set α} : IsC
ofinal s
-/
theorem isCofinal_empty_iff : IsCofinal (∅ : Set α) ↔ IsEmpty α := by
  refine ⟨fun h ↦ ⟨fun a ↦ ?_⟩, fun h ↦ .of_isEmpty⟩
  simpa using h a
/-
**IsCofinal.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinal.nonempty [Nonempty α] {s : Set α} (hs : IsCofinal s) : s.Nonempt
y
参数：hs : IsCofinal s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsCofinal.nonempty [Nonempty α] {s : Set α} (hs : IsCofinal s) : s.Nonempty := by
  inhabit α
  exact (hs default).imp fun _ ↦ And.left

@[simp]
/-
**isCofinal_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCofinal_singleton_iff {x : α} : IsCofinal {x} ↔ IsTop x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCofinal_singleton_iff {x : α} : IsCofinal {x} ↔ IsTop x := by
  simp [IsCofinal, IsTop]
/-
**IsCofinal.singleton_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinal.singleton_top [OrderTop α] : IsCofinal {(⊤ : α)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem IsCofinal.singleton_top [OrderTop α] : IsCofinal {(⊤ : α)} := by
  simp
/-
**IsCofinal.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinal.mono {s t : Set α} (h : s subseteq t) (hs : IsCofinal s) : IsCof
inal t
参数：h : s subseteq t；hs : IsCofinal s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsCofinal.mono {s t : Set α} (h : s ⊆ t) (hs : IsCofinal s) : IsCofinal t := by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs a
  exact ⟨b, h hb, hb'⟩

end LE

section Preorder
variable [Preorder α] [Preorder β]

@[simp]
/-
**IsCofinal.univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinal.univ : IsCofinal (@univ α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IsCofinal.univ : IsCofinal (@univ α) :=
  fun a ↦ ⟨a, ⟨⟩, le_rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited {s : Set α // IsCofinal s} :=
  ⟨_, .univ⟩
/-
**IsCofinal.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinal.image {f : α -> β} {s : Set α} (hs : IsCofinal s) (hf : Monotone
 f) (hf' : IsCofinal (.range f)) : IsCofinal (f '' s)
参数：hs : IsCofinal s；hf : Monotone f；hf' : IsCofinal (.range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsCofinal.image {f : α → β} {s : Set α} (hs : IsCofinal s)
    (hf : Monotone f) (hf' : IsCofinal (.range f)) : IsCofinal (f '' s) := by
  intro a
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf' a
  obtain ⟨c, hc, hc'⟩ := hs b
  exact ⟨_, mem_image_of_mem f hc, hb.trans (hf hc')⟩

/-- A cofinal subset of a cofinal subset is cofinal. -/
/-
**IsCofinal.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinal.trans {s : Set α} {t : Set s} (hs : IsCofinal s) (ht : IsCofinal
 t) : IsCofinal (Subtype.val '' t)
参数：hs : IsCofinal s；ht : IsCofinal t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCofinal.image`：IsCofinal.image {f : α -> β} {s : Set α} (hs : IsCofina
l s) (hf : Monotone f) (hf' : IsCofinal (.range f)) : IsCofinal (f '' s)
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }

--- 原说明 ---
A cofinal subset of a cofinal subset is cofinal.
-/
theorem IsCofinal.trans {s : Set α} {t : Set s} (hs : IsCofinal s) (ht : IsCofinal t) :
    IsCofinal (Subtype.val '' t) :=
  ht.image (Subtype.mono_coe _) (by simpa)
/-
**GaloisConnection.isCofinal_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GaloisConnection.isCofinal_range {f : β -> α} {g : α -> β} (h : GaloisConn
ection f g) : IsCofinal (range g)
参数：h : GaloisConnection f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
-/
theorem GaloisConnection.isCofinal_range {f : β → α} {g : α → β} (h : GaloisConnection f g) :
    IsCofinal (range g) :=
  fun a ↦ ⟨_, mem_range_self _, le_u_l h a⟩
/-
**GaloisConnection.map_isCofinal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GaloisConnection.map_isCofinal {f : β -> α} {g : α -> β} (h : GaloisConnec
tion f g) {s : Set α} (hs : IsCofinal s) : IsCofinal (g '' s)
参数：h : GaloisConnection f g；hs : IsCofinal s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCofinal.image`：IsCofinal.image {f : α -> β} {s : Set α} (hs : IsCofina
l s) (hf : Monotone f) (hf' : IsCofinal (.range f)) : IsCofinal (f '' s)
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `GaloisConnection.isCofinal_range`：GaloisConnection.isCofinal_range {f : 
β -> α} {g : α -> β} (h : GaloisConnection f g) : IsCofinal (range g)
-/
theorem GaloisConnection.map_isCofinal {f : β → α} {g : α → β}
    (h : GaloisConnection f g) {s : Set α} (hs : IsCofinal s) : IsCofinal (g '' s) :=
  hs.image h.monotone_u h.isCofinal_range

@[deprecated (since := "2026-03-15")]
alias GaloisConnection.map_cofinal := GaloisConnection.map_isCofinal
/-
**OrderIso.map_isCofinal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_isCofinal (e : α ≃o β) {s : Set α} (hs : IsCofinal s) : IsCof
inal (e '' s)
参数：e : α ≃o β；hs : IsCofinal s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.map_isCofinal`：GaloisConnection.map_isCofinal {f : β ->
 α} {g : α -> β} (h : GaloisConnection f g) {s : Set α} (hs : IsCofinal s) : IsC
ofinal (g '' s)
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
theorem OrderIso.map_isCofinal (e : α ≃o β) {s : Set α} (hs : IsCofinal s) : IsCofinal (e '' s) :=
  e.symm.to_galoisConnection.map_isCofinal hs

@[simp]
/-
**OrderIso.map_isCofinal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_isCofinal_iff (e : α ≃o β) {s : Set α} : IsCofinal (e '' s) ↔
 IsCofinal s
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_image_image`：symm_image_image (e : α ≃o β) (s : Set α) : e
.symm '' e '' s = s
· 使用定理 `OrderIso.map_isCofinal`：OrderIso.map_isCofinal (e : α ≃o β) {s : Set α} 
(hs : IsCofinal s) : IsCofinal (e '' s)
-/
theorem OrderIso.map_isCofinal_iff (e : α ≃o β) {s : Set α} : IsCofinal (e '' s) ↔ IsCofinal s :=
  ⟨fun hs ↦ by simpa using e.symm.map_isCofinal hs, e.map_isCofinal⟩

@[deprecated (since := "2026-03-15")]
alias OrderIso.map_cofinal := OrderIso.map_isCofinal
/-
**isCofinal_iff_iUnion_Iic_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCofinal_iff_iUnion_Iic_eq_univ {s : Set α} : IsCofinal s ↔ ⋃ i in s, Iic
 i = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCofinal_iff_iUnion_Iic_eq_univ {s : Set α} :
    IsCofinal s ↔ ⋃ i ∈ s, Iic i = univ := by
  simp [IsCofinal, eq_univ_iff_forall]
/-
**isCofinal_iff_iUnion_Iio_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCofinal_iff_iUnion_Iio_eq_univ [NoMaxOrder α] {s : Set α} : IsCofinal s 
↔ ⋃ i in s, Iio i = univ where mpr hs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `isCofinal_iff_iUnion_Iic_eq_univ`：isCofinal_iff_iUnion_Iic_eq_univ {s : 
Set α} : IsCofinal s ↔ ⋃ i in s, Iic i = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Set.iUnion_mono''`：iUnion_mono'' {s t : ι -> Set α} (h : forall i, s i s
ubseteq t i) : iUnion s subseteq iUnion t
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
theorem isCofinal_iff_iUnion_Iio_eq_univ [NoMaxOrder α] {s : Set α} :
    IsCofinal s ↔ ⋃ i ∈ s, Iio i = univ where
  mpr hs := by
    rw [isCofinal_iff_iUnion_Iic_eq_univ, ← univ_subset_iff, ← hs]
    gcongr
    exact Iio_subset_Iic_self
  mp hs := by
    simp_rw [eq_univ_iff_forall, mem_iUnion, exists_prop]
    intro x
    obtain ⟨y, hy⟩ := exists_gt x
    obtain ⟨z, hz, hz'⟩ := hs y
    exact ⟨z, hz, hy.trans_le hz'⟩

end Preorder

section PartialOrder
variable [PartialOrder α]

/-
**IsCofinal.mem_of_isMax** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinal.mem_of_isMax {s : Set α} {a : α} (ha : IsMax a) (hs : IsCofinal 
s) : a in s
参数：ha : IsMax a；hs : IsCofinal s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMax.eq_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMa
x a → a ≤ b → b = a
-/
theorem IsCofinal.mem_of_isMax {s : Set α} {a : α} (ha : IsMax a) (hs : IsCofinal s) : a ∈ s := by
  obtain ⟨b, hb, hb'⟩ := hs a
  rwa [ha.eq_of_ge hb'] at hb
/-
**IsCofinal.top_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinal.top_mem [OrderTop α] {s : Set α} (hs : IsCofinal s) : ⊤ in s
参数：hs : IsCofinal s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCofinal.mem_of_isMax`：IsCofinal.mem_of_isMax {s : Set α} {a : α} (ha :
 IsMax a) (hs : IsCofinal s) : a in s
· 使用定理 `isMax_top`：isMax_top : IsMax (⊤ : α)
-/
theorem IsCofinal.top_mem [OrderTop α] {s : Set α} (hs : IsCofinal s) : ⊤ ∈ s :=
  hs.mem_of_isMax isMax_top

@[simp]
/-
**isCofinal_iff_top_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCofinal_iff_top_mem [OrderTop α] {s : Set α} : IsCofinal s ↔ ⊤ in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCofinal.top_mem`：IsCofinal.top_mem [OrderTop α] {s : Set α} (hs : IsCo
final s) : ⊤ in s
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem isCofinal_iff_top_mem [OrderTop α] {s : Set α} : IsCofinal s ↔ ⊤ ∈ s :=
  ⟨IsCofinal.top_mem, fun hs _ ↦ ⟨⊤, hs, le_top⟩⟩

end PartialOrder

section LinearOrder
variable [LinearOrder α]

/-
**not_isCofinal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isCofinal_iff {s : Set α} : ¬ IsCofinal s ↔ exists x, forall y in s, y
 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_isCofinal_iff {s : Set α} : ¬ IsCofinal s ↔ ∃ x, ∀ y ∈ s, y < x := by
  simp [IsCofinal]
/-
**BddAbove.of_not_isCofinal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.of_not_isCofinal {s : Set α} (h : ¬ IsCofinal s) : BddAbove s
参数：h : ¬ IsCofinal s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_isCofinal_iff`：not_isCofinal_iff {s : Set α} : ¬ IsCofinal s ↔ exist
s x, forall y in s, y < x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem BddAbove.of_not_isCofinal {s : Set α} (h : ¬ IsCofinal s) : BddAbove s := by
  rw [not_isCofinal_iff] at h
  obtain ⟨x, h⟩ := h
  exact ⟨x, fun y hy ↦ (h y hy).le⟩
/-
**IsCofinal.of_not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinal.of_not_bddAbove {s : Set α} (h : ¬ BddAbove s) : IsCofinal s
参数：h : ¬ BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `BddAbove.of_not_isCofinal`：BddAbove.of_not_isCofinal {s : Set α} (h : ¬ 
IsCofinal s) : BddAbove s
-/
theorem IsCofinal.of_not_bddAbove {s : Set α} (h : ¬ BddAbove s) : IsCofinal s := by
  contrapose h
  exact .of_not_isCofinal h

/-- In a linear order with no maximum, cofinal sets are the same as unbounded sets. -/
/-
**not_isCofinal_iff_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isCofinal_iff_bddAbove [NoMaxOrder α] {s : Set α} : ¬ IsCofinal s ↔ Bd
dAbove s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.of_not_isCofinal`：BddAbove.of_not_isCofinal {s : Set α} (h : ¬ 
IsCofinal s) : BddAbove s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_isCofinal_iff`：not_isCofinal_iff {s : Set α} : ¬ IsCofinal s ↔ exist
s x, forall y in s, y < x
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
In a linear order with no maximum, cofinal sets are the same as unbounded sets.
-/
theorem not_isCofinal_iff_bddAbove [NoMaxOrder α] {s : Set α} : ¬ IsCofinal s ↔ BddAbove s := by
  use .of_not_isCofinal
  rw [not_isCofinal_iff]
  rintro ⟨x, h⟩
  obtain ⟨z, hz⟩ := exists_gt x
  exact ⟨z, fun y hy ↦ (h hy).trans_lt hz⟩

/-- In a linear order with no maximum, cofinal sets are the same as unbounded sets. -/
/-
**not_bddAbove_iff_isCofinal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_bddAbove_iff_isCofinal [NoMaxOrder α] {s : Set α} : ¬ BddAbove s ↔ IsC
ofinal s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `not_isCofinal_iff_bddAbove`：not_isCofinal_iff_bddAbove [NoMaxOrder α] {s
 : Set α} : ¬ IsCofinal s ↔ BddAbove s

--- 原说明 ---
In a linear order with no maximum, cofinal sets are the same as unbounded sets.
-/
theorem not_bddAbove_iff_isCofinal [NoMaxOrder α] {s : Set α} : ¬ BddAbove s ↔ IsCofinal s :=
  not_iff_comm.1 not_isCofinal_iff_bddAbove

/-- The set of "records" (the smallest inputs yielding the highest values) with respect to a
well-ordering of `α` is a cofinal set. -/
/-
**isCofinal_setOfPred_imp_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCofinal_setOfPred_imp_lt (r : α -> α -> Prop) [h : IsWellFounded α r] : 
IsCofinal { a | forall b, r b a -> b < a }
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `Set.nonempty_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set.Ici
 a).Nonempty
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
The set of "records" (the smallest inputs yielding the highest values) with resp
ect to a
well-ordering of `α` is a cofinal set.
-/
theorem isCofinal_setOfPred_imp_lt (r : α → α → Prop) [h : IsWellFounded α r] :
    IsCofinal { a | ∀ b, r b a → b < a } := by
  intro a
  obtain ⟨b, hb, hb'⟩ := h.wf.has_min (Set.Ici a) Set.nonempty_Ici
  refine ⟨b, fun c hc ↦ ?_, hb⟩
  by_contra! hc'
  exact hb' c (hb.trans hc') hc

@[deprecated (since := "2026-07-09")] alias isCofinal_setOf_imp_lt := isCofinal_setOfPred_imp_lt
/-
**isCofinal_range_of_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCofinal_range_of_strictMono [WellFoundedLT α] {f : α -> α} (hf : StrictM
ono f) : IsCofinal (range f)
参数：hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
-/
theorem isCofinal_range_of_strictMono [WellFoundedLT α] {f : α → α} (hf : StrictMono f) :
    IsCofinal (range f) :=
  fun x ↦ ⟨_, ⟨x, rfl⟩, hf.le_apply⟩

end LinearOrder

