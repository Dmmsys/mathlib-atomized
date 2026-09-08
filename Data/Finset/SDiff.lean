/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# Difference of finite sets

## Main declarations

* `Finset.instSDiff`: Defines the set difference `s \ t` for finsets `s` and `t`.
* `Finset.instGeneralizedBooleanAlgebra`: Finsets almost have a Boolean algebra structure

## Tags

finite sets, finset

-/

public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### sdiff -/


section Sdiff

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
/-
**Finset.instSDiff** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instSDiff : SDiff (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s \ t` is the set consisting of the elements of `s` that are not in `t`.
-/
instance instSDiff : SDiff (Finset α) :=
  ⟨fun s₁ s₂ => ⟨s₁.1 - s₂.1, nodup_of_le (Multiset.sub_le_self ..) s₁.2⟩⟩

@[simp]
/-
**Finset.sdiff_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_val (s₁ s₂ : Finset α) : (s₁ \ s₂).val = s₁.val - s₂.val
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_val (s₁ s₂ : Finset α) : (s₁ \ s₂).val = s₁.val - s₂.val :=
  rfl

@[simp, grind =]
/-
**Finset.mem_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_sub_of_nodup`：mem_sub_of_nodup [DecidableEq α] {a : α} {s t
 : Multiset α} (d : Nodup s) : a in s - t ↔ a in s ∧ a ∉ t
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem mem_sdiff : a ∈ s \ t ↔ a ∈ s ∧ a ∉ t :=
  mem_sub_of_nodup s.2

@[simp]
/-
**Finset.inter_sdiff_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_sdiff_self (s₁ s₂ : Finset α) : s₁ inter (s₂ \ s₁) = ∅
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_sdiff_self (s₁ s₂ : Finset α) : s₁ ∩ (s₂ \ s₁) = ∅ := by grind
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GeneralizedBooleanAlgebra (Finset α) where
  sup_inf_sdiff := by grind
  inf_inf_sdiff := by grind
/-
**Finset.notMem_sdiff_of_mem_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_sdiff_of_mem_right (h : a in t) : a ∉ s \ t
参数：h : a in t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_sdiff_of_mem_right (h : a ∈ t) : a ∉ s \ t := by grind
/-
**Finset.notMem_sdiff_of_notMem_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_sdiff_of_notMem_left (h : a ∉ s) : a ∉ s \ t
参数：h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem notMem_sdiff_of_notMem_left (h : a ∉ s) : a ∉ s \ t := by simp [h]
/-
**Finset.union_sdiff_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_sdiff_of_subset (h : s subseteq t) : s union t \ s = t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_sdiff_of_subset (h : s ⊆ t) : s ∪ t \ s = t := by grind
/-
**Finset.sdiff_union_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ subseteq s₂) : s₂ \ s₁ un
ion s₁ = s₂
参数：h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₂ \ s₁ ∪ s₁ = s₂ := by grind

/-- See also `Finset.sdiff_inter_right_comm`. -/
/-
**Finset.inter_sdiff_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inter_sdiff_assoc (s t u : Finset α) : (s inter t) \ u = s inter (t \ u)
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sdiff_assoc`：inf_sdiff_assoc (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z

--- 原说明 ---
See also `Finset.sdiff_inter_right_comm`.
-/
lemma inter_sdiff_assoc (s t u : Finset α) : (s ∩ t) \ u = s ∩ (t \ u) := inf_sdiff_assoc ..

/-- See also `Finset.inter_sdiff_assoc`. -/
/-
**Finset.sdiff_inter_right_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sdiff_inter_right_comm (s t u : Finset α) : s \ t inter u = (s inter u) \ 
t
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_inf_right_comm`：sdiff_inf_right_comm (x y z : α) : x \ z ⊓ y = (x 
⊓ y) \ z

--- 原说明 ---
See also `Finset.inter_sdiff_assoc`.
-/
lemma sdiff_inter_right_comm (s t u : Finset α) : s \ t ∩ u = (s ∩ u) \ t := sdiff_inf_right_comm ..
/-
**Finset.inter_sdiff_left_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inter_sdiff_left_comm (s t u : Finset α) : s inter (t \ u) = t inter (s \ 
u)
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inf_sdiff_left_comm`：inf_sdiff_left_comm (a b c : α) : a ⊓ (b \ c) = b ⊓
 (a \ c)
-/
lemma inter_sdiff_left_comm (s t u : Finset α) : s ∩ (t \ u) = t ∩ (s \ u) := inf_sdiff_left_comm ..

@[simp]
/-
**Finset.sdiff_inter_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_inter_self (s₁ s₂ : Finset α) : s₂ \ s₁ inter s₁ = ∅
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sdiff_self_left`：inf_sdiff_self_left : y \ x ⊓ x = ⊥
-/
theorem sdiff_inter_self (s₁ s₂ : Finset α) : s₂ \ s₁ ∩ s₁ = ∅ :=
  inf_sdiff_self_left
/-
**Finset.sdiff_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s₁ : Finset α), s₁ \ s₁ = ∅
参数：s₁ : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
-/
protected theorem sdiff_self (s₁ : Finset α) : s₁ \ s₁ = ∅ :=
  _root_.sdiff_self
/-
**Finset.sdiff_inter_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_inter_distrib_right (s t u : Finset α) : s \ (t inter u) = s \ t uni
on s \ u
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_inf`：sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c
-/
theorem sdiff_inter_distrib_right (s t u : Finset α) : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf

@[simp]
/-
**Finset.sdiff_inter_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_inter_self_left (s t : Finset α) : s \ (s inter t) = s \ t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_inf_self_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebr
a α] (a b : α), a \ (a ⊓ b) = a \ b
-/
theorem sdiff_inter_self_left (s t : Finset α) : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left _ _

@[simp]
/-
**Finset.sdiff_inter_self_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_inter_self_right (s t : Finset α) : s \ (t inter s) = s \ t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_inf_self_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] (a b : α), b \ (a ⊓ b) = b \ a
-/
theorem sdiff_inter_self_right (s t : Finset α) : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right _ _

@[simp]
/-
**Finset.sdiff_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_empty : s \ ∅ = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
-/
theorem sdiff_empty : s \ ∅ = s :=
  sdiff_bot

@[mono, gcongr]
/-
**Finset.sdiff_subset_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_subset_sdiff (hst : s subseteq t) (hvu : v subseteq u) : s \ u subse
teq t \ v
参数：hst : s subseteq t；hvu : v subseteq u。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_subset_sdiff (hst : s ⊆ t) (hvu : v ⊆ u) : s \ u ⊆ t \ v := by grind

variable (u) in
/-
**Finset.sdiff_subset_sdiff_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sdiff_subset_sdiff_left (h : s subseteq t) : s \ u subseteq t \ u
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sdiff_subset_sdiff`：sdiff_subset_sdiff (hst : s subseteq t) (hvu 
: v subseteq u) : s \ u subseteq t \ v
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma sdiff_subset_sdiff_left (h : s ⊆ t) : s \ u ⊆ t \ u := by gcongr

variable (u) in
/-
**Finset.sdiff_subset_sdiff_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sdiff_subset_sdiff_right (h : s subseteq t) : u \ t subseteq u \ s
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sdiff_subset_sdiff`：sdiff_subset_sdiff (hst : s subseteq t) (hvu 
: v subseteq u) : s \ u subseteq t \ v
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma sdiff_subset_sdiff_right (h : s ⊆ t) : u \ t ⊆ u \ s := by gcongr
/-
**Finset.sdiff_subset_sdiff_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_subset_sdiff_iff_subset {r : Finset α} (hs : s subseteq r) (ht : t s
ubseteq r) : r \ s subseteq r \ t ↔ t subseteq s
参数：hs : s subseteq r；ht : t subseteq r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le_sdiff_iff_le`：sdiff_le_sdiff_iff_le (hx : x <= z) (hy : y <= z)
 : z \ x <= z \ y ↔ y <= x
-/
theorem sdiff_subset_sdiff_iff_subset {r : Finset α} (hs : s ⊆ r) (ht : t ⊆ r) :
    r \ s ⊆ r \ t ↔ t ⊆ s :=
  sdiff_le_sdiff_iff_le hs ht

@[simp, grind =, norm_cast]
/-
**Finset.coe_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ : Set α)
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
-/
theorem coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ : Set α) :=
  Set.ext fun _ => mem_sdiff

@[simp]
/-
**Finset.union_sdiff_self_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_sdiff_self_eq_union : s union t \ s = s union t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_self_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] (a b : α), a ⊔ b \ a = a ⊔ b
-/
theorem union_sdiff_self_eq_union : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self_right _ _

@[simp]
/-
**Finset.sdiff_union_self_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_union_self_eq_union : s \ t union t = s union t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_self_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebr
a α] (a b : α), b \ a ⊔ a = b ⊔ a
-/
theorem sdiff_union_self_eq_union : s \ t ∪ t = s ∪ t :=
  sup_sdiff_self_left _ _
/-
**Finset.union_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_sdiff_left (s t : Finset α) : (s union t) \ s = t \ s
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_left_self`：sup_sdiff_left_self : (a ⊔ b) \ a = b \ a
-/
theorem union_sdiff_left (s t : Finset α) : (s ∪ t) \ s = t \ s :=
  sup_sdiff_left_self
/-
**Finset.union_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_sdiff_right (s t : Finset α) : (s union t) \ t = s \ t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_right_self`：sup_sdiff_right_self : (a ⊔ b) \ b = a \ b
-/
theorem union_sdiff_right (s t : Finset α) : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self
/-
**Finset.union_sdiff_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_sdiff_cancel_left (h : Disjoint s t) : (s union t) \ s = t
参数：h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.sup_sdiff_cancel_left`：∀ {α : Type u_2} [inst : GeneralizedCohe
ytingAlgebra α] {a b : α}, Disjoint a b → (a ⊔ b) \ a = b
-/
theorem union_sdiff_cancel_left (h : Disjoint s t) : (s ∪ t) \ s = t :=
  h.sup_sdiff_cancel_left
/-
**Finset.union_sdiff_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_sdiff_cancel_right (h : Disjoint s t) : (s union t) \ t = s
参数：h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.sup_sdiff_cancel_right`：∀ {α : Type u_2} [inst : GeneralizedCoh
eytingAlgebra α] {a b : α}, Disjoint a b → (a ⊔ b) \ b = a
-/
theorem union_sdiff_cancel_right (h : Disjoint s t) : (s ∪ t) \ t = s :=
  h.sup_sdiff_cancel_right

/-- `· ∪ s` is injective on finsets disjoint from `s`. -/
/-
**Finset.disjoint_injOn_union_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjoint_injOn_union_left (s : Finset α) : {t | Disjoint s t}.InjOn (· uni
on s)
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`· ∪ s` is injective on finsets disjoint from `s`.
-/
lemma disjoint_injOn_union_left (s : Finset α) : {t | Disjoint s t}.InjOn (· ∪ s) := by
  grind [Set.InjOn, union_sdiff_cancel_right]

/-- `· \ s` is injective on finsets containing `s`. -/
/-
**Finset.superset_injOn_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：superset_injOn_sdiff (s : Finset α) : {t | s subseteq t}.InjOn (· \ s)
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`· \ s` is injective on finsets containing `s`.
-/
lemma superset_injOn_sdiff (s : Finset α) : {t | s ⊆ t}.InjOn (· \ s) := by
  grind [Set.InjOn, sdiff_union_of_subset]
/-
**Finset.union_sdiff_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_sdiff_symm : s union t \ s = t union s \ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_sdiff_self_eq_union`：union_sdiff_self_eq_union : s union t 
\ s = s union t
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem union_sdiff_symm : s ∪ t \ s = t ∪ s \ t := by simp [union_comm]
/-
**Finset.sdiff_union_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_union_inter (s t : Finset α) : s \ t union s inter t = s
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_inf`：sup_sdiff_inf (x y : α) : x \ y ⊔ x ⊓ y = x
-/
theorem sdiff_union_inter (s t : Finset α) : s \ t ∪ s ∩ t = s :=
  sup_sdiff_inf _ _
/-
**Finset.sdiff_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_idem (s t : Finset α) : (s \ t) \ t = s \ t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_idem`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b
 : α}, (a \ b) \ b = a \ b
-/
theorem sdiff_idem (s t : Finset α) : (s \ t) \ t = s \ t :=
  _root_.sdiff_idem
/-
**Finset.subset_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjoint s u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_sdiff`：le_sdiff : x <= y \ z ↔ x <= y ∧ Disjoint x z
-/
theorem subset_sdiff : s ⊆ t \ u ↔ s ⊆ t ∧ Disjoint s u :=
  le_sdiff

@[simp]
/-
**Finset.sdiff_eq_empty_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_eq_empty_iff_subset : s \ t = ∅ ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_eq_bot_iff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α
] {a b : α}, b \ a = ⊥ ↔ b ≤ a
-/
theorem sdiff_eq_empty_iff_subset : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff

@[grind =]
/-
**Finset.sdiff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_nonempty : (s \ t).Nonempty ↔ ¬s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.sdiff_eq_empty_iff_subset`：sdiff_eq_empty_iff_subset : s \ t = ∅ 
↔ s subseteq t
-/
theorem sdiff_nonempty : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  nonempty_iff_ne_empty.trans sdiff_eq_empty_iff_subset.not

@[simp]
/-
**Finset.empty_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_sdiff (s : Finset α) : ∅ \ s = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, ⊥ \ a = ⊥
-/
theorem empty_sdiff (s : Finset α) : ∅ \ s = ∅ :=
  bot_sdiff
/-
**Finset.insert_sdiff_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_sdiff_of_notMem (s : Finset α) {t : Finset α} {x : α} (h : x ∉ t) :
 insert x s \ t = insert x (s \ t)
参数：s : Finset α；h : x ∉ t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_sdiff_of_notMem (s : Finset α) {t : Finset α} {x : α} (h : x ∉ t) :
    insert x s \ t = insert x (s \ t) := by grind
/-
**Finset.insert_sdiff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_sdiff_of_mem (s : Finset α) {x : α} (h : x in t) : insert x s \ t =
 s \ t
参数：s : Finset α；h : x in t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_sdiff_of_mem (s : Finset α) {x : α} (h : x ∈ t) : insert x s \ t = s \ t := by grind
/-
**Finset.insert_sdiff_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {a : α}, a ∈ s → in
sert a (s \ {a}) = s
参数：s \ {a}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma insert_sdiff_self_of_mem (ha : a ∈ s) : insert a (s \ {a}) = s := by grind
/-
**Finset.insert_sdiff_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {a : α}, a ∉ s → in
sert a s \ s = {a}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma insert_sdiff_cancel (ha : a ∉ s) : insert a s \ s = {a} := by grind

@[simp]
/-
**Finset.insert_sdiff_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_sdiff_insert (s t : Finset α) (x : α) : insert x s \ insert x t = s
 \ insert x t
参数：s t : Finset α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.insert_sdiff_of_mem`：insert_sdiff_of_mem (s : Finset α) {x : α} (
h : x in t) : insert x s \ t = s \ t
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
theorem insert_sdiff_insert (s t : Finset α) (x : α) : insert x s \ insert x t = s \ insert x t :=
  insert_sdiff_of_mem _ (mem_insert_self _ _)
/-
**Finset.insert_sdiff_insert'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_sdiff_insert' (hab : a != b) (ha : a ∉ s) : insert a s \ insert b s
 = {a}
参数：hab : a != b；ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma insert_sdiff_insert' (hab : a ≠ b) (ha : a ∉ s) : insert a s \ insert b s = {a} := by
  ext; aesop
/-
**Finset.cons_sdiff_cons** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：cons_sdiff_cons (hab : a != b) (ha hb) : s.cons a ha \ s.cons b hb = {a}
参数：hab : a != b；ha hb。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cons_sdiff_cons (hab : a ≠ b) (ha hb) : s.cons a ha \ s.cons b hb = {a} := by grind
/-
**Finset.sdiff_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_insert_of_notMem {x : α} (h : x ∉ s) (t : Finset α) : s \ insert x t
 = s \ t
参数：h : x ∉ s；t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_insert_of_notMem {x : α} (h : x ∉ s) (t : Finset α) : s \ insert x t = s \ t := by
  grind
/-
**Finset.sdiff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_subset {s t : Finset α} : s \ t subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem sdiff_subset {s t : Finset α} : s \ t ⊆ s := by simp
/-
**Finset.sdiff_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_ssubset (h : t subseteq s) (ht : t.Nonempty) : s \ t ⊂ s
参数：h : t subseteq s；ht : t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_ssubset (h : t ⊆ s) (ht : t.Nonempty) : s \ t ⊂ s := by grind
/-
**Finset.union_sdiff_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_sdiff_distrib (s₁ s₂ t : Finset α) : (s₁ union s₂) \ t = s₁ \ t unio
n s₂ \ t
参数：s₁ s₂ t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff`：sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c
-/
theorem union_sdiff_distrib (s₁ s₂ t : Finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t :=
  sup_sdiff
/-
**Finset.sdiff_union_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_union_distrib (s t₁ t₂ : Finset α) : s \ (t₁ union t₂) = s \ t₁ inte
r (s \ t₂)
参数：s t₁ t₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sup`：sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z
-/
theorem sdiff_union_distrib (s t₁ t₂ : Finset α) : s \ (t₁ ∪ t₂) = s \ t₁ ∩ (s \ t₂) :=
  sdiff_sup
/-
**Finset.union_sdiff_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_sdiff_self (s t : Finset α) : (s union t) \ t = s \ t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_right_self`：sup_sdiff_right_self : (a ⊔ b) \ b = a \ b
-/
theorem union_sdiff_self (s t : Finset α) : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self
/-
**Finset.Nontrivial.sdiff_singleton_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset.N
ontrivial`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {c : α} {s : Finset α}, s.Nontrivi
al → (s \ {c}).Nonempty
参数：s \ {c}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nontrivial.sdiff_singleton_nonempty {c : α} {s : Finset α} (hS : s.Nontrivial) :
    (s \ {c}).Nonempty := by grind
/-
**Finset.sdiff_sdiff_left'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_sdiff_left' (s t u : Finset α) : (s \ t) \ u = s \ t inter (s \ u)
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_left'`：sdiff_sdiff_left' : (x \ y) \ z = x \ y ⊓ x \ z
-/
theorem sdiff_sdiff_left' (s t u : Finset α) : (s \ t) \ u = s \ t ∩ (s \ u) :=
  _root_.sdiff_sdiff_left'
/-
**Finset.sdiff_union_sdiff_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_union_sdiff_cancel (hts : t subseteq s) (hut : u subseteq t) : s \ t
 union t \ u = s \ u
参数：hts : t subseteq s；hut : u subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sup_sdiff_cancel`：sdiff_sup_sdiff_cancel (hba : b <= a) (hcb : c <
= b) : a \ b ⊔ b \ c = a \ c
-/
theorem sdiff_union_sdiff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut
/-
**Finset.sdiff_sdiff_eq_sdiff_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_sdiff_eq_sdiff_union (h : u subseteq s) : s \ (t \ u) = s \ t union 
u
参数：h : u subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_eq_sdiff_sup`：sdiff_sdiff_eq_sdiff_sup (h : z <= x) : x \ (y
 \ z) = x \ y ⊔ z
-/
theorem sdiff_sdiff_eq_sdiff_union (h : u ⊆ s) : s \ (t \ u) = s \ t ∪ u :=
  sdiff_sdiff_eq_sdiff_sup h
/-
**Finset.sdiff_sdiff_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_sdiff_self_left (s t : Finset α) : s \ (s \ t) = s inter t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
-/
theorem sdiff_sdiff_self_left (s t : Finset α) : s \ (s \ t) = s ∩ t :=
  sdiff_sdiff_right_self
/-
**Finset.sdiff_sdiff_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_sdiff_eq_self (h : t subseteq s) : s \ (s \ t) = t
参数：h : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_eq_self`：sdiff_sdiff_eq_self (h : y <= x) : x \ (x \ y) = y
-/
theorem sdiff_sdiff_eq_self (h : t ⊆ s) : s \ (s \ t) = t :=
  _root_.sdiff_sdiff_eq_self h
/-
**Finset.sdiff_eq_sdiff_iff_inter_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : Finset α} : s \ t₁ = s \ t₂ ↔
 s inter t₁ = s inter t₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_eq_sdiff_iff_inf_eq_inf`：sdiff_eq_sdiff_iff_inf_eq_inf : y \ x = y
 \ z ↔ y ⊓ x = y ⊓ z
-/
theorem sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : Finset α} :
    s \ t₁ = s \ t₂ ↔ s ∩ t₁ = s ∩ t₂ :=
  sdiff_eq_sdiff_iff_inf_eq_inf
/-
**Finset.union_eq_sdiff_union_sdiff_union_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finse
t`。
形式化陈述：union_eq_sdiff_union_sdiff_union_inter (s t : Finset α) : s union t = s \ 
t union t \ s union s inter t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_sdiff_sup_sdiff_sup_inf`：sup_eq_sdiff_sup_sdiff_sup_inf : x ⊔ y =
 x \ y ⊔ y \ x ⊔ x ⊓ y
-/
theorem union_eq_sdiff_union_sdiff_union_inter (s t : Finset α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf
/-
**Finset.sdiff_eq_self_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_eq_self_iff_disjoint : s \ t = s ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
-/
theorem sdiff_eq_self_iff_disjoint : s \ t = s ↔ Disjoint s t :=
  sdiff_eq_left
/-
**Finset.sdiff_eq_self_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_eq_self_of_disjoint (h : Disjoint s t) : s \ t = s
参数：h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sdiff_eq_self_iff_disjoint`：sdiff_eq_self_iff_disjoint : s \ t = 
s ↔ Disjoint s t
-/
theorem sdiff_eq_self_of_disjoint (h : Disjoint s t) : s \ t = s :=
  sdiff_eq_self_iff_disjoint.2 h

end Sdiff

end Finset

