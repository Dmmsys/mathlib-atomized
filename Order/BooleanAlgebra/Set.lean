/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Insert
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.FastInstance

/-!
# Boolean algebra of sets

This file proves that `Set α` is a Boolean algebra, and proves results about set difference and
complement.

## Notation

* `sᶜ` for the complement of `s`

## Tags

set, sets, subset, subsets, complement
-/

@[expose] public section

assert_not_exists RelIso

open Function

namespace Set
variable {α β : Type*} {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HImp (Set α) where
  himp s t := {x | x ∈ s → x ∈ t}
/-
**Set.mem_himp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s t : Set α} {a : α}, a ∈ s ⇨ t ↔ a ∈ s → a ∈ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_himp_iff : a ∈ s ⇨ t ↔ a ∈ s → a ∈ t := .rfl
/-
**Set.instBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：instBooleanAlgebra : BooleanAlgebra (Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBooleanAlgebra : BooleanAlgebra (Set α) :=
  fast_instance% { (inferInstance : BooleanAlgebra (α → Prop)) with }
/-
**Set.himp_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：himp_def : s ⇨ t = t union sᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
-/
theorem himp_def : s ⇨ t = t ∪ sᶜ := himp_eq

/-- See also `Set.sdiff_inter_right_comm`. -/
/-
**Set.inter_sdiff_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inter_sdiff_assoc (a b c : Set α) : (a inter b) \ c = a inter (b \ c)
参数：a b c : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sdiff_assoc`：inf_sdiff_assoc (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z

--- 原说明 ---
See also `Set.sdiff_inter_right_comm`.
-/
lemma inter_sdiff_assoc (a b c : Set α) : (a ∩ b) \ c = a ∩ (b \ c) := inf_sdiff_assoc ..

@[deprecated (since := "2026-06-03")] alias inter_diff_assoc := inter_sdiff_assoc

/-- See also `Set.inter_sdiff_assoc`. -/
/-
**Set.sdiff_inter_right_comm** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiff_inter_right_comm (s t u : Set α) : s \ t inter u = (s inter u) \ t
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_inf_right_comm`：sdiff_inf_right_comm (x y z : α) : x \ z ⊓ y = (x 
⊓ y) \ z

--- 原说明 ---
See also `Set.inter_sdiff_assoc`.
-/
lemma sdiff_inter_right_comm (s t u : Set α) : s \ t ∩ u = (s ∩ u) \ t := sdiff_inf_right_comm ..
/-
**Set.inter_sdiff_left_comm** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inter_sdiff_left_comm (s t u : Set α) : s inter (t \ u) = t inter (s \ u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inf_sdiff_left_comm`：inf_sdiff_left_comm (a b c : α) : a ⊓ (b \ c) = b ⊓
 (a \ c)
-/
lemma inter_sdiff_left_comm (s t u : Set α) : s ∩ (t \ u) = t ∩ (s \ u) := inf_sdiff_left_comm ..
/-
**Set.sdiff_union_sdiff_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
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

@[deprecated (since := "2026-06-03")] alias diff_union_diff_cancel := sdiff_union_sdiff_cancel

/-- A version of `sdiff_union_sdiff_cancel` with more general hypotheses. -/
/-
**Set.sdiff_union_sdiff_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_union_sdiff_cancel' (hi : s inter u subseteq t) (hu : t subseteq s u
nion u) : (s \ t) union (t \ u) = s \ u
参数：hi : s inter u subseteq t；hu : t subseteq s union u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sup_sdiff_cancel'`：sdiff_sup_sdiff_cancel' (hinf : a ⊓ c <= b) (hs
up : b <= a ⊔ c) : a \ b ⊔ b \ c = a \ c

--- 原说明 ---
A version of `sdiff_union_sdiff_cancel` with more general hypotheses.
-/
theorem sdiff_union_sdiff_cancel' (hi : s ∩ u ⊆ t) (hu : t ⊆ s ∪ u) : (s \ t) ∪ (t \ u) = s \ u :=
  sdiff_sup_sdiff_cancel' hi hu

@[deprecated (since := "2026-06-03")] alias diff_union_diff_cancel' := sdiff_union_sdiff_cancel'
/-
**Set.sdiff_sdiff_eq_sdiff_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
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

@[deprecated (since := "2026-06-03")] alias diff_diff_eq_sdiff_union := sdiff_sdiff_eq_sdiff_union
/-
**Set.inter_sdiff_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_sdiff_distrib_left (s t u : Set α) : s inter (t \ u) = (s inter t) \
 (s inter u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sdiff_distrib_left`：inf_sdiff_distrib_left (a b c : α) : a ⊓ b \ c =
 (a ⊓ b) \ (a ⊓ c)
-/
theorem inter_sdiff_distrib_left (s t u : Set α) : s ∩ (t \ u) = (s ∩ t) \ (s ∩ u) :=
  inf_sdiff_distrib_left _ _ _

@[deprecated (since := "2026-06-03")] alias inter_diff_distrib_left := inter_sdiff_distrib_left
/-
**Set.inter_sdiff_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_sdiff_distrib_right (s t u : Set α) : (s \ t) inter u = (s inter u) 
\ (t inter u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sdiff_distrib_right`：inf_sdiff_distrib_right (a b c : α) : a \ b ⊓ c
 = (a ⊓ c) \ (b ⊓ c)
-/
theorem inter_sdiff_distrib_right (s t u : Set α) : (s \ t) ∩ u = (s ∩ u) \ (t ∩ u) :=
  inf_sdiff_distrib_right _ _ _

@[deprecated (since := "2026-06-03")] alias inter_diff_distrib_right := inter_sdiff_distrib_right
/-
**Set.sdiff_inter_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_inter_distrib_right (s t r : Set α) : (t inter r) \ s = (t \ s) inte
r (r \ s)
参数：s t r : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sdiff`：inf_sdiff : (x ⊓ y) \ z = x \ z ⊓ y \ z
-/
theorem sdiff_inter_distrib_right (s t r : Set α) : (t ∩ r) \ s = (t \ s) ∩ (r \ s) :=
  inf_sdiff

@[deprecated (since := "2026-06-03")] alias diff_inter_distrib_right := sdiff_inter_distrib_right

/-! ### Lemmas about complement -/

/-
**Set.compl_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_def (s : Set α) : sᶜ = { x | x ∉ s }
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Lemmas about complement
-/
theorem compl_def (s : Set α) : sᶜ = { x | x ∉ s } :=
  rfl
/-
**Set.mem_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
参数：h : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_compl {s : Set α} {x : α} (h : x ∉ s) : x ∈ sᶜ :=
  h
/-
**Set.compl_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_ofPred {α} (p : α -> Prop) : { a | p a }ᶜ = { a | ¬p a }
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl_ofPred {α} (p : α → Prop) : { a | p a }ᶜ = { a | ¬p a } :=
  rfl

@[deprecated (since := "2026-07-09")] alias compl_setOf := compl_ofPred
/-
**Set.notMem_of_mem_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_of_mem_compl {s : Set α} {x : α} (h : x in sᶜ) : x ∉ s
参数：h : x in sᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_of_mem_compl {s : Set α} {x : α} (h : x ∈ sᶜ) : x ∉ s :=
  h
/-
**Set.notMem_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x ∈ s :=
  not_not

@[simp]
/-
**Set.inter_compl_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_compl_self (s : Set α) : s inter sᶜ = ∅
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_compl_eq_bot`：inf_compl_eq_bot : a ⊓ aᶜ = ⊥
-/
theorem inter_compl_self (s : Set α) : s ∩ sᶜ = ∅ :=
  inf_compl_eq_bot

@[simp]
/-
**Set.compl_inter_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_inter_self (s : Set α) : sᶜ inter s = ∅
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_inf_eq_bot`：compl_inf_eq_bot : aᶜ ⊓ a = ⊥
-/
theorem compl_inter_self (s : Set α) : sᶜ ∩ s = ∅ :=
  compl_inf_eq_bot

@[simp]
/-
**Set.compl_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_empty : (∅ : Set α)ᶜ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_bot`：compl_bot : (⊥ : α)ᶜ = ⊤
-/
theorem compl_empty : (∅ : Set α)ᶜ = univ :=
  compl_bot

@[simp]
/-
**Set.compl_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_sup`：compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
-/
theorem compl_union (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  compl_sup
/-
**Set.compl_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_inf`：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
-/
theorem compl_inter (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  compl_inf

@[simp]
/-
**Set.compl_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_univ : (univ : Set α)ᶜ = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_top`：compl_top : (⊤ : α)ᶜ = ⊥
-/
theorem compl_univ : (univ : Set α)ᶜ = ∅ :=
  compl_top

@[simp]
/-
**Set.compl_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_eq_bot`：compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤
-/
theorem compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot

@[simp]
/-
**Set.compl_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_eq_top`：compl_eq_top : xᶜ = ⊤ ↔ x = ⊥
-/
theorem compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top
/-
**Set.compl_ne_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_ne_univ : sᶜ != univ ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.compl_univ_iff`：compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
theorem compl_ne_univ : sᶜ ≠ univ ↔ s.Nonempty :=
  compl_univ_iff.not.trans nonempty_iff_ne_empty.symm
/-
**Set.inl_compl_union_inr_compl** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inl_compl_union_inr_compl {s : Set α} {t : Set β} : Sum.inl '' sᶜ union Su
m.inr '' tᶜ = (Sum.inl '' s union Sum.inr '' t)ᶜ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inl_compl_union_inr_compl {s : Set α} {t : Set β} :
    Sum.inl '' sᶜ ∪ Sum.inr '' tᶜ = (Sum.inl '' s ∪ Sum.inr '' t)ᶜ := by
  grind
/-
**Set.nonempty_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_compl : sᶜ.Nonempty ↔ s != univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.ne_univ_iff_exists_notMem`：ne_univ_iff_exists_notMem {α : Type*} (s 
: Set α) : s != univ ↔ exists a, a ∉ s
-/
theorem nonempty_compl : sᶜ.Nonempty ↔ s ≠ univ :=
  (ne_univ_iff_exists_notMem s).symm
/-
**Set.union_eq_compl_compl_inter_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_eq_compl_compl_inter_compl (s t : Set α) : s union t = (sᶜ inter tᶜ)
ᶜ
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `or_iff_not_and_not`：or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b)
-/
theorem union_eq_compl_compl_inter_compl (s t : Set α) : s ∪ t = (sᶜ ∩ tᶜ)ᶜ :=
  ext fun _ => or_iff_not_and_not
/-
**Set.inter_eq_compl_compl_union_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_eq_compl_compl_union_compl (s t : Set α) : s inter t = (sᶜ union tᶜ)
ᶜ
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_iff_not_or_not`：and_iff_not_or_not : a ∧ b ↔ ¬(¬a ∨ ¬b)
-/
theorem inter_eq_compl_compl_union_compl (s t : Set α) : s ∩ t = (sᶜ ∪ tᶜ)ᶜ :=
  ext fun _ => and_iff_not_or_not

@[simp]
/-
**Set.union_compl_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_compl_self (s : Set α) : s union sᶜ = univ
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem union_compl_self (s : Set α) : s ∪ sᶜ = univ :=
  eq_univ_iff_forall.2 fun _ => em _

@[simp]
/-
**Set.compl_union_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_union_self (s : Set α) : sᶜ union s = univ
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
-/
theorem compl_union_self (s : Set α) : sᶜ ∪ s = univ := by rw [union_comm, union_compl_self]
/-
**Set.compl_subset_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_le_iff_compl_le`：compl_le_iff_compl_le : xᶜ <= y ↔ yᶜ <= x
-/
theorem compl_subset_comm : sᶜ ⊆ t ↔ tᶜ ⊆ s :=
  compl_le_iff_compl_le
/-
**Set.subset_compl_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_compl_iff_le_compl`：∀ {α : Type u_2} [inst : HeytingAlgebra α] {a b :
 α}, a ≤ bᶜ ↔ b ≤ aᶜ
-/
theorem subset_compl_comm : s ⊆ tᶜ ↔ t ⊆ sᶜ :=
  le_compl_iff_le_compl
/-
**Set.compl_subset_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_le_compl_iff_le`：compl_le_compl_iff_le : yᶜ <= xᶜ ↔ x <= y
-/
theorem compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s :=
  compl_le_compl_iff_le
/-
**Set.compl_subset_compl_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_subset_compl_of_subset (h : t subseteq s) : sᶜ subseteq tᶜ
参数：h : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
-/
theorem compl_subset_compl_of_subset (h : t ⊆ s) : sᶜ ⊆ tᶜ := by gcongr
/-
**Set.subset_union_compl_iff_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_union_compl_iff_inter_subset {s t u : Set α} : s subseteq t union u
ᶜ ↔ s inter u subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.le_sup_right_iff_inf_left_le`：le_sup_right_iff_inf_left_le {a b}
 (h : IsCompl x y) : a <= b ⊔ y ↔ a ⊓ x <= b
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
-/
theorem subset_union_compl_iff_inter_subset {s t u : Set α} : s ⊆ t ∪ uᶜ ↔ s ∩ u ⊆ t :=
  (@isCompl_compl _ u _).le_sup_right_iff_inf_left_le
/-
**Set.compl_subset_iff_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_subset_iff_union {s t : Set α} : sᶜ subseteq t ↔ s union t = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem compl_subset_iff_union {s t : Set α} : sᶜ ⊆ t ↔ s ∪ t = univ :=
  Iff.symm <| eq_univ_iff_forall.trans <| forall_congr' fun _ => or_iff_not_imp_left
/-
**Set.inter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_subset (a b c : Set α) : a inter b subseteq c ↔ a subseteq bᶜ union 
c
参数：a b c : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `imp_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a → b ↔ a → c)
· 使用定理 `imp_iff_not_or`：imp_iff_not_or : a -> b ↔ ¬a ∨ b
-/
theorem inter_subset (a b c : Set α) : a ∩ b ⊆ c ↔ a ⊆ bᶜ ∪ c :=
  forall_congr' fun _ => and_imp.trans <| imp_congr_right fun _ => imp_iff_not_or
/-
**Set.inter_compl_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_compl_nonempty_iff {s t : Set α} : (s inter tᶜ).Nonempty ↔ ¬s subset
eq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inter_compl_nonempty_iff {s t : Set α} : (s ∩ tᶜ).Nonempty ↔ ¬s ⊆ t :=
  (not_subset.trans <| exists_congr fun x => by simp).symm
/-
**Set.subset_compl_iff_disjoint_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_compl_iff_disjoint_left : s subseteq tᶜ ↔ Disjoint t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_compl_iff_disjoint_left`：le_compl_iff_disjoint_left : a <= bᶜ ↔ Disjo
int b a
-/
lemma subset_compl_iff_disjoint_left : s ⊆ tᶜ ↔ Disjoint t s := le_compl_iff_disjoint_left
/-
**Set.subset_compl_iff_disjoint_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_compl_iff_disjoint_right : s subseteq tᶜ ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_compl_iff_disjoint_right`：le_compl_iff_disjoint_right : a <= bᶜ ↔ Dis
joint a b
-/
lemma subset_compl_iff_disjoint_right : s ⊆ tᶜ ↔ Disjoint s t := le_compl_iff_disjoint_right
/-
**Set.disjoint_compl_left_iff_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_compl_left_iff_subset : Disjoint sᶜ t ↔ t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_compl_left_iff`：disjoint_compl_left_iff : Disjoint xᶜ y ↔ y <= 
x
-/
lemma disjoint_compl_left_iff_subset : Disjoint sᶜ t ↔ t ⊆ s := disjoint_compl_left_iff
/-
**Set.disjoint_compl_right_iff_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_compl_right_iff_subset : Disjoint s tᶜ ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_compl_right_iff`：disjoint_compl_right_iff : Disjoint x yᶜ ↔ x <
= y
-/
lemma disjoint_compl_right_iff_subset : Disjoint s tᶜ ↔ s ⊆ t := disjoint_compl_right_iff

alias ⟨_, _root_.Disjoint.subset_compl_right⟩ := subset_compl_iff_disjoint_right
alias ⟨_, _root_.Disjoint.subset_compl_left⟩ := subset_compl_iff_disjoint_left
@[deprecated LE.le.disjoint_compl_left (since := "2026-06-05")]
alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_left⟩ := disjoint_compl_left_iff_subset
@[deprecated LE.le.disjoint_compl_right (since := "2026-06-05")]
alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_right⟩ := disjoint_compl_right_iff_subset
/-
**Set.nonempty_compl_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [Nontrivial α] (x : α), {x}ᶜ.Nonempty
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
-/
@[simp] lemma nonempty_compl_of_nontrivial [Nontrivial α] (x : α) : Set.Nonempty {x}ᶜ := exists_ne x
/-
**Set.mem_compl_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_compl_singleton_iff : a in ({b} : Set α)ᶜ ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_compl_singleton_iff : a ∈ ({b} : Set α)ᶜ ↔ a ≠ b := .rfl
/-
**Set.compl_singleton_eq** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：compl_singleton_eq (a : α) : {a}ᶜ = {x | x != a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compl_singleton_eq (a : α) : {a}ᶜ = {x | x ≠ a} := rfl

@[simp]
/-
**Set.compl_ne_eq_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：compl_ne_eq_singleton (a : α) : {x | x != a}ᶜ = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
lemma compl_ne_eq_singleton (a : α) : {x | x ≠ a}ᶜ = {a} := compl_compl _

@[simp]
/-
**Set.subset_compl_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_compl_singleton_iff : s subseteq {a}ᶜ ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
lemma subset_compl_singleton_iff : s ⊆ {a}ᶜ ↔ a ∉ s := subset_compl_comm.trans singleton_subset_iff

/-! ### Lemmas about set difference -/

/-
**Set.notMem_sdiff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_sdiff_of_mem {s t : Set α} {x : α} (hx : x in t) : x ∉ s \ t
参数：hx : x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
### Lemmas about set difference
-/
theorem notMem_sdiff_of_mem {s t : Set α} {x : α} (hx : x ∈ t) : x ∉ s \ t := fun h => h.2 hx

@[deprecated (since := "2026-06-03")] alias notMem_diff_of_mem := notMem_sdiff_of_mem
/-
**Set.mem_of_mem_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_of_mem_sdiff {s t : Set α} {x : α} (h : x in s \ t) : x in s
参数：h : x in s \ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mem_of_mem_sdiff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
  h.left

@[deprecated (since := "2026-06-03")] alias mem_of_mem_diff := mem_of_mem_sdiff
/-
**Set.notMem_of_mem_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_of_mem_sdiff {s t : Set α} {x : α} (h : x in s \ t) : x ∉ t
参数：h : x in s \ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem notMem_of_mem_sdiff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
  h.right

@[deprecated (since := "2026-06-03")] alias notMem_of_mem_diff := notMem_of_mem_sdiff
/-
**Set.sdiff_eq_compl_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_eq_compl_inter {s t : Set α} : s \ t = tᶜ inter s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem sdiff_eq_compl_inter {s t : Set α} : s \ t = tᶜ ∩ s := by rw [sdiff_eq, inter_comm]

@[deprecated (since := "2026-06-03")] alias diff_eq_compl_inter := sdiff_eq_compl_inter
/-
**Set.sdiff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_nonempty {s t : Set α} : (s \ t).Nonempty ↔ ¬s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_compl_nonempty_iff`：inter_compl_nonempty_iff {s t : Set α} : (
s inter tᶜ).Nonempty ↔ ¬s subseteq t
-/
theorem sdiff_nonempty {s t : Set α} : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  inter_compl_nonempty_iff

@[deprecated (since := "2026-06-03")] alias diff_nonempty := sdiff_nonempty
/-
**Set.sdiff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_subset {s t : Set α} : s \ t subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem sdiff_subset {s t : Set α} : s \ t ⊆ s := sdiff_le

@[deprecated (since := "2026-06-03")] alias diff_subset := sdiff_subset
/-
**Set.sdiff_subset_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_subset_compl (s t : Set α) : s \ t subseteq tᶜ
参数：s t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
-/
theorem sdiff_subset_compl (s t : Set α) : s \ t ⊆ tᶜ :=
  sdiff_eq_compl_inter ▸ inter_subset_left

@[deprecated (since := "2026-06-03")] alias diff_subset_compl := sdiff_subset_compl
/-
**Set.union_sdiff_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_sdiff_cancel' {s t u : Set α} (h₁ : s subseteq t) (h₂ : t subseteq u
) : t union u \ s = u
参数：h₁ : s subseteq t；h₂ : t subseteq u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_cancel'`：sup_sdiff_cancel' (hab : a <= b) (hbc : b <= c) : b ⊔
 c \ a = c
-/
theorem union_sdiff_cancel' {s t u : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ u \ s = u :=
  sup_sdiff_cancel' h₁ h₂

@[deprecated (since := "2026-06-03")] alias union_diff_cancel' := union_sdiff_cancel'
/-
**Set.union_sdiff_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_sdiff_cancel {s t : Set α} (h : s subseteq t) : s union t \ s = t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_cancel_right`：sup_sdiff_cancel_right (h : a <= b) : a ⊔ b \ a 
= b
-/
theorem union_sdiff_cancel {s t : Set α} (h : s ⊆ t) : s ∪ t \ s = t :=
  sup_sdiff_cancel_right h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel := union_sdiff_cancel
/-
**Set.union_sdiff_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_sdiff_cancel_left {s t : Set α} (h : s inter t subseteq ∅) : (s unio
n t) \ s = t
参数：h : s inter t subseteq ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.sup_sdiff_cancel_left`：∀ {α : Type u_2} [inst : GeneralizedCohe
ytingAlgebra α] {a b : α}, Disjoint a b → (a ⊔ b) \ a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
-/
theorem union_sdiff_cancel_left {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
  Disjoint.sup_sdiff_cancel_left <| disjoint_iff_inf_le.2 h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel_left := union_sdiff_cancel_left
/-
**Set.union_sdiff_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_sdiff_cancel_right {s t : Set α} (h : s inter t subseteq ∅) : (s uni
on t) \ t = s
参数：h : s inter t subseteq ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.sup_sdiff_cancel_right`：∀ {α : Type u_2} [inst : GeneralizedCoh
eytingAlgebra α] {a b : α}, Disjoint a b → (a ⊔ b) \ b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
-/
theorem union_sdiff_cancel_right {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
  Disjoint.sup_sdiff_cancel_right <| disjoint_iff_inf_le.2 h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel_right := union_sdiff_cancel_right

@[simp]
/-
**Set.union_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_sdiff_left {s t : Set α} : (s union t) \ s = t \ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_left_self`：sup_sdiff_left_self : (a ⊔ b) \ a = b \ a
-/
theorem union_sdiff_left {s t : Set α} : (s ∪ t) \ s = t \ s :=
  sup_sdiff_left_self

@[deprecated (since := "2026-06-03")] alias union_diff_left := union_sdiff_left

@[simp]
/-
**Set.union_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_sdiff_right {s t : Set α} : (s union t) \ t = s \ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_right_self`：sup_sdiff_right_self : (a ⊔ b) \ b = a \ b
-/
theorem union_sdiff_right {s t : Set α} : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self

@[deprecated (since := "2026-06-03")] alias union_diff_right := union_sdiff_right
/-
**Set.union_sdiff_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_sdiff_distrib {s t u : Set α} : (s union t) \ u = s \ u union t \ u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff`：sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c
-/
theorem union_sdiff_distrib {s t u : Set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
  sup_sdiff

@[deprecated (since := "2026-06-03")] alias union_diff_distrib := union_sdiff_distrib

@[simp]
/-
**Set.inter_sdiff_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_sdiff_self (a b : Set α) : a inter (b \ a) = ∅
参数：a b : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sdiff_self_right`：inf_sdiff_self_right : x ⊓ y \ x = ⊥
-/
theorem inter_sdiff_self (a b : Set α) : a ∩ (b \ a) = ∅ :=
  inf_sdiff_self_right

@[deprecated (since := "2026-06-03")] alias inter_diff_self := inter_sdiff_self

@[simp]
/-
**Set.inter_union_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_union_sdiff (s t : Set α) : s inter t union s \ t = s
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
-/
theorem inter_union_sdiff (s t : Set α) : s ∩ t ∪ s \ t = s :=
  sup_inf_sdiff s t

@[deprecated (since := "2026-06-03")] alias inter_union_diff := inter_union_sdiff

@[simp]
/-
**Set.sdiff_union_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_union_inter (s t : Set α) : s \ t union s inter t = s
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `sup_inf_sdiff`：sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x
-/
theorem sdiff_union_inter (s t : Set α) : s \ t ∪ s ∩ t = s := by
  rw [union_comm]
  exact sup_inf_sdiff _ _

@[deprecated (since := "2026-06-03")] alias diff_union_inter := sdiff_union_inter

@[simp]
/-
**Set.inter_union_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_union_compl (s t : Set α) : s inter t union s inter tᶜ = s
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
-/
theorem inter_union_compl (s t : Set α) : s ∩ t ∪ s ∩ tᶜ = s :=
  inter_union_sdiff _ _
/-
**Set.subset_inter_union_compl_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_inter_union_compl_left (s t : Set α) : t subseteq s inter t union s
ᶜ
参数：s t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_union_distrib_right`：inter_union_distrib_right (s t u : Set α)
 : s inter t union u = (s union u) inter (t union u)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem subset_inter_union_compl_left (s t : Set α) : t ⊆ s ∩ t ∪ sᶜ := by
  simp [inter_union_distrib_right]
/-
**Set.subset_inter_union_compl_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_inter_union_compl_right (s t : Set α) : s subseteq s inter t union 
tᶜ
参数：s t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_union_distrib_right`：inter_union_distrib_right (s t u : Set α)
 : s inter t union u = (s union u) inter (t union u)
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem subset_inter_union_compl_right (s t : Set α) : s ⊆ s ∩ t ∪ tᶜ := by
  simp [inter_union_distrib_right]
/-
**Set.union_inter_compl_left_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_inter_compl_left_subset (s t : Set α) : (s union t) inter sᶜ subsete
q t
参数：s t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
-/
theorem union_inter_compl_left_subset (s t : Set α) : (s ∪ t) ∩ sᶜ ⊆ t := by
  simp [union_inter_distrib_right]
/-
**Set.union_inter_compl_right_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_inter_compl_right_subset (s t : Set α) : (s union t) inter tᶜ subset
eq s
参数：s t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
-/
theorem union_inter_compl_right_subset (s t : Set α) : (s ∪ t) ∩ tᶜ ⊆ s := by
  simp [union_inter_distrib_right]
/-
**Set.sdiff_subset_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ subseteq s₂ -> t₂ subseteq t
₁ -> s₁ \ t₁ subseteq s₂ \ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
-/
theorem sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
  sdiff_le_sdiff

@[deprecated (since := "2026-06-03")] alias diff_subset_diff := sdiff_subset_sdiff
/-
**Set.sdiff_subset_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (h : s₁ subseteq s₂) : s₁ \ t su
bseteq s₂ \ t
参数：h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t := by
  gcongr

@[deprecated (since := "2026-06-03")] alias diff_subset_diff_left := sdiff_subset_sdiff_left
/-
**Set.sdiff_subset_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_subset_sdiff_right {s t u : Set α} (h : t subseteq u) : s \ u subset
eq s \ t
参数：h : t subseteq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem sdiff_subset_sdiff_right {s t u : Set α} (h : t ⊆ u) : s \ u ⊆ s \ t := by
  gcongr

@[deprecated (since := "2026-06-03")] alias diff_subset_diff_right := sdiff_subset_sdiff_right
/-
**Set.sdiff_subset_sdiff_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_subset_sdiff_iff_subset {r : Set α} (hs : s subseteq r) (ht : t subs
eteq r) : r \ s subseteq r \ t ↔ t subseteq s
参数：hs : s subseteq r；ht : t subseteq r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le_sdiff_iff_le`：sdiff_le_sdiff_iff_le (hx : x <= z) (hy : y <= z)
 : z \ x <= z \ y ↔ y <= x
-/
theorem sdiff_subset_sdiff_iff_subset {r : Set α} (hs : s ⊆ r) (ht : t ⊆ r) :
    r \ s ⊆ r \ t ↔ t ⊆ s :=
  sdiff_le_sdiff_iff_le hs ht

@[deprecated (since := "2026-06-03")]
alias diff_subset_diff_iff_subset := sdiff_subset_sdiff_iff_subset
/-
**Set.compl_eq_univ_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_sdiff`：top_sdiff : ⊤ \ x = xᶜ
-/
theorem compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s :=
  top_sdiff.symm

@[deprecated (since := "2026-06-03")] alias compl_eq_univ_diff := compl_eq_univ_sdiff

@[simp]
/-
**Set.empty_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, ⊥ \ a = ⊥
-/
theorem empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅ :=
  bot_sdiff

@[deprecated (since := "2026-06-03")] alias empty_diff := empty_sdiff
/-
**Set.sdiff_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_eq_bot_iff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α
] {a b : α}, b \ a = ⊥ ↔ b ≤ a
-/
theorem sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff

@[deprecated (since := "2026-06-03")] alias diff_eq_empty := sdiff_eq_empty

@[simp]
/-
**Set.sdiff_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_empty {s : Set α} : s \ ∅ = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
-/
theorem sdiff_empty {s : Set α} : s \ ∅ = s :=
  sdiff_bot

@[deprecated (since := "2026-06-03")] alias diff_empty := sdiff_empty

@[simp]
/-
**Set.sdiff_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_univ (s : Set α) : s \ univ = ∅
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem sdiff_univ (s : Set α) : s \ univ = ∅ :=
  sdiff_eq_empty.2 (subset_univ s)

@[deprecated (since := "2026-06-03")] alias diff_univ := sdiff_univ
/-
**Set.sdiff_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t union u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_left`：sdiff_sdiff_left : (a \ b) \ c = a \ (b ⊔ c)
-/
theorem sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t ∪ u) :=
  sdiff_sdiff_left

@[deprecated (since := "2026-06-03")] alias diff_diff := sdiff_sdiff

-- the following statement contains parentheses to help the reader
/-
**Set.sdiff_sdiff_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_sdiff_comm {s t u : Set α} : (s \ t) \ u = (s \ u) \ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_comm`：sdiff_sdiff_comm : (a \ b) \ c = (a \ c) \ b
-/
theorem sdiff_sdiff_comm {s t u : Set α} : (s \ t) \ u = (s \ u) \ t :=
  _root_.sdiff_sdiff_comm

@[deprecated (since := "2026-06-03")] alias diff_diff_comm := sdiff_sdiff_comm

@[simp]
/-
**Set.sdiff_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_subset_iff {s t u : Set α} : s \ t subseteq u ↔ s subseteq t union u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le_iff`：sdiff_le_iff [GeneralizedCoheytingAlgebra α] {a b c : α} :
 a \ b <= c ↔ a <= b ⊔ c
-/
theorem sdiff_subset_iff {s t u : Set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
  sdiff_le_iff

@[deprecated (since := "2026-06-03")] alias diff_subset_iff := sdiff_subset_iff
/-
**Set.subset_sdiff_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_sdiff_union (s t : Set α) : s subseteq s \ t union t
参数：s t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sdiff_sup`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a
 b : α}, b ≤ b \ a ⊔ a
-/
theorem subset_sdiff_union (s t : Set α) : s ⊆ s \ t ∪ t :=
  le_sdiff_sup

@[deprecated (since := "2026-06-03")] alias subset_diff_union := subset_sdiff_union
/-
**Set.sdiff_union_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_union_of_subset {s t : Set α} (h : t subseteq s) : s \ t union t = s
参数：h : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.subset_sdiff_union`：subset_sdiff_union (s t : Set α) : s subseteq s 
\ t union t
-/
theorem sdiff_union_of_subset {s t : Set α} (h : t ⊆ s) : s \ t ∪ t = s :=
  Subset.antisymm (union_subset sdiff_subset h) (subset_sdiff_union _ _)

@[deprecated (since := "2026-06-03")] alias diff_union_of_subset := sdiff_union_of_subset
/-
**Set.sdiff_subset_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_subset_comm {s t u : Set α} : s \ t subseteq u ↔ s \ u subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le_comm`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {
a b c : α}, c \ b ≤ a ↔ c \ a ≤ b
-/
theorem sdiff_subset_comm {s t u : Set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
  sdiff_le_comm

@[deprecated (since := "2026-06-03")] alias diff_subset_comm := sdiff_subset_comm
/-
**Set.sdiff_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_inter {s t u : Set α} : s \ (t inter u) = s \ t union s \ u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_inf`：sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c
-/
theorem sdiff_inter {s t u : Set α} : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf

@[deprecated (since := "2026-06-03")] alias diff_inter := sdiff_inter
/-
**Set.sdiff_inter_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_inter_sdiff : s \ t inter (s \ u) = s \ (t union u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_sup`：sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z
-/
theorem sdiff_inter_sdiff : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
  sdiff_sup.symm

@[deprecated (since := "2026-06-03")] alias diff_inter_diff := sdiff_inter_sdiff
/-
**Set.sdiff_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_compl : s \ tᶜ = s inter t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_compl`：sdiff_compl : x \ yᶜ = x ⊓ y
-/
theorem sdiff_compl : s \ tᶜ = s ∩ t :=
  _root_.sdiff_compl

@[deprecated (since := "2026-06-03")] alias diff_compl := sdiff_compl
/-
**Set.compl_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_sdiff : (t \ s)ᶜ = s union tᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `compl_sdiff`：compl_sdiff : (x \ y)ᶜ = x ⇨ y
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
-/
theorem compl_sdiff : (t \ s)ᶜ = s ∪ tᶜ :=
  Eq.trans _root_.compl_sdiff himp_eq

@[deprecated (since := "2026-06-03")] alias compl_diff := compl_sdiff
/-
**Set.sdiff_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_sdiff_right {s t u : Set α} : s \ (t \ u) = s \ t union s inter u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_right'`：sdiff_sdiff_right' : x \ (y \ z) = x \ y ⊔ x ⊓ z
-/
theorem sdiff_sdiff_right {s t u : Set α} : s \ (t \ u) = s \ t ∪ s ∩ u :=
  sdiff_sdiff_right'

@[deprecated (since := "2026-06-03")] alias diff_diff_right := sdiff_sdiff_right
/-
**Set.inter_sdiff_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_sdiff_right_comm : (s inter t) \ u = s \ u inter t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_right_comm`：inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ 
inter s₃ = s₁ inter s₃ inter s₂
-/
theorem inter_sdiff_right_comm : (s ∩ t) \ u = s \ u ∩ t := by
  rw [sdiff_eq, sdiff_eq, inter_right_comm]

@[deprecated (since := "2026-06-03")] alias diff_inter_right_comm := inter_sdiff_right_comm

@[simp]
/-
**Set.union_sdiff_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_sdiff_self {s t : Set α} : s union t \ s = s union t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), a ⊔ b \ a = a ⊔ b
-/
theorem union_sdiff_self {s t : Set α} : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self _ _

@[deprecated (since := "2026-06-03")] alias union_diff_self := union_sdiff_self

@[simp]
/-
**Set.sdiff_union_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_union_self {s t : Set α} : s \ t union t = s union t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sup_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), b \ a ⊔ a = b ⊔ a
-/
theorem sdiff_union_self {s t : Set α} : s \ t ∪ t = s ∪ t :=
  sdiff_sup_self _ _

@[deprecated (since := "2026-06-03")] alias diff_union_self := sdiff_union_self

@[simp]
/-
**Set.sdiff_inter_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_inter_self {a b : Set α} : b \ a inter a = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sdiff_self_left`：inf_sdiff_self_left : y \ x ⊓ x = ⊥
-/
theorem sdiff_inter_self {a b : Set α} : b \ a ∩ a = ∅ :=
  inf_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias diff_inter_self := sdiff_inter_self

@[simp]
/-
**Set.sdiff_inter_self_eq_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_inter_self_eq_sdiff {s t : Set α} : s \ (t inter s) = s \ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_inf_self_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] (a b : α), b \ (a ⊓ b) = b \ a
-/
theorem sdiff_inter_self_eq_sdiff {s t : Set α} : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right _ _

@[deprecated (since := "2026-06-03")] alias diff_inter_self_eq_diff := sdiff_inter_self_eq_sdiff

@[simp]
/-
**Set.sdiff_self_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_self_inter {s t : Set α} : s \ (s inter t) = s \ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_inf_self_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebr
a α] (a b : α), a \ (a ⊓ b) = a \ b
-/
theorem sdiff_self_inter {s t : Set α} : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left _ _

@[deprecated (since := "2026-06-03")] alias diff_self_inter := sdiff_self_inter
/-
**Set.sdiff_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_self {s : Set α} : s \ s = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
-/
theorem sdiff_self {s : Set α} : s \ s = ∅ :=
  _root_.sdiff_self

@[deprecated (since := "2026-06-03")] alias diff_self := sdiff_self
/-
**Set.sdiff_sdiff_right_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_sdiff_right_self (s t : Set α) : s \ (s \ t) = s inter t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
-/
theorem sdiff_sdiff_right_self (s t : Set α) : s \ (s \ t) = s ∩ t :=
  _root_.sdiff_sdiff_right_self

@[deprecated (since := "2026-06-03")] alias diff_diff_right_self := sdiff_sdiff_right_self
/-
**Set.sdiff_sdiff_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_sdiff_cancel_left {s t : Set α} (h : s subseteq t) : t \ (t \ s) = s
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_eq_self`：sdiff_sdiff_eq_self (h : y <= x) : x \ (x \ y) = y
-/
theorem sdiff_sdiff_cancel_left {s t : Set α} (h : s ⊆ t) : t \ (t \ s) = s :=
  sdiff_sdiff_eq_self h

@[deprecated (since := "2026-06-03")] alias diff_diff_cancel_left := sdiff_sdiff_cancel_left
/-
**Set.union_eq_sdiff_union_sdiff_union_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_eq_sdiff_union_sdiff_union_inter (s t : Set α) : s union t = s \ t u
nion t \ s union s inter t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_sdiff_sup_sdiff_sup_inf`：sup_eq_sdiff_sup_sdiff_sup_inf : x ⊔ y =
 x \ y ⊔ y \ x ⊔ x ⊓ y
-/
theorem union_eq_sdiff_union_sdiff_union_inter (s t : Set α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf

@[deprecated (since := "2026-06-03")]
alias union_eq_diff_union_diff_union_inter := union_eq_sdiff_union_sdiff_union_inter
/-
**Set.sdiff_sep_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (s : Set α) (p : α → Prop), s \ {a | a ∈ s ∧ p a} = {a | 
a ∈ s ∧ ¬p a}
参数：s : Set α；p : α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
-/
@[simp] lemma sdiff_sep_self (s : Set α) (p : α → Prop) : s \ {a ∈ s | p a} = {a ∈ s | ¬ p a} :=
  sdiff_self_inter
/-
**Set.disjoint_sdiff_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_sdiff_left : Disjoint (t \ s) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
-/
lemma disjoint_sdiff_left : Disjoint (t \ s) s := disjoint_sdiff_self_left
/-
**Set.disjoint_sdiff_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_sdiff_right : Disjoint s (t \ s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
-/
lemma disjoint_sdiff_right : Disjoint s (t \ s) := disjoint_sdiff_self_right

-- TODO: prove this in terms of a Boolean algebra lemma
/-
**Set.disjoint_sdiff_inter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_sdiff_inter : Disjoint (s \ t) (s inter t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subseteq u
) (d : Disjoint s u) : Disjoint s t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
-/
lemma disjoint_sdiff_inter : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right inter_subset_right disjoint_sdiff_left
/-
**Set.subset_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjoint s u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_sdiff`：le_sdiff : x <= y \ z ↔ x <= y ∧ Disjoint x z
-/
lemma subset_sdiff : s ⊆ t \ u ↔ s ⊆ t ∧ Disjoint s u := le_sdiff

@[deprecated (since := "2026-06-03")] alias subset_diff := subset_sdiff
/-
**Set.disjoint_of_subset_iff_left_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_of_subset_iff_left_eq_empty (h : s subseteq t) : Disjoint s t ↔ s
 = ∅
参数：h : s subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_of_le_iff_left_eq_bot`：disjoint_of_le_iff_left_eq_bot (h : a <=
 b) : Disjoint a b ↔ a = ⊥
-/
lemma disjoint_of_subset_iff_left_eq_empty (h : s ⊆ t) : Disjoint s t ↔ s = ∅ :=
  disjoint_of_le_iff_left_eq_bot h

@[simp]
/-
**Set.sdiff_ssubset_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiff_ssubset_left_iff : s \ t ⊂ s ↔ (s inter t).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `sdiff_lt_left`：sdiff_lt_left : x \ y < x ↔ ¬ Disjoint y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sdiff_ssubset_left_iff : s \ t ⊂ s ↔ (s ∩ t).Nonempty :=
  sdiff_lt_left.trans <| by rw [not_disjoint_iff_nonempty_inter, inter_comm]

@[deprecated (since := "2026-06-03")] alias diff_ssubset_left_iff := sdiff_ssubset_left_iff
/-
**Set._root_.LE.le.sdiff_ssubset_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LE.le.sdiff_ssubset_of_nonempty (hst : s ⊆ t) (hs : s.Nonempty) :
    t \ s ⊂ t := by
  simpa [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-05")]
alias _root_.HasSubset.Subset.sdiff_ssubset_of_nonempty := LE.le.sdiff_ssubset_of_nonempty

@[deprecated (since := "2026-06-03")]
alias _root_.HasSubset.Subset.diff_ssubset_of_nonempty :=
  _root_.LE.le.sdiff_ssubset_of_nonempty
/-
**Set.ssubset_iff_sdiff_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ssubset_iff_sdiff_singleton : s ⊂ t ↔ exists a in t, s subseteq t \ {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ssubset_iff_sdiff_singleton : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t \ {a} := by
  grind
/-
**Set.sdiff_singleton_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiff_singleton_subset_iff : s \ {a} subseteq t ↔ s subseteq insert a t
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
lemma sdiff_singleton_subset_iff : s \ {a} ⊆ t ↔ s ⊆ insert a t := by
  simp

@[deprecated (since := "2026-06-03")] alias diff_singleton_subset_iff := sdiff_singleton_subset_iff
/-
**Set.subset_sdiff_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_sdiff_singleton (h : s subseteq t) (ha : a ∉ s) : s subseteq t \ {a
}
参数：h : s subseteq t；ha : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
lemma subset_sdiff_singleton (h : s ⊆ t) (ha : a ∉ s) : s ⊆ t \ {a} :=
  subset_inter h <| subset_compl_comm.1 <| singleton_subset_iff.2 ha

@[deprecated (since := "2026-06-03")] alias subset_diff_singleton := subset_sdiff_singleton
/-
**Set.subset_insert_sdiff_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_insert_sdiff_singleton (x : α) (s : Set α) : s subseteq insert x (s
 \ {x})
参数：x : α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.sdiff_singleton_subset_iff`：sdiff_singleton_subset_iff : s \ {a} sub
seteq t ↔ s subseteq insert a t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma subset_insert_sdiff_singleton (x : α) (s : Set α) : s ⊆ insert x (s \ {x}) := by
  rw [← sdiff_singleton_subset_iff]

@[deprecated (since := "2026-06-03")]
alias subset_insert_diff_singleton := subset_insert_sdiff_singleton
/-
**Set.sdiff_insert_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiff_insert_of_notMem (h : a ∉ s) : s \ insert a t = s \ t
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sdiff_insert_of_notMem (h : a ∉ s) : s \ insert a t = s \ t := by
  grind

@[deprecated (since := "2026-06-03")] alias diff_insert_of_notMem := sdiff_insert_of_notMem

@[simp]
/-
**Set.insert_sdiff_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_sdiff_of_mem (s) (h : a in t) : insert a s \ t = s \ t
参数：s；h : a in t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma insert_sdiff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t := by
  grind

@[deprecated (since := "2026-06-03")] alias insert_diff_of_mem := insert_sdiff_of_mem
/-
**Set.insert_sdiff_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_sdiff_of_notMem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t)
参数：s；h : a ∉ t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma insert_sdiff_of_notMem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) := by
  grind

@[deprecated (since := "2026-06-03")] alias insert_diff_of_notMem := insert_sdiff_of_notMem
/-
**Set.insert_sdiff_self_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_sdiff_self_of_notMem (h : a ∉ s) : insert a s \ {a} = s
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma insert_sdiff_self_of_notMem (h : a ∉ s) : insert a s \ {a} = s := by
  ext x; simp [and_iff_left_of_imp (ne_of_mem_of_not_mem · h)]

@[deprecated (since := "2026-06-03")]
alias insert_diff_self_of_notMem := insert_sdiff_self_of_notMem
/-
**Set.insert_sdiff_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s → insert a (s \ {a}) = s
参数：s \ {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma insert_sdiff_self_of_mem (ha : a ∈ s) : insert a (s \ {a}) = s := by
  ext; simp +contextual [or_and_left, em, ha]

@[deprecated (since := "2026-06-03")] alias insert_diff_self_of_mem := insert_sdiff_self_of_mem
/-
**Set.insert_sdiff_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_sdiff_subset : insert a s \ t subseteq insert a (s \ t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma insert_sdiff_subset : insert a s \ t ⊆ insert a (s \ t) := by
  rintro b ⟨rfl | hbs, hbt⟩ <;> simp [*]

@[deprecated (since := "2026-06-03")] alias insert_diff_subset := insert_sdiff_subset
/-
**Set.insert_erase_invOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_erase_invOn : InvOn (insert a) (fun s => s \ {a}) {s : Set α | a in
 s} {s : Set α | a ∉ s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.insert_sdiff_self_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ 
s → insert a (s \ {a}) = s
· 使用引理 `Set.insert_sdiff_self_of_notMem`：insert_sdiff_self_of_notMem (h : a ∉ s)
 : insert a s \ {a} = s
-/
lemma insert_erase_invOn :
    InvOn (insert a) (fun s ↦ s \ {a}) {s : Set α | a ∈ s} {s : Set α | a ∉ s} :=
  ⟨fun _s ha ↦ insert_sdiff_self_of_mem ha, fun _s ↦ insert_sdiff_self_of_notMem⟩

@[simp]
/-
**Set.sdiff_singleton_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiff_singleton_eq_self (h : a ∉ s) : s \ {a} = s
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_eq_self_iff_disjoint`：sdiff_eq_self_iff_disjoint : x \ y = x ↔ Dis
joint y x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma sdiff_singleton_eq_self (h : a ∉ s) : s \ {a} = s :=
  sdiff_eq_self_iff_disjoint.2 <| by simp [h]

@[deprecated (since := "2026-06-03")] alias diff_singleton_eq_self := sdiff_singleton_eq_self
/-
**Set.sdiff_singleton_ssubset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiff_singleton_ssubset : s \ {a} ⊂ s ↔ a in s
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
lemma sdiff_singleton_ssubset : s \ {a} ⊂ s ↔ a ∈ s := by simp

@[deprecated (since := "2026-06-03")] alias diff_singleton_ssubset := sdiff_singleton_ssubset

@[simp]
/-
**Set.insert_sdiff_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_sdiff_singleton : insert a (s \ {a}) = insert a s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma insert_sdiff_singleton : insert a (s \ {a}) = insert a s := by
  simp [insert_eq, union_sdiff_self, -union_singleton, -singleton_union]

@[deprecated (since := "2026-06-03")] alias insert_diff_singleton := insert_sdiff_singleton
/-
**Set.insert_sdiff_singleton_comm** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_sdiff_singleton_comm (hab : a != b) (s : Set α) : insert a (s \ {b}
) = insert a s \ {b}
参数：hab : a != b；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_sdiff_distrib`：union_sdiff_distrib {s t u : Set α} : (s union 
t) \ u = s \ u union t \ u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma insert_sdiff_singleton_comm (hab : a ≠ b) (s : Set α) :
    insert a (s \ {b}) = insert a s \ {b} := by
  simp_rw [← union_singleton, union_sdiff_distrib,
    sdiff_singleton_eq_self (mem_singleton_iff.not.2 hab.symm)]

@[deprecated (since := "2026-06-03")]
alias insert_diff_singleton_comm := insert_sdiff_singleton_comm

@[simp]
/-
**Set.insert_sdiff_insert** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_sdiff_insert : insert a (s \ insert a t) = insert a (s \ t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.sdiff_sdiff`：sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t union u)
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
-/
lemma insert_sdiff_insert : insert a (s \ insert a t) = insert a (s \ t) := by
  rw [← union_singleton (s := t), ← sdiff_sdiff, insert_sdiff_singleton]

@[deprecated (since := "2026-06-03")] alias insert_diff_insert := insert_sdiff_insert
/-
**Set.mem_sdiff_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_sdiff_singleton : a in s \ {b} ↔ a in s ∧ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_sdiff_singleton : a ∈ s \ {b} ↔ a ∈ s ∧ a ≠ b := .rfl

@[deprecated (since := "2026-06-03")] alias mem_diff_singleton := mem_sdiff_singleton
/-
**Set.mem_sdiff_singleton_empty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_sdiff_singleton_empty {t : Set (Set α)} : s in t \ {∅} ↔ s in t ∧ s.No
nempty
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Set.mem_sdiff_singleton`：mem_sdiff_singleton : a in s \ {b} ↔ a in s ∧ a
 != b
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
lemma mem_sdiff_singleton_empty {t : Set (Set α)} : s ∈ t \ {∅} ↔ s ∈ t ∧ s.Nonempty :=
  mem_sdiff_singleton.trans <| and_congr_right' nonempty_iff_ne_empty.symm

@[deprecated (since := "2026-06-03")] alias mem_diff_singleton_empty := mem_sdiff_singleton_empty
/-
**Set.subset_insert_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_insert_iff : s subseteq insert a t ↔ s subseteq t ∨ (a in s ∧ s \ {
a} subseteq t)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subset_insert_iff : s ⊆ insert a t ↔ s ⊆ t ∨ (a ∈ s ∧ s \ {a} ⊆ t) := by
  grind
/-
**Set.pair_sdiff_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：pair_sdiff_left (hab : a != b) : ({a, b} : Set α) \ {a} = {b}
参数：hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
-/
lemma pair_sdiff_left (hab : a ≠ b) : ({a, b} : Set α) \ {a} = {b} := by
  rw [insert_sdiff_of_mem _ (mem_singleton a), sdiff_singleton_eq_self (by simpa)]

@[deprecated (since := "2026-06-03")] alias pair_diff_left := pair_sdiff_left
/-
**Set.pair_sdiff_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：pair_sdiff_right (hab : a != b) : ({a, b} : Set α) \ {b} = {a}
参数：hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用引理 `Set.pair_sdiff_left`：pair_sdiff_left (hab : a != b) : ({a, b} : Set α) \
 {a} = {b}
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma pair_sdiff_right (hab : a ≠ b) : ({a, b} : Set α) \ {b} = {a} := by
  rw [pair_comm, pair_sdiff_left hab.symm]

@[deprecated (since := "2026-06-03")] alias pair_diff_right := pair_sdiff_right

/-! ### If-then-else for sets -/

/-- `ite` for sets: `Set.ite t s s' ∩ t = s ∩ t`, `Set.ite t s s' ∩ tᶜ = s' ∩ tᶜ`.
Defined as `s ∩ t ∪ s' \ t`. -/
/-
**Set.ite** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → Set α → Set α → Set α → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ite` for sets: `Set.ite t s s' ∩ t = s ∩ t`, `Set.ite t s s' ∩ tᶜ = s' ∩ tᶜ`.
Defined as `s ∩ t ∪ s' \ t`.
-/
protected def ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t

@[simp]
/-
**Set.ite_inter_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_inter_self (t s s' : Set α) : t.ite s s' inter t = s inter t
参数：t s s' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ite.eq_1`：∀ {α : Type u_1} (t s s' : Set α), t.ite s s' = s ∩ t ∪ s'
 \ t
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.sdiff_inter_self`：sdiff_inter_self {a b : Set α} : b \ a inter a = ∅
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
-/
theorem ite_inter_self (t s s' : Set α) : t.ite s s' ∩ t = s ∩ t := by
  rw [Set.ite, union_inter_distrib_right, sdiff_inter_self, inter_assoc, inter_self, union_empty]

@[simp]
/-
**Set.ite_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s
参数：t s s' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ite.eq_1`：∀ {α : Type u_1} (t s s' : Set α), t.ite s s' = s ∩ t ∪ s'
 \ t
· 使用定理 `Set.sdiff_compl`：sdiff_compl : s \ tᶜ = s inter t
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
-/
theorem ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s := by
  rw [Set.ite, Set.ite, sdiff_compl, union_comm, sdiff_eq]

@[simp]
/-
**Set.ite_inter_compl_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_inter_compl_self (t s s' : Set α) : t.ite s s' inter tᶜ = s' inter tᶜ
参数：t s s' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ite_compl`：ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s
· 使用定理 `Set.ite_inter_self`：ite_inter_self (t s s' : Set α) : t.ite s s' inter t
 = s inter t
-/
theorem ite_inter_compl_self (t s s' : Set α) : t.ite s s' ∩ tᶜ = s' ∩ tᶜ := by
  rw [← ite_compl, ite_inter_self]

@[simp]
/-
**Set.ite_sdiff_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_sdiff_self (t s s' : Set α) : t.ite s s' \ t = s' \ t
参数：t s s' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ite_inter_compl_self`：ite_inter_compl_self (t s s' : Set α) : t.ite 
s s' inter tᶜ = s' inter tᶜ
-/
theorem ite_sdiff_self (t s s' : Set α) : t.ite s s' \ t = s' \ t :=
  ite_inter_compl_self t s s'

@[deprecated (since := "2026-06-03")] alias ite_diff_self := ite_sdiff_self

@[simp]
/-
**Set.ite_same** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_same (t s : Set α) : t.ite s s = s
参数：t s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
-/
theorem ite_same (t s : Set α) : t.ite s s = s :=
  inter_union_sdiff _ _

@[simp]
/-
**Set.ite_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_left (s t : Set α) : s.ite s t = s union t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ite_left (s t : Set α) : s.ite s t = s ∪ t := by simp [Set.ite]

@[simp]
/-
**Set.ite_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_right (s t : Set α) : s.ite t s = t inter s
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ite_right (s t : Set α) : s.ite t s = t ∩ s := by simp [Set.ite]

@[simp]
/-
**Set.ite_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_empty (s s' : Set α) : Set.ite ∅ s s' = s'
参数：s s' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ite_empty (s s' : Set α) : Set.ite ∅ s s' = s' := by simp [Set.ite]

@[simp]
/-
**Set.ite_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_univ (s s' : Set α) : Set.ite univ s s' = s
参数：s s' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.sdiff_univ`：sdiff_univ (s : Set α) : s \ univ = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ite_univ (s s' : Set α) : Set.ite univ s s' = s := by simp [Set.ite]

@[simp]
/-
**Set.ite_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_empty_left (t s : Set α) : t.ite ∅ s = s \ t
参数：t s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ite_empty_left (t s : Set α) : t.ite ∅ s = s \ t := by simp [Set.ite]

@[simp]
/-
**Set.ite_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_empty_right (t s : Set α) : t.ite s ∅ = s inter t
参数：t s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_sdiff`：empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ite_empty_right (t s : Set α) : t.ite s ∅ = s ∩ t := by simp [Set.ite]
/-
**Set.ite_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ subseteq s₂) (h' : s₁
' subseteq s₂') : t.ite s₁ s₁' subseteq t.ite s₂ s₂'
参数：t : Set α；h : s₁ subseteq s₂；h' : s₁' subseteq s₂'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
-/
theorem ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ ⊆ s₂) (h' : s₁' ⊆ s₂') :
    t.ite s₁ s₁' ⊆ t.ite s₂ s₂' :=
  union_subset_union (inter_subset_inter_left _ h) (sdiff_subset_sdiff_left h')
/-
**Set.ite_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_subset_union (t s s' : Set α) : t.ite s s' subseteq s union s'
参数：t s s' : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
theorem ite_subset_union (t s s' : Set α) : t.ite s s' ⊆ s ∪ s' :=
  union_subset_union inter_subset_left sdiff_subset
/-
**Set.inter_subset_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_subset_ite (t s s' : Set α) : s inter s' subseteq t.ite s s'
参数：t s s' : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ite_mono`：ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ subse
teq s₂) (h' : s₁' subseteq s₂') : t.ite s₁ s₁' subseteq t.ite s₂ s₂'
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.ite_same`：ite_same (t s : Set α) : t.ite s s = s
-/
theorem inter_subset_ite (t s s' : Set α) : s ∩ s' ⊆ t.ite s s' :=
  ite_same t (s ∩ s') ▸ ite_mono _ inter_subset_left inter_subset_right
/-
**Set.ite_inter_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_inter_inter (t s₁ s₂ s₁' s₂' : Set α) : t.ite (s₁ inter s₂) (s₁' inter
 s₂') = t.ite s₁ s₁' inter t.ite s₂ s₂'
参数：t s₁ s₂ s₁' s₂' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
theorem ite_inter_inter (t s₁ s₂ s₁' s₂' : Set α) :
    t.ite (s₁ ∩ s₂) (s₁' ∩ s₂') = t.ite s₁ s₁' ∩ t.ite s₂ s₂' := by
  ext x
  unfold Set.ite
  push _ ∈ _
  tauto
/-
**Set.ite_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_inter (t s₁ s₂ s : Set α) : t.ite (s₁ inter s) (s₂ inter s) = t.ite s₁
 s₂ inter s
参数：t s₁ s₂ s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ite_inter_inter`：ite_inter_inter (t s₁ s₂ s₁' s₂' : Set α) : t.ite (
s₁ inter s₂) (s₁' inter s₂') = t.ite s₁ s₁' inter t.ite s₂ s₂'
· 使用定理 `Set.ite_same`：ite_same (t s : Set α) : t.ite s s = s
-/
theorem ite_inter (t s₁ s₂ s : Set α) : t.ite (s₁ ∩ s) (s₂ ∩ s) = t.ite s₁ s₂ ∩ s := by
  rw [ite_inter_inter, ite_same]
/-
**Set.ite_inter_of_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : Set α} (h : s₁ inter s = s₂ i
nter s) : t.ite s₁ s₂ inter s = s₁ inter s
参数：t : Set α；h : s₁ inter s = s₂ inter s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ite_inter`：ite_inter (t s₁ s₂ s : Set α) : t.ite (s₁ inter s) (s₂ in
ter s) = t.ite s₁ s₂ inter s
· 使用定理 `Set.ite_same`：ite_same (t s : Set α) : t.ite s s = s
-/
theorem ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : Set α} (h : s₁ ∩ s = s₂ ∩ s) :
    t.ite s₁ s₂ ∩ s = s₁ ∩ s := by rw [← ite_inter, ← h, ite_same]
/-
**Set.subset_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_ite {t s s' u : Set α} : u subseteq t.ite s s' ↔ u inter t subseteq
 s ∧ u \ t subseteq s'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem subset_ite {t s s' u : Set α} : u ⊆ t.ite s s' ↔ u ∩ t ⊆ s ∧ u \ t ⊆ s' := by
  simp only [subset_def, ← forall_and]
  refine forall_congr' fun x => ?_
  by_cases hx : x ∈ t <;> simp [*, Set.ite]
/-
**Set.ite_eq_of_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_eq_of_subset_left (t : Set α) {s₁ s₂ : Set α} (h : s₁ subseteq s₂) : t
.ite s₁ s₂ = s₁ union (s₂ \ t)
参数：t : Set α；h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `or_iff_right_of_imp`：∀ {a b : Prop}, (a → b) → (a ∨ b ↔ b)
-/
theorem ite_eq_of_subset_left (t : Set α) {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) :
    t.ite s₁ s₂ = s₁ ∪ (s₂ \ t) := by
  ext x
  by_cases hx : x ∈ t <;> simp [*, Set.ite, or_iff_right_of_imp (@h x)]
/-
**Set.ite_eq_of_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ite_eq_of_subset_right (t : Set α) {s₁ s₂ : Set α} (h : s₂ subseteq s₁) : 
t.ite s₁ s₂ = (s₁ inter t) union s₂
参数：t : Set α；h : s₂ subseteq s₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_iff_left_of_imp`：∀ {b a : Prop}, (b → a) → (a ∨ b ↔ a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem ite_eq_of_subset_right (t : Set α) {s₁ s₂ : Set α} (h : s₂ ⊆ s₁) :
    t.ite s₁ s₂ = (s₁ ∩ t) ∪ s₂ := by
  ext x
  by_cases hx : x ∈ t <;> simp [*, Set.ite, or_iff_left_of_imp (@h x)]

end Set

