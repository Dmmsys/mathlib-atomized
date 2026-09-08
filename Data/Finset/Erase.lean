/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.Filter

/-!
# Erasing an element from a finite set

## Main declarations

* `Finset.erase`: For any `a : α`, `erase s a` returns `s` with the element `a` removed.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### erase -/

section Erase

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
/-
**Finset.erase** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：erase (s : Finset α) (a : α) : Finset α
参数：s : Finset α；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`.
-/
def erase (s : Finset α) (a : α) : Finset α :=
  ⟨_, s.2.erase a⟩

@[simp]
/-
**Finset.erase_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_val (s : Finset α) (a : α) : (erase s a).1 = s.1.erase a
参数：s : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_val (s : Finset α) (a : α) : (erase s a).1 = s.1.erase a :=
  rfl

@[simp, grind =]
/-
**Finset.mem_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ a != b ∧ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.mem_erase_iff`：∀ {α : Type u_1} [inst : DecidableEq α] {a
 b : α} {l : Multiset α}, l.Nodup → (a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l)
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem mem_erase {a b : α} {s : Finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
  s.2.mem_erase_iff
/-
**Finset.notMem_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
参数：a : α；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.notMem_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {a 
: α} {s : Multiset α}, s.Nodup → a ∉ s.erase a
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem notMem_erase (a : α) (s : Finset α) : a ∉ erase s a :=
  s.2.notMem_erase
/-
**Finset.ne_of_mem_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ne_of_mem_erase : b in erase s a -> b != a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
-/
theorem ne_of_mem_erase : b ∈ erase s a → b ≠ a := fun h => (mem_erase.1 h).1
/-
**Finset.mem_of_mem_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_of_mem_erase : b in erase s a -> b in s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_of_mem_erase`：mem_of_mem_erase {a b : α} {s : Multiset α} :
 a in s.erase b -> a in s
-/
theorem mem_of_mem_erase : b ∈ erase s a → b ∈ s :=
  Multiset.mem_of_mem_erase
/-
**Finset.mem_erase_of_ne_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_erase_of_ne_of_mem : a != b -> a in s -> a in erase s b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem mem_erase_of_ne_of_mem : a ≠ b → a ∈ s → a ∈ erase s b := by
  simp only [mem_erase]; exact And.intro

/-- An element of `s` that is not an element of `erase s a` must be `a`. -/
/-
**Finset.eq_of_mem_of_notMem_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_of_mem_of_notMem_erase (hs : b in s) (hsa : b ∉ s.erase a) : b = a
参数：hs : b in s；hsa : b ∉ s.erase a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of `s` that is not an element of `erase s a` must be `a`.
-/
theorem eq_of_mem_of_notMem_erase (hs : b ∈ s) (hsa : b ∉ s.erase a) : b = a := by grind

@[simp]
/-
**Finset.erase_eq_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_eq_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : erase s a = s
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.erase_of_notMem`：erase_of_notMem {a : α} {s : Multiset α} : a ∉
 s -> s.erase a = s
-/
theorem erase_eq_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : erase s a = s :=
  eq_of_veq <| erase_of_notMem h

@[simp]
/-
**Finset.erase_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_eq_self : s.erase a = s ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
-/
theorem erase_eq_self : s.erase a = s ↔ a ∉ s :=
  ⟨fun h => h ▸ notMem_erase _ _, erase_eq_of_notMem⟩
/-
**Finset.erase_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_ne_self : s.erase a != s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `Finset.erase_eq_self`：erase_eq_self : s.erase a = s ↔ a ∉ s
-/
theorem erase_ne_self : s.erase a ≠ s ↔ a ∈ s :=
  erase_eq_self.not_left

@[gcongr]
/-
**Finset.erase_subset_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_subset_erase (a : α) {s t : Finset α} (h : s subseteq t) : erase s a
 subseteq erase t a
参数：a : α；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.val_le_iff`：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ sub
seteq s₂
· 使用定理 `Multiset.erase_le_erase`：erase_le_erase {s t : Multiset α} (a : α) (h : 
s <= t) : s.erase a <= t.erase a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem erase_subset_erase (a : α) {s t : Finset α} (h : s ⊆ t) : erase s a ⊆ erase t a :=
  val_le_iff.1 <| erase_le_erase _ <| val_le_iff.2 h
/-
**Finset.erase_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_subset (a : α) (s : Finset α) : erase s a subseteq s
参数：a : α；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.erase_subset`：erase_subset (a : α) (s : Multiset α) : s.erase a
 subseteq s
-/
theorem erase_subset (a : α) (s : Finset α) : erase s a ⊆ s :=
  Multiset.erase_subset _ _
/-
**Finset.subset_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_erase {a : α} {s t : Finset α} : s subseteq t.erase a ↔ s subseteq 
t ∧ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_erase {a : α} {s t : Finset α} : s ⊆ t.erase a ↔ s ⊆ t ∧ a ∉ s := by grind

@[simp, norm_cast]
/-
**Finset.coe_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \ {a} : Set α)
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \ {a} : Set α) := by grind
/-
**Finset.erase_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_idem {a : α} {s : Finset α} : erase (erase s a) a = erase s a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem erase_idem {a : α} {s : Finset α} : erase (erase s a) a = erase s a := by simp
/-
**Finset.erase_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_right_comm {a b : α} {s : Finset α} : erase (erase s a) b = erase (e
rase s b) a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_right_comm {a b : α} {s : Finset α} : erase (erase s a) b = erase (erase s b) a := by
  grind
/-
**Finset.erase_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_inj {x y : α} (s : Finset α) (hx : x in s) : s.erase x = s.erase y ↔
 x = y
参数：s : Finset α；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_inj {x y : α} (s : Finset α) (hx : x ∈ s) : s.erase x = s.erase y ↔ x = y := by
  grind [eq_of_mem_of_notMem_erase]
/-
**Finset.erase_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_injOn (s : Finset α) : Set.InjOn s.erase s
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.erase_inj`：erase_inj {x y : α} (s : Finset α) (hx : x in s) : s.e
rase x = s.erase y ↔ x = y
-/
theorem erase_injOn (s : Finset α) : Set.InjOn s.erase s := fun _ _ _ _ => (erase_inj s ‹_›).mp

end Erase

end Finset

