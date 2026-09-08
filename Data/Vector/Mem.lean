/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.Vector.Basic

/-!
# Theorems about membership of elements in vectors

This file contains theorems for membership in a `v.toList` for a vector `v`.
Having the length available in the type allows some of the lemmas to be
  simpler and more general than the original version for lists.
In particular we can avoid some assumptions about types being `Inhabited`,
  and make more general statements about `head` and `tail`.
-/

public section

namespace List

namespace Vector

variable {α β : Type*} {n : ℕ} (a a' : α)

@[simp]
/-
**List.Vector.get_mem** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_mem (i : Fin n) (v : Vector α n) : v.get i in v.toList
参数：i : Fin n；v : Vector α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
-/
theorem get_mem (i : Fin n) (v : Vector α n) : v.get i ∈ v.toList := List.get_mem _ _
/-
**List.Vector.mem_iff_get** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mem_iff_get (v : Vector α n) : a in v.toList ↔ exists i, v.get i = a
参数：v : Vector α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem mem_iff_get (v : Vector α n) : a ∈ v.toList ↔ ∃ i, v.get i = a := by
  simp only [List.mem_iff_get, Fin.exists_iff, Vector.get_eq_get_toList]
  exact
    ⟨fun ⟨i, hi, h⟩ => ⟨i, by rwa [toList_length] at hi, h⟩, fun ⟨i, hi, h⟩ =>
      ⟨i, by rwa [toList_length], h⟩⟩
/-
**List.Vector.notMem_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：notMem_nil : a ∉ (Vector.nil : Vector α 0).toList
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.toList_empty`：toList_empty (v : Vector α 0) : v.toList = []
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem notMem_nil : a ∉ (Vector.nil : Vector α 0).toList := by
  simp
/-
**List.Vector.notMem_zero** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：notMem_zero (v : Vector α 0) : a ∉ v.toList
参数：v : Vector α 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.notMem_nil`：notMem_nil : a ∉ (Vector.nil : Vector α 0).toLis
t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.eq_nil`：∀ {α : Type u_1} (v : List.Vector α 0), v = List.Vec
tor.nil
-/
theorem notMem_zero (v : Vector α 0) : a ∉ v.toList :=
  (Vector.eq_nil v).symm ▸ notMem_nil a
/-
**List.Vector.mem_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mem_cons_iff (v : Vector α n) : a' in (a ::ᵥ v).toList ↔ a' = a ∨ a' in v.
toList
参数：v : Vector α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.toList_cons`：toList_cons (a : α) (v : Vector α n) : toList (
cons a v) = a :: toList v
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cons_iff (v : Vector α n) : a' ∈ (a ::ᵥ v).toList ↔ a' = a ∨ a' ∈ v.toList := by
  rw [Vector.toList_cons, List.mem_cons]

set_option backward.isDefEq.respectTransparency false in
/-
**List.Vector.mem_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mem_succ_iff (v : Vector α (n + 1)) : a in v.toList ↔ a = v.head ∨ a in v.
tail.toList
参数：v : Vector α (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.exists_eq_cons`：exists_eq_cons (v : Vector α n.succ) : exist
s (a : α) (as : Vector α n), v = a ::ᵥ as
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.head_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).head = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.Vector.tail_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).tail = v
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_succ_iff (v : Vector α (n + 1)) : a ∈ v.toList ↔ a = v.head ∨ a ∈ v.tail.toList := by
  obtain ⟨a', v', h⟩ := exists_eq_cons v
  simp_rw [h, Vector.mem_cons_iff, Vector.head_cons, Vector.tail_cons]
/-
**List.Vector.mem_cons_self** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mem_cons_self (v : Vector α n) : a in (a ::ᵥ v).toList
参数：v : Vector α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Vector.mem_iff_get`：mem_iff_get (v : Vector α n) : a in v.toList ↔ 
exists i, v.get i = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `List.Vector.get_cons_zero`：get_cons_zero (a : α) (v : Vector α n) : get 
(a ::ᵥ v) 0 = a
-/
theorem mem_cons_self (v : Vector α n) : a ∈ (a ::ᵥ v).toList :=
  (Vector.mem_iff_get a (a ::ᵥ v)).2 ⟨0, Vector.get_cons_zero a v⟩

@[simp]
/-
**List.Vector.head_mem** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：head_mem (v : Vector α (n + 1)) : v.head in v.toList
参数：v : Vector α (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Vector.mem_iff_get`：mem_iff_get (v : Vector α n) : a in v.toList ↔ 
exists i, v.get i = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `List.Vector.get_zero`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n.succ
), v.get 0 = v.head
-/
theorem head_mem (v : Vector α (n + 1)) : v.head ∈ v.toList :=
  (Vector.mem_iff_get v.head v).2 ⟨0, Vector.get_zero v⟩
/-
**List.Vector.mem_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mem_cons_of_mem (v : Vector α n) (ha' : a' in v.toList) : a' in (a ::ᵥ v).
toList
参数：v : Vector α n；ha' : a' in v.toList。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Vector.mem_cons_iff`：mem_cons_iff (v : Vector α n) : a' in (a ::ᵥ v
).toList ↔ a' = a ∨ a' in v.toList
-/
theorem mem_cons_of_mem (v : Vector α n) (ha' : a' ∈ v.toList) : a' ∈ (a ::ᵥ v).toList :=
  (Vector.mem_cons_iff a a' v).2 (Or.inr ha')
/-
**List.Vector.mem_of_mem_tail** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mem_of_mem_tail (v : Vector α n) (ha : a in v.tail.toList) : a in v.toList
参数：v : Vector α n；ha : a in v.tail.toList。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.notMem_zero`：notMem_zero (v : Vector α 0) : a ∉ v.toList
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Vector.mem_succ_iff`：mem_succ_iff (v : Vector α (n + 1)) : a in v.t
oList ↔ a = v.head ∨ a in v.tail.toList
-/
theorem mem_of_mem_tail (v : Vector α n) (ha : a ∈ v.tail.toList) : a ∈ v.toList := by
  induction n with
  | zero => exact False.elim (Vector.notMem_zero a v.tail ha)
  | succ n _ => exact (mem_succ_iff a v).2 (Or.inr ha)
/-
**List.Vector.mem_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mem_map_iff (b : β) (v : Vector α n) (f : α -> β) : b in (v.map f).toList 
↔ exists a : α, a in v.toList ∧ f a = b
参数：b : β；v : Vector α n；f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.toList_map`：toList_map {β : Type*} (v : Vector α n) (f : α -
> β) : (v.map f).toList = v.toList.map f
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map_iff (b : β) (v : Vector α n) (f : α → β) :
    b ∈ (v.map f).toList ↔ ∃ a : α, a ∈ v.toList ∧ f a = b := by
  rw [Vector.toList_map, List.mem_map]
/-
**List.Vector.notMem_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：notMem_map_zero (b : β) (v : Vector α 0) (f : α -> β) : b ∉ (v.map f).toLi
st
参数：b : β；v : Vector α 0；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.eq_nil`：∀ {α : Type u_1} (v : List.Vector α 0), v = List.Vec
tor.nil
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
-/
theorem notMem_map_zero (b : β) (v : Vector α 0) (f : α → β) : b ∉ (v.map f).toList := by
  simpa only [Vector.eq_nil v, Vector.map_nil, Vector.toList_nil] using List.not_mem_nil
/-
**List.Vector.mem_map_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mem_map_succ_iff (b : β) (v : Vector α (n + 1)) (f : α -> β) : b in (v.map
 f).toList ↔ f v.head = b ∨ exists a : α, a in v.tail.toList ∧ f a = b
参数：b : β；v : Vector α (n + 1)；f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.mem_succ_iff`：mem_succ_iff (v : Vector α (n + 1)) : a in v.t
oList ↔ a = v.head ∨ a in v.tail.toList
· 使用定理 `List.Vector.head_map`：head_map {β : Type*} (v : Vector α (n + 1)) (f : α
 -> β) : (v.map f).head = f v.head
· 使用定理 `List.Vector.tail_map`：tail_map {β : Type*} (v : Vector α (n + 1)) (f : α
 -> β) : (v.map f).tail = v.tail.map f
· 使用定理 `List.Vector.mem_map_iff`：mem_map_iff (b : β) (v : Vector α n) (f : α -> 
β) : b in (v.map f).toList ↔ exists a : α, a in v.toList ∧ f a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map_succ_iff (b : β) (v : Vector α (n + 1)) (f : α → β) :
    b ∈ (v.map f).toList ↔ f v.head = b ∨ ∃ a : α, a ∈ v.tail.toList ∧ f a = b := by
  rw [mem_succ_iff, head_map, tail_map, mem_map_iff, @eq_comm _ b]

end Vector

end List

