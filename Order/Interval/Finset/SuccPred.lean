/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.SuccPred

/-!
# Finset intervals in a successor-predecessor order

This file proves relations between the various finset intervals in a successor/predecessor order.

## Notes

Please keep in sync with:
* `Mathlib/Algebra/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Algebra/Order/Interval/Set/SuccPred.lean`
* `Mathlib/Order/Interval/Set/SuccPred.lean`

## TODO

Copy over `insert` lemmas from `Mathlib/Order/Interval/Finset/Nat.lean`.
-/

public section

assert_not_exists MonoidWithZero

open Order

namespace Finset
variable {α : Type*} [LinearOrder α]

/-! ### Two-sided intervals -/

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

section SuccOrder
variable [SuccOrder α] {a b : α}

/-!
#### Orders possibly with maximal elements

##### Equalities of intervals
-/

/-
**Finset.Ico_succ_left_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) b = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用引理 `Set.Ico_succ_left_eq_Ioo`：Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) 
b = Ioo a b

--- 原说明 ---
#### Orders possibly with maximal elements

##### Equalities of intervals
-/
lemma Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) b = Ioo a b :=
  coe_injective <| by simpa using Set.Ico_succ_left_eq_Ioo _ _
/-
**Finset.Icc_succ_left_eq_Ioc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Icc_succ_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (succ a) 
b = Ioc a b
参数：ha : ¬ IsMax a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用引理 `Set.Icc_succ_left_eq_Ioc_of_not_isMax`：Icc_succ_left_eq_Ioc_of_not_isMax
 (ha : ¬ IsMax a) (b : α) : Icc (succ a) b = Ioc a b
-/
lemma Icc_succ_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (succ a) b = Ioc a b :=
  coe_injective <| by simpa using Set.Icc_succ_left_eq_Ioc_of_not_isMax ha _
/-
**Finset.Ico_succ_right_eq_Icc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ico_succ_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (succ 
b) = Icc a b
参数：hb : ¬ IsMax b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用引理 `Set.Ico_succ_right_eq_Icc_of_not_isMax`：Ico_succ_right_eq_Icc_of_not_isM
ax (hb : ¬ IsMax b) (a : α) : Ico a (succ b) = Icc a b
-/
lemma Ico_succ_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (succ b) = Icc a b :=
  coe_injective <| by simpa using Set.Ico_succ_right_eq_Icc_of_not_isMax hb _
/-
**Finset.Ioo_succ_right_eq_Ioc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioo_succ_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (succ 
b) = Ioc a b
参数：hb : ¬ IsMax b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用引理 `Set.Ioo_succ_right_eq_Ioc_of_not_isMax`：Ioo_succ_right_eq_Ioc_of_not_isM
ax (hb : ¬ IsMax b) (a : α) : Ioo a (succ b) = Ioc a b
-/
lemma Ioo_succ_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (succ b) = Ioc a b :=
  coe_injective <| by simpa using Set.Ioo_succ_right_eq_Ioc_of_not_isMax hb _
/-
**Finset.Ico_succ_succ_eq_Ioc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ico_succ_succ_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico (succ a) 
(succ b) = Ioc a b
参数：hb : ¬ IsMax b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用引理 `Set.Ico_succ_succ_eq_Ioc_of_not_isMax`：Ico_succ_succ_eq_Ioc_of_not_isMax
 (hb : ¬ IsMax b) (a : α) : Ico (succ a) (succ b) = Ioc a b
-/
lemma Ico_succ_succ_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (succ a) (succ b) = Ioc a b :=
  coe_injective <| by simpa using Set.Ico_succ_succ_eq_Ioc_of_not_isMax hb _

/-! ##### Inserting into intervals -/

/-
**Finset.insert_Icc_succ_left_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Icc_succ_left_eq_Icc (h : a <= b) : insert a (Icc (succ a) b) = Icc
 a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用引理 `Set.insert_Icc_succ_left_eq_Icc`：insert_Icc_succ_left_eq_Icc (h : a <= b
) : insert a (Icc (succ a) b) = Icc a b

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Icc_succ_left_eq_Icc (h : a ≤ b) : insert a (Icc (succ a) b) = Icc a b :=
  coe_injective <| by simpa using Set.insert_Icc_succ_left_eq_Icc h
/-
**Finset.insert_Icc_right_eq_Icc_succ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Icc_right_eq_Icc_succ (h : a <= succ b) : insert (succ b) (Icc a b)
 = Icc a (succ b)
参数：h : a <= succ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用引理 `Set.insert_Icc_right_eq_Icc_succ`：insert_Icc_right_eq_Icc_succ (h : a <=
 succ b) : insert (succ b) (Icc a b) = Icc a (succ b)
-/
lemma insert_Icc_right_eq_Icc_succ (h : a ≤ succ b) : insert (succ b) (Icc a b) = Icc a (succ b) :=
  coe_injective <| by simpa using Set.insert_Icc_right_eq_Icc_succ h
/-
**Finset.insert_Ico_right_eq_Ico_succ_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Fi
nset`。
形式化陈述：insert_Ico_right_eq_Ico_succ_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : 
insert b (Ico a b) = Ico a (succ b)
参数：h : a <= b；hb : ¬ IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用引理 `Set.insert_Ico_right_eq_Ico_succ_of_not_isMax`：insert_Ico_right_eq_Ico_s
ucc_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : insert b (Ico a b) = Ico a (suc
c b)
-/
lemma insert_Ico_right_eq_Ico_succ_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (succ b) :=
  coe_injective <| by simpa using Set.insert_Ico_right_eq_Ico_succ_of_not_isMax h hb
/-
**Finset.insert_Ico_succ_left_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ico_succ_left_eq_Ico (h : a < b) : insert a (Ico (succ a) b) = Ico 
a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用引理 `Set.insert_Ico_succ_left_eq_Ico`：insert_Ico_succ_left_eq_Ico (h : a < b)
 : insert a (Ico (succ a) b) = Ico a b
-/
lemma insert_Ico_succ_left_eq_Ico (h : a < b) : insert a (Ico (succ a) b) = Ico a b :=
  coe_injective <| by simpa using Set.insert_Ico_succ_left_eq_Ico h
/-
**Finset.insert_Ioc_right_eq_Ioc_succ_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Fi
nset`。
形式化陈述：insert_Ioc_right_eq_Ioc_succ_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : 
insert (succ b) (Ioc a b) = Ioc a (succ b)
参数：h : a <= b；hb : ¬ IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用引理 `Set.insert_Ioc_right_eq_Ioc_succ_of_not_isMax`：insert_Ioc_right_eq_Ioc_s
ucc_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : insert (succ b) (Ioc a b) = Ioc
 a (succ b)
-/
lemma insert_Ioc_right_eq_Ioc_succ_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert (succ b) (Ioc a b) = Ioc a (succ b) :=
  coe_injective <| by simpa using Set.insert_Ioc_right_eq_Ioc_succ_of_not_isMax h hb
/-
**Finset.insert_Ioc_succ_left_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ioc_succ_left_eq_Ioc (h : a < b) : insert (succ a) (Ioc (succ a) b)
 = Ioc a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用引理 `Set.insert_Ioc_succ_left_eq_Ioc`：insert_Ioc_succ_left_eq_Ioc (h : a < b)
 : insert (succ a) (Ioc (succ a) b) = Ioc a b
-/
lemma insert_Ioc_succ_left_eq_Ioc (h : a < b) : insert (succ a) (Ioc (succ a) b) = Ioc a b :=
  coe_injective <| by simpa using Set.insert_Ioc_succ_left_eq_Ioc h

/-!
#### Orders with no maximal elements

##### Equalities of intervals
-/

variable [NoMaxOrder α]

/-
**Finset.Icc_succ_left_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Icc_succ_left_eq_Ioc (a b : α) : Icc (succ a) b = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Order.Icc_succ_left`：Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Icc_succ_left_eq_Ioc (a b : α) : Icc (succ a) b = Ioc a b := coe_injective <| by simp
/-
**Finset.Ico_succ_right_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ico_succ_right_eq_Icc (a b : α) : Ico a (succ b) = Icc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Order.Ico_succ_right`：Ico_succ_right (a b : α) : Ico a (succ b) = Icc a 
b
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ico_succ_right_eq_Icc (a b : α) : Ico a (succ b) = Icc a b := coe_injective <| by simp
/-
**Finset.Ioo_succ_right_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (succ b) = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Order.Ioo_succ_right`：Ioo_succ_right (a b : α) : Ioo a (succ b) = Ioc a 
b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (succ b) = Ioc a b := coe_injective <| by simp
/-
**Finset.Ico_succ_succ_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ a) (succ b) = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Order.Ico_succ_right`：Ico_succ_right (a b : α) : Ico a (succ b) = Icc a 
b
· 使用定理 `Order.Icc_succ_left`：Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ a) (succ b) = Ioc a b := coe_injective <| by simp

/-! ##### Inserting into intervals -/

/-
**Finset.insert_Ico_right_eq_Ico_succ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ico_right_eq_Ico_succ (h : a <= b) : insert b (Ico a b) = Ico a (su
cc b)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Order.Ico_succ_right`：Ico_succ_right (a b : α) : Ico a (succ b) = Icc a 
b
· 使用引理 `Set.insert_Ico_right_eq_Ico_succ`：insert_Ico_right_eq_Ico_succ (h : a <=
 b) : insert b (Ico a b) = Ico a (succ b)

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Ico_right_eq_Ico_succ (h : a ≤ b) : insert b (Ico a b) = Ico a (succ b) :=
  coe_injective <| by simpa using Set.insert_Ico_right_eq_Ico_succ h
/-
**Finset.insert_Ioc_right_eq_Ioc_succ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ioc_right_eq_Ioc_succ (h : a <= b) : insert (succ b) (Ioc a b) = Io
c a (succ b)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用引理 `Set.insert_Ioc_right_eq_Ioc_succ`：insert_Ioc_right_eq_Ioc_succ (h : a <=
 b) : insert (succ b) (Ioc a b) = Ioc a (succ b)
-/
lemma insert_Ioc_right_eq_Ioc_succ (h : a ≤ b) : insert (succ b) (Ioc a b) = Ioc a (succ b) :=
  coe_injective <| by simpa using Set.insert_Ioc_right_eq_Ioc_succ h

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

/-!
#### Orders possibly with minimal elements

##### Equalities of intervals
-/

/-
**Finset.Ioc_pred_right_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioc_pred_right_eq_Ioo (a b : α) : Ioc a (pred b) = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用引理 `Set.Ioc_pred_right_eq_Ioo`：Ioc_pred_right_eq_Ioo (a b : α) : Ioc a (pred
 b) = Ioo a b

--- 原说明 ---
#### Orders possibly with minimal elements

##### Equalities of intervals
-/
lemma Ioc_pred_right_eq_Ioo (a b : α) : Ioc a (pred b) = Ioo a b :=
  coe_injective <| by simpa using Set.Ioc_pred_right_eq_Ioo _ _
/-
**Finset.Icc_pred_right_eq_Ico_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Icc_pred_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (pred 
b) = Ico a b
参数：hb : ¬ IsMin b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用引理 `Set.Icc_pred_right_eq_Ico_of_not_isMin`：Icc_pred_right_eq_Ico_of_not_isM
in (hb : ¬ IsMin b) (a : α) : Icc a (pred b) = Ico a b
-/
lemma Icc_pred_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (pred b) = Ico a b :=
  coe_injective <| by simpa using Set.Icc_pred_right_eq_Ico_of_not_isMin hb _
/-
**Finset.Ioc_pred_left_eq_Icc_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioc_pred_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (pred a) 
b = Icc a b
参数：ha : ¬ IsMin a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用引理 `Set.Ioc_pred_left_eq_Icc_of_not_isMin`：Ioc_pred_left_eq_Icc_of_not_isMin
 (ha : ¬ IsMin a) (b : α) : Ioc (pred a) b = Icc a b
-/
lemma Ioc_pred_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (pred a) b = Icc a b :=
  coe_injective <| by simpa using Set.Ioc_pred_left_eq_Icc_of_not_isMin ha _
/-
**Finset.Ioo_pred_left_eq_Ioc_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioo_pred_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (pred a) 
b = Ico a b
参数：ha : ¬ IsMin a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用引理 `Set.Ioo_pred_left_eq_Ioc_of_not_isMin`：Ioo_pred_left_eq_Ioc_of_not_isMin
 (ha : ¬ IsMin a) (b : α) : Ioo (pred a) b = Ico a b
-/
lemma Ioo_pred_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (pred a) b = Ico a b :=
  coe_injective <| by simpa using Set.Ioo_pred_left_eq_Ioc_of_not_isMin ha _
/-
**Finset.Ioc_pred_pred_eq_Ico_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioc_pred_pred_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (pred a) 
(pred b) = Ico a b
参数：ha : ¬ IsMin a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用引理 `Set.Ioc_pred_pred_eq_Ico_of_not_isMin`：Ioc_pred_pred_eq_Ico_of_not_isMin
 (ha : ¬ IsMin a) (b : α) : Ioc (pred a) (pred b) = Ico a b
-/
lemma Ioc_pred_pred_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) :
    Ioc (pred a) (pred b) = Ico a b :=
  coe_injective <| by simpa using Set.Ioc_pred_pred_eq_Ico_of_not_isMin ha _

/-! ##### Inserting into intervals -/

/-
**Finset.insert_Icc_pred_right_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Icc_pred_right_eq_Icc (h : a <= b) : insert b (Icc a (pred b)) = Ic
c a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用引理 `Set.insert_Icc_pred_right_eq_Icc`：insert_Icc_pred_right_eq_Icc (h : a <=
 b) : insert b (Icc a (pred b)) = Icc a b

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Icc_pred_right_eq_Icc (h : a ≤ b) : insert b (Icc a (pred b)) = Icc a b :=
  coe_injective <| by simpa using Set.insert_Icc_pred_right_eq_Icc h
/-
**Finset.insert_Icc_left_eq_Icc_pred** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Icc_left_eq_Icc_pred (h : pred a <= b) : insert (pred a) (Icc a b) 
= Icc (pred a) b
参数：h : pred a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用引理 `Set.insert_Icc_left_eq_Icc_pred`：insert_Icc_left_eq_Icc_pred (h : pred a
 <= b) : insert (pred a) (Icc a b) = Icc (pred a) b
-/
lemma insert_Icc_left_eq_Icc_pred (h : pred a ≤ b) : insert (pred a) (Icc a b) = Icc (pred a) b :=
  coe_injective <| by simpa using Set.insert_Icc_left_eq_Icc_pred h
/-
**Finset.insert_Ioc_left_eq_Ioc_pred_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Fin
set`。
形式化陈述：insert_Ioc_left_eq_Ioc_pred_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : i
nsert a (Ioc a b) = Ioc (pred a) b
参数：h : a <= b；ha : ¬ IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用引理 `Set.insert_Ioc_left_eq_Ioc_pred_of_not_isMin`：insert_Ioc_left_eq_Ioc_pre
d_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : insert a (Ioc a b) = Ioc (pred a)
 b
-/
lemma insert_Ioc_left_eq_Ioc_pred_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert a (Ioc a b) = Ioc (pred a) b :=
  coe_injective <| by simpa using Set.insert_Ioc_left_eq_Ioc_pred_of_not_isMin h ha
/-
**Finset.insert_Ioc_pred_right_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ioc_pred_right_eq_Ioc (h : a < b) : insert b (Ioc a (pred b)) = Ioc
 a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用引理 `Set.insert_Ioc_pred_right_eq_Ioc`：insert_Ioc_pred_right_eq_Ioc (h : a < 
b) : insert b (Ioc a (pred b)) = Ioc a b
-/
lemma insert_Ioc_pred_right_eq_Ioc (h : a < b) : insert b (Ioc a (pred b)) = Ioc a b :=
  coe_injective <| by simpa using Set.insert_Ioc_pred_right_eq_Ioc h
/-
**Finset.insert_Ico_left_eq_Ico_pred_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Fin
set`。
形式化陈述：insert_Ico_left_eq_Ico_pred_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : i
nsert (pred a) (Ico a b) = Ico (pred a) b
参数：h : a <= b；ha : ¬ IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用引理 `Set.insert_Ico_left_eq_Ico_pred_of_not_isMin`：insert_Ico_left_eq_Ico_pre
d_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : insert (pred a) (Ico a b) = Ico (
pred a) b
-/
lemma insert_Ico_left_eq_Ico_pred_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert (pred a) (Ico a b) = Ico (pred a) b :=
  coe_injective <| by simpa using Set.insert_Ico_left_eq_Ico_pred_of_not_isMin h ha
/-
**Finset.insert_Ico_pred_right_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ico_pred_right_eq_Ico (h : a < b) : insert (pred b) (Ico a (pred b)
) = Ico a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用引理 `Set.insert_Ico_pred_right_eq_Ico`：insert_Ico_pred_right_eq_Ico (h : a < 
b) : insert (pred b) (Ico a (pred b)) = Ico a b
-/
lemma insert_Ico_pred_right_eq_Ico (h : a < b) : insert (pred b) (Ico a (pred b)) = Ico a b :=
  coe_injective <| by simpa using Set.insert_Ico_pred_right_eq_Ico h

/-!
#### Orders with no minimal elements

##### Equalities of intervals
-/

variable [NoMinOrder α]

/-
**Finset.Icc_pred_right_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Icc_pred_right_eq_Ico (a b : α) : Icc a (pred b) = Ico a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Order.Icc_pred_right`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pre
dOrder α] [NoMinOrder α] (a b : α),   Set.Icc b (Order.pred a) = Set.Ico b a
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Icc_pred_right_eq_Ico (a b : α) : Icc a (pred b) = Ico a b := coe_injective <| by simp
/-
**Finset.Ioc_pred_left_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioc_pred_left_eq_Icc (a b : α) : Ioc (pred a) b = Icc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Order.Ioc_pred_left`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : P
redOrder α] [NoMinOrder α] (a b : α),   Set.Ioc (Order.pred b) a = Set.Icc b a
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ioc_pred_left_eq_Icc (a b : α) : Ioc (pred a) b = Icc a b := coe_injective <| by simp
/-
**Finset.Ioo_pred_left_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioo_pred_left_eq_Ioc (a b : α) : Ioo (pred a) b = Ico a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Order.Ioo_pred_left`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : P
redOrder α] [NoMinOrder α] (a b : α),   Set.Ioo (Order.pred b) a = Set.Ico b a
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ioo_pred_left_eq_Ioc (a b : α) : Ioo (pred a) b = Ico a b := coe_injective <| by simp
/-
**Finset.Ioc_pred_pred_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioc_pred_pred_eq_Ico (a b : α) : Ioc (pred a) (pred b) = Ico a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Order.Ioc_pred_right`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pre
dOrder α] [NoMinOrder α] (a b : α),   Set.Ioc b (Order.pred a) = Set.Ioo b a
· 使用定理 `Order.Ioo_pred_left`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : P
redOrder α] [NoMinOrder α] (a b : α),   Set.Ioo (Order.pred b) a = Set.Ico b a
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ioc_pred_pred_eq_Ico (a b : α) : Ioc (pred a) (pred b) = Ico a b := coe_injective <| by simp

/-! ##### Inserting into intervals -/

/-
**Finset.insert_Ioc_left_eq_Ioc_pred** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ioc_left_eq_Ioc_pred (h : a <= b) : insert a (Ioc a b) = Ioc (pred 
a) b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Order.Ioc_pred_left`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : P
redOrder α] [NoMinOrder α] (a b : α),   Set.Ioc (Order.pred b) a = Set.Icc b a
· 使用引理 `Set.insert_Ioc_left_eq_Ioc_pred`：insert_Ioc_left_eq_Ioc_pred (h : a <= b
) : insert a (Ioc a b) = Ioc (pred a) b

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Ioc_left_eq_Ioc_pred (h : a ≤ b) : insert a (Ioc a b) = Ioc (pred a) b :=
  coe_injective <| by simpa using Set.insert_Ioc_left_eq_Ioc_pred h
/-
**Finset.insert_Ico_left_eq_Ico_pred** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ico_left_eq_Ico_pred (h : a <= b) : insert (pred a) (Ico a b) = Ico
 (pred a) b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.insert_Ico_left_eq_Ico_pred_of_not_isMin`：insert_Ico_left_eq_Ico_
pred_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : insert (pred a) (Ico a b) = Ic
o (pred a) b
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
lemma insert_Ico_left_eq_Ico_pred (h : a ≤ b) : insert (pred a) (Ico a b) = Ico (pred a) b :=
  insert_Ico_left_eq_Ico_pred_of_not_isMin h (not_isMin _)

end PredOrder

section SuccPredOrder
variable [SuccOrder α] [PredOrder α] [Nontrivial α]

/-
**Finset.Icc_succ_pred_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Icc_succ_pred_eq_Ioo (a b : α) : Icc (succ a) (pred b) = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用引理 `Set.Icc_succ_pred_eq_Ioo`：Icc_succ_pred_eq_Ioo (a b : α) : Icc (succ a) 
(pred b) = Ioo a b
-/
lemma Icc_succ_pred_eq_Ioo (a b : α) : Icc (succ a) (pred b) = Ioo a b :=
  coe_injective <| by simpa using Set.Icc_succ_pred_eq_Ioo _ _

end SuccPredOrder
end LocallyFiniteOrder

/-! ### One-sided interval towards `⊥` -/

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

section SuccOrder
variable [SuccOrder α] {b : α}

/-
**Finset.Iio_succ_eq_Iic_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Iio_succ_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (succ b) = Iic b
参数：hb : ¬ IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用引理 `Set.Iio_succ_eq_Iic_of_not_isMax`：Iio_succ_eq_Iic_of_not_isMax (hb : ¬ I
sMax b) : Iio (succ b) = Iic b
-/
lemma Iio_succ_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (succ b) = Iic b :=
  coe_injective <| by simpa using Set.Iio_succ_eq_Iic_of_not_isMax hb

variable [NoMaxOrder α]
/-
**Finset.Iio_succ_eq_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Iio_succ_eq_Iic (b : α) : Iio (succ b) = Iic b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Order.Iio_succ`：Iio_succ (a : α) : Iio (succ a) = Iic a
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Iio_succ_eq_Iic (b : α) : Iio (succ b) = Iic b := coe_injective <| by simp

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

/-
**Finset.Iic_pred_eq_Iio_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Iic_pred_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (pred b) = Iio b
参数：hb : ¬ IsMin b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用引理 `Set.Iic_pred_eq_Iio_of_not_isMin`：Iic_pred_eq_Iio_of_not_isMin (hb : ¬ I
sMin b) : Iic (pred b) = Iio b
-/
lemma Iic_pred_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (pred b) = Iio b :=
  coe_injective <| by simpa using Set.Iic_pred_eq_Iio_of_not_isMin hb

variable [NoMinOrder α]
/-
**Finset.Iic_pred_eq_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Iic_pred_eq_Iio (b : α) : Iic (pred b) = Iio b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Order.Iic_pred`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrder
 α] [NoMinOrder α] (a : α), Set.Iic (Order.pred a) = Set.Iio a
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Iic_pred_eq_Iio (b : α) : Iic (pred b) = Iio b := coe_injective <| by simp

end PredOrder
end LocallyFiniteOrderBot

/-! ### One-sided interval towards `⊤` -/

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

section SuccOrder
variable [SuccOrder α] {a : α}

/-
**Finset.Ici_succ_eq_Ioi_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ici_succ_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (succ a) = Ioi a
参数：ha : ¬ IsMax a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用引理 `Set.Ici_succ_eq_Ioi_of_not_isMax`：Ici_succ_eq_Ioi_of_not_isMax (ha : ¬ I
sMax a) : Ici (succ a) = Ioi a
-/
lemma Ici_succ_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (succ a) = Ioi a :=
  coe_injective <| by simpa using Set.Ici_succ_eq_Ioi_of_not_isMax ha

variable [NoMaxOrder α]
/-
**Finset.Ici_succ_eq_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ici_succ_eq_Ioi (a : α) : Ici (succ a) = Ioi a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Order.Ici_succ`：Ici_succ (a : α) : Ici (succ a) = Ioi a
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ici_succ_eq_Ioi (a : α) : Ici (succ a) = Ioi a := coe_injective <| by simp

end SuccOrder

section PredOrder
variable [PredOrder α] {a a : α}

/-
**Finset.Ioi_pred_eq_Ici_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioi_pred_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (pred a) = Ici a
参数：ha : ¬ IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用引理 `Set.Ioi_pred_eq_Ici_of_not_isMin`：Ioi_pred_eq_Ici_of_not_isMin (ha : ¬ I
sMin a) : Ioi (pred a) = Ici a
-/
lemma Ioi_pred_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (pred a) = Ici a :=
  coe_injective <| by simpa using Set.Ioi_pred_eq_Ici_of_not_isMin ha

variable [NoMinOrder α]
/-
**Finset.Ioi_pred_eq_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioi_pred_eq_Ici (a : α) : Ioi (pred a) = Ici a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Order.Ioi_pred`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : PredOr
der α] [NoMinOrder α] (a : α),   Set.Ioi (Order.pred a) = Set.Ici a
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ioi_pred_eq_Ici (a : α) : Ioi (pred a) = Ici a := coe_injective <| by simp

end PredOrder
end LocallyFiniteOrderTop
end Finset

