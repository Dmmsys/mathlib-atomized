/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Tree

import Batteries.Data.List.Count
import Mathlib.Tactic.Positivity.Finset

/-!
# Dyck words

A Dyck word is a sequence consisting of an equal number `n` of symbols of two types such that
for all prefixes one symbol occurs at least as many times as the other.
If the symbols are `(` and `)` the latter restriction is equivalent to balanced brackets;
if they are `U = (1, 1)` and `D = (1, -1)` the sequence is a lattice path from `(0, 0)` to `(0, 2n)`
and the restriction requires the path to never go below the x-axis.

This file defines Dyck words and constructs their bijection with rooted binary trees,
one consequence being that the number of Dyck words with length `2 * n` is `catalan n`.

## Main definitions

* `DyckWord`: a list of `U`s and `D`s with as many `U`s as `D`s and with every prefix having
  at least as many `U`s as `D`s.
* `DyckWord.semilength`: semilength (half the length) of a Dyck word.
* `DyckWord.firstReturn`: for a nonempty word, the index of the `D` matching the initial `U`.

## Main results

* `DyckWord.equivTree`: equivalence between Dyck words and rooted binary trees.
  See the docstrings of `DyckWord.toTree` and `DyckWord.ofTree` for details.
* `DyckWord.equivTreesOfNumNodesEq`: equivalence between Dyck words of length `2 * n` and
  rooted binary trees with `n` internal nodes.
* `DyckWord.card_dyckWord_semilength_eq_catalan`:
  there are `catalan n` Dyck words of length `2 * n` or semilength `n`.

## Implementation notes

While any two-valued type could have been used for `DyckStep`, a new enumerated type is used here
to emphasise that the definition of a Dyck word does not depend on that underlying type.
-/

@[expose] public section

open List

/-- A `DyckStep` is either `U` or `D`, corresponding to `(` and `)` respectively. -/
/-
**DyckStep** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `DyckStep` is either `U` or `D`, corresponding to `(` and `)` respectively.
-/
inductive DyckStep
  | U : DyckStep
  | D : DyckStep
  deriving Inhabited, DecidableEq

/-- Named in analogy to `Bool.dichotomy`. -/
/-
**DyckStep.dichotomy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DyckStep.dichotomy (s : DyckStep) : s = U ∨ s = D
参数：s : DyckStep。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Named in analogy to `Bool.dichotomy`.
-/
lemma DyckStep.dichotomy (s : DyckStep) : s = U ∨ s = D := by cases s <;> tauto

open DyckStep

/-- A Dyck word is a list of `DyckStep`s with as many `U`s as `D`s and with every prefix having
at least as many `U`s as `D`s. -/
@[ext]
/-
**DyckWord** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Dyck word is a list of `DyckStep`s with as many `U`s as `D`s and with every pr
efix having
at least as many `U`s as `D`s.
-/
structure DyckWord where
  /-- The underlying list -/
  toList : List DyckStep
  /-- There are as many `U`s as `D`s -/
  count_U_eq_count_D : toList.count U = toList.count D
  /-- Each prefix has at least as many `U`s as `D`s -/
  count_D_le_count_U i : (toList.take i).count D ≤ (toList.take i).count U
  deriving DecidableEq

attribute [coe] DyckWord.toList
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe DyckWord (List DyckStep) := ⟨DyckWord.toList⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add DyckWord where
  add p q := ⟨p ++ q, by
    simp only [count_append, p.count_U_eq_count_D, q.count_U_eq_count_D], by
    simp only [take_append, count_append]
    exact fun _ ↦ add_le_add (p.count_D_le_count_U _) (q.count_D_le_count_U _)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero DyckWord := ⟨[], by simp, by simp⟩

/-- Dyck words form an additive cancellative monoid under concatenation,
with the empty word as 0. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dyck words form an additive cancellative monoid under concatenation,
with the empty word as 0.
-/
instance : AddCancelMonoid DyckWord where
  add_zero p := by ext1; exact append_nil _
  zero_add p := by ext1; rfl
  add_assoc p q r := by ext1; apply append_assoc
  nsmul := nsmulRec
  add_left_cancel p q r h := by rw [DyckWord.ext_iff] at *; exact append_cancel_left h
  add_right_cancel p q r h := by rw [DyckWord.ext_iff] at *; exact append_cancel_right h

namespace DyckWord

variable {p q : DyckWord}

/-
**DyckWord.toList_eq_nil** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：toList_eq_nil : p.toList = [] ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DyckWord.ext_iff`：∀ {x y : DyckWord}, x = y ↔ ↑x = ↑y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toList_eq_nil : p.toList = [] ↔ p = 0 := by rw [DyckWord.ext_iff]; rfl
/-
**DyckWord.toList_ne_nil** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：toList_ne_nil : p.toList != [] ↔ p != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `DyckWord.toList_eq_nil`：toList_eq_nil : p.toList = [] ↔ p = 0
-/
lemma toList_ne_nil : p.toList ≠ [] ↔ p ≠ 0 := toList_eq_nil.ne

/-- The only Dyck word that is an additive unit is the empty word. -/
/-
**DyckWord.** 是 Mathlib 中的一个实例，位于命名空间 `DyckWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The only Dyck word that is an additive unit is the empty word.
-/
instance : Unique (AddUnits DyckWord) where
  uniq p := by
    obtain ⟨a, b, h, -⟩ := p
    obtain ⟨ha, hb⟩ := append_eq_nil_iff.mp (toList_eq_nil.mpr h)
    congr
    · exact toList_eq_nil.mp ha
    · exact toList_eq_nil.mp hb

variable (h : p ≠ 0)

/-- The first element of a nonempty Dyck word is `U`. -/
/-
**DyckWord.head_eq_U** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：head_eq_U (p : DyckWord) (h) : p.toList.head h = U
参数：p : DyckWord；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.head_cons`：∀ {α : Type u} {a : α} {l : List α} {h : a :: l ≠ []}, (
a :: l).head h = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `DyckStep.dichotomy`：DyckStep.dichotomy (s : DyckStep) : s = U ∨ s = D
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.count_cons_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {b 
a : α}, b ≠ a → ∀ {l : List α}, List.count a (b :: l) = List.count a l
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
The first element of a nonempty Dyck word is `U`.
-/
lemma head_eq_U (p : DyckWord) (h) : p.toList.head h = U := by
  rcases p with - | s; · tauto
  rw [head_cons]
  by_contra f
  rename_i _ nonneg
  simpa [s.dichotomy.resolve_left f] using nonneg 1

/-- The last element of a nonempty Dyck word is `D`. -/
/-
**DyckWord.getLast_eq_D** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：getLast_eq_D (p : DyckWord) (h) : p.toList.getLast h = D
参数：p : DyckWord；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `DyckWord.count_U_eq_count_D`：∀ (self : DyckWord), List.count DyckStep.U 
↑self = List.count DyckStep.D ↑self
· 使用定理 `DyckWord.count_D_le_count_U`：∀ (self : DyckWord) (i : ℕ), List.count Dyc
kStep.D (List.take i ↑self) ≤ List.count DyckStep.U (List.take i ↑self)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.count_singleton'`：∀ {α : Type u_1} [inst : DecidableEq α] (a b : α)
, List.count a [b] = if b = a then 1 else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.count_append`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l₁ l₂ : List
 α}, List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.dropLast_eq_take`：∀ {α : Type u_1} {l : List α}, l.dropLast = List.
take (l.length - 1) l
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `DyckStep.dichotomy`：DyckStep.dichotomy (s : DyckStep) : s = U ∨ s = D
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.dropLast_append_getLast`：∀ {α : Type u} {l : List α} (h : l ≠ []), 
l.dropLast ++ [l.getLast h] = l

--- 原说明 ---
The last element of a nonempty Dyck word is `D`.
-/
lemma getLast_eq_D (p : DyckWord) (h) : p.toList.getLast h = D := by
  by_contra f; have s := p.count_U_eq_count_D
  rw [← dropLast_append_getLast h, (dichotomy _).resolve_right f] at s
  simp_rw [dropLast_eq_take, count_append, count_singleton', ite_true, reduceCtorEq, ite_false] at s
  have := p.count_D_le_count_U (p.toList.length - 1); lia

include h in
/-
**DyckWord.cons_tail_dropLast_concat** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：cons_tail_dropLast_concat : U :: p.toList.dropLast.tail ++ [D] = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DyckWord.toList_ne_nil`：toList_ne_nil : p.toList != [] ↔ p != 0
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.count_cons_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {b 
a : α}, b ≠ a → ∀ {l : List α}, List.count a (b :: l) = List.count a l
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.dropLast_append_getLast`：∀ {α : Type u} {l : List α} (h : l ≠ []), 
l.dropLast ++ [l.getLast h] = l
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用引理 `DyckWord.getLast_eq_D`：getLast_eq_D (p : DyckWord) (h) : p.toList.getLas
t h = D
· 使用定理 `List.drop_one`：∀ {α : Type u_1} {l : List α}, List.drop 1 l = l.tail
· 使用引理 `DyckWord.head_eq_U`：head_eq_U (p : DyckWord) (h) : p.toList.head h = U
-/
lemma cons_tail_dropLast_concat : U :: p.toList.dropLast.tail ++ [D] = p := by
  have h' := toList_ne_nil.mpr h
  have : p.toList.dropLast.take 1 = [p.toList.head h'] := by
    rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
    · tauto
    · rename_i bal _
      cases s <;> simp at bal
    · tauto
  nth_rw 2 [← p.toList.dropLast_append_getLast h', ← p.toList.dropLast.take_append_drop 1]
  rw [getLast_eq_D, drop_one, this, head_eq_U]
  rfl

variable (p) in
/-- Prefix of a Dyck word as a Dyck word, given that the count of `U`s and `D`s in it are equal. -/
/-
**DyckWord.take** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：take (i : Nat) (hi : (p.toList.take i).count U = (p.toList.take i).count D
) : DyckWord where toList
参数：i : Nat；hi : (p.toList.take i).count U = (p.toList.take i).count D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prefix of a Dyck word as a Dyck word, given that the count of `U`s and `D`s in i
t are equal.
-/
def take (i : ℕ) (hi : (p.toList.take i).count U = (p.toList.take i).count D) : DyckWord where
  toList := p.toList.take i
  count_U_eq_count_D := hi
  count_D_le_count_U k := by rw [take_take]; exact p.count_D_le_count_U (min k i)

variable (p) in
/-- Suffix of a Dyck word as a Dyck word, given that the count of `U`s and `D`s in the prefix
are equal. -/
/-
**DyckWord.drop** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：drop (i : Nat) (hi : (p.toList.take i).count U = (p.toList.take i).count D
) : DyckWord where toList
参数：i : Nat；hi : (p.toList.take i).count U = (p.toList.take i).count D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suffix of a Dyck word as a Dyck word, given that the count of `U`s and `D`s in t
he prefix
are equal.
-/
def drop (i : ℕ) (hi : (p.toList.take i).count U = (p.toList.take i).count D) : DyckWord where
  toList := p.toList.drop i
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← take_append_drop i p.toList, count_append, count_append] at this
    lia
  count_D_le_count_U k := by
    rw [show i = min i (i + k) by omega, ← take_take] at hi
    rw [take_drop, ← add_le_add_iff_left (((p.toList.take (i + k)).take i).count U),
      ← count_append, hi, ← count_append, take_append_drop]
    exact p.count_D_le_count_U _

variable (p) in
/-- Nest `p` in one pair of brackets, i.e. `x` becomes `(x)`. -/
/-
**DyckWord.nest** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：nest : DyckWord where toList
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Nest `p` in one pair of brackets, i.e. `x` becomes `(x)`.
-/
def nest : DyckWord where
  toList := [U] ++ p ++ [D]
  count_U_eq_count_D := by simp [p.count_U_eq_count_D]
  count_D_le_count_U i := by
    simp only [take_append, count_append]
    rw [← add_rotate (count D _), ← add_rotate (count U _)]
    apply add_le_add _ (p.count_D_le_count_U _)
    rcases i.eq_zero_or_pos with hi | hi; · simp [hi]
    rw [take_of_length_le (show [U].length ≤ i by rwa [length_singleton]), count_singleton']
    simp only [reduceCtorEq, ite_false]
    rw [add_comm]
    exact add_le_add zero_le (count_le_length.trans (by simp))
/-
**DyckWord.nest_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：∀ {p : DyckWord}, p.nest ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma nest_ne_zero : p.nest ≠ 0 := by simp [← toList_ne_nil, nest]

variable (p) in
/-- A property stating that `p` is nonempty and strictly positive in its interior,
i.e. is of the form `(x)` with `x` a Dyck word. -/
/-
**DyckWord.IsNested** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：IsNested : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property stating that `p` is nonempty and strictly positive in its interior,
i.e. is of the form `(x)` with `x` a Dyck word.
-/
def IsNested : Prop :=
  p ≠ 0 ∧ ∀ ⦃i⦄, 0 < i → i < p.toList.length → (p.toList.take i).count D < (p.toList.take i).count U
/-
**DyckWord.IsNested.nest** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord.IsNested`。
形式化陈述：∀ {p : DyckWord}, p.nest.IsNested
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DyckWord.nest_ne_zero`：∀ {p : DyckWord}, p.nest ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.take_append_of_le_length`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}
, i ≤ l₁.length → List.take i (l₁ ++ l₂) = List.take i l₁
· 使用定理 `List.singleton_append`：∀ {α : Type u_1} {x : α} {l : List α}, [x] ++ l =
 x :: l
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.take_append`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, List.take i
 (l₁ ++ l₂) = List.take i l₁ ++ List.take (i - l₁.length) l₂
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
· 使用定理 `List.length_singleton`：∀ {α : Type u} {a : α}, [a].length = 1
· 使用定理 `List.count_cons_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {b 
a : α}, b ≠ a → ∀ {l : List α}, List.count a (b :: l) = List.count a l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.count_cons_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a :
 α} {l : List α}, List.count a (a :: l) = List.count a l + 1
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
· 使用定理 `DyckWord.count_D_le_count_U`：∀ (self : DyckWord) (i : ℕ), List.count Dyc
kStep.D (List.take i ↑self) ≤ List.count DyckStep.U (List.take i ↑self)
-/
protected lemma IsNested.nest : p.nest.IsNested := ⟨nest_ne_zero, fun i lb ub ↦ by
  simp_rw [nest, length_append, length_singleton] at ub ⊢
  rw [take_append_of_le_length (by rw [singleton_append, length_cons]; lia),
    take_append, take_of_length_le (by rw [length_singleton]; lia),
    length_singleton, singleton_append, count_cons_of_ne (by simp), count_cons_self,
    Nat.lt_add_one_iff]
  exact p.count_D_le_count_U _⟩

variable (p) in
/-- Denest `p`, i.e. `(x)` becomes `x`, given that `p.IsNested`. -/
/-
**DyckWord.denest** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：denest (hn : p.IsNested) : DyckWord where toList
参数：hn : p.IsNested。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Denest `p`, i.e. `(x)` becomes `x`, given that `p.IsNested`.
-/
def denest (hn : p.IsNested) : DyckWord where
  toList := p.toList.dropLast.tail
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← cons_tail_dropLast_concat hn.1, count_append, count_cons] at this
    simpa using this
  count_D_le_count_U i := by
    replace h := toList_ne_nil.mpr hn.1
    have l1 : p.toList.take 1 = [p.toList.head h] := by rcases p with - | - <;> tauto
    have l3 : p.toList.length - 1 = p.toList.length - 1 - 1 + 1 := by
      rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
      · tauto
      · rename_i bal _
        cases s <;> simp at bal
      · tauto
    rw [← drop_one, take_drop, dropLast_eq_take, take_take]
    have ub : min (1 + i) (p.toList.length - 1) < p.toList.length :=
      (min_le_right _ p.toList.length.pred).trans_lt (Nat.pred_lt ((length_pos_iff.mpr h).ne'))
    have lb : 0 < min (1 + i) (p.toList.length - 1) := by omega
    have eq := hn.2 lb ub
    set j := min (1 + i) (p.toList.length - 1)
    rw [← (p.toList.take j).take_append_drop 1, count_append, count_append, take_take,
      min_eq_left (by lia), l1, head_eq_U] at eq
    simp only [count_singleton', ite_true] at eq
    lia

variable (p) in
/-
**DyckWord.nest_denest** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：nest_denest (hn) : (p.denest hn).nest = p
参数：hn。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.cons_tail_dropLast_concat`：cons_tail_dropLast_concat : U :: p.t
oList.dropLast.tail ++ [D] = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma nest_denest (hn) : (p.denest hn).nest = p := by
  simpa [DyckWord.ext_iff] using! p.cons_tail_dropLast_concat hn.1

variable (p) in
/-
**DyckWord.denest_nest** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：denest_nest : p.nest.denest .nest = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DyckWord.IsNested.nest`：∀ {p : DyckWord}, p.nest.IsNested
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dropLast_concat`：∀ {α : Type u_1} {l₁ : List α} {b : α}, (l₁ ++ [b]
).dropLast = l₁
-/
lemma denest_nest : p.nest.denest .nest = p := by
  simp_rw [nest, denest, DyckWord.ext_iff, dropLast_concat]; rfl

section Semilength

variable (p) in
/-- The semilength of a Dyck word is half of the number of `DyckStep`s in it, or equivalently
its number of `U`s. -/
/-
**DyckWord.semilength** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：semilength : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The semilength of a Dyck word is half of the number of `DyckStep`s in it, or equ
ivalently
its number of `U`s.
-/
def semilength : ℕ := p.toList.count U
/-
**DyckWord.semilength_zero** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：DyckWord.semilength 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma semilength_zero : semilength 0 = 0 := rfl
/-
**DyckWord.semilength_add** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：∀ {p q : DyckWord}, (p + q).semilength = p.semilength + q.semilength
参数：p + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.count_append`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l₁ l₂ : List
 α}, List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂
-/
@[simp] lemma semilength_add : (p + q).semilength = p.semilength + q.semilength := count_append ..
/-
**DyckWord.semilength_nest** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：∀ {p : DyckWord}, p.nest.semilength = p.semilength + 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.count_cons_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a :
 α} {l : List α}, List.count a (a :: l) = List.count a l + 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.count_append`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l₁ l₂ : List
 α}, List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂
· 使用定理 `List.count_cons_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {b 
a : α}, b ≠ a → ∀ {l : List α}, List.count a (b :: l) = List.count a l
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma semilength_nest : p.nest.semilength = p.semilength + 1 := by simp [semilength, nest]
/-
**DyckWord.semilength_eq_count_D** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：semilength_eq_count_D : p.semilength = p.toList.count D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DyckWord.count_U_eq_count_D`：∀ (self : DyckWord), List.count DyckStep.U 
↑self = List.count DyckStep.D ↑self
-/
lemma semilength_eq_count_D : p.semilength = p.toList.count D := by
  rw [← count_U_eq_count_D]; rfl

@[simp]
/-
**DyckWord.two_mul_semilength_eq_length** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：two_mul_semilength_eq_length : 2 * p.semilength = p.toList.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `DyckWord.semilength.eq_1`：∀ (p : DyckWord), p.semilength = List.count Dy
ckStep.U ↑p
· 使用定理 `DyckWord.count_U_eq_count_D`：∀ (self : DyckWord), List.count DyckStep.U 
↑self = List.count DyckStep.D ↑self
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.count.eq_1`：∀ {α : Type u} [inst : BEq α] (a : α), List.count a = L
ist.countP fun x => x == a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.length_eq_countP_add_countP`：∀ {α : Type u_1} (p : α → Bool) {l : L
ist α}, l.length = List.countP p l + List.countP (fun a => decide ¬p a = true) l
-/
lemma two_mul_semilength_eq_length : 2 * p.semilength = p.toList.length := by
  nth_rw 1 [two_mul, semilength, p.count_U_eq_count_D, semilength]
  convert! (p.toList.length_eq_countP_add_countP (· == D)).symm
  rw [count]; congr!; rename_i s; cases s <;> tauto

end Semilength

section FirstReturn

variable (p) in
/-- `p.firstReturn` is 0 if `p = 0` and the index of the `D` matching the initial `U` otherwise. -/
/-
**DyckWord.firstReturn** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：firstReturn : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p.firstReturn` is 0 if `p = 0` and the index of the `D` matching the initial `U
` otherwise.
-/
def firstReturn : ℕ :=
  (range p.toList.length).findIdx fun i ↦
    (p.toList.take (i + 1)).count U = (p.toList.take (i + 1)).count D
/-
**DyckWord.firstReturn_zero** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：DyckWord.firstReturn 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma firstReturn_zero : firstReturn 0 = 0 := rfl

include h in
/-
**DyckWord.firstReturn_pos** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：firstReturn_pos : 0 < p.firstReturn
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `DyckWord.firstReturn.eq_1`：∀ (p : DyckWord),   p.firstReturn =     List.
findIdx       (fun i => decide (List.count DyckStep.U (List.take (i + 1) ↑p) = L
ist.count DyckS…
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `List.length_pos_iff`：∀ {α : Type u_1} {l : List α}, 0 < l.length ↔ l ≠ [
]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DyckWord.toList_ne_nil`：toList_ne_nil : p.toList != [] ↔ p != 0
· 使用定理 `Nat.lt_trans`：∀ {n m k : ℕ}, n < m → m < k → n < k
· 使用定理 `List.findIdx_eq`：∀ {α : Type u_1} {p : α → Bool} {xs : List α} {i : ℕ} (
h : i < xs.length),   List.findIdx p xs = i ↔ p xs[i] = true ∧ ∀ (j : ℕ) (hji : 
j < i…
· 使用定理 `List.getElem_range`：∀ {j n : ℕ} (h : j < (List.range n).length), (List.r
ange n)[j] = j
· 使用引理 `DyckWord.cons_tail_dropLast_concat`：cons_tail_dropLast_concat : U :: p.t
oList.dropLast.tail ++ [D] = p
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.count_cons_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {b 
a : α}, b ≠ a → ∀ {l : List α}, List.count a (b :: l) = List.count a l
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
（共 45 条，此处仅展示前 30 条）
-/
lemma firstReturn_pos : 0 < p.firstReturn := by
  rw [← not_le, Nat.le_zero, firstReturn, findIdx_eq, getElem_range]
  · rw! [← p.cons_tail_dropLast_concat h]
    simp
  · rw [length_range, length_pos_iff]
    exact toList_ne_nil.mpr h

include h in
/-
**DyckWord.firstReturn_lt_length** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：firstReturn_lt_length : p.firstReturn < p.toList.length
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_pos_of_ne_nil`：∀ {α : Type u_1} {l : List α}, l ≠ [] → 0 < l
.length
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DyckWord.toList_ne_nil`：toList_ne_nil : p.toList != [] ↔ p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `List.findIdx_lt_length_of_exists`：∀ {α : Type u_1} {p : α → Bool} {xs : 
List α}, (∃ x ∈ xs, p x = true) → List.findIdx p xs < xs.length
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `DyckWord.count_U_eq_count_D`：∀ (self : DyckWord), List.count DyckStep.U 
↑self = List.count DyckStep.D ↑self
-/
lemma firstReturn_lt_length : p.firstReturn < p.toList.length := by
  have lp := length_pos_of_ne_nil (toList_ne_nil.mpr h)
  rw [← length_range (n := p.toList.length)]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.toList.length - 1
  exact ⟨by lia, by rw [Nat.sub_add_cancel lp, take_of_length_le (le_refl _),
    p.count_U_eq_count_D]⟩

set_option backward.isDefEq.respectTransparency false in
include h in
/-
**DyckWord.count_take_firstReturn_add_one** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：count_take_firstReturn_add_one : (p.toList.take (p.firstReturn + 1)).count
 U = (p.toList.take (p.firstReturn + 1)).count D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.firstReturn_lt_length`：firstReturn_lt_length : p.firstReturn < 
p.toList.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `List.findIdx_getElem`：∀ {α : Type u_1} {p : α → Bool} {xs : List α} {w :
 List.findIdx p xs < xs.length}, p xs[List.findIdx p xs] = true
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.getElem_range`：∀ {j n : ℕ} (h : j < (List.range n).length), (List.r
ange n)[j] = j
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
-/
lemma count_take_firstReturn_add_one :
    (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 1)).count D := by
  have := findIdx_getElem
    (w := (length_range (n := p.toList.length)).symm ▸ firstReturn_lt_length h)
  simpa using! this
/-
**DyckWord.count_D_lt_count_U_of_lt_firstReturn** 是 Mathlib 中的一个引理，位于命名空间 `DyckW
ord`。
形式化陈述：count_D_lt_count_U_of_lt_firstReturn {i : Nat} (hi : i < p.firstReturn) : 
(p.toList.take (i + 1)).count D < (p.toList.take (i + 1)).count U
参数：hi : i < p.firstReturn。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `List.findIdx_le_length`：∀ {α : Type u_1} {p : α → Bool} {xs : List α}, L
ist.findIdx p xs ≤ xs.length
· 使用定理 `List.not_of_lt_findIdx`：∀ {α : Type u_1} {p : α → Bool} {xs : List α} {i
 : ℕ} (h : i < List.findIdx p xs), p xs[i] = false
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `DyckWord.count_D_le_count_U`：∀ (self : DyckWord) (i : ℕ), List.count Dyc
kStep.D (List.take i ↑self) ≤ List.count DyckStep.U (List.take i ↑self)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_range`：∀ {j n : ℕ} (h : j < (List.range n).length), (List.r
ange n)[j] = j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `decide_eq_false_iff_not`：∀ {p : Prop} {x : Decidable p}, decide p = fals
e ↔ ¬p
-/
lemma count_D_lt_count_U_of_lt_firstReturn {i : ℕ} (hi : i < p.firstReturn) :
    (p.toList.take (i + 1)).count D < (p.toList.take (i + 1)).count U := by
  have ne := not_of_lt_findIdx hi
  rw [decide_eq_false_iff_not, ← ne_eq, getElem_range] at ne
  exact lt_of_le_of_ne (p.count_D_le_count_U (i + 1)) ne.symm

@[simp]
/-
**DyckWord.firstReturn_add** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：firstReturn_add : (p + q).firstReturn = if p = 0 then q.firstReturn else p
.firstReturn
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DyckWord.firstReturn.eq_1`：∀ (p : DyckWord),   p.firstReturn =     List.
findIdx       (fun i => decide (List.count DyckStep.U (List.take (i + 1) ↑p) = L
ist.count DyckS…
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `Nat.lt_add_right`：∀ {a b : ℕ} (c : ℕ), a < b → a < b + c
· 使用引理 `DyckWord.firstReturn_lt_length`：firstReturn_lt_length : p.firstReturn < 
p.toList.length
· 使用定理 `Nat.lt_trans`：∀ {n m k : ℕ}, n < m → m < k → n < k
· 使用定理 `List.findIdx_eq`：∀ {α : Type u_1} {p : α → Bool} {xs : List α} {i : ℕ} (
h : i < xs.length),   List.findIdx p xs = i ↔ p xs[i] = true ∧ ∀ (j : ℕ) (hji : 
j < i…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `List.getElem_range`：∀ {j n : ℕ} (h : j < (List.range n).length), (List.r
ange n)[j] = j
· 使用定理 `List.take_append`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, List.take i
 (l₁ ++ l₂) = List.take i l₁ ++ List.take (i - l₁.length) l₂
· 使用定理 `List.take_zero`：∀ {α : Type u} {l : List α}, List.take 0 l = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用引理 `DyckWord.count_take_firstReturn_add_one`：count_take_firstReturn_add_one 
: (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 
1)).count D
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `DyckWord.count_D_lt_count_U_of_lt_firstReturn`：count_D_lt_count_U_of_lt_
firstReturn {i : Nat} (hi : i < p.firstReturn) : (p.toList.take (i + 1)).count D
 < (p.toList.take (i + 1)).count U
-/
lemma firstReturn_add : (p + q).firstReturn = if p = 0 then q.firstReturn else p.firstReturn := by
  split_ifs with h; · simp [h]
  have u : (p + q).toList = p.toList ++ q.toList := rfl
  rw [firstReturn, findIdx_eq]
  · simp_rw [u, decide_eq_true_eq, getElem_range]
    have v := firstReturn_lt_length h
    constructor
    · rw [take_append, show p.firstReturn + 1 - p.toList.length = 0 by lia,
        take_zero, append_nil, count_take_firstReturn_add_one h]
    · intro j hj
      rw [take_append, show j + 1 - p.toList.length = 0 by lia,
        take_zero, append_nil]
      simpa using (count_D_lt_count_U_of_lt_firstReturn hj).ne'
  · rw [length_range, u, length_append]
    exact Nat.lt_add_right _ (firstReturn_lt_length h)

@[simp]
/-
**DyckWord.firstReturn_nest** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：firstReturn_nest : p.nest.firstReturn = p.toList.length + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DyckWord.firstReturn.eq_1`：∀ (p : DyckWord),   p.firstReturn =     List.
findIdx       (fun i => decide (List.count DyckStep.U (List.take (i + 1) ↑p) = L
ist.count DyckS…
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
· 使用定理 `Nat.lt_trans`：∀ {n m k : ℕ}, n < m → m < k → n < k
· 使用定理 `List.findIdx_eq`：∀ {α : Type u_1} {p : α → Bool} {xs : List α} {i : ℕ} (
h : i < xs.length),   List.findIdx p xs = i ↔ p xs[i] = true ∧ ∀ (j : ℕ) (hji : 
j < i…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `List.getElem_range`：∀ {j n : ℕ} (h : j < (List.range n).length), (List.r
ange n)[j] = j
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DyckWord.count_U_eq_count_D`：∀ (self : DyckWord), List.count DyckStep.U 
↑self = List.count DyckStep.D ↑self
· 使用定理 `List.count_cons`：∀ {α : Type u_1} [inst : BEq α] {a b : α} {l : List α},
   List.count a (b :: l) = List.count a l + if (b == a) = true then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `beq_self_eq_true`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] (a : α), (
a == a) = true
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `List.take_append`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, List.take i
 (l₁ ++ l₂) = List.take i l₁ ++ List.take (i - l₁.length) l₂
（共 33 条，此处仅展示前 30 条）
-/
lemma firstReturn_nest : p.nest.firstReturn = p.toList.length + 1 := by
  have u : p.nest.toList = U :: p.toList ++ [D] := rfl
  rw [firstReturn, findIdx_eq]
  · simp_rw [u, decide_eq_true_eq, getElem_range]
    constructor
    · rw [take_of_length_le (by simp), ← u, p.nest.count_U_eq_count_D]
    · intro j hj
      simp_rw [cons_append, take_succ_cons, count_cons, beq_self_eq_true, ite_true,
        beq_iff_eq, reduceCtorEq, ite_false, take_append,
        show j - p.toList.length = 0 by lia, take_zero, append_nil]
      have := p.count_D_le_count_U j
      simp only [add_zero, decide_eq_false_iff_not, ne_eq]
      lia
  · simp_rw [length_range, u, length_append, length_cons]
    exact Nat.lt_add_one _

variable (p) in
/-- The left part of the Dyck word decomposition,
inside the `U, D` pair that `firstReturn` refers to. `insidePart 0 = 0`. -/
/-
**DyckWord.insidePart** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：insidePart : DyckWord
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.count_take_firstReturn_add_one`：count_take_firstReturn_add_one 
: (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 
1)).count D

--- 原说明 ---
The left part of the Dyck word decomposition,
inside the `U, D` pair that `firstReturn` refers to. `insidePart 0 = 0`.
-/
def insidePart : DyckWord :=
  if h : p = 0 then 0 else
  (p.take (p.firstReturn + 1) (count_take_firstReturn_add_one h)).denest
    ⟨by rw [← toList_ne_nil, take]; simpa using toList_ne_nil.mpr h, fun i lb ub ↦ by
      simp only [take, length_take, lt_min_iff] at ub ⊢
      replace ub := ub.1
      rw [take_take, min_eq_left ub.le]
      rw [show i = i - 1 + 1 by lia] at ub ⊢
      rw [Nat.add_lt_add_iff_right] at ub
      exact count_D_lt_count_U_of_lt_firstReturn ub⟩

variable (p) in
/-- The right part of the Dyck word decomposition,
outside the `U, D` pair that `firstReturn` refers to. `outsidePart 0 = 0`. -/
/-
**DyckWord.outsidePart** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：outsidePart : DyckWord
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.count_take_firstReturn_add_one`：count_take_firstReturn_add_one 
: (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 
1)).count D

--- 原说明 ---
The right part of the Dyck word decomposition,
outside the `U, D` pair that `firstReturn` refers to. `outsidePart 0 = 0`.
-/
def outsidePart : DyckWord :=
  if h : p = 0 then 0 else p.drop (p.firstReturn + 1) (count_take_firstReturn_add_one h)
/-
**DyckWord.insidePart_zero** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：DyckWord.insidePart 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `DyckWord.count_take_firstReturn_add_one`：count_take_firstReturn_add_one 
: (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 
1)).count D
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma insidePart_zero : insidePart 0 = 0 := by simp [insidePart]
/-
**DyckWord.outsidePart_zero** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：DyckWord.outsidePart 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `DyckWord.count_take_firstReturn_add_one`：count_take_firstReturn_add_one 
: (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 
1)).count D
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma outsidePart_zero : outsidePart 0 = 0 := by simp [outsidePart]

include h in
@[simp]
/-
**DyckWord.insidePart_add** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：insidePart_add : (p + q).insidePart = p.insidePart
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.count_take_firstReturn_add_one`：count_take_firstReturn_add_one 
: (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 
1)).count D
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DyckWord.firstReturn_add`：firstReturn_add : (p + q).firstReturn = if p =
 0 then q.firstReturn else p.firstReturn
· 使用定理 `DyckWord.take.congr_simp`：∀ (p p_1 : DyckWord) (e_p : p = p_1) (i i_1 : 
ℕ) (e_i : i = i_1)   (hi : List.count DyckStep.U (List.take i ↑p) = List.count D
yckStep.D (Lis…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `DyckWord.denest.congr_simp`：∀ (p p_1 : DyckWord) (e_p : p = p_1) (hn : p
.IsNested), p.denest hn = p_1.denest ⋯
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false`：¬False
· 使用定理 `List.take_append_of_le_length`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}
, i ≤ l₁.length → List.take i (l₁ ++ l₂) = List.take i l₁
· 使用引理 `DyckWord.firstReturn_lt_length`：firstReturn_lt_length : p.firstReturn < 
p.toList.length
-/
lemma insidePart_add : (p + q).insidePart = p.insidePart := by
  simp_rw [insidePart, firstReturn_add, add_eq_zero', h, false_and, dite_false, ite_false,
    DyckWord.ext_iff, take]
  congr 3
  exact take_append_of_le_length (firstReturn_lt_length h)

include h in
@[simp]
/-
**DyckWord.outsidePart_add** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：outsidePart_add : (p + q).outsidePart = p.outsidePart + q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.count_take_firstReturn_add_one`：count_take_firstReturn_add_one 
: (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 
1)).count D
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DyckWord.firstReturn_add`：firstReturn_add : (p + q).firstReturn = if p =
 0 then q.firstReturn else p.firstReturn
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `DyckWord.drop.congr_simp`：∀ (p p_1 : DyckWord) (e_p : p = p_1) (i i_1 : 
ℕ) (e_i : i = i_1)   (hi : List.count DyckStep.U (List.take i ↑p) = List.count D
yckStep.D (Lis…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false`：¬False
· 使用定理 `List.drop_append_of_le_length`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}
, i ≤ l₁.length → List.drop i (l₁ ++ l₂) = List.drop i l₁ ++ l₂
· 使用引理 `DyckWord.firstReturn_lt_length`：firstReturn_lt_length : p.firstReturn < 
p.toList.length
-/
lemma outsidePart_add : (p + q).outsidePart = p.outsidePart + q := by
  simp_rw [outsidePart, firstReturn_add, add_eq_zero', h, false_and, dite_false, ite_false,
    DyckWord.ext_iff, drop]
  exact drop_append_of_le_length (firstReturn_lt_length h)

@[simp]
/-
**DyckWord.insidePart_nest** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：insidePart_nest : p.nest.insidePart = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.count_take_firstReturn_add_one`：count_take_firstReturn_add_one 
: (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 
1)).count D
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `not_false`：¬False
· 使用引理 `DyckWord.firstReturn_nest`：firstReturn_nest : p.nest.firstReturn = p.toL
ist.length + 1
· 使用定理 `DyckWord.take.congr_simp`：∀ (p p_1 : DyckWord) (e_p : p = p_1) (i i_1 : 
ℕ) (e_i : i = i_1)   (hi : List.count DyckStep.U (List.take i ↑p) = List.count D
yckStep.D (Lis…
· 使用定理 `DyckWord.denest.congr_simp`：∀ (p p_1 : DyckWord) (e_p : p = p_1) (hn : p
.IsNested), p.denest hn = p_1.denest ⋯
· 使用定理 `DyckWord.IsNested.nest`：∀ {p : DyckWord}, p.nest.IsNested
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DyckWord.ext_iff`：∀ {x y : DyckWord}, x = y ↔ ↑x = ↑y
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用引理 `DyckWord.denest_nest`：denest_nest : p.nest.denest .nest = p
-/
lemma insidePart_nest : p.nest.insidePart = p := by
  simp_rw [insidePart, nest_ne_zero, dite_false, firstReturn_nest]
  convert! p.denest_nest; rw [DyckWord.ext_iff]; apply take_of_length_le
  simp_rw [nest, length_append, length_singleton]; lia

@[simp]
/-
**DyckWord.outsidePart_nest** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：outsidePart_nest : p.nest.outsidePart = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.count_take_firstReturn_add_one`：count_take_firstReturn_add_one 
: (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 
1)).count D
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `not_false`：¬False
· 使用引理 `DyckWord.firstReturn_nest`：firstReturn_nest : p.nest.firstReturn = p.toL
ist.length + 1
· 使用定理 `DyckWord.drop.congr_simp`：∀ (p p_1 : DyckWord) (e_p : p = p_1) (i i_1 : 
ℕ) (e_i : i = i_1)   (hi : List.count DyckStep.U (List.take i ↑p) = List.count D
yckStep.D (Lis…
· 使用定理 `DyckWord.ext_iff`：∀ {x y : DyckWord}, x = y ↔ ↑x = ↑y
· 使用定理 `List.drop_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.drop i l = []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
-/
lemma outsidePart_nest : p.nest.outsidePart = 0 := by
  simp_rw [outsidePart, nest_ne_zero, dite_false, firstReturn_nest]
  rw [DyckWord.ext_iff]; apply drop_of_length_le
  simp_rw [nest, length_append, length_singleton]; lia

set_option backward.isDefEq.respectTransparency false in
include h in
@[simp]
/-
**DyckWord.nest_insidePart_add_outsidePart** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：nest_insidePart_add_outsidePart : p.insidePart.nest + p.outsidePart = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.count_take_firstReturn_add_one`：count_take_firstReturn_add_one 
: (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 
1)).count D
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `not_false`：¬False
· 使用引理 `DyckWord.nest_denest`：nest_denest (hn) : (p.denest hn).nest = p
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
-/
theorem nest_insidePart_add_outsidePart : p.insidePart.nest + p.outsidePart = p := by
  simp_rw [insidePart, outsidePart, h, dite_false, nest_denest, DyckWord.ext_iff]
  apply take_append_drop

include h in
/-
**DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one** 是 Mathlib 
中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：semilength_insidePart_add_semilength_outsidePart_add_one : p.insidePart.se
milength + p.outsidePart.semilength + 1 = p.semilength
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DyckWord.nest_insidePart_add_outsidePart`：nest_insidePart_add_outsidePar
t : p.insidePart.nest + p.outsidePart = p
· 使用定理 `DyckWord.semilength_add`：∀ {p q : DyckWord}, (p + q).semilength = p.semi
length + q.semilength
· 使用定理 `DyckWord.semilength_nest`：∀ {p : DyckWord}, p.nest.semilength = p.semile
ngth + 1
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
-/
lemma semilength_insidePart_add_semilength_outsidePart_add_one :
    p.insidePart.semilength + p.outsidePart.semilength + 1 = p.semilength := by
  rw [← congrArg semilength (nest_insidePart_add_outsidePart h), semilength_add, semilength_nest,
    add_right_comm]

include h in
/-
**DyckWord.semilength_insidePart_lt** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：semilength_insidePart_lt : p.insidePart.semilength < p.semilength
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one`：semil
ength_insidePart_add_semilength_outsidePart_add_one : p.insidePart.semilength + 
p.outsidePart.semilength + 1 = p.semilength
-/
theorem semilength_insidePart_lt : p.insidePart.semilength < p.semilength := by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  lia

include h in
/-
**DyckWord.semilength_outsidePart_lt** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：semilength_outsidePart_lt : p.outsidePart.semilength < p.semilength
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one`：semil
ength_insidePart_add_semilength_outsidePart_add_one : p.insidePart.semilength + 
p.outsidePart.semilength + 1 = p.semilength
-/
theorem semilength_outsidePart_lt : p.outsidePart.semilength < p.semilength := by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  lia

end FirstReturn

section Order

/-
**DyckWord.** 是 Mathlib 中的一个实例，位于命名空间 `DyckWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder DyckWord where
  le := Relation.ReflTransGen (fun p q ↦ p = q.insidePart ∨ p = q.outsidePart)
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
/-
**DyckWord.le_add_self** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：le_add_self (p q : DyckWord) : q <= p + q
参数：p q : DyckWord。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DyckWord.le_add_self._unary`：∀ (q p : DyckWord), q ≤ p + q
-/
lemma le_add_self (p q : DyckWord) : q ≤ p + q := by
  by_cases h : p = 0
  · simp [h]
  · have := semilength_outsidePart_lt h
    exact (le_add_self p.outsidePart q).trans
      (Relation.ReflTransGen.single (Or.inr (outsidePart_add h).symm))
termination_by p.semilength

variable (p) in protected lemma zero_le : 0 ≤ p := add_zero p ▸ le_add_self p 0
/-
**DyckWord.infix_of_le** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：infix_of_le (h : p <= q) : p.toList <:+: q.toList
参数：h : p <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.infix_refl`：∀ {α : Type u_1} (l : List α), l <:+: l
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `DyckWord.outsidePart_zero`：DyckWord.outsidePart 0 = 0
· 使用定理 `DyckWord.insidePart_zero`：DyckWord.insidePart 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DyckWord.ext_iff`：∀ {x y : DyckWord}, x = y ↔ ↑x = ↑y
· 使用定理 `DyckWord.nest_insidePart_add_outsidePart`：nest_insidePart_add_outsidePar
t : p.insidePart.nest + p.outsidePart = p
-/
lemma infix_of_le (h : p ≤ q) : p.toList <:+: q.toList := by
  induction h with
  | refl => exact infix_refl _
  | tail _pm mq ih =>
    rename_i m r
    rcases eq_or_ne r 0 with rfl | hr
    · rw [insidePart_zero, outsidePart_zero, or_self] at mq
      rwa [mq] at ih
    · have : [U] ++ r.insidePart ++ [D] ++ r.outsidePart = r :=
        DyckWord.ext_iff.mp (nest_insidePart_add_outsidePart hr)
      grind
/-
**DyckWord.le_of_suffix** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：le_of_suffix (h : p.toList <:+ q.toList) : p <= q
参数：h : p.toList <:+ q.toList。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DyckWord.count_U_eq_count_D`：∀ (self : DyckWord), List.count DyckStep.U 
↑self = List.count DyckStep.D ↑self
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `List.take_left'`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, l₁.length = 
i → List.take i (l₁ ++ l₂) = l₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_right_cancel_iff`：∀ {m k n : ℕ}, m + n = k + n ↔ m = k
· 使用定理 `List.count_append`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l₁ l₂ : List
 α}, List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂
· 使用定理 `DyckWord.ext`：∀ {x y : DyckWord}, ↑x = ↑y → x = y
· 使用引理 `DyckWord.le_add_self`：le_add_self (p q : DyckWord) : q <= p + q
-/
lemma le_of_suffix (h : p.toList <:+ q.toList) : p ≤ q := by
  obtain ⟨r', h⟩ := h
  have hc : (q.toList.take (q.toList.length - p.toList.length)).count U =
      (q.toList.take (q.toList.length - p.toList.length)).count D := by
    have hq := q.count_U_eq_count_D
    rw [← h] at hq ⊢
    rw [count_append, count_append, p.count_U_eq_count_D, Nat.add_right_cancel_iff] at hq
    simp [hq]
  let r : DyckWord := q.take _ hc
  have e : r' = r := by
    simp_rw [r, take, ← h, length_append, add_tsub_cancel_right, take_left']
  rw [e] at h; replace h : r + p = q := DyckWord.ext h; rw [← h]; exact le_add_self ..

/-- Partial order on Dyck words: `p ≤ q` if a (possibly empty) sequence of
`insidePart` and `outsidePart` operations can turn `q` into `p`. -/
/-
**DyckWord.** 是 Mathlib 中的一个实例，位于命名空间 `DyckWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partial order on Dyck words: `p ≤ q` if a (possibly empty) sequence of
`insidePart` and `outsidePart` operations can turn `q` into `p`.
-/
instance : PartialOrder DyckWord where
  le_antisymm p q pq qp := by
    have h₁ := infix_of_le pq
    have h₂ := infix_of_le qp
    exact DyckWord.ext <| h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le
/-
**DyckWord.pos_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：∀ {p : DyckWord}, 0 < p ↔ p ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `ne_iff_lt_iff_le`：ne_iff_lt_iff_le : (a != b ↔ a < b) ↔ a <= b
· 使用定理 `DyckWord.zero_le`：∀ (p : DyckWord), 0 ≤ p
-/
protected lemma pos_iff_ne_zero : 0 < p ↔ p ≠ 0 := by
  rw [ne_comm, iff_comm, ne_iff_lt_iff_le]
  exact DyckWord.zero_le p
/-
**DyckWord.monotone_semilength** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：monotone_semilength : Monotone semilength
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `DyckWord.outsidePart_zero`：DyckWord.outsidePart 0 = 0
· 使用定理 `DyckWord.insidePart_zero`：DyckWord.insidePart 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `DyckWord.semilength_insidePart_lt`：semilength_insidePart_lt : p.insidePa
rt.semilength < p.semilength
· 使用定理 `DyckWord.semilength_outsidePart_lt`：semilength_outsidePart_lt : p.outsid
ePart.semilength < p.semilength
-/
lemma monotone_semilength : Monotone semilength := fun p q pq ↦ by
  induction pq with
  | refl => rfl
  | tail _ mq ih =>
    rename_i m r _
    rcases eq_or_ne r 0 with rfl | hr
    · rw [insidePart_zero, outsidePart_zero, or_self] at mq
      rwa [mq] at ih
    · rcases mq with hm | hm
      · exact ih.trans (hm ▸ semilength_insidePart_lt hr).le
      · exact ih.trans (hm ▸ semilength_outsidePart_lt hr).le
/-
**DyckWord.strictMono_semilength** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：strictMono_semilength : StrictMono semilength
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `DyckWord.monotone_semilength`：monotone_semilength : Monotone semilength
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DyckWord.ext`：∀ {x y : DyckWord}, ↑x = ↑y → x = y
· 使用定理 `List.IsInfix.eq_of_length`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+: l₂
 → l₁.length = l₂.length → l₁ = l₂
· 使用引理 `DyckWord.infix_of_le`：infix_of_le (h : p <= q) : p.toList <:+: q.toList
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `DyckWord.two_mul_semilength_eq_length`：two_mul_semilength_eq_length : 2 
* p.semilength = p.toList.length
-/
lemma strictMono_semilength : StrictMono semilength := fun p q pq ↦ by
  obtain ⟨plq, pnq⟩ := lt_iff_le_and_ne.mp pq
  apply lt_of_le_of_ne (monotone_semilength plq)
  contrapose pnq
  replace pnq := congr(2 * $(pnq))
  simp_rw [two_mul_semilength_eq_length] at pnq
  exact DyckWord.ext ((infix_of_le plq).eq_of_length pnq)

end Order

section BinaryTree

open BinaryTree

/-- Convert a Dyck word to a binary rooted tree.

`f(0) = nil`. For a nonzero word find the `D` that matches the initial `U`,
which has index `p.firstReturn`, then let `x` be everything strictly between said `U` and `D`,
and `y` be everything strictly after said `D`. `p = x.nest + y` with `x, y` (possibly empty)
Dyck words. `f(p) = f(x) △ f(y)`, where △ (defined in `Mathlib/Data/Tree/Basic.lean`) joins two
subtrees to a new root node. -/
/-
**DyckWord.toTree** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：toTree (p : DyckWord) : BinaryTree Unit
参数：p : DyckWord。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a Dyck word to a binary rooted tree.

`f(0) = nil`. For a nonzero word find the `D` that matches the initial `U`,
which has index `p.firstReturn`, then let `x` be everything strictly between sai
d `U` and `D`,
and `y` be everything strictly after said `D`. `p = x.nest + y` with `x, y` (pos
sibly empty)
Dyck words. `f(p) = f(x) △ f(y)`, where △ (defined in `Mathlib/Data/Tree/Basic.l
ean`) joins two
subtrees to a new root node.
-/
def toTree (p : DyckWord) : BinaryTree Unit :=
  if p = 0 then nil else p.insidePart.toTree △ p.outsidePart.toTree
termination_by p.semilength
decreasing_by exacts [semilength_insidePart_lt ‹_›, semilength_outsidePart_lt ‹_›]

/-- Convert a binary rooted tree to a Dyck word.

`g(nil) = 0`. A nonempty tree with left subtree `l` and right subtree `r`
is sent to `g(l).nest + g(r)`. -/
/-
**DyckWord.ofTree** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：BinaryTree Unit → DyckWord
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a binary rooted tree to a Dyck word.

`g(nil) = 0`. A nonempty tree with left subtree `l` and right subtree `r`
is sent to `g(l).nest + g(r)`.
-/
def ofTree : BinaryTree Unit → DyckWord
  | BinaryTree.nil => 0
  | BinaryTree.node _ l r => (ofTree l).nest + ofTree r
/-
**DyckWord.ofTree_toTree** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：ofTree_toTree (p) : ofTree p.toTree = p
参数：p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DyckWord.toTree.eq_1`：∀ (p : DyckWord),   p.toTree = if p = 0 then Binar
yTree.nil else BinaryTree.node () p.insidePart.toTree p.outsidePart.toTree
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DyckWord.ofTree.eq_1`：DyckWord.ofTree BinaryTree.nil = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `DyckWord.semilength_insidePart_lt`：semilength_insidePart_lt : p.insidePa
rt.semilength < p.semilength
· 使用定理 `DyckWord.semilength_outsidePart_lt`：semilength_outsidePart_lt : p.outsid
ePart.semilength < p.semilength
· 使用定理 `DyckWord.nest_insidePart_add_outsidePart`：nest_insidePart_add_outsidePar
t : p.insidePart.nest + p.outsidePart = p
-/
lemma ofTree_toTree (p) : ofTree p.toTree = p := by
  by_cases h : p = 0
  · simp [h, toTree, ofTree]
  · rw [toTree]
    simp_rw [h, ite_false, ofTree]
    rw [ofTree_toTree p.insidePart, ofTree_toTree p.outsidePart]
    exact nest_insidePart_add_outsidePart h
termination_by p.semilength
decreasing_by exacts [semilength_insidePart_lt h, semilength_outsidePart_lt h]
/-
**DyckWord.toTree_ofTree** 是 Mathlib 中的一个定理，位于命名空间 `DyckWord`。
形式化陈述：∀ (t : BinaryTree Unit), (DyckWord.ofTree t).toTree = t
参数：t : BinaryTree Unit；DyckWord.ofTree t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toTree_ofTree : ∀ t, (ofTree t).toTree = t
  | BinaryTree.nil => by simp [ofTree, toTree]
  | BinaryTree.node _ _ _ => by simp [ofTree, toTree, toTree_ofTree]

/-- Equivalence between Dyck words and rooted binary trees. -/
/-
**DyckWord.equivTree** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：DyckWord ≃ BinaryTree Unit
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `DyckWord.ofTree_toTree`：ofTree_toTree (p) : ofTree p.toTree = p
· 使用定理 `DyckWord.toTree_ofTree`：∀ (t : BinaryTree Unit), (DyckWord.ofTree t).toT
ree = t

--- 原说明 ---
Equivalence between Dyck words and rooted binary trees.
-/
@[simps] def equivTree : DyckWord ≃ BinaryTree Unit where
  toFun := toTree
  invFun := ofTree
  left_inv := ofTree_toTree
  right_inv := toTree_ofTree

@[simp]
/-
**DyckWord.numNodes_toTree** 是 Mathlib 中的一个引理，位于命名空间 `DyckWord`。
形式化陈述：numNodes_toTree (p : DyckWord) : p.toTree.numNodes = p.semilength
参数：p : DyckWord。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DyckWord.toTree.eq_1`：∀ (p : DyckWord),   p.toTree = if p = 0 then Binar
yTree.nil else BinaryTree.node () p.insidePart.toTree p.outsidePart.toTree
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `BinaryTree.numNodes.eq_1`：∀ {α : Type u}, BinaryTree.nil.numNodes = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one`：semil
ength_insidePart_add_semilength_outsidePart_add_one : p.insidePart.semilength + 
p.outsidePart.semilength + 1 = p.semilength
· 使用定理 `DyckWord.semilength_insidePart_lt`：semilength_insidePart_lt : p.insidePa
rt.semilength < p.semilength
· 使用定理 `DyckWord.semilength_outsidePart_lt`：semilength_outsidePart_lt : p.outsid
ePart.semilength < p.semilength
-/
lemma numNodes_toTree (p : DyckWord) : p.toTree.numNodes = p.semilength := by
  by_cases h : p = 0
  · simp [h, toTree]
  · rw [toTree]
    simp_rw [h, ite_false, numNodes]
    rw [← semilength_insidePart_add_semilength_outsidePart_add_one h,
      numNodes_toTree p.insidePart, numNodes_toTree p.outsidePart]
termination_by p.semilength
decreasing_by exacts [semilength_insidePart_lt h, semilength_outsidePart_lt h]

@[deprecated (since := "2026-02-03")] alias semilength_eq_numNodes_equivTree := numNodes_toTree

/-- Equivalence between Dyck words of semilength `n` and rooted binary trees with
`n` internal nodes. -/
@[simps!]
/-
**DyckWord.equivTreesOfNumNodesEq** 是 Mathlib 中的一个定义，位于命名空间 `DyckWord`。
形式化陈述：equivTreesOfNumNodesEq (n : Nat) : { p : DyckWord // p.semilength = n } ≃ 
treesOfNumNodesEq n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between Dyck words of semilength `n` and rooted binary trees with
`n` internal nodes.
-/
def equivTreesOfNumNodesEq (n : ℕ) : { p : DyckWord // p.semilength = n } ≃ treesOfNumNodesEq n :=
  equivTree.subtypeEquiv (by simp)
/-
**DyckWord.** 是 Mathlib 中的一个实例，位于命名空间 `DyckWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} : Fintype { p : DyckWord // p.semilength = n } :=
  Fintype.ofEquiv _ (equivTreesOfNumNodesEq n).symm

/-- There are `catalan n` Dyck words of semilength `n` (or length `2 * n`). -/
/-
**DyckWord.card_dyckWord_semilength_eq_catalan** 是 Mathlib 中的一个定理，位于命名空间 `DyckWo
rd`。
形式化陈述：card_dyckWord_semilength_eq_catalan (n : Nat) : Fintype.card { p : DyckWor
d // p.semilength = n } = catalan n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `BinaryTree.treesOfNumNodesEq_card_eq_catalan`：treesOfNumNodesEq_card_eq_
catalan (n : Nat) : #(treesOfNumNodesEq n) = catalan n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s

--- 原说明 ---
There are `catalan n` Dyck words of semilength `n` (or length `2 * n`).
-/
theorem card_dyckWord_semilength_eq_catalan (n : ℕ) :
    Fintype.card { p : DyckWord // p.semilength = n } = catalan n := by
  rw [← Fintype.ofEquiv_card (equivTreesOfNumNodesEq n), ← treesOfNumNodesEq_card_eq_catalan]
  convert! Fintype.card_coe _

end BinaryTree

end DyckWord

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `p.firstReturn` is positive if `p` is nonzero. -/
@[positivity DyckWord.firstReturn _]
meta def evalDyckWordFirstReturn : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(DyckWord.firstReturn $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(DyckWord.firstReturn_pos ($pa).ne'))
    | .nonzero pa => pure (.positive q(DyckWord.firstReturn_pos $pa))
    | _ => pure .none
  | _, _, _ => throwError "not DyckWord.firstReturn"

end Mathlib.Meta.Positivity

