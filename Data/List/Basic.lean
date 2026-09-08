/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Data.List.Monad
public import Mathlib.Logic.OpClass
public import Mathlib.Logic.Unique
public import Mathlib.Tactic.Common
public import Batteries.Data.List.Lemmas
public import Batteries.Tactic.Lint.Simp
public import Batteries.Tactic.SeqFocus
public import Mathlib.Data.Subtype
public import Mathlib.Tactic.Attr.Core

/-!
# Basic properties of lists
-/

public section

assert_not_exists Lattice
assert_not_exists Monoid
assert_not_exists Preorder
assert_not_exists Prod.swap_eq_iff_eq_swap
assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l l₁ l₂ : List α}

/-- There is only one list of an empty type -/
/-
**List.uniqueOfIsEmpty** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：uniqueOfIsEmpty [IsEmpty α] : Unique (List α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is only one list of an empty type
-/
instance uniqueOfIsEmpty [IsEmpty α] : Unique (List α) :=
  { instInhabitedList with
    uniq := fun l =>
      match l with
      | [] => rfl
      | a :: _ => isEmptyElim a }
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.LawfulIdentity (α := List α) Append.append [] where
  left_id := nil_append
  right_id := append_nil
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Associative (α := List α) Append.append where
  assoc := append_assoc
/-
**List.cons_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {a : α}, Function.Injective (List.cons a)
参数：List.cons a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.tail_eq_of_cons_eq`：∀ {α : Type u_1} {h₁ : α} {t₁ : List α} {h₂ : α
} {t₂ : List α}, h₁ :: t₁ = h₂ :: t₂ → t₁ = t₂
-/
@[simp] theorem cons_injective {a : α} : Injective (cons a) := fun _ _ => tail_eq_of_cons_eq
/-
**List.singleton_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：singleton_injective : Injective fun a : α => [a]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.cons_eq_cons`：∀ {α : Type u_1} {a b : α} {l l' : List α}, a :: l = 
b :: l' ↔ a = b ∧ l = l'
-/
theorem singleton_injective : Injective fun a : α => [a] := fun _ _ h => (cons_eq_cons.1 h).1
/-
**List.setOfPred_mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：setOfPred_mem_cons (l : List α) (a : α) : { x | x in a :: l } = insert a {
 x | x in l }
参数：l : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
-/
theorem setOfPred_mem_cons (l : List α) (a : α) : { x | x ∈ a :: l } = insert a { x | x ∈ l } :=
  Set.ext fun _ => mem_cons

@[deprecated (since := "2026-07-13")] alias set_of_mem_cons := setOfPred_mem_cons

/-! ### mem -/

/-
**List._root_.Decidable.List.eq_or_ne_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### mem
-/
theorem _root_.Decidable.List.eq_or_ne_mem_of_mem [DecidableEq α]
    {a b : α} {l : List α} (h : a ∈ b :: l) : a = b ∨ a ≠ b ∧ a ∈ l := by
  by_cases hab : a = b
  · exact Or.inl hab
  · exact ((List.mem_cons.1 h).elim Or.inl (fun h => Or.inr ⟨hab, h⟩))
/-
**List.mem_pair** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：mem_pair {a b c : α} : a in [b, c] ↔ a = b ∨ a = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `List.mem_singleton`：∀ {α : Type u_1} {a b : α}, a ∈ [b] ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_pair {a b c : α} : a ∈ [b, c] ↔ a = b ∨ a = c := by
  rw [mem_cons, mem_singleton]

@[simp 1100]
/-
**List.mem_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_map_of_injective {f : α -> β} (H : Injective f) {a : α} {l : List α} :
 f a in map f l ↔ a in l
参数：H : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.exists_of_mem_map`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} 
{l : List α} {b : α_1}, b ∈ List.map f l → ∃ a ∈ l, f a = b
· 使用定理 `List.mem_map_of_mem`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {a : α
} {f : α → β}, a ∈ l → f a ∈ List.map f l
-/
theorem mem_map_of_injective {f : α → β} (H : Injective f) {a : α} {l : List α} :
    f a ∈ map f l ↔ a ∈ l :=
  ⟨fun m => let ⟨_, m', e⟩ := exists_of_mem_map m; H e ▸ m', mem_map_of_mem⟩

@[simp]
/-
**List._root_.Function.Involutive.exists_mem_and_apply_eq_iff** 是 Mathlib 中的一个定理
，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Involutive.exists_mem_and_apply_eq_iff {f : α → α}
    (hf : Function.Involutive f) (x : α) (l : List α) : (∃ y : α, y ∈ l ∧ f y = x) ↔ f x ∈ l :=
  ⟨by rintro ⟨y, h, rfl⟩; rwa [hf y], fun h => ⟨f x, h, hf _⟩⟩
/-
**List.mem_map_of_involutive** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_map_of_involutive {f : α -> α} (hf : Involutive f) {a : α} {l : List α
} : a in map f l ↔ f a in l
参数：hf : Involutive f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Function.Involutive.exists_mem_and_apply_eq_iff`：∀ {α : Type u} {f : α →
 α}, Function.Involutive f → ∀ (x : α) (l : List α), (∃ y ∈ l, f y = x) ↔ f x ∈ 
l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map_of_involutive {f : α → α} (hf : Involutive f) {a : α} {l : List α} :
    a ∈ map f l ↔ f a ∈ l := by rw [mem_map, hf.exists_mem_and_apply_eq_iff]

/-! ### length -/

alias ⟨_, length_pos_of_ne_nil⟩ := length_pos_iff

/-
**List.length_pos_iff_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l != []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ne_nil_of_length_pos`：∀ {α : Type u_1} {l : List α}, 0 < l.length →
 l ≠ []
· 使用定理 `List.length_pos_of_ne_nil`：∀ {α : Type u_1} {l : List α}, l ≠ [] → 0 < l
.length
-/
theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
  ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩
/-
**List.exists_of_length_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {n : ℕ} (l : List α), l.length = n + 1 → ∃ h t, l = h :: t
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem exists_of_length_succ {n} : ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t
  | [], H => absurd H.symm <| succ_ne_zero n
  | h :: t, _ => ⟨h, t, rfl⟩
/-
**List.length_eq_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_eq_succ_iff {n} {l : List α} : l.length = n + 1 ↔ exists h t, h :: 
t = l ∧ t.length = n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_eq_succ_iff {n} {l : List α} :
    l.length = n + 1 ↔ ∃ h t, h :: t = l ∧ t.length = n := by
  grind [cases List]
/-
**List.length_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u}, Function.Injective List.length ↔ Subsingleton α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
@[simp] lemma length_injective_iff : Injective (List.length : List α → ℕ) ↔ Subsingleton α := by
  constructor
  · intro h; refine ⟨fun x y => ?_⟩; (suffices [x] = [y] by simpa using this); apply h; rfl
  · intro hα l1 l2 hl
    induction l1 generalizing l2 <;> cases l2
    · rfl
    · cases hl
    · cases hl
    · next ih _ _ =>
      congr
      · subsingleton
      · apply ih; simpa using hl

@[simp default + 1] -- Raise priority above `length_injective_iff`.
/-
**List.length_injective** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：length_injective [Subsingleton α] : Injective (length : List α -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.length_injective_iff`：∀ {α : Type u}, Function.Injective List.lengt
h ↔ Subsingleton α
-/
lemma length_injective [Subsingleton α] : Injective (length : List α → ℕ) :=
  length_injective_iff.mpr inferInstance
/-
**List.length_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_eq_two {l : List α} : l.length = 2 ↔ exists a b, l = [a, b]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
  ⟨fun _ => let [a, b] := l; ⟨a, b, rfl⟩, fun ⟨_, _, e⟩ => e ▸ rfl⟩
/-
**List.length_eq_two'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_eq_two' {l : List α} (h : l != []) : l.length = 2 ↔ l = [l.head h, 
l.getLast h]
参数：h : l != []。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_eq_two`：length_eq_two {l : List α} : l.length = 2 ↔ exists a
 b, l = [a, b]
-/
theorem length_eq_two' {l : List α} (h : l ≠ []) : l.length = 2 ↔ l = [l.head h, l.getLast h] := by
  rw [length_eq_two]; grind
/-
**List.length_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_eq_three {l : List α} : l.length = 3 ↔ exists a b c, l = [a, b, c]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
  ⟨fun _ => let [a, b, c] := l; ⟨a, b, c, rfl⟩, fun ⟨_, _, _, e⟩ => e ▸ rfl⟩
/-
**List.length_eq_four** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_eq_four {l : List α} : l.length = 4 ↔ exists a b c d, l = [a, b, c,
 d]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem length_eq_four {l : List α} : l.length = 4 ↔ ∃ a b c d, l = [a, b, c, d] :=
  ⟨fun _ => let [a, b, c, d] := l; ⟨a, b, c, d, rfl⟩, fun ⟨_, _, _, _, e⟩ => e ▸ rfl⟩

/-! ### set-theoretic notation of lists -/

/-
**List.instSingletonList** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：instSingletonList : Singleton α (List α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### set-theoretic notation of lists
-/
instance instSingletonList : Singleton α (List α) := ⟨fun x => [x]⟩
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : Insert α (List α) := ⟨List.insert⟩
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : LawfulSingleton α (List α) :=
  { insert_empty_eq := fun x =>
      show (if x ∈ ([] : List α) then [] else [x]) = [x] from if_neg not_mem_nil }
/-
**List.singleton_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：singleton_eq (x : α) : ({x} : List α) = [x]
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_eq (x : α) : ({x} : List α) = [x] :=
  rfl
/-
**List.insert_neg** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) : Insert.inser
t x l = x :: l
参数：h : x ∉ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.insert_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a
 : α} {l : List α}, a ∉ l → List.insert a l = a :: l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) :
    Insert.insert x l = x :: l :=
  insert_of_not_mem h
/-
**List.insert_pos** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insert_pos [DecidableEq α] {x : α} {l : List α} (h : x in l) : Insert.inse
rt x l = l
参数：h : x in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.insert_of_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, a ∈ l → List.insert a l = l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem insert_pos [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) : Insert.insert x l = l :=
  insert_of_mem h
/-
**List.doubleton_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：doubleton_eq [DecidableEq α] {x y : α} (h : x != y) : ({x, y} : List α) = 
[x, y]
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.insert_neg`：insert_neg [DecidableEq α] {x : α} {l : List α} (h : x 
∉ l) : Insert.insert x l = x :: l
· 使用定理 `List.singleton_eq`：singleton_eq (x : α) : ({x} : List α) = [x]
· 使用定理 `List.mem_singleton`：∀ {α : Type u_1} {a b : α}, a ∈ [b] ↔ a = b
-/
theorem doubleton_eq [DecidableEq α] {x y : α} (h : x ≠ y) : ({x, y} : List α) = [x, y] := by
  rw [insert_neg, singleton_eq]
  rwa [singleton_eq, mem_singleton]

/-! ### bounded quantifiers over lists -/

/-
**List.forall_mem_of_forall_mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_mem_of_forall_mem_cons {p : α -> Prop} {a : α} {l : List α} (h : fo
rall x in a :: l, p x) : forall x in l, p x
参数：h : forall x in a :: l, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.forall_mem_cons`：∀ {α : Type u_1} {p : α → Prop} {a : α} {l : List 
α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x

--- 原说明 ---
### bounded quantifiers over lists
-/
theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α} (h : ∀ x ∈ a :: l, p x) :
    ∀ x ∈ l, p x := (forall_mem_cons.1 h).2
/-
**List.exists_mem_cons_of** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：exists_mem_cons_of {p : α -> Prop} {a : α} (l : List α) (h : p a) : exists
 x in a :: l, p x
参数：l : List α；h : p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
-/
theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) : ∃ x ∈ a :: l, p x :=
  ⟨a, mem_cons_self, h⟩
/-
**List.exists_mem_cons_of_exists** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：exists_mem_cons_of_exists {p : α -> Prop} {a : α} {l : List α} : (exists x
 in l, p x) -> exists x in a :: l, p x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ l, p x) →
    ∃ x ∈ a :: l, p x :=
  fun ⟨x, xl, px⟩ => ⟨x, mem_cons_of_mem _ xl, px⟩
/-
**List.or_exists_of_exists_mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：or_exists_of_exists_mem_cons {p : α -> Prop} {a : α} {l : List α} : (exist
s x in a :: l, p x) -> p a ∨ exists x in l, p x
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ a :: l, p x) →
    p a ∨ ∃ x ∈ l, p x := by grind
/-
**List.exists_mem_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：exists_mem_cons_iff (p : α -> Prop) (a : α) (l : List α) : (exists x in a 
:: l, p x) ↔ p a ∨ exists x in l, p x
参数：p : α -> Prop；a : α；l : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x := by grind

/-! ### list subset -/

/-
**List.cons_subset_of_subset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_subset_of_subset_of_mem {a : α} {l m : List α} (ainm : a in m) (lsubm
 : l subseteq m) : a::l subseteq m
参数：ainm : a in m；lsubm : l subseteq m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.cons_subset`：∀ {α : Type u_1} {a : α} {l m : List α}, a :: l ⊆ m ↔ 
a ∈ m ∧ l ⊆ m

--- 原说明 ---
### list subset
-/
theorem cons_subset_of_subset_of_mem {a : α} {l m : List α}
    (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m :=
  cons_subset.2 ⟨ainm, lsubm⟩
/-
**List.append_subset_of_subset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ subseteq
 l) (l₂subl : l₂ subseteq l) : l₁ ++ l₂ subseteq l
参数：l₁subl : l₁ subseteq l；l₂subl : l₂ subseteq l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_append`：∀ {α : Type u_1} {a : α} {s t : List α}, a ∈ s ++ t ↔ a
 ∈ s ∨ a ∈ t
-/
theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
    l₁ ++ l₂ ⊆ l :=
  fun _ h ↦ (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)
/-
**List.map_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_subset_iff {l₁ l₂ : List α} (f : α -> β) (h : Injective f) : map f l₁ 
subseteq map f l₂ ↔ l₁ subseteq l₂
参数：f : α -> β；h : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `List.mem_map_of_mem`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {a : α
} {f : α → β}, a ∈ l → f a ∈ List.map f l
· 使用定理 `List.map_subset`：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α} (f : α
 → β), l₁ ⊆ l₂ → List.map f l₁ ⊆ List.map f l₂
-/
theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : Injective f) :
    map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ := by
  refine ⟨?_, map_subset f⟩; intro h2 x hx
  rcases mem_map.1 (h2 (mem_map_of_mem hx)) with ⟨x', hx', hxx'⟩
  cases h hxx'; exact hx'
/-
**List.notMem_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：notMem_of_subset (h : l subseteq l₁) {a : α} (ha : a ∉ l₁) : a ∉ l
参数：h : l subseteq l₁；ha : a ∉ l₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma notMem_of_subset (h : l ⊆ l₁) {a : α} (ha : a ∉ l₁) : a ∉ l := (ha <| h ·)

/-! ### append -/

/-
**List.append_eq_has_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### append
-/
theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ :=
  rfl
/-
**List.append_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：append_right_injective (s : List α) : Injective fun t => s ++ t
参数：s : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.append_cancel_left`：∀ {α : Type u_1} {as bs cs : List α}, as ++ bs 
= as ++ cs → bs = cs
-/
theorem append_right_injective (s : List α) : Injective fun t ↦ s ++ t :=
  fun _ _ ↦ append_cancel_left
/-
**List.append_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：append_left_injective (t : List α) : Injective fun s => s ++ t
参数：t : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.append_cancel_right`：∀ {α : Type u_1} {as bs cs : List α}, as ++ bs
 = cs ++ bs → as = cs
-/
theorem append_left_injective (t : List α) : Injective fun s ↦ s ++ t :=
  fun _ _ ↦ append_cancel_right

/-! ### replicate -/

/-
**List.eq_replicate_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {a : α} {l : List α}, l = List.replicate l.length a ↔ ∀ b ∈
 l, b = a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### replicate
-/
theorem eq_replicate_length {a : α} : ∀ {l : List α}, l = replicate l.length a ↔ ∀ b ∈ l, b = a
  | [] => by simp
  | (b :: l) => by simp [eq_replicate_length, replicate_succ]
/-
**List.replicate_add** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：replicate_add (m n) (a : α) : replicate (m + n) a = replicate m a ++ repli
cate n a
参数：m n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.replicate_append_replicate`：∀ {n : ℕ} {α : Type u_1} {a : α} {m : ℕ
}, List.replicate n a ++ List.replicate m a = List.replicate (n + m) a
-/
theorem replicate_add (m n) (a : α) : replicate (m + n) a = replicate m a ++ replicate n a := by
  rw [replicate_append_replicate]
/-
**List.replicate_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：replicate_subset_singleton (n) (a : α) : replicate n a subseteq [a]
参数：n；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_singleton`：∀ {α : Type u_1} {a b : α}, a ∈ [b] ↔ a = b
· 使用定理 `List.eq_of_mem_replicate`：∀ {α : Type u_1} {a b : α} {n : ℕ}, b ∈ List.r
eplicate n a → b = a
-/
theorem replicate_subset_singleton (n) (a : α) : replicate n a ⊆ [a] := fun _ h =>
  mem_singleton.2 (eq_of_mem_replicate h)
/-
**List.subset_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：subset_singleton_iff {a : α} {L : List α} : L subseteq [a] ↔ exists n, L =
 replicate n a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subset_singleton_iff {a : α} {L : List α} : L ⊆ [a] ↔ ∃ n, L = replicate n a := by
  simp only [eq_replicate_iff, subset_def, mem_singleton, exists_eq_left']
/-
**List.replicate_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：replicate_right_injective {n : Nat} (hn : n != 0) : Injective (@replicate 
α n)
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.eq_replicate_iff`：∀ {α : Type u_1} {a : α} {n : ℕ} {l : List α}, l 
= List.replicate n a ↔ l.length = n ∧ ∀ b ∈ l, b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_replicate`：∀ {α : Type u_1} {a b : α} {n : ℕ}, b ∈ List.replica
te n a ↔ n ≠ 0 ∧ b = a
-/
theorem replicate_right_injective {n : ℕ} (hn : n ≠ 0) : Injective (@replicate α n) :=
  fun _ _ h => (eq_replicate_iff.1 h).2 _ <| mem_replicate.2 ⟨hn, rfl⟩
/-
**List.replicate_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：replicate_right_inj {a b : α} {n : Nat} (hn : n != 0) : replicate n a = re
plicate n b ↔ a = b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `List.replicate_right_injective`：replicate_right_injective {n : Nat} (hn 
: n != 0) : Injective (@replicate α n)
-/
theorem replicate_right_inj {a b : α} {n : ℕ} (hn : n ≠ 0) :
    replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective hn).eq_iff
/-
**List.replicate_right_inj'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {a b : α} {n : ℕ}, List.replicate n a = List.replicate n b 
↔ n = 0 ∨ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.replicate_right_inj`：replicate_right_inj {a b : α} {n : Nat} (hn : 
n != 0) : replicate n a = replicate n b ↔ a = b
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem replicate_right_inj' {a b : α} : ∀ {n},
    replicate n a = replicate n b ↔ n = 0 ∨ a = b
  | 0 => by simp
  | n + 1 => (replicate_right_inj n.succ_ne_zero).trans <| by simp only [n.succ_ne_zero, false_or]
/-
**List.replicate_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：replicate_left_injective (a : α) : Injective (replicate · a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
-/
theorem replicate_left_injective (a : α) : Injective (replicate · a) :=
  LeftInverse.injective (length_replicate (n := ·))
/-
**List.replicate_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：replicate_left_inj {a : α} {n m : Nat} : replicate n a = replicate m a ↔ n
 = m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `List.replicate_left_injective`：replicate_left_injective (a : α) : Inject
ive (replicate · a)
-/
theorem replicate_left_inj {a : α} {n m : ℕ} : replicate n a = replicate m a ↔ n = m :=
  (replicate_left_injective a).eq_iff

@[simp]
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head?_flatten_replicate {n : ℕ} (h : n ≠ 0) (l : List α) :
    (List.replicate n l).flatten.head? = l.head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  induction l <;> simp [replicate]

@[simp]
/-
**List.getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.rep
licate n l).flatten.getLast? = l.getLast?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getLast?_flatten_replicate {n : ℕ} (h : n ≠ 0) (l : List α) :
    (List.replicate n l).flatten.getLast? = l.getLast? := by
  rw [← List.head?_reverse, ← List.head?_reverse, List.reverse_flatten, List.map_replicate,
  List.reverse_replicate, head?_flatten_replicate h]

/-! ### pure -/

/-
**List.mem_pure** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_pure (x y : α) : x in (pure y : List α) ↔ x = y
参数：x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### pure
-/
theorem mem_pure (x y : α) : x ∈ (pure y : List α) ↔ x = y := by simp

/-! ### bind -/

@[simp]
/-
**List.bind_eq_flatMap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：bind_eq_flatMap {α β} (f : α -> List β) (l : List α) : l >>= f = l.flatMap
 f
参数：f : α -> List β；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### bind
-/
theorem bind_eq_flatMap {α β} (f : α → List β) (l : List α) : l >>= f = l.flatMap f :=
  rfl

/-! ### concat -/

/-! ### reverse -/

/-
**List.reverse_cons'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l)
 a
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### reverse
-/
theorem reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a := by
  simp only [reverse_cons, concat_eq_append]
/-
**List.reverse_concat'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverse_concat' (l : List α) (a : α) : (l ++ [a]).reverse = a :: l.reverse
参数：l : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
-/
theorem reverse_concat' (l : List α) (a : α) : (l ++ [a]).reverse = a :: l.reverse := by
  rw [reverse_append]; rfl

@[simp]
/-
**List.reverse_involutive** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverse_involutive : Involutive (@reverse α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
theorem reverse_involutive : Involutive (@reverse α) :=
  reverse_reverse

@[simp]
/-
**List.reverse_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverse_injective : Injective (@reverse α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `List.reverse_involutive`：reverse_involutive : Involutive (@reverse α)
-/
theorem reverse_injective : Injective (@reverse α) :=
  reverse_involutive.injective
/-
**List.reverse_surjective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverse_surjective : Surjective (@reverse α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `List.reverse_involutive`：reverse_involutive : Involutive (@reverse α)
-/
theorem reverse_surjective : Surjective (@reverse α) :=
  reverse_involutive.surjective
/-
**List.reverse_bijective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverse_bijective : Bijective (@reverse α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用定理 `List.reverse_involutive`：reverse_involutive : Involutive (@reverse α)
-/
theorem reverse_bijective : Bijective (@reverse α) :=
  reverse_involutive.bijective
/-
**List.concat_eq_reverse_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：concat_eq_reverse_cons (a : α) (l : List α) : concat l a = reverse (a :: r
everse l)
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem concat_eq_reverse_cons (a : α) (l : List α) : concat l a = reverse (a :: reverse l) := by
  grind
/-
**List.map_reverseAux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_reverseAux (f : α -> β) (l₁ l₂ : List α) : map f (reverseAux l₁ l₂) = 
reverseAux (map f l₁) (map f l₂)
参数：f : α -> β；l₁ l₂ : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverseAux_eq`：∀ {α : Type u_1} {as bs : List α}, as.reverseAux bs 
= as.reverse ++ bs
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_reverseAux (f : α → β) (l₁ l₂ : List α) :
    map f (reverseAux l₁ l₂) = reverseAux (map f l₁) (map f l₂) := by
  simp only [reverseAux_eq, map_append, map_reverse]

-- TODO: Rename `List.reverse_perm` to `List.reverse_perm_self`
/-
**List.reverse_perm'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁.reverse.Perm l₂ ↔ l₁.Perm l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.reverse_perm`：∀ {α : Type u_1} (l : List α), l.reverse.Perm l
-/
@[simp] lemma reverse_perm' : l₁.reverse ~ l₂ ↔ l₁ ~ l₂ where
  mp := l₁.reverse_perm.symm.trans
  mpr := l₁.reverse_perm.trans
/-
**List.perm_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Perm l₂.reverse ↔ l₁.Perm l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.reverse_perm`：∀ {α : Type u_1} (l : List α), l.reverse.Perm l
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
-/
@[simp] lemma perm_reverse : l₁ ~ l₂.reverse ↔ l₁ ~ l₂ where
  mp hl := hl.trans l₂.reverse_perm
  mpr hl := hl.trans l₂.reverse_perm.symm

/-! ### getLast -/

attribute [simp] getLast_cons

/-
**List.getLast_append_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast_append_singleton {a : α} (l : List α) : getLast (l ++ [a]) (append
_ne_nil_of_right_ne_nil l (cons_ne_nil a _)) = a
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.append_ne_nil_of_right_ne_nil`：∀ {α : Type u_1} {t : List α} (s : L
ist α), t ≠ [] → s ++ t ≠ []
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getLast_append_of_ne_nil`：∀ {α : Type u_1} {l' l : List α} (h₁ : l 
++ l' ≠ []) (h₂ : l' ≠ []), (l ++ l').getLast h₁ = l'.getLast h₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### getLast
-/
theorem getLast_append_singleton {a : α} (l : List α) :
    getLast (l ++ [a]) (append_ne_nil_of_right_ne_nil l (cons_ne_nil a _)) = a := by
  simp
/-
**List.getLast_append_of_right_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast_append_of_right_ne_nil (l₁ l₂ : List α) (h : l₂ != []) : getLast (
l₁ ++ l₂) (append_ne_nil_of_right_ne_nil l₁ h) = getLast l₂ h
参数：l₁ l₂ : List α；h : l₂ != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.append_ne_nil_of_right_ne_nil`：∀ {α : Type u_1} {t : List α} (s : L
ist α), t ≠ [] → s ++ t ≠ []
-/
theorem getLast_append_of_right_ne_nil (l₁ l₂ : List α) (h : l₂ ≠ []) :
    getLast (l₁ ++ l₂) (append_ne_nil_of_right_ne_nil l₁ h) = getLast l₂ h := by
  induction l₁ with grind
/-
**List.getLast_concat'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast_concat' {a : α} (l : List α) : getLast (concat l a) (by simp) = a
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `List.getLast_append_of_ne_nil`：∀ {α : Type u_1} {l' l : List α} (h₁ : l 
++ l' ≠ []) (h₂ : l' ≠ []), (l ++ l').getLast h₁ = l'.getLast h₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem getLast_concat' {a : α} (l : List α) : getLast (concat l a) (by simp) = a := by
  simp

@[simp]
/-
**List.getLast_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast_singleton' (a : α) : getLast [a] (cons_ne_nil a []) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
-/
theorem getLast_singleton' (a : α) : getLast [a] (cons_ne_nil a []) = a := rfl
/-
**List.dropLast_append_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {l : List α} (h : l ≠ []), l.dropLast ++ [l.getLast h] = l
参数：h : l ≠ []。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem dropLast_append_getLast : ∀ {l : List α} (h : l ≠ []), dropLast l ++ [getLast l h] = l
  | [], h => absurd rfl h
  | [_], _ => rfl
  | a :: b :: l, h => by
    rw [dropLast_cons_cons, cons_append, getLast_cons (cons_ne_nil _ _)]
    congr
    exact dropLast_append_getLast (cons_ne_nil b l)
/-
**List.getLast_congr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast_congr {l₁ l₂ : List α} (h₁ : l₁ != []) (h₂ : l₂ != []) (h₃ : l₁ = 
l₂) : getLast l₁ h₁ = getLast l₂ h₂
参数：h₁ : l₁ != []；h₂ : l₂ != []；h₃ : l₁ = l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem getLast_congr {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
    getLast l₁ h₁ = getLast l₂ h₂ := by subst l₁; rfl
/-
**List.getLast_replicate_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast_replicate_succ (m : Nat) (a : α) : (replicate (m + 1) a).getLast (
ne_nil_of_length_eq_add_one length_replicate) = a
参数：m : Nat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.ne_nil_of_length_eq_add_one`：∀ {α : Type u_1} {l : List α} {n : ℕ},
 l.length = n + 1 → l ≠ []
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `List.replicate_succ'`：∀ {n : ℕ} {α : Type u_1} {a : α}, List.replicate (
n + 1) a = List.replicate n a ++ [a]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `List.getLast_append_singleton`：getLast_append_singleton {a : α} (l : Lis
t α) : getLast (l ++ [a]) (append_ne_nil_of_right_ne_nil l (cons_ne_nil a _)) = 
a
-/
theorem getLast_replicate_succ (m : ℕ) (a : α) :
    (replicate (m + 1) a).getLast (ne_nil_of_length_eq_add_one length_replicate) = a := by
  simp only [replicate_succ']
  exact getLast_append_singleton _

/-! ### getLast? -/

/-
**List.mem_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_getLast?_append_of_mem_getLast? {l₁ l₂ : List α} {x : α} (h : x in l₂.
getLast?) : x in (l₁ ++ l₂).getLast?
参数：h : x in l₂.getLast?。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### getLast?
-/
theorem mem_getLast?_eq_getLast : ∀ {l : List α} {x : α}, x ∈ l.getLast? → ∃ h, x = getLast l h
  | [], x, hx
  | [a], x, hx
  | a :: b :: l, x, hx => by grind
/-
**List.getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.rep
licate n l).flatten.getLast? = l.getLast?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getLast?_eq_getLast_of_ne_nil : ∀ {l : List α} (h : l ≠ []), l.getLast? = some (l.getLast h)
  | [], h => (h rfl).elim
  | [_], _ => rfl
  | _ :: b :: l, _ => @getLast?_eq_getLast_of_ne_nil (b :: l) (cons_ne_nil _ _)
/-
**List.mem_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_getLast?_append_of_mem_getLast? {l₁ l₂ : List α} {x : α} (h : x in l₂.
getLast?) : x in (l₁ ++ l₂).getLast?
参数：h : x in l₂.getLast?。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_getLast?_cons {x y : α} : ∀ {l : List α}, x ∈ l.getLast? → x ∈ (y :: l).getLast?
  | [], _ => by contradiction
  | _ :: _, h => h
/-
**List.dropLast_append_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {l : List α} (h : l ≠ []), l.dropLast ++ [l.getLast h] = l
参数：h : l ≠ []。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem dropLast_append_getLast? : ∀ {l : List α}, ∀ a ∈ l.getLast?, dropLast l ++ [a] = l
  | [], a, ha => (Option.not_mem_none a ha).elim
  | [a], _, rfl => rfl
  | a :: b :: l, c, hc => by
    rw [getLast?_cons_cons] at hc
    rw [dropLast_cons_cons, cons_append, dropLast_append_getLast? _ hc]
/-
**List.getLastI_eq_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLastI_eq_getLast? [Inhabited α] : forall l : List α, l.getLastI = l.get
Last?.getD default
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getLastI_eq_getLast?_getD [Inhabited α] : ∀ l : List α, l.getLastI = l.getLast?.getD default
  | [] => by simp [getLastI]
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: c :: l => by simp [getLastI, getLastI_eq_getLast?_getD (c :: l)]

@[deprecated getLastI_eq_getLast?_getD (since := "2026-01-05")]
/-
**List.getLastI_eq_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLastI_eq_getLast? [Inhabited α] : forall l : List α, l.getLastI = l.get
Last?.getD default
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getLastI_eq_getLast? [Inhabited α] : ∀ l : List α, l.getLastI = l.getLast?.getD default :=
  getLastI_eq_getLast?_getD
/-
**List.getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.rep
licate n l).flatten.getLast? = l.getLast?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getLast?_append_cons :
    ∀ (l₁ : List α) (a : α) (l₂ : List α), getLast? (l₁ ++ a :: l₂) = getLast? (a :: l₂)
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | b :: c :: l₁, a, l₂ => by rw [cons_append, cons_append, getLast?_cons_cons,
    ← cons_append, getLast?_append_cons (c :: l₁)]
/-
**List.getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.rep
licate n l).flatten.getLast? = l.getLast?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getLast?_append_of_ne_nil (l₁ : List α) :
    ∀ {l₂ : List α} (_ : l₂ ≠ []), getLast? (l₁ ++ l₂) = getLast? l₂
  | [], hl₂ => by contradiction
  | b :: l₂, _ => getLast?_append_cons l₁ b l₂
/-
**List.mem_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_getLast?_append_of_mem_getLast? {l₁ l₂ : List α} {x : α} (h : x in l₂.
getLast?) : x in (l₁ ++ l₂).getLast?
参数：h : x in l₂.getLast?。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_getLast?_append_of_mem_getLast? {l₁ l₂ : List α} {x : α} (h : x ∈ l₂.getLast?) :
    x ∈ (l₁ ++ l₂).getLast? := by grind
/-
**List.mem_dropLast_of_mem_of_ne_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_dropLast_of_mem_of_ne_getLast {a : α} (ha : a in l) (ha' : a != l.getL
ast (ne_nil_of_mem ha)) : a in l.dropLast
参数：ha : a in l；ha' : a != l.getLast (ne_nil_of_mem ha)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
-/
theorem mem_dropLast_of_mem_of_ne_getLast {a : α} (ha : a ∈ l)
    (ha' : a ≠ l.getLast (ne_nil_of_mem ha)) : a ∈ l.dropLast := by
  grind [dropLast_concat_getLast]
/-
**List.mem_dropLast_of_mem_of_ne_getLastD** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_dropLast_of_mem_of_ne_getLastD {a d : α} (ha : a in l) (ha' : a != l.g
etLastD d) : a in l.dropLast
参数：ha : a in l；ha' : a != l.getLastD d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_dropLast_of_mem_of_ne_getLast`：mem_dropLast_of_mem_of_ne_getLas
t {a : α} (ha : a in l) (ha' : a != l.getLast (ne_nil_of_mem ha)) : a in l.dropL
ast
-/
theorem mem_dropLast_of_mem_of_ne_getLastD {a d : α} (ha : a ∈ l) (ha' : a ≠ l.getLastD d) :
    a ∈ l.dropLast :=
  mem_dropLast_of_mem_of_ne_getLast ha <| by grind
/-
**List.mem_dropLast_of_mem_of_ne_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_dropLast_of_mem_of_ne_getLast {a : α} (ha : a in l) (ha' : a != l.getL
ast (ne_nil_of_mem ha)) : a in l.dropLast
参数：ha : a in l；ha' : a != l.getLast (ne_nil_of_mem ha)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
-/
theorem mem_dropLast_of_mem_of_ne_getLast? {a : α} (ha : a ∈ l) (ha' : a ≠ l.getLast?) :
    a ∈ l.dropLast :=
  mem_dropLast_of_mem_of_ne_getLast ha <| by grind

/-! ### head(!?) and tail -/

@[simp]
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### head(!?) and tail
-/
theorem head!_nil [Inhabited α] : ([] : List α).head! = default := rfl
/-
**List.head_eq_getElem_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head_eq_getElem_zero {l : List α} (hl : l != []) : l.head hl = l[0]'(lengt
h_pos_iff.2 hl)
参数：hl : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.length_pos_iff`：∀ {α : Type u_1} {l : List α}, 0 < l.length ↔ l ≠ [
]
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.getElem_zero`：∀ {α : Type u_1} {l : List α} (h : 0 < l.length), l[0
] = l.head ⋯
-/
theorem head_eq_getElem_zero {l : List α} (hl : l ≠ []) :
    l.head hl = l[0]'(length_pos_iff.2 hl) :=
  (getElem_zero _).symm
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head!_eq_head?_getD [Inhabited α] (l : List α) : head! l = (head? l).getD default := by
  cases l <;> rfl

@[deprecated head!_eq_head?_getD (since := "2026-01-05")]
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head!_eq_head? [Inhabited α] (l : List α) : head! l = (head? l).getD default :=
  head!_eq_head?_getD l
/-
**List.surjective_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：surjective_head! [Inhabited α] : Surjective (@head! α _)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem surjective_head! [Inhabited α] : Surjective (@head! α _) := fun x => ⟨[x], rfl⟩
/-
**List.surjective_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：surjective_head! [Inhabited α] : Surjective (@head! α _)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem surjective_head? : Surjective (@head? α) :=
  Option.forall.2 ⟨⟨[], rfl⟩, fun x => ⟨[x], rfl⟩⟩
/-
**List.surjective_tail** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u}, Function.Surjective List.tail
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem surjective_tail : Surjective (@tail α)
  | [] => ⟨[], rfl⟩
  | a :: l => ⟨a :: a :: l, rfl⟩
/-
**List.eq_cons_of_mem_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: tail l
  | [], h => (Option.not_mem_none _ h).elim
  | a :: l, h => by
    simp only [head?, Option.mem_def, Option.some_inj] at h
    exact h ▸ rfl
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem head!_cons [Inhabited α] (a : α) (l : List α) : head! (a :: l) = a := rfl

@[simp]
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head!_append [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) :
    head! (s ++ t) = head! s := by
  induction s
  · contradiction
  · rfl
/-
**List.mem_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_head?_append_of_mem_head? {s t : List α} {x : α} (h : x in s.head?) : 
x in (s ++ t).head?
参数：h : x in s.head?。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_head?_append_of_mem_head? {s t : List α} {x : α} (h : x ∈ s.head?) :
    x ∈ (s ++ t).head? := by
  grind [Option.mem_def]
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head?_append_of_ne_nil :
    ∀ (l₁ : List α) {l₂ : List α} (_ : l₁ ≠ []), head? (l₁ ++ l₂) = head? l₁
  | _ :: _, _, _ => rfl
/-
**List.tail_append_singleton_of_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l != nil) : tail
 (l ++ [a]) = tail l ++ [a]
参数：h : l != nil。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ nil) :
    tail (l ++ [a]) = tail l ++ [a] := by grind
/-
**List.cons_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_head?_tail : forall {l : List α} {a : α}, a in head? l -> a :: tail l
 = l | [], a, h => by contradiction | b :: l, a, h => by have : b = a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_head?_tail : ∀ {l : List α} {a : α}, a ∈ head? l → a :: tail l = l
  | [], a, h => by contradiction
  | b :: l, a, h => by
    have : b = a := by simpa using h
    simp [this]
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head!_mem_head? [Inhabited α] : ∀ {l : List α}, l ≠ [] → head! l ∈ head? l
  | [], h => by contradiction
  | _ :: _, _ => rfl
/-
**List.cons_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_head?_tail : forall {l : List α} {a : α}, a in head? l -> a :: tail l
 = l | [], a, h => by contradiction | b :: l, a, h => by have : b = a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_head!_tail [Inhabited α] {l : List α} (h : l ≠ []) : head! l :: tail l = l :=
  cons_head?_tail (head!_mem_head? h)
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head!_mem_self [Inhabited α] {l : List α} (h : l ≠ nil) : l.head! ∈ l := by
  have h' : l.head! ∈ l.head! :: l.tail := mem_cons_self
  rwa [cons_head!_tail h] at h'
/-
**List.get_eq_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_eq_getElem? (l : List α) (i : Fin l.length) : l.get i = l[i]?.get (by 
simp)
参数：l : List α；i : Fin l.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_eq_getElem? (l : List α) (i : Fin l.length) :
    l.get i = l[i]?.get (by simp) := by
  simp
/-
**List.exists_mem_iff_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：exists_mem_iff_getElem {l : List α} {p : α -> Prop} : (exists x in l, p x)
 ↔ exists (i : Nat) (_ : i < l.length), p l[i]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_mem_iff_getElem {l : List α} {p : α → Prop} :
    (∃ x ∈ l, p x) ↔ ∃ (i : ℕ) (_ : i < l.length), p l[i] := by
  simp only [mem_iff_getElem]
  exact ⟨fun ⟨_x, ⟨i, hi, hix⟩, hxp⟩ ↦ ⟨i, hi, hix ▸ hxp⟩, fun ⟨i, hi, hp⟩ ↦ ⟨_, ⟨i, hi, rfl⟩, hp⟩⟩
/-
**List.exists_mem_iff_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：exists_mem_iff_get {l : List α} {p : α -> Prop} : (exists x in l, p x) ↔ e
xists (i : Fin l.length), p (l.get i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.exists_mem_iff_getElem`：exists_mem_iff_getElem {l : List α} {p : α 
-> Prop} : (exists x in l, p x) ↔ exists (i : Nat) (_ : i < l.length), p l[i]
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem exists_mem_iff_get {l : List α} {p : α → Prop} :
    (∃ x ∈ l, p x) ↔ ∃ (i : Fin l.length), p (l.get i) :=
  exists_mem_iff_getElem.trans ⟨fun ⟨i, hi, h⟩ ↦ ⟨⟨i, hi⟩, h⟩, fun ⟨i, h⟩ ↦ ⟨i, i.isLt, h⟩⟩
/-
**List.forall_mem_iff_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_mem_iff_getElem {l : List α} {p : α -> Prop} : (forall x in l, p x)
 ↔ forall (i : Nat) (_ : i < l.length), p l[i]
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_mem_iff_getElem {l : List α} {p : α → Prop} :
    (∀ x ∈ l, p x) ↔ ∀ (i : ℕ) (_ : i < l.length), p l[i] := by
  simp [mem_iff_getElem, @forall_comm α]
/-
**List.forall_mem_iff_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_mem_iff_get {l : List α} {p : α -> Prop} : (forall x in l, p x) ↔ f
orall (i : Fin l.length), p (l.get i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.forall_mem_iff_getElem`：forall_mem_iff_getElem {l : List α} {p : α 
-> Prop} : (forall x in l, p x) ↔ forall (i : Nat) (_ : i < l.length), p l[i]
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem forall_mem_iff_get {l : List α} {p : α → Prop} :
    (∀ x ∈ l, p x) ↔ ∀ (i : Fin l.length), p (l.get i) :=
  forall_mem_iff_getElem.trans ⟨fun h i ↦ h i i.isLt, fun h i hi ↦ h ⟨i, hi⟩⟩

@[simp]
/-
**List.get_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_surjective_iff {l : List α} : l.get.Surjective ↔ (forall x, x in l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.mem_iff_get`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ ∃ n, l.
get n = a
-/
theorem get_surjective_iff {l : List α} : l.get.Surjective ↔ (∀ x, x ∈ l) :=
  forall_congr' fun _ ↦ mem_iff_get.symm

@[simp]
/-
**List.getElem_fin_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_fin_surjective_iff {l : List α} : (fun (n : Fin l.length) => l[n.v
al]).Surjective ↔ (forall x, x in l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.get_surjective_iff`：get_surjective_iff {l : List α} : l.get.Surject
ive ↔ (forall x, x in l)
-/
theorem getElem_fin_surjective_iff {l : List α} :
    (fun (n : Fin l.length) ↦ l[n.val]).Surjective ↔ (∀ x, x ∈ l) :=
  get_surjective_iff

@[simp]
/-
**List.getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.
prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem?_surjective_iff {l : List α} : (fun (n : ℕ) ↦ l[n]?).Surjective ↔ (∀ x, x ∈ l) := by
  refine ⟨fun h x ↦ mem_iff_getElem?.mpr <| h x, fun h x ↦ ?_⟩
  cases x with
  | none => exact ⟨l.length, getElem?_eq_none <| Nat.le_refl _⟩
  | some x => exact mem_iff_getElem?.mp <| h x
/-
**List.get_tail** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_tail (l : List α) (i) (h : i < l.tail.length) (h' : i + 1 < l.length
参数：l : List α；i；h : i < l.tail.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.add_lt_of_lt_sub`：∀ {a b c : ℕ}, a < c - b → a + b < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_tail`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i < l.tail
.length), l.tail[i] = l[i + 1]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_tail (l : List α) (i) (h : i < l.tail.length)
    (h' : i + 1 < l.length := (by simp only [length_tail] at h; lia)) :
    l.tail.get ⟨i, h⟩ = l.get ⟨i + 1, h'⟩ := by
  simp
/-
**List.getElem_mem_tail** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_mem_tail {k : Nat} (l : List α) (h : k != 0) (hk : k < l.length) :
 l[k]'hk in l.tail
参数：l : List α；h : k != 0；hk : k < l.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem getElem_mem_tail {k : ℕ} (l : List α) (h : k ≠ 0) (hk : k < l.length) :
    l[k]'hk ∈ l.tail := by
  cases l <;> grind

/-! ### sublists -/

attribute [refl] List.Sublist.refl

/-
**List.cons_sublist_cons'** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：cons_sublist_cons' {a b : α} : a :: l₁ <+ b :: l₂ ↔ a :: l₁ <+ l₂ ∨ a = b 
∧ l₁ <+ l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### sublists
-/
lemma cons_sublist_cons' {a b : α} : a :: l₁ <+ b :: l₂ ↔ a :: l₁ <+ l₂ ∨ a = b ∧ l₁ <+ l₂ := by
  grind
/-
**List.sublist_cons_of_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_cons_of_sublist (a : α) (h : l₁ <+ l₂) : l₁ <+ a :: l₂
参数：a : α；h : l₁ <+ l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublist_cons_of_sublist (a : α) (h : l₁ <+ l₂) : l₁ <+ a :: l₂ := h.cons _
/-
**List.sublist_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {l : List α} {a : α}, l.Sublist [a] ↔ l = [] ∨ l = [a]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
@[simp] lemma sublist_singleton {l : List α} {a : α} : l <+ [a] ↔ l = [] ∨ l = [a] := by
  constructor <;> rintro (_ | _) <;> aesop
/-
**List.Sublist.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Sublist l₂ → l₂.Sublist l₁ → l₁ = l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.eq_of_length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Subl
ist l₂ → l₂.length ≤ l₁.length → l₁ = l₂
· 使用定理 `List.Sublist.length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂
 → l₁.length ≤ l₂.length
-/
theorem Sublist.antisymm (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
  s₁.eq_of_length_le s₂.length_le

/-- If the first element of two lists are different, then a sublist relation can be reduced. -/
/-
**List.Sublist.of_cons_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α} {a b : α}, a ≠ b → (a :: l₁).Sublist (b ::
 l₂) → (a :: l₁).Sublist l₂
参数：a :: l₁；b :: l₂；a :: l₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the first element of two lists are different, then a sublist relation can be 
reduced.
-/
theorem Sublist.of_cons_of_ne {a b} (h₁ : a ≠ b) (h₂ : a :: l₁ <+ b :: l₂) : a :: l₁ <+ l₂ :=
  match h₁, h₂ with
  | _, .cons _ h => h

/-! ### indexOf -/

section IndexOf

variable [BEq α] [LawfulBEq α]

/-
**List.idxOf_cons_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} [inst : BEq α] [LawfulBEq α] {a b : α} (l : List α), b = a 
→ List.idxOf a (b :: l) = 0
参数：l : List α；b :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.idxOf_cons_self`：∀ {α : Type u_1} {a : α} [inst : BEq α] [ReflBEq α
] {l : List α}, List.idxOf a (a :: l) = 0
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
-/
theorem idxOf_cons_eq {a b : α} (l : List α) : b = a → idxOf a (b :: l) = 0
  | e => by rw [← e]; exact idxOf_cons_self

@[simp]
/-
**List.idxOf_cons_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：idxOf_cons_ne {a b : α} (l : List α) (h : b != a) : idxOf a (b :: l) = suc
c (idxOf a l)
参数：l : List α；h : b != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.idxOf_cons`：∀ {α : Type u_1} {x : α} {xs : List α} {y : α} [inst : 
BEq α],   List.idxOf y (x :: xs) = bif x == y then 0 else List.idxOf y xs + 1
· 使用定理 `beq_false_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a b : α}
, a ≠ b → (a == b) = false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem idxOf_cons_ne {a b : α} (l : List α) (h : b ≠ a) : idxOf a (b :: l) = succ (idxOf a l) := by
  simp [idxOf_cons, beq_false_of_ne h]
/-
**List.idxOf_eq_length_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：idxOf_eq_length_iff {a : α} {l : List α} : idxOf a l = length l ↔ a ∉ l
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idxOf_eq_length_iff {a : α} {l : List α} : idxOf a l = length l ↔ a ∉ l := by
  grind

@[simp]
/-
**List.idxOf_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：idxOf_of_notMem {l : List α} {a : α} : a ∉ l -> idxOf a l = length l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.idxOf_eq_length_iff`：idxOf_eq_length_iff {a : α} {l : List α} : idx
Of a l = length l ↔ a ∉ l
-/
theorem idxOf_of_notMem {l : List α} {a : α} : a ∉ l → idxOf a l = length l :=
  idxOf_eq_length_iff.2
/-
**List.idxOf_eq_zero_iff_eq_nil_or_head_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：idxOf_eq_zero_iff_eq_nil_or_head_eq {l : List α} (a : α) : l.idxOf a = 0 ↔
 l = [] ∨ l.head? = a
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.idxOf_of_notMem`：idxOf_of_notMem {l : List α} {a : α} : a ∉ l -> id
xOf a l = length l
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem idxOf_eq_zero_iff_eq_nil_or_head_eq {l : List α} (a : α) :
    l.idxOf a = 0 ↔ l = [] ∨ l.head? = a := by
  cases l
  · simp
  · grind
/-
**List.idxOf_eq_zero_iff_head_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：idxOf_eq_zero_iff_head_eq {l : List α} (hl : l != []) {a : α} : l.idxOf a 
= 0 ↔ l.head hl = a
参数：hl : l != []。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.head?_eq_some_head`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.h
ead? = some (l.head h)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem idxOf_eq_zero_iff_head_eq {l : List α} (hl : l ≠ []) {a : α} :
    l.idxOf a = 0 ↔ l.head hl = a := by
  simp [hl, idxOf_eq_zero_iff_eq_nil_or_head_eq, head?_eq_some_head]
/-
**List.idxOf_append_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：idxOf_append_of_mem {a : α} (h : a in l₁) : idxOf a (l₁ ++ l₂) = idxOf a l
₁
参数：h : a in l₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idxOf_append_of_mem {a : α} (h : a ∈ l₁) : idxOf a (l₁ ++ l₂) = idxOf a l₁ := by grind
/-
**List.idxOf_append_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：idxOf_append_of_notMem {a : α} (h : a ∉ l₁) : idxOf a (l₁ ++ l₂) = l₁.leng
th + idxOf a l₂
参数：h : a ∉ l₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idxOf_append_of_notMem {a : α} (h : a ∉ l₁) :
    idxOf a (l₁ ++ l₂) = l₁.length + idxOf a l₂ := by grind
/-
**List.IsPrefix.idxOf_le** 是 Mathlib 中的一个定理，位于命名空间 `List.IsPrefix`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α} [inst : BEq α] [LawfulBEq α], l₁ <+: l₂ → 
∀ (a : α), List.idxOf a l₁ ≤ List.idxOf a l₂
该定理/引理表达了一个蕴含关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsPrefix.idxOf_le (hl : l₁ <+: l₂) (a : α) : l₁.idxOf a ≤ l₂.idxOf a := by
  obtain ⟨l₃, rfl⟩ := hl
  grind
/-
**List.IsPrefix.idxOf_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List.IsPrefix`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α} [inst : BEq α] [LawfulBEq α],   l₁ <+: l₂ 
→ ∀ {a : α}, a ∈ l₁ → List.idxOf a l₁ = List.idxOf a l₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.idxOf_append_of_mem`：idxOf_append_of_mem {a : α} (h : a in l₁) : id
xOf a (l₁ ++ l₂) = idxOf a l₁
-/
theorem IsPrefix.idxOf_eq_of_mem (hl : l₁ <+: l₂) {a : α} (ha : a ∈ l₁) :
    l₁.idxOf a = l₂.idxOf a := by
  obtain ⟨l₃, rfl⟩ := hl
  exact idxOf_append_of_mem ha |>.symm
/-
**List.IsPrefix.mem_iff_idxOf_lt_length** 是 Mathlib 中的一个定理，位于命名空间 `List.IsPrefix
`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α} [inst : BEq α] [LawfulBEq α],   l₁ <+: l₂ 
→ ∀ (a : α), a ∈ l₁ ↔ List.idxOf a l₂ < l₁.length
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.idxOf_lt_length_of_mem`：∀ {α : Type u_1} {a : α} [inst : BEq α] [Eq
uivBEq α] {l : List α}, a ∈ l → List.idxOf a l < l.length
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `List.IsPrefix.idxOf_eq_of_mem`：∀ {α : Type u} {l₁ l₂ : List α} [inst : B
Eq α] [LawfulBEq α],   l₁ <+: l₂ → ∀ {a : α}, a ∈ l₁ → List.idxOf a l₁ = List.id
xOf a l₂
· 使用定理 `List.IsPrefix.idxOf_le`：∀ {α : Type u} {l₁ l₂ : List α} [inst : BEq α] [
LawfulBEq α], l₁ <+: l₂ → ∀ (a : α), List.idxOf a l₁ ≤ List.idxOf a l₂
-/
theorem IsPrefix.mem_iff_idxOf_lt_length (hl : l₁ <+: l₂) (a : α) :
    a ∈ l₁ ↔ l₂.idxOf a < l₁.length := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact hl.idxOf_eq_of_mem h ▸ idxOf_lt_length_of_mem h
  · have := hl.idxOf_le a
    grind [List.idxOf_lt_length_iff]
/-
**List.IsSuffix.idxOf_le** 是 Mathlib 中的一个定理，位于命名空间 `List.IsSuffix`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α} [inst : BEq α] [LawfulBEq α],   l₁ <:+ l₂ 
→ ∀ (a : α), List.idxOf a l₂ ≤ l₂.length - l₁.length + List.idxOf a l₁
该定理/引理表达了一个蕴含关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSuffix.idxOf_le (hl : l₁ <:+ l₂) (a : α) :
    l₂.idxOf a ≤ l₂.length - l₁.length + l₁.idxOf a := by
  obtain ⟨l₃, rfl⟩ := hl
  grind
/-
**List.IsSuffix.idxOf_add_length_le** 是 Mathlib 中的一个定理，位于命名空间 `List.IsSuffix`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α} [inst : BEq α] [LawfulBEq α],   l₁ <:+ l₂ 
→ ∀ (a : α), List.idxOf a l₂ + l₁.length ≤ List.idxOf a l₁ + l₂.length
该定理/引理表达了一个蕴含关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSuffix.idxOf_add_length_le (hl : l₁ <:+ l₂) (a : α) :
    l₂.idxOf a + l₁.length ≤ l₁.idxOf a + l₂.length := by
  obtain ⟨l₃, rfl⟩ := hl
  grind
/-
**List.mem_take_iff_idxOf_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_take_iff_idxOf_lt {a : α} {n : Nat} {l : List α} (ha : a in l) : a in 
l.take n ↔ l.idxOf a < n
参数：ha : a in l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.IsPrefix.mem_iff_idxOf_lt_length`：∀ {α : Type u} {l₁ l₂ : List α} [
inst : BEq α] [LawfulBEq α],   l₁ <+: l₂ → ∀ (a : α), a ∈ l₁ ↔ List.idxOf a l₂ <
 l₁.length
· 使用定理 `List.take_prefix`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take i l <
+: l
-/
theorem mem_take_iff_idxOf_lt {a : α} {n : ℕ} {l : List α} (ha : a ∈ l) :
    a ∈ l.take n ↔ l.idxOf a < n := by
  rw [l.take_prefix n |>.mem_iff_idxOf_lt_length]
  grind
/-
**List.mem_dropLast_iff_idxOf_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_dropLast_iff_idxOf_lt {l : List α} {a : α} (ha : a in l) : a in l.drop
Last ↔ l.idxOf a < l.length - 1
参数：ha : a in l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dropLast_eq_take`：∀ {α : Type u_1} {l : List α}, l.dropLast = List.
take (l.length - 1) l
· 使用定理 `List.mem_take_iff_idxOf_lt`：mem_take_iff_idxOf_lt {a : α} {n : Nat} {l :
 List α} (ha : a in l) : a in l.take n ↔ l.idxOf a < n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_dropLast_iff_idxOf_lt {l : List α} {a : α} (ha : a ∈ l) :
    a ∈ l.dropLast ↔ l.idxOf a < l.length - 1 := by
  rw [dropLast_eq_take, mem_take_iff_idxOf_lt ha]
/-
**List.succ_idxOf_lt_length_of_mem_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：succ_idxOf_lt_length_of_mem_dropLast {l : List α} {a : α} (ha : a in l.dro
pLast) : l.idxOf a + 1 < l.length
参数：ha : a in l.dropLast。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.idxOf_lt_length_of_mem`：∀ {α : Type u_1} {a : α} [inst : BEq α] [Eq
uivBEq α] {l : List α}, a ∈ l → List.idxOf a l < l.length
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
-/
theorem succ_idxOf_lt_length_of_mem_dropLast {l : List α} {a : α} (ha : a ∈ l.dropLast) :
    l.idxOf a + 1 < l.length := by
  have := idxOf_lt_length_of_mem ha
  grind [IsPrefix.idxOf_eq_of_mem]
/-
**List.idxOf_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：idxOf_getLast {l : List α} (hl : l != []) (hl' : l.getLast hl ∉ l.dropLast
) : l.idxOf (l.getLast hl) = l.length - 1
参数：hl : l != []；hl' : l.getLast hl ∉ l.dropLast。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Nat.le_antisymm`：∀ {n m : ℕ}, n ≤ m → m ≤ n → n = m
· 使用定理 `Nat.le_pred_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m.pred
· 使用定理 `List.idxOf_lt_length_of_mem`：∀ {α : Type u_1} {a : α} [inst : BEq α] [Eq
uivBEq α] {l : List α}, a ∈ l → List.idxOf a l < l.length
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_dropLast_iff_idxOf_lt`：mem_dropLast_iff_idxOf_lt {l : List α} {
a : α} (ha : a in l) : a in l.dropLast ↔ l.idxOf a < l.length - 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.not_le`：∀ {a b : ℕ}, ¬a ≤ b ↔ b < a
-/
theorem idxOf_getLast {l : List α} (hl : l ≠ []) (hl' : l.getLast hl ∉ l.dropLast) :
    l.idxOf (l.getLast hl) = l.length - 1 :=
  Nat.le_antisymm (Nat.le_pred_of_lt <| l.idxOf_lt_length_of_mem <| getLast_mem hl) <| by
    contrapose hl'
    rwa [mem_dropLast_iff_idxOf_lt <| getLast_mem hl, ← Nat.not_le]

end IndexOf

/-! ### nth element -/

section deprecated

/-
**List.getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.
prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem?_length (l : List α) : l[l.length]? = none := getElem?_eq_none (Nat.le_refl _)

/-- A version of `getElem_map` that can be used for rewriting. -/
/-
**List.getElem_map_rev** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_map_rev (f : α -> β) {l} {n : Nat} {h : n < l.length} : f l[n] = (
map f l)[n]'((l.length_map f).symm ▸ h)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]

--- 原说明 ---
A version of `getElem_map` that can be used for rewriting.
-/
theorem getElem_map_rev (f : α → β) {l} {n : Nat} {h : n < l.length} :
    f l[n] = (map f l)[n]'((l.length_map f).symm ▸ h) := Eq.symm (getElem_map _)
/-
**List.get_length_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_length_sub_one {l : List α} (h : l.length - 1 < l.length) : l.get ⟨l.l
ength - 1, h⟩ = l.getLast (by rintro rfl; exact Nat.lt_irrefl 0 h)
参数：h : l.length - 1 < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.getLast_eq_getElem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.g
etLast h = l[l.length - 1]
-/
theorem get_length_sub_one {l : List α} (h : l.length - 1 < l.length) :
    l.get ⟨l.length - 1, h⟩ = l.getLast (by rintro rfl; exact Nat.lt_irrefl 0 h) :=
  (getLast_eq_getElem _).symm
/-
**List.ext_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁.length l₂.length, l
₁[n]? = l₂[n]?) : l₁ = l₂
参数：h' : forall n < max l₁.length l₂.length, l₁[n]? = l₂[n]?。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.le_of_not_lt`：∀ {a b : ℕ}, ¬a < b → b ≤ a
· 使用定理 `List.getElem?_eq_none`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l.length ≤
 i → l[i]? = none
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext_getElem?' {l₁ l₂ : List α} (h' : ∀ n < max l₁.length l₂.length, l₁[n]? = l₂[n]?) :
    l₁ = l₂ := by
  apply ext_getElem?
  grind
/-
**List.ext_get_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ext_get_iff {l₁ l₂ : List α} : l₁ = l₂ ↔ l₁.length = l₂.length ∧ forall n 
h₁ h₂, get l₁ ⟨n, h₁⟩ = get l₂ ⟨n, h₂⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
-/
theorem ext_get_iff {l₁ l₂ : List α} :
    l₁ = l₂ ↔ l₁.length = l₂.length ∧ ∀ n h₁ h₂, get l₁ ⟨n, h₁⟩ = get l₂ ⟨n, h₂⟩ := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ _ ↦ rfl⟩
  · intro ⟨h₁, h₂⟩
    exact ext_get h₁ h₂
/-
**List.ext_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁.length l₂.length, l
₁[n]? = l₂[n]?) : l₁ = l₂
参数：h' : forall n < max l₁.length l₂.length, l₁[n]? = l₂[n]?。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.le_of_not_lt`：∀ {a b : ℕ}, ¬a < b → b ≤ a
· 使用定理 `List.getElem?_eq_none`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l.length ≤
 i → l[i]? = none
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext_getElem?_iff' {l₁ l₂ : List α} : l₁ = l₂ ↔
    ∀ n < max l₁.length l₂.length, l₁[n]? = l₂[n]? :=
  ⟨by rintro rfl _ _; rfl, ext_getElem?'⟩

/-- If two lists `l₁` and `l₂` are the same length and `l₁[n]! = l₂[n]!` for all `n`,
then the lists are equal. -/
/-
**List.ext_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁.length l₂.length, l
₁[n]? = l₂[n]?) : l₁ = l₂
参数：h' : forall n < max l₁.length l₂.length, l₁[n]? = l₂[n]?。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.le_of_not_lt`：∀ {a b : ℕ}, ¬a < b → b ≤ a
· 使用定理 `List.getElem?_eq_none`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l.length ≤
 i → l[i]? = none
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If two lists `l₁` and `l₂` are the same length and `l₁[n]! = l₂[n]!` for all `n`
,
then the lists are equal.
-/
theorem ext_getElem! [Inhabited α] (hl : length l₁ = length l₂) (h : ∀ n : ℕ, l₁[n]! = l₂[n]!) :
    l₁ = l₂ :=
  ext_getElem hl fun n h₁ h₂ ↦ by simpa only [← getElem!_pos] using h n

-- This is incorrectly named and should be `get_idxOf`;
-- this already exists, so will require a deprecation dance.
/-
**List.idxOf_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：idxOf_get [BEq α] [LawfulBEq α] {a : α} {l : List α} (h) : get l ⟨idxOf a 
l, h⟩ = a
参数：h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_idxOf`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {x : α
} {xs : List α} (h : List.idxOf x xs < xs.length),   xs[List.idxOf x xs] = x
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem idxOf_get [BEq α] [LawfulBEq α] {a : α} {l : List α} (h) : get l ⟨idxOf a l, h⟩ = a := by
  simp

@[simp]
/-
**List.getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.
prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem?_idxOf [BEq α] [LawfulBEq α] {a : α} {l : List α} (h : a ∈ l) :
    l[idxOf a l]? = some a := by
  rw [getElem?_eq_getElem (idxOf_lt_length_iff.2 h), getElem_idxOf]
/-
**List.idxOf_inj** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：idxOf_inj [BEq α] [LawfulBEq α] {l : List α} {x y : α} (hx : x in l) : idx
Of x l = idxOf y l ↔ x = y
参数：hx : x in l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.idxOf_lt_length_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] 
{l : List α} {a : α}, List.idxOf a l < l.length ↔ a ∈ l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getElem_idxOf`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {x : α
} {xs : List α} (h : List.idxOf x xs < xs.length),   xs[List.idxOf x xs] = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem idxOf_inj [BEq α] [LawfulBEq α] {l : List α} {x y : α} (hx : x ∈ l) :
    idxOf x l = idxOf y l ↔ x = y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  rw [← getElem_idxOf (idxOf_lt_length_iff.mpr hx)]
  simp [h]
/-
**List.get_reverse'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_reverse' (l : List α) (n) (hn') : l.reverse.get n = l.get ⟨l.length - 
1 - n, hn'⟩
参数：l : List α；n；hn'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.sub_one_sub_lt_of_lt`：∀ {a b : ℕ}, a < b → b - 1 - a < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_reverse`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i < l.r
everse.length), l.reverse[i] = l[l.length - 1 - i]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_reverse' (l : List α) (n) (hn') :
    l.reverse.get n = l.get ⟨l.length - 1 - n, hn'⟩ := by
  simp
/-
**List.eq_cons_of_length_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：eq_cons_of_length_one {l : List α} (h : l.length = 1) : l = [l.get ⟨0, by 
lia⟩]
参数：h : l.length = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_cons_of_length_one {l : List α} (h : l.length = 1) : l = [l.get ⟨0, by lia⟩] := by
  refine ext_get (by convert! h) (by grind)

end deprecated

/-
**List.getElem_set_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_set_of_ne {l : List α} {i j : Nat} (h : i != j) (a : α) (hj : j < 
(l.set i a).length) : (l.set i a)[j] = l[j]'(by simpa using hj)
参数：h : i != j；a : α；hj : j < (l.set i a).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_set_ne`：∀ {α : Type u_1} {l : List α} {i j : ℕ}, i ≠ j → ∀ 
{a : α} (hj : j < (l.set i a).length), (l.set i a)[j] = l[j]
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem getElem_set_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a)[j] = l[j]'(by simpa using hj) := by
  simp [h]

/-! ### map -/

-- `List.map_const` (the version with `Function.const` instead of a lambda) is already tagged
-- `simp` in Core
-- TODO: Upstream the tagging to Core?
attribute [simp] map_const'

/-
**List.flatMap_pure_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：flatMap_pure_eq_map (f : α -> β) (l : List α) : l.flatMap (pure ∘ f) = map
 f l
参数：f : α -> β；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_eq_flatMap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Li
st α}, List.map f l = List.flatMap (fun x => [f x]) l
-/
theorem flatMap_pure_eq_map (f : α → β) (l : List α) : l.flatMap (pure ∘ f) = map f l :=
  .symm <| map_eq_flatMap ..
/-
**List.flatMap_congr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：flatMap_congr {l : List α} {f g : α -> List β} (h : forall x in l, f x = g
 x) : l.flatMap f = l.flatMap g
参数：h : forall x in l, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.map_congr_left`：∀ {α : Type u_1} {l : List α} {α_1 : Type u_2} {f g
 : α → α_1}, (∀ a ∈ l, f a = g a) → List.map f l = List.map g l
-/
theorem flatMap_congr {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g :=
  (congr_arg List.flatten <| map_congr_left h :)
/-
**List.infix_flatMap_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：infix_flatMap_of_mem {a : α} {as : List α} (h : a in as) (f : α -> List α)
 : f a <:+: as.flatMap f
参数：h : a in as；f : α -> List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.infix_of_mem_flatten`：∀ {α : Type u_1} {l : List α} {L : List (List
 α)}, l ∈ L → l <:+: L.flatten
· 使用定理 `List.mem_map_of_mem`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {a : α
} {f : α → β}, a ∈ l → f a ∈ List.map f l
-/
theorem infix_flatMap_of_mem {a : α} {as : List α} (h : a ∈ as) (f : α → List α) :
    f a <:+: as.flatMap f :=
  infix_of_mem_flatten (mem_map_of_mem h)

@[simp]
/-
**List.map_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_eq_map {α β} (f : α -> β) (l : List α) : f < > l = map f l
参数：f : α -> β；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_eq_map {α β} (f : α → β) (l : List α) : f <$> l = map f l :=
  rfl

/-- A single `List.map` of a composition of functions is equal to
composing a `List.map` with another `List.map`, fully applied.
This is the reverse direction of `List.map_map`.
-/
/-
**List.comp_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：comp_map (h : β -> γ) (g : α -> β) (l : List α) : map (h ∘ g) l = map h (m
ap g l)
参数：h : β -> γ；g : α -> β；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l

--- 原说明 ---
A single `List.map` of a composition of functions is equal to
composing a `List.map` with another `List.map`, fully applied.
This is the reverse direction of `List.map_map`.
-/
theorem comp_map (h : β → γ) (g : α → β) (l : List α) : map (h ∘ g) l = map h (map g l) :=
  map_map.symm

/-- Composing a `List.map` with another `List.map` is equal to
a single `List.map` of composed functions.
-/
@[simp]
/-
**List.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_comp_map (g : β -> γ) (f : α -> β) : map g ∘ map f = map (g ∘ f)
参数：g : β -> γ；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.comp_map`：comp_map (h : β -> γ) (g : α -> β) (l : List α) : map (h 
∘ g) l = map h (map g l)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Composing a `List.map` with another `List.map` is equal to
a single `List.map` of composed functions.
-/
theorem map_comp_map (g : β → γ) (f : α → β) : map g ∘ map f = map (g ∘ f) := by
  ext l; rw [comp_map, Function.comp_apply]

section map_bijectivity

/-
**List._root_.Function.LeftInverse.list_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.LeftInverse.list_map {f : α → β} {g : β → α} (h : LeftInverse f g) :
    LeftInverse (map f) (map g)
  | [] => by simp_rw [map_nil]
  | x :: xs => by simp_rw [map_cons, h x, h.list_map xs]

nonrec theorem _root_.Function.RightInverse.list_map {f : α → β} {g : β → α}
    (h : RightInverse f g) : RightInverse (map f) (map g) :=
  h.list_map

nonrec theorem _root_.Function.Involutive.list_map {f : α → α}
    (h : Involutive f) : Involutive (map f) :=
  Function.LeftInverse.list_map h

@[simp]
/-
**List.map_leftInverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_leftInverse_iff {f : α -> β} {g : β -> α} : LeftInverse (map f) (map g
) ↔ LeftInverse f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Function.LeftInverse.list_map`：∀ {α : Type u} {β : Type v} {f : α → β} {
g : β → α},   Function.LeftInverse f g → Function.LeftInverse (List.map f) (List
.map g)
-/
theorem map_leftInverse_iff {f : α → β} {g : β → α} :
    LeftInverse (map f) (map g) ↔ LeftInverse f g :=
  ⟨fun h x => by injection h [x], (·.list_map)⟩

@[simp]
/-
**List.map_rightInverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_rightInverse_iff {f : α -> β} {g : β -> α} : RightInverse (map f) (map
 g) ↔ RightInverse f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.map_leftInverse_iff`：map_leftInverse_iff {f : α -> β} {g : β -> α} 
: LeftInverse (map f) (map g) ↔ LeftInverse f g
-/
theorem map_rightInverse_iff {f : α → β} {g : β → α} :
    RightInverse (map f) (map g) ↔ RightInverse f g := map_leftInverse_iff

@[simp]
/-
**List.map_involutive_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_involutive_iff {f : α -> α} : Involutive (map f) ↔ Involutive f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.map_leftInverse_iff`：map_leftInverse_iff {f : α -> β} {g : β -> α} 
: LeftInverse (map f) (map g) ↔ LeftInverse f g
-/
theorem map_involutive_iff {f : α → α} :
    Involutive (map f) ↔ Involutive f := map_leftInverse_iff
/-
**List._root_.Function.Injective.list_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.list_map {f : α → β} (h : Injective f) :
    Injective (map f)
  | [], [], _ => rfl
  | x :: xs, y :: ys, hxy => by
    injection hxy with hxy hxys
    rw [h hxy, h.list_map hxys]

@[simp]
/-
**List.map_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_injective_iff {f : α -> β} : Injective (map f) ↔ Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Function.Injective.list_map`：∀ {α : Type u} {β : Type v} {f : α → β}, Fu
nction.Injective f → Function.Injective (List.map f)
-/
theorem map_injective_iff {f : α → β} : Injective (map f) ↔ Injective f := by
  refine ⟨fun h x y hxy => ?_, (·.list_map)⟩
  suffices [x] = [y] by simpa using this
  apply h
  simp [hxy]
/-
**List._root_.Function.Surjective.list_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Surjective.list_map {f : α → β} (h : Surjective f) :
    Surjective (map f) :=
  let ⟨_, h⟩ := h.hasRightInverse; h.list_map.surjective

@[simp]
/-
**List.map_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_surjective_iff {f : α -> β} : Surjective (map f) ↔ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.singleton_injective`：singleton_injective : Injective fun a : α => [
a]
· 使用定理 `Function.Surjective.list_map`：∀ {α : Type u} {β : Type v} {f : α → β}, F
unction.Surjective f → Function.Surjective (List.map f)
-/
theorem map_surjective_iff {f : α → β} : Surjective (map f) ↔ Surjective f := by
  refine ⟨fun h x => ?_, (·.list_map)⟩
  let ⟨[y], hxy⟩ := h [x]
  exact ⟨_, List.singleton_injective hxy⟩
/-
**List._root_.Function.Bijective.list_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Bijective.list_map {f : α → β} (h : Bijective f) : Bijective (map f) :=
  ⟨h.1.list_map, h.2.list_map⟩

@[simp]
/-
**List.map_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_bijective_iff {f : α -> β} : Bijective (map f) ↔ Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_bijective_iff {f : α → β} : Bijective (map f) ↔ Bijective f := by
  simp_rw [Function.Bijective, map_injective_iff, map_surjective_iff]

end map_bijectivity

/-
**List.eq_of_mem_map_const** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ in map (const α b₂) l
) : b₁ = b₂
参数：h : b₁ in map (const α b₂) l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.eq_of_mem_replicate`：∀ {α : Type u_1} {a b : α} {n : ℕ}, b ∈ List.r
eplicate n a → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_const`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, Li
st.map (Function.const α b) l = List.replicate l.length b
-/
theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (const α b₂) l) :
    b₁ = b₂ := by rw [map_const] at h; exact eq_of_mem_replicate h

/-- `eq_nil_or_concat` in simp normal form -/
/-
**List.eq_nil_or_concat'** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：eq_nil_or_concat' (l : List α) : l = [] ∨ exists L b, l = L ++ [b]
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.eq_nil_or_concat`：∀ {α : Type u_1} (l : List α), l = [] ∨ ∃ l' b, l
 = l'.concat b

--- 原说明 ---
`eq_nil_or_concat` in simp normal form
-/
lemma eq_nil_or_concat' (l : List α) : l = [] ∨ ∃ L b, l = L ++ [b] := by
  simpa using l.eq_nil_or_concat

/-! ### foldl, foldr -/

/-
**List.foldl_ext** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_ext (f g : α -> β -> α) (a : α) {l : List β} (H : forall a : α, fora
ll b in l, f a b = g a b) : foldl f a l = foldl g a l
参数：f g : α -> β -> α；a : α；H : forall a : α, forall b in l, f a b = g a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldl.eq_def`：∀ {α : Type u} {β : Type v} (f : α → β → α) (x : α) (
x_1 : List β),   List.foldl f x x_1 =     match x, x_1 with     | a, [] => a    
 | a, b…
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l

--- 原说明 ---
### foldl, foldr
-/
theorem foldl_ext (f g : α → β → α) (a : α) {l : List β} (H : ∀ a : α, ∀ b ∈ l, f a b = g a b) :
    foldl f a l = foldl g a l := by
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih =>
    unfold foldl
    rw [ih _ fun a b bin => H a b <| mem_cons_of_mem _ bin, H a hd mem_cons_self]
/-
**List.foldr_ext** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldr_ext (f g : α -> β -> β) (b : β) {l : List α} (H : forall a in l, for
all b : β, f a b = g a b) : foldr f b l = foldr g b l
参数：f g : α -> β -> β；b : β；H : forall a in l, forall b : β, f a b = g a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldr_ext (f g : α → β → β) (b : β) {l : List α} (H : ∀ a ∈ l, ∀ b : β, f a b = g a b) :
    foldr f b l = foldr g b l := by
  induction l with | nil => rfl | cons hd tl ih => ?_
  simp only [mem_cons, or_imp, forall_and, forall_eq] at H
  simp only [foldr, ih H.2, H.1]
/-
**List.foldl_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_concat (f : β -> α -> β) (b : β) (x : α) (xs : List α) : List.foldl 
f b (xs ++ [x]) = f (List.foldl f b xs) x
参数：f : β -> α -> β；b : β；x : α；xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldl_concat
    (f : β → α → β) (b : β) (x : α) (xs : List α) :
    List.foldl f b (xs ++ [x]) = f (List.foldl f b xs) x := by
  simp only [List.foldl_append, List.foldl]
/-
**List.foldr_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldr_concat (f : α -> β -> β) (b : β) (x : α) (xs : List α) : List.foldr 
f b (xs ++ [x]) = (List.foldr f (f x b) xs)
参数：f : α -> β -> β；b : β；x : α；xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldr_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {b : 
β} {l l' : List α},   List.foldr f b (l ++ l') = List.foldr f (List.foldr f b l'
) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldr_concat
    (f : α → β → β) (b : β) (x : α) (xs : List α) :
    List.foldr f b (xs ++ [x]) = (List.foldr f (f x b) xs) := by
  simp only [List.foldr_append, List.foldr]
/-
**List.foldl_fixed'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β → α} {a : α}, (∀ (b : β), f a b = a
) → ∀ (l : List β), List.foldl f a l = a
参数：∀ (b : β), f a b = a；l : List β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldl_fixed' {f : α → β → α} {a : α} (hf : ∀ b, f a b = a) : ∀ l : List β, foldl f a l = a
  | [] => rfl
  | b :: l => by rw [foldl_cons, hf b, foldl_fixed' hf l]
/-
**List.foldr_fixed'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β → β} {b : β}, (∀ (a : α), f a b = b
) → ∀ (l : List α), List.foldr f b l = b
参数：∀ (a : α), f a b = b；l : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr_fixed' {f : α → β → β} {b : β} (hf : ∀ a, f a b = b) : ∀ l : List α, foldr f b l = b
  | [] => rfl
  | a :: l => by rw [foldr_cons, foldr_fixed' hf l, hf a]

@[simp]
/-
**List.foldl_fixed** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_fixed {a : α} : forall l : List β, foldl (fun a _ => a) a l = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.foldl_fixed'`：∀ {α : Type u} {β : Type v} {f : α → β → α} {a : α}, 
(∀ (b : β), f a b = a) → ∀ (l : List β), List.foldl f a l = a
-/
theorem foldl_fixed {a : α} : ∀ l : List β, foldl (fun a _ => a) a l = a :=
  foldl_fixed' fun _ => rfl

@[simp]
/-
**List.foldr_fixed** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldr_fixed {b : β} : forall l : List α, foldr (fun _ b => b) b l = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.foldr_fixed'`：∀ {α : Type u} {β : Type v} {f : α → β → β} {b : β}, 
(∀ (a : α), f a b = b) → ∀ (l : List α), List.foldr f b l = b
-/
theorem foldr_fixed {b : β} : ∀ l : List α, foldr (fun _ b => b) b l = b :=
  foldr_fixed' fun _ => rfl
/-
**List.reverse_foldl** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverse_foldl {l : List α} : reverse (foldl (fun t h => h :: t) [] l) = l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldl_flip_cons_eq_append`：∀ {α : Type u_1} {β : Type u_2} {l : Lis
t α} {f : α → β} {l' : List β},   List.foldl (fun xs y => f y :: xs) l' l = (Lis
t.map f l).reverse +…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverse_foldl {l : List α} : reverse (foldl (fun t h => h :: t) [] l) = l := by
  simp
/-
**List.foldl_hom** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} (f : α₁ → α₂) {g₁ : α₁ → 
β → α₁} {g₂ : α₂ → β → α₂} {l : List β}   {init : α₁}, (∀ (x : α₁) (y : β), g₂ (
f x) y = f (g₁ x y)) → List.foldl g₂ (f init) l = f (List.foldl g₁ init l)
参数：f : α₁ → α₂；∀ (x : α₁) (y : β), g₂ (f x) y = f (g₁ x y)；f init；List.foldl g₁ 
init l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem foldl_hom₂ (l : List ι) (f : α → β → γ) (op₁ : α → ι → α) (op₂ : β → ι → β)
    (op₃ : γ → ι → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ a i) (op₂ b i) = op₃ (f a b) i) :
    foldl op₃ (f a b) l = f (foldl op₁ a l) (foldl op₂ b l) :=
  Eq.symm <| by
    revert a b
    induction l <;> intros <;> [rfl; simp only [*, foldl]]
/-
**List.foldr_hom** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {β₁ : Type u_1} {β₂ : Type u_2} {α : Type u_3} (f : β₁ → β₂) {g₁ : α → β
₁ → β₁} {g₂ : α → β₂ → β₂} {l : List α}   {init : β₁}, (∀ (x : α) (y : β₁), g₂ x
 (f y) = f (g₁ x y)) → List.foldr g₂ (f init) l = f (List.foldr g₁ init l)
参数：f : β₁ → β₂；∀ (x : α) (y : β₁), g₂ x (f y) = f (g₁ x y)；f init；List.foldr g₁ 
init l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem foldr_hom₂ (l : List ι) (f : α → β → γ) (op₁ : ι → α → α) (op₂ : ι → β → β)
    (op₃ : ι → γ → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ i a) (op₂ i b) = op₃ i (f a b)) :
    foldr op₃ (f a b) l = f (foldr op₁ a l) (foldr op₂ b l) := by
  revert a
  induction l <;> intros <;> [rfl; simp only [*, foldr]]
/-
**List.injective_foldl_comp** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：injective_foldl_comp {l : List (α -> α)} {f : α -> α} (hl : forall f in l,
 Function.Injective f) (hf : Function.Injective f) : Function.Injective (@List.f
oldl (α -> α) (α -> α) Function.comp f l)
参数：α -> α；hl : forall f in l, Function.Injective f；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
-/
theorem injective_foldl_comp {l : List (α → α)} {f : α → α}
    (hl : ∀ f ∈ l, Function.Injective f) (hf : Function.Injective f) :
    Function.Injective (@List.foldl (α → α) (α → α) Function.comp f l) := by
  induction l generalizing f with
  | nil => exact hf
  | cons lh lt l_ih =>
    apply l_ih fun _ h => hl _ (List.mem_cons_of_mem _ h)
    apply Function.Injective.comp hf
    apply hl _ mem_cons_self

/-- Consider two lists `l₁` and `l₂` with designated elements `a₁` and `a₂` somewhere in them:
`l₁ = x₁ ++ [a₁] ++ z₁` and `l₂ = x₂ ++ [a₂] ++ z₂`.
Assume the designated element `a₂` is present in neither `x₁` nor `z₁`.
We conclude that the lists are equal (`l₁ = l₂`) if and only if their respective parts are equal
(`x₁ = x₂ ∧ a₁ = a₂ ∧ z₁ = z₂`). -/
/-
**List.append_cons_inj_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：append_cons_inj_of_notMem {x₁ x₂ z₁ z₂ : List α} {a₁ a₂ : α} (notin_x : a₂
 ∉ x₁) (notin_z : a₂ ∉ z₁) : x₁ ++ a₁ :: z₁ = x₂ ++ a₂ :: z₂ ↔ x₁ = x₂ ∧ a₁ = a₂
 ∧ z₁ = z₂
参数：notin_x : a₂ ∉ x₁；notin_z : a₂ ∉ z₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
Consider two lists `l₁` and `l₂` with designated elements `a₁` and `a₂` somewher
e in them:
`l₁ = x₁ ++ [a₁] ++ z₁` and `l₂ = x₂ ++ [a₂] ++ z₂`.
Assume the designated element `a₂` is present in neither `x₁` nor `z₁`.
We conclude that the lists are equal (`l₁ = l₂`) if and only if their respective
 parts are equal
(`x₁ = x₂ ∧ a₁ = a₂ ∧ z₁ = z₂`).
-/
lemma append_cons_inj_of_notMem {x₁ x₂ z₁ z₂ : List α} {a₁ a₂ : α}
    (notin_x : a₂ ∉ x₁) (notin_z : a₂ ∉ z₁) :
    x₁ ++ a₁ :: z₁ = x₂ ++ a₂ :: z₂ ↔ x₁ = x₂ ∧ a₁ = a₂ ∧ z₁ = z₂ := by
  constructor
  · simp only [append_eq_append_iff, cons_eq_append_iff, cons_eq_cons]
    rintro (⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩ |
      ⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩) <;> simp_all
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-! ### foldlM, foldrM, mapM -/

section FoldlMFoldrM

variable {m : Type v → Type w} [Monad m]

variable [LawfulMonad m]

/-
**List.foldrM_eq_foldr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldrM_eq_foldr (f : α -> β -> m β) (b l) : foldrM f b l = foldr (fun a mb
 => mb >>= f a) (pure b) l
参数：f : α -> β -> m β；b l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldrM_cons`：∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u
_1} [inst : Monad m] [LawfulMonad m] {a : α} {l : List α}   {f : α → β → m β} {b
 : β},…
-/
theorem foldrM_eq_foldr (f : α → β → m β) (b l) :
    foldrM f b l = foldr (fun a mb => mb >>= f a) (pure b) l := by induction l <;> simp [*]
/-
**List.foldlM_eq_foldl** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldlM_eq_foldl (f : β -> α -> m β) (b l) : List.foldlM f b l = foldl (fun
 mb a => mb >>= fun b => f b a) (pure b) l
参数：f : β -> α -> m β；b l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bind_pure`：∀ {m : Type u_1 → Type u_2} {α : Type u_1} [inst : Monad m] [
LawfulMonad m] (x : m α), x >>= pure = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulMonad.bind_assoc`：∀ {m : Type u → Type v} {inst : Monad m} [self :
 LawfulMonad m] {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),   x >>= 
f >>= g = x …
· 使用定理 `LawfulMonad.pure_bind`：∀ {m : Type u → Type v} {inst : Monad m} [self : 
LawfulMonad m] {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
-/
theorem foldlM_eq_foldl (f : β → α → m β) (b l) :
    List.foldlM f b l = foldl (fun mb a => mb >>= fun b => f b a) (pure b) l := by
  suffices h :
    ∀ mb : m β, (mb >>= fun b => List.foldlM f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
    by simp [← h (pure b)]
  induction l with
  | nil => simp
  | cons _ _ l_ih => intro; simp only [List.foldlM, foldl, ← l_ih, functor_norm]

end FoldlMFoldrM

/-! ### filter -/

/-
**List.length_eq_length_filter_add** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_eq_length_filter_add {l : List (α)} (f : α -> Bool) : l.length = (l
.filter f).length + (l.filter (!f ·)).length
参数：α；f : α -> Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_eq_countP_add_countP`：∀ {α : Type u_1} (p : α → Bool) {l : L
ist α}, l.length = List.countP p l + List.countP (fun a => decide ¬p a = true) l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.decide_eq_false`：∀ {b : Bool} {x : Decidable (b = false)}, decide (
b = false) = !b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### filter
-/
theorem length_eq_length_filter_add {l : List (α)} (f : α → Bool) :
    l.length = (l.filter f).length + (l.filter (!f ·)).length := by
  simp_rw [← List.countP_eq_length_filter, l.length_eq_countP_add_countP f, Bool.not_eq_true,
    Bool.decide_eq_false]

/-! ### filterMap -/

/-
**List.filterMap_eq_flatMap_toList** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：filterMap_eq_flatMap_toList (f : α -> Option β) (l : List α) : l.filterMap
 f = l.flatMap fun a => (f a).toList
参数：f : α -> Option β；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatMap_nil`：∀ {α : Type u} {β : Type v} {f : α → List β}, List.fla
tMap f [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
### filterMap
-/
theorem filterMap_eq_flatMap_toList (f : α → Option β) (l : List α) :
    l.filterMap f = l.flatMap fun a ↦ (f a).toList := by
  induction l with | nil => ?_ | cons a l ih => ?_ <;> simp [filterMap_cons]
  rcases f a <;> simp [ih]

@[congr]
/-
**List.filterMap_congr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：filterMap_congr {f g : α -> Option β} {l : List α} (h : forall x in l, f x
 = g x) : l.filterMap f = l.filterMap g
参数：h : forall x in l, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem filterMap_congr {f g : α → Option β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l <;> simp_all [filterMap_cons]
/-
**List.filterMap_eq_map_iff_forall_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：filterMap_eq_map_iff_forall_eq_some {f : α -> Option β} {g : α -> β} {l : 
List α} : l.filterMap f = l.map g ↔ forall x in l, f x = some (g x) where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.filterMap_cons_some`：∀ {α : Type u_1} {β : Type u_2} {f : α → Optio
n β} {a : α} {l : List α} {b : β},   f a = some b → List.filterMap f (a :: l) = 
b :: List.filt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `List.filterMap_congr`：filterMap_congr {f g : α -> Option β} {l : List α}
 (h : forall x in l, f x = g x) : l.filterMap f = l.filterMap g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.filterMap_eq_map'`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, (Li
st.filterMap fun x => some (f x)) = List.map f
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `List.filterMap_eq_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, List
.filterMap (some ∘ f) = List.map f
-/
theorem filterMap_eq_map_iff_forall_eq_some {f : α → Option β} {g : α → β} {l : List α} :
    l.filterMap f = l.map g ↔ ∀ x ∈ l, f x = some (g x) where
  mp := by
    induction l with | nil => simp | cons a l ih => ?_
    rcases ha : f a with - | b
    · intro h
      have : (filterMap f l).length = l.length + 1 := by grind
      grind
    · simp +contextual [ha, ih]
  mpr h := Eq.trans (filterMap_congr <| by simpa) (congr_fun filterMap_eq_map _)

@[simp]
/-
**List.filterMap_none** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：filterMap_none (l : List α) : l.filterMap (fun _ => @Option.none β) = []
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filterMap_cons_none`：∀ {α : Type u_1} {β : Type u_2} {f : α → Optio
n β} {a : α} {l : List α},   f a = none → List.filterMap f (a :: l) = List.filte
rMap f l
-/
lemma filterMap_none (l : List α) :
    l.filterMap (fun _ ↦ @Option.none β) = [] := by
  induction l <;> simp [*]

/-! ### filter -/

section Filter

variable {p : α → Bool}

/-
**List.filter_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：filter_singleton {a : α} : [a].filter p = bif p a then [a] else []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_singleton {a : α} : [a].filter p = bif p a then [a] else [] :=
  rfl
/-
**List.filter_eq_foldr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：filter_eq_foldr (p : α -> Bool) (l : List α) : filter p l = foldr (fun a o
ut => bif p a then a :: out else out) [] l
参数：p : α -> Bool；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem filter_eq_foldr (p : α → Bool) (l : List α) :
    filter p l = foldr (fun a out => bif p a then a :: out else out) [] l := by
  induction l <;> simp [*, filter]; rfl

@[simp]
/-
**List.filter_subset_self** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：filter_subset_self (l : List α) : filter p l subseteq l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `List.filter_sublist`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, (List
.filter p l).Sublist l
-/
theorem filter_subset_self (l : List α) : filter p l ⊆ l :=
  filter_sublist.subset

@[deprecated (since := "2026-04-24")] alias filter_subset' := filter_subset_self
/-
**List.of_mem_filter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：of_mem_filter {a : α} {l} (h : a in filter p l) : p a
参数：h : a in filter p l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_filter`：∀ {α : Type u_1} {p : α → Bool} {as : List α} {x : α}, 
x ∈ List.filter p as ↔ x ∈ as ∧ p x = true
-/
theorem of_mem_filter {a : α} {l} (h : a ∈ filter p l) : p a := (mem_filter.1 h).2
/-
**List.mem_of_mem_filter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_of_mem_filter {a : α} {l} (h : a in filter p l) : a in l
参数：h : a in filter p l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.filter_subset_self`：filter_subset_self (l : List α) : filter p l su
bseteq l
-/
theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  filter_subset_self l h
/-
**List.mem_filter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_filter_of_mem {a : α} {l} (h₁ : a in l) (h₂ : p a) : a in filter p l
参数：h₁ : a in l；h₂ : p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_filter`：∀ {α : Type u_1} {p : α → Bool} {as : List α} {x : α}, 
x ∈ List.filter p as ↔ x ∈ as ∧ p x = true
-/
theorem mem_filter_of_mem {a : α} {l} (h₁ : a ∈ l) (h₂ : p a) : a ∈ filter p l :=
  mem_filter.2 ⟨h₁, h₂⟩

variable (p)
/-
**List.monotone_filter_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：monotone_filter_right (l : List α) ⦃p q : α -> Bool⦄ (h : forall a, p a ->
 q a) : l.filter p <+ l.filter q
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monotone_filter_right (l : List α) ⦃p q : α → Bool⦄
    (h : ∀ a, p a → q a) : l.filter p <+ l.filter q := by
  induction l with grind
/-
**List.map_filter** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：map_filter {f : α -> β} (hf : Injective f) (l : List α) [DecidablePred fun
 b => exists a, p a ∧ f a = b] : (l.filter p).map f = (l.map f).filter fun b => 
exists a, p a ∧ f a = b
参数：hf : Injective f；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filter_map`：∀ {β : Type u_1} {α : Type u_2} {f : β → α} {p : α → Bo
ol} {l : List β},   List.filter p (List.map f l) = List.map f (List.filter (p ∘ 
f) l)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Bool.decide_eq_true`：∀ {b : Bool} {x : Decidable (b = true)}, decide (b 
= true) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_filter {f : α → β} (hf : Injective f) (l : List α)
    [DecidablePred fun b => ∃ a, p a ∧ f a = b] :
    (l.filter p).map f = (l.map f).filter fun b => ∃ a, p a ∧ f a = b := by
  simp [comp_def, filter_map, hf.eq_iff]
/-
**List.filter_attach'** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：filter_attach' (l : List α) (p : {a // a in l} -> Bool) [DecidableEq α] : 
l.attach.filter p = (l.filter fun x => exists h, p ⟨x, h⟩).attach.map (Subtype.m
ap id fun _ => mem_of_mem_filter)
参数：l : List α；p : {a // a in l} -> Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.map_injective_iff`：map_injective_iff {f : α -> β} : Injective (map 
f) ↔ Injective f
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.mem_of_mem_filter`：mem_of_mem_filter {a : α} {l} (h : a in filter p
 l) : a in l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.map_filter`：map_filter {f : α -> β} (hf : Injective f) (l : List α)
 [DecidablePred fun b => exists a, p a ∧ f a = b] : (l.filter p).map f = (l.map 
f).fi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `List.map_subtype`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {l : Li
st { x // p x }} {f : { x // p x } → β} {g : α → β},   (∀ (x : α) (h : p x), f ⟨
x, h⟩ …
· 使用定理 `List.unattach_attach`：∀ {α : Type u_1} {l : List α}, l.attach.unattach =
 l
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.map_coe`：∀ {α : Sort u_1} {β : Sort u_2} {p : α → Prop} {q : β →
 Prop} (f : α → β) (h : ∀ (a : α), p a → q (f a))   (a : Subtype p), ↑(Subtype.m
ap f …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_attach' (l : List α) (p : {a // a ∈ l} → Bool) [DecidableEq α] :
    l.attach.filter p =
      (l.filter fun x => ∃ h, p ⟨x, h⟩).attach.map (Subtype.map id fun _ => mem_of_mem_filter) := by
  classical
  refine map_injective_iff.2 Subtype.coe_injective ?_
  simp [comp_def, map_filter _ Subtype.coe_injective]
/-
**List.filter_attach** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：filter_attach (l : List α) (p : α -> Bool) : (l.attach.filter fun x => p x
 : List {x // x in l}) = (l.filter p).attach.map (Subtype.map id fun _ => mem_of
_mem_filter)
参数：l : List α；p : α -> Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.map_injective_iff`：map_injective_iff {f : α -> β} : Injective (map 
f) ↔ Injective f
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `List.mem_of_mem_filter`：mem_of_mem_filter {a : α} {l} (h : a in filter p
 l) : a in l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.attach_map_subtype_val`：∀ {α : Type u_1} (l : List α), List.map Sub
type.val l.attach = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_attach (l : List α) (p : α → Bool) :
    (l.attach.filter fun x => p x : List {x // x ∈ l}) =
      (l.filter p).attach.map (Subtype.map id fun _ => mem_of_mem_filter) :=
  map_injective_iff.2 Subtype.coe_injective <| by
    simp_rw [map_map, comp_def, Subtype.map, id, ← Function.comp_apply (g := Subtype.val),
      ← filter_map, attach_map_subtype_val]
/-
**List.filter_comm** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：filter_comm (q) (l : List α) : filter p (filter q l) = filter q (filter p 
l)
参数：q；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filter_filter`：∀ {α : Type u_1} {p q : α → Bool} {l : List α}, List
.filter p (List.filter q l) = List.filter (fun a => p a && q a) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bool.and_comm`：∀ (x y : Bool), (x && y) = (y && x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_comm (q) (l : List α) : filter p (filter q l) = filter q (filter p l) := by
  simp [Bool.and_comm]

@[simp]
/-
**List.filter_true** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：filter_true (l : List α) : filter (fun _ => true) l = l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem filter_true (l : List α) :
    filter (fun _ => true) l = l := by induction l <;> simp [*, filter]

@[simp]
/-
**List.filter_false** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：filter_false (l : List α) : filter (fun _ => false) l = []
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem filter_false (l : List α) :
    filter (fun _ => false) l = [] := by induction l <;> simp [*, filter]

end Filter

/-! ### eraseP -/

section eraseP

variable {p : α → Bool}

-- Cannot be @[simp] because `a` cannot be inferred by `simp`.
/-
**List.length_eraseP_add_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_eraseP_add_one {l : List α} {a} (al : a in l) (pa : p a) : (l.erase
P p).length + 1 = l.length
参数：al : a in l；pa : p a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_eraseP_add_one {l : List α} {a} (al : a ∈ l) (pa : p a) :
    (l.eraseP p).length + 1 = l.length := by grind

end eraseP

/-! ### erase -/

section Erase

variable [BEq α] [LawfulBEq α]

-- @[simp] -- removed because LHS is not in simp normal form
/-
**List.length_erase_add_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_erase_add_one {a : α} {l : List α} (h : a in l) : (l.erase a).lengt
h + 1 = l.length
参数：h : a in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.erase_eq_eraseP`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a :
 α) (l : List α), l.erase a = List.eraseP (fun x => a == x) l
· 使用定理 `List.length_eraseP_add_one`：length_eraseP_add_one {l : List α} {a} (al :
 a in l) (pa : p a) : (l.eraseP p).length + 1 = l.length
· 使用定理 `BEq.rfl`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] {a : α}, (a == a) =
 true
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
-/
theorem length_erase_add_one {a : α} {l : List α} (h : a ∈ l) :
    (l.erase a).length + 1 = l.length := by
  rw [erase_eq_eraseP, length_eraseP_add_one h BEq.rfl]
/-
**List.map_erase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_erase [BEq β] [LawfulBEq β] {f : α -> β} (finj : Injective f) {a : α} 
(l : List α) : map f (l.erase a) = (map f l).erase (f a)
参数：finj : Injective f；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.erase_eq_eraseP`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a :
 α) (l : List α), l.erase a = List.eraseP (fun x => a == x) l
· 使用定理 `List.eraseP_map`：∀ {β : Type u_1} {α : Type u_2} {p : α → Bool} {f : β →
 α} {l : List β},   List.eraseP p (List.map f l) = List.map f (List.eraseP (p ∘ 
f) l)
-/
theorem map_erase [BEq β] [LawfulBEq β] {f : α → β} (finj : Injective f) {a : α} (l : List α) :
    map f (l.erase a) = (map f l).erase (f a) := by
  have : (a == ·) = (f a == f ·) := by ext b; simp [finj.eq_iff]
  rw [erase_eq_eraseP, erase_eq_eraseP, eraseP_map, this]; rfl
/-
**List.map_foldl_erase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_foldl_erase [BEq β] [LawfulBEq β] {f : α -> β} (finj : Injective f) {l
₁ l₂ : List α} : map f (foldl List.erase l₁ l₂) = foldl (fun l a => l.erase (f a
)) (map f l₁) l₂
参数：finj : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_erase`：map_erase [BEq β] [LawfulBEq β] {f : α -> β} (finj : Inj
ective f) {a : α} (l : List α) : map f (l.erase a) = (map f l).erase (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_foldl_erase [BEq β] [LawfulBEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (foldl List.erase l₁ l₂) = foldl (fun l a => l.erase (f a)) (map f l₁) l₂ := by
  induction l₂ generalizing l₁ <;> [rfl; simp only [foldl_cons, map_erase finj, *]]
/-
**List.erase_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：erase_getElem [BEq ι] [LawfulBEq ι] {l : List ι} {i : Nat} (hi : i < l.len
gth) : Perm (l.erase l[i]) (l.eraseIdx i)
参数：hi : i < l.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem erase_getElem [BEq ι] [LawfulBEq ι] {l : List ι} {i : ℕ} (hi : i < l.length) :
    Perm (l.erase l[i]) (l.eraseIdx i) := by
  induction l generalizing i with
  | nil => simp
  | cons a l IH => cases i with grind
/-
**List.length_eraseIdx_add_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_eraseIdx_add_one {l : List ι} {i : Nat} (h : i < l.length) : (l.era
seIdx i).length + 1 = l.length
参数：h : i < l.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_eraseIdx_add_one {l : List ι} {i : ℕ} (h : i < l.length) :
    (l.eraseIdx i).length + 1 = l.length := by grind

end Erase

/-! ### diff -/

section Diff

@[simp]
/-
**List.map_diff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_diff [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α -> β} (finj : 
Injective f) {l₁ l₂ : List α} : map f (l₁.diff l₂) = (map f l₁).diff (map f l₂)
参数：finj : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.diff_eq_foldl`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (l₁ l₂
 : List α), l₁.diff l₂ = List.foldl List.erase l₁ l₂
· 使用定理 `List.map_foldl_erase`：map_foldl_erase [BEq β] [LawfulBEq β] {f : α -> β}
 (finj : Injective f) {l₁ l₂ : List α} : map f (foldl List.erase l₁ l₂) = foldl 
(fun l a =…
· 使用定理 `List.foldl_map`：∀ {β₁ : Type u_1} {β₂ : Type u_2} {α : Type u_3} {f : β₁
 → β₂} {g : α → β₂ → α} {l : List β₁} {init : α},   List.foldl g init (List.map 
f l)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_diff [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (finj : Injective f) {l₁ l₂ : List α} :
    map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) := by
  simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]

end Diff

section Choose

variable (p : α → Prop) [DecidablePred p] (l : List α)

/-
**List.choose_spec** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：choose_spec (hp : exists a, a in l ∧ p a) : choose p l hp in l ∧ p (choose
 p l hp)
参数：hp : exists a, a in l ∧ p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem choose_spec (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property
/-
**List.choose_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：choose_mem (hp : exists a, a in l ∧ p a) : choose p l hp in l
参数：hp : exists a, a in l ∧ p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.choose_spec`：choose_spec (hp : exists a, a in l ∧ p a) : choose p l
 hp in l ∧ p (choose p l hp)
-/
theorem choose_mem (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1
/-
**List.choose_property** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：choose_property (hp : exists a, a in l ∧ p a) : p (choose p l hp)
参数：hp : exists a, a in l ∧ p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.choose_spec`：choose_spec (hp : exists a, a in l ∧ p a) : choose p l
 hp in l ∧ p (choose p l hp)
-/
theorem choose_property (hp : ∃ a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2

end Choose

/-! ### Forall -/

section Forall

variable {p q : α → Prop} {l : List α}

@[simp]
/-
**List.forall_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (p : α → Prop) (x : α) (l : List α), List.Forall p (x :: l)
 ↔ p x ∧ List.Forall p l
参数：p : α → Prop；x : α；l : List α；x :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `trivial`：True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem forall_cons (p : α → Prop) (x : α) : ∀ l : List α, Forall p (x :: l) ↔ p x ∧ Forall p l
  | [] => (and_iff_left_of_imp fun _ ↦ trivial).symm
  | _ :: _ => Iff.rfl

@[simp]
/-
**List.forall_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {p : α → Prop} {xs ys : List α}, List.Forall p (xs ++ ys) ↔
 List.Forall p xs ∧ List.Forall p ys
参数：xs ++ ys。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_append {p : α → Prop} : ∀ {xs ys : List α},
    Forall p (xs ++ ys) ↔ Forall p xs ∧ Forall p ys
  | [] => by simp
  | _ :: _ => by simp [forall_append, and_assoc]
/-
**List.forall_iff_forall_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {p : α → Prop} {l : List α}, List.Forall p l ↔ ∀ x ∈ l, p x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_iff_forall_mem : ∀ {l : List α}, Forall p l ↔ ∀ x ∈ l, p x
  | [] => (iff_true_intro <| forall_mem_nil _).symm
  | x :: l => by rw [forall_mem_cons, forall_cons, forall_iff_forall_mem]
/-
**List.Forall.imp** 是 Mathlib 中的一个定理，位于命名空间 `List.Forall`。
形式化陈述：∀ {α : Type u} {p q : α → Prop}, (∀ (x : α), p x → q x) → ∀ {l : List α}, 
List.Forall p l → List.Forall q l
参数：∀ (x : α), p x → q x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Forall.imp (h : ∀ x, p x → q x) : ∀ {l : List α}, Forall p l → Forall q l
  | [] => id
  | x :: l => by
    simp only [forall_cons, and_imp]
    rw [← and_imp]
    exact And.imp (h x) (Forall.imp h)

@[simp]
/-
**List.forall_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_map_iff {p : β -> Prop} (f : α -> β) : Forall p (l.map f) ↔ Forall 
(p ∘ f) l
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.Forall.eq_1`：∀ {α : Type u_1} (p : α → Prop), List.Forall p [] = Tr
ue
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem forall_map_iff {p : β → Prop} (f : α → β) : Forall p (l.map f) ↔ Forall (p ∘ f) l := by
  induction l <;> simp [*]
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : α → Prop) [DecidablePred p] : DecidablePred (Forall p) := fun _ =>
  decidable_of_iff' _ forall_iff_forall_mem

end Forall

/-! ### Miscellaneous lemmas -/

/-
**List.get_attach** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_attach (l : List α) (i) : (l.attach.get i).1 = l.get ⟨i, length_attach
 (l
参数：l : List α；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.length_attach`：∀ {α : Type u_1} {l : List α}, l.attach.length = l.l
ength
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `List.getElem_attach`：∀ {α : Type u_1} {xs : List α} {i : ℕ} (h : i < xs.
attach.length), xs.attach[i] = ⟨xs[i], ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Miscellaneous lemmas
-/
theorem get_attach (l : List α) (i) :
    (l.attach.get i).1 = l.get ⟨i, length_attach (l := l) ▸ i.2⟩ := by simp

section Disjoint

/-- The images of disjoint lists under a partially defined map are disjoint -/
/-
**List.disjoint_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：disjoint_pmap {p : α -> Prop} {f : forall a : α, p a -> β} {s t : List α} 
(hs : forall a in s, p a) (ht : forall a in t, p a) (hf : forall (a a' : α) (ha 
: p a) (ha' : p a'), f a ha = f a' ha' -> a = a') (h : Disjoint s t) : Disjoint 
(s.pmap f hs) (t.pmap f ht)
参数：hs : forall a in s, p a；ht : forall a in t, p a；hf : forall (a a' : α) (ha : 
p a) (ha' : p a'), f a ha = f a' ha' -> a = a'；h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The images of disjoint lists under a partially defined map are disjoint
-/
theorem disjoint_pmap {p : α → Prop} {f : ∀ a : α, p a → β} {s t : List α}
    (hs : ∀ a ∈ s, p a) (ht : ∀ a ∈ t, p a)
    (hf : ∀ (a a' : α) (ha : p a) (ha' : p a'), f a ha = f a' ha' → a = a')
    (h : Disjoint s t) :
    Disjoint (s.pmap f hs) (t.pmap f ht) := by
  simp only [Disjoint, mem_pmap]
  rintro b ⟨a, ha, rfl⟩ ⟨a', ha', ha''⟩
  apply h ha
  rwa [hf a a' (hs a ha) (ht a' ha') ha''.symm]

/-- The images of disjoint lists under an injective map are disjoint -/
/-
**List.disjoint_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：disjoint_map {f : α -> β} {s t : List α} (hf : Function.Injective f) (h : 
Disjoint s t) : Disjoint (s.map f) (t.map f)
参数：hf : Function.Injective f；h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.pmap_eq_map`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : α 
→ β} {l : List α} (H : ∀ a ∈ l, p a),   List.pmap (fun a x => f a) l H = List.ma
p f l
· 使用定理 `List.disjoint_pmap`：disjoint_pmap {p : α -> Prop} {f : forall a : α, p a
 -> β} {s t : List α} (hs : forall a in s, p a) (ht : forall a in t, p a) (hf : 
forall (…

--- 原说明 ---
The images of disjoint lists under an injective map are disjoint
-/
theorem disjoint_map {f : α → β} {s t : List α} (hf : Function.Injective f)
    (h : Disjoint s t) : Disjoint (s.map f) (t.map f) := by
  rw [← pmap_eq_map (fun _ _ ↦ trivial), ← pmap_eq_map (fun _ _ ↦ trivial)]
  exact disjoint_pmap _ _ (fun _ _ _ _ h' ↦ hf h') h

alias Disjoint.map := disjoint_map
/-
**List.Disjoint.of_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Disjoint`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} {s t : List α}, (List.map f s).Dis
joint (List.map f t) → s.Disjoint t
参数：List.map f s；List.map f t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_map_of_mem`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {a : α
} {f : α → β}, a ∈ l → f a ∈ List.map f l
-/
theorem Disjoint.of_map {f : α → β} {s t : List α} (h : Disjoint (s.map f) (t.map f)) :
    Disjoint s t := fun _a has hat ↦
  h (mem_map_of_mem has) (mem_map_of_mem hat)
/-
**List.Disjoint.map_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Disjoint`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} {s t : List α},   Function.Injecti
ve f → ((List.map f s).Disjoint (List.map f t) ↔ s.Disjoint t)
参数：(List.map f s).Disjoint (List.map f t) ↔ s.Disjoint t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Disjoint.of_map`：∀ {α : Type u} {β : Type v} {f : α → β} {s t : Lis
t α}, (List.map f s).Disjoint (List.map f t) → s.Disjoint t
· 使用定理 `List.Disjoint.map`：∀ {α : Type u} {β : Type v} {f : α → β} {s t : List α
},   Function.Injective f → s.Disjoint t → (List.map f s).Disjoint (List.map f t
)
-/
theorem Disjoint.map_iff {f : α → β} {s t : List α} (hf : Function.Injective f) :
    Disjoint (s.map f) (t.map f) ↔ Disjoint s t :=
  ⟨fun h ↦ h.of_map, fun h ↦ h.map hf⟩
/-
**List.Perm.disjoint_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u} {l₁ l₂ l : List α}, l₁.Perm l₂ → (l₁.Disjoint l ↔ l₂.Disjoi
nt l)
参数：l₁.Disjoint l ↔ l₂.Disjoint l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Perm.disjoint_left {l₁ l₂ l : List α} (p : List.Perm l₁ l₂) :
    Disjoint l₁ l ↔ Disjoint l₂ l := by
  simp_rw [List.disjoint_left, p.mem_iff]
/-
**List.Perm.disjoint_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u} {l₁ l₂ l : List α}, l₁.Perm l₂ → (l.Disjoint l₁ ↔ l.Disjoin
t l₂)
参数：l.Disjoint l₁ ↔ l.Disjoint l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Perm.disjoint_right {l₁ l₂ l : List α} (p : List.Perm l₁ l₂) :
    Disjoint l l₁ ↔ Disjoint l l₂ := by
  simp_rw [List.disjoint_right, p.mem_iff]

@[simp]
/-
**List.disjoint_reverse_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：disjoint_reverse_left {l₁ l₂ : List α} : Disjoint l₁.reverse l₂ ↔ Disjoint
 l₁ l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.disjoint_left`：∀ {α : Type u} {l₁ l₂ l : List α}, l₁.Perm l₂ →
 (l₁.Disjoint l ↔ l₂.Disjoint l)
· 使用定理 `List.reverse_perm`：∀ {α : Type u_1} (l : List α), l.reverse.Perm l
-/
theorem disjoint_reverse_left {l₁ l₂ : List α} : Disjoint l₁.reverse l₂ ↔ Disjoint l₁ l₂ :=
  reverse_perm _ |>.disjoint_left

@[simp]
/-
**List.disjoint_reverse_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：disjoint_reverse_right {l₁ l₂ : List α} : Disjoint l₁ l₂.reverse ↔ Disjoin
t l₁ l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.disjoint_right`：∀ {α : Type u} {l₁ l₂ l : List α}, l₁.Perm l₂ 
→ (l.Disjoint l₁ ↔ l.Disjoint l₂)
· 使用定理 `List.reverse_perm`：∀ {α : Type u_1} (l : List α), l.reverse.Perm l
-/
theorem disjoint_reverse_right {l₁ l₂ : List α} : Disjoint l₁ l₂.reverse ↔ Disjoint l₁ l₂ :=
  reverse_perm _ |>.disjoint_right

end Disjoint

section lookup
variable [BEq α] [LawfulBEq α]

/-
**List.lookup_graph** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：lookup_graph (f : α -> β) {a : α} {as : List α} (h : a in as) : lookup a (
as.map fun x => (x, f x)) = some (f a)
参数：f : α -> β；h : a in as。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lookup_graph (f : α → β) {a : α} {as : List α} (h : a ∈ as) :
    lookup a (as.map fun x => (x, f x)) = some (f a) := by
  induction as with grind

end lookup

section range'

@[simp]
/-
**List.range'_0** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (a b : ℕ), List.range' a b 0 = List.replicate b a
参数：a b : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.range'_zero`：∀ {s step : ℕ}, List.range' s 0 step = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.range'_succ`：∀ {s n step : ℕ}, List.range' s (n + 1) step = s :: Li
st.range' (s + step) n step
-/
lemma range'_0 (a b : ℕ) : range' a b 0 = replicate b a := by
  induction b with
  | zero => simp
  | succ b ih => simp [range'_succ, ih, replicate_succ]
/-
**List.left_le_of_mem_range'** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：left_le_of_mem_range' {a b s x : Nat} (hx : x in List.range' a b s) : a <=
 x
参数：hx : x in List.range' a b s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_range'`：∀ {s step m n : ℕ}, m ∈ List.range' s n step ↔ ∃ i < n,
 m = s + step * i
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma left_le_of_mem_range' {a b s x : ℕ} (hx : x ∈ List.range' a b s) : a ≤ x := by
  obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hx
  exact le_add_right a (s * i)

end range'

end List

