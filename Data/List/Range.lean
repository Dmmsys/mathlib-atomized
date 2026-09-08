/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Kim Morrison
-/
module

public import Mathlib.Data.List.Chain

/-!
# Ranges of naturals as lists

This file shows basic results about `List.iota`, `List.range`, `List.range'`
and defines `List.finRange`.
`finRange n` is the list of elements of `Fin n`.
`iota n = [n, n - 1, ..., 1]` and `range n = [0, ..., n - 1]` are basic list constructions used for
tactics. `range' a b = [a, ..., a + b - 1]` is there to help prove properties about them.
Actual maths should use `List.Ico` instead.
-/

@[expose] public section

universe u

open Nat

namespace List

variable {α : Type u}

/-
**List.getElem_range'_1** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {n m : ℕ} (i : ℕ) (H : i < (List.range' n m).length), (List.range' n m)[
i] = n + i
参数：i : ℕ；H : i < (List.range' n m).length；List.range' n m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_range'`：getElem_range'_1 {n m} (i) (H : i < (range' n m).le
ngth) : (range' n m)[i] = n + i
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem getElem_range'_1 {n m} (i) (H : i < (range' n m).length) :
    (range' n m)[i] = n + i := by simp
/-
**List.isChain_range** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_range (r : Nat -> Nat -> Prop) (n : Nat) : IsChain r (range n) ↔ f
orall m < n - 1, r m m.succ
参数：r : Nat -> Nat -> Prop；n : Nat。
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
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Nat.forall_lt_succ_right`：∀ {n : ℕ} {p : ℕ → Prop}, (∀ m < n + 1, p m) ↔
 (∀ m < n, p m) ∧ p n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isChain_range (r : ℕ → ℕ → Prop) (n : ℕ) :
    IsChain r (range n) ↔ ∀ m < n - 1, r m m.succ := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp only [range_succ, Nat.add_one_sub_one, Nat.lt_sub_iff_add_lt] at hn ⊢
    cases n with
    | zero => simp
    | succ n =>
      simp only [range_succ, Nat.add_lt_add_iff_right, succ_eq_add_one, append_assoc, cons_append,
        nil_append, isChain_append_cons_cons, IsChain.singleton, and_true] at hn ⊢
      rw [hn, forall_lt_succ_right]
/-
**List.isChain_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_range_succ (r : Nat -> Nat -> Prop) (n : Nat) : IsChain r (range n
.succ) ↔ forall m < n, r m m.succ
参数：r : Nat -> Nat -> Prop；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.isChain_range`：isChain_range (r : Nat -> Nat -> Prop) (n : Nat) : I
sChain r (range n) ↔ forall m < n - 1, r m m.succ
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Nat.add_one_sub_one`：∀ (n : ℕ), n + 1 - 1 = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isChain_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) :
    IsChain r (range n.succ) ↔ ∀ m < n, r m m.succ := by
  rw [isChain_range, succ_eq_add_one, Nat.add_one_sub_one]
/-
**List.isChain_cons_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_range_succ (r : Nat -> Nat -> Prop) (n a : Nat) : IsChain r (
a :: range n.succ) ↔ r a 0 ∧ forall m < n, r m m.succ
参数：r : Nat -> Nat -> Prop；n a : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.range_succ_eq_map`：∀ {n : ℕ}, List.range (n + 1) = 0 :: List.map Na
t.succ (List.range n)
· 使用定理 `List.isChain_cons_cons`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l
 : List α},   List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.isChain_range_succ`：isChain_range_succ (r : Nat -> Nat -> Prop) (n 
: Nat) : IsChain r (range n.succ) ↔ forall m < n, r m m.succ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isChain_cons_range_succ (r : ℕ → ℕ → Prop) (n a : ℕ) :
    IsChain r (a :: range n.succ) ↔ r a 0 ∧ ∀ m < n, r m m.succ := by
  rw [range_succ_eq_map, isChain_cons_cons, and_congr_right_iff,
    ← isChain_range_succ, range_succ_eq_map]
  exact fun _ => Iff.rfl

section Ranges

/--
From `l : List ℕ`, construct `l.ranges : List (List ℕ)` such that `l.ranges.map List.length = l`
and `l.ranges.join = range l.sum`
* Example: `[1,2,3].ranges = [[0],[1,2],[3,4,5]]` -/
/-
**List.ranges** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：List ℕ → List (List ℕ)
参数：List ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From `l : List ℕ`, construct `l.ranges : List (List ℕ)` such that `l.ranges.map 
List.length = l`
and `l.ranges.join = range l.sum`
* Example: `[1,2,3].ranges = [[0],[1,2],[3,4,5]]`
-/
def ranges : List ℕ → List (List ℕ)
  | [] => nil
  | a::l => range a::(ranges l).map (map (a + ·))

/-- The members of `l.ranges` are pairwise disjoint -/
/-
**List.ranges_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ranges_disjoint (l : List Nat) : Pairwise Disjoint (ranges l)
参数：l : List Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_range`：∀ {m n : ℕ}, m ∈ List.range n ↔ m < n
· 使用定理 `List.pairwise_map`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {R : 
α_1 → α_1 → Prop} {l : List α},   List.Pairwise R (List.map f l) ↔ List.Pairwise
 (fun a…
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `List.disjoint_map`：disjoint_map {f : α -> β} {s t : List α} (hf : Functi
on.Injective f) (h : Disjoint s t) : Disjoint (s.map f) (t.map f)
· 使用定理 `Nat.add_left_cancel`：∀ {n m k : ℕ}, n + m = n + k → m = k

--- 原说明 ---
The members of `l.ranges` are pairwise disjoint
-/
theorem ranges_disjoint (l : List ℕ) :
    Pairwise Disjoint (ranges l) := by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l hl =>
    simp only [ranges, pairwise_cons]
    constructor
    · intro s hs
      obtain ⟨s', _, rfl⟩ := mem_map.mp hs
      intro u hu
      rw [mem_map]
      rw [mem_range] at hu
      lia
    · rw [pairwise_map]
      apply Pairwise.imp _ hl
      intro u v
      apply disjoint_map
      exact fun u v => Nat.add_left_cancel

/-- The lengths of the members of `l.ranges` are those given by `l` -/
/-
**List.ranges_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ranges_length (l : List Nat) : l.ranges.map length = l
参数：l : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_congr_left`：∀ {α : Type u_1} {l : List α} {α_1 : Type u_2} {f g
 : α → α_1}, (∀ a ∈ l, f a = g a) → List.map f l = List.map g l
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length

--- 原说明 ---
The lengths of the members of `l.ranges` are those given by `l`
-/
theorem ranges_length (l : List ℕ) :
    l.ranges.map length = l := by
  induction l with
  | nil => simp only [ranges, map_nil]
  | cons a l hl => -- (a :: l)
    simp only [ranges, map_cons, length_range, map_map, cons.injEq, true_and]
    conv_rhs => rw [← hl]
    apply map_congr_left
    intro s _
    simp only [Function.comp_apply, length_map]

end Ranges

end List

