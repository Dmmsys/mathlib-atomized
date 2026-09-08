/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Sym.Sym2

/-! # Unordered tuples of elements of a list

Defines `List.sym` and the specialized `List.sym2` for computing lists of all unordered n-tuples
from a given list. These are list versions of `Nat.multichoose`.

## Main declarations

* `List.sym`: `xs.sym n` is a list of all unordered n-tuples of elements from `xs`,
  with multiplicity. The list's values are in `Sym α n`.
* `List.sym2`: `xs.sym2` is a list of all unordered pairs of elements from `xs`,
  with multiplicity. The list's values are in `Sym2 α`.

## TODO

* Prove `protected theorem Perm.sym (n : ℕ) {xs ys : List α} (h : xs ~ ys) : xs.sym n ~ ys.sym n`
  and lift the result to `Multiset` and `Finset`.

-/

@[expose] public section

namespace List

variable {α β : Type*}

section Sym2

/-- `xs.sym2` is a list of all unordered pairs of elements from `xs`.
If `xs` has no duplicates then neither does `xs.sym2`. -/
/-
**List.sym2** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → List α → List (Sym2 α)
参数：Sym2 α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`xs.sym2` is a list of all unordered pairs of elements from `xs`.
If `xs` has no duplicates then neither does `xs.sym2`.
-/
protected def sym2 : List α → List (Sym2 α)
  | [] => []
  | x :: xs => (x :: xs).map (fun y => s(x, y)) ++ xs.sym2
/-
**List.sym2_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sym2_map (f : α -> β) (xs : List α) : (xs.map f).sym2 = xs.sym2.map (Sym2.
map f)
参数：f : α -> β；xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.sym2.eq_1`：∀ {α : Type u_1}, [].sym2 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.sym2.eq_2`：∀ {α : Type u_1} (x_1 : α) (xs : List α), (x_1 :: xs).sy
m2 = List.map (fun y => s(x_1, y)) (x_1 :: xs) ++ xs.sym2
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `List.append_cancel_right_eq`：∀ {α : Type u_1} (as bs cs : List α), (as +
+ bs = cs ++ bs) = (as = cs)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem sym2_map (f : α → β) (xs : List α) :
    (xs.map f).sym2 = xs.sym2.map (Sym2.map f) := by
  induction xs with
  | nil => simp [List.sym2]
  | cons x xs ih => simp [List.sym2, ih, Function.comp]
/-
**List.mem_sym2_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_sym2_cons_iff {x : α} {xs : List α} {z : Sym2 α} : z in (x :: xs).sym2
 ↔ z = s(x, x) ∨ (exists y, y in xs ∧ z = s(x, y)) ∨ z in xs.sym2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sym2_cons_iff {x : α} {xs : List α} {z : Sym2 α} :
    z ∈ (x :: xs).sym2 ↔ z = s(x, x) ∨ (∃ y, y ∈ xs ∧ z = s(x, y)) ∨ z ∈ xs.sym2 := by
  simp only [List.sym2, map_cons, cons_append, mem_cons, mem_append, mem_map]
  simp only [eq_comm]

@[simp]
/-
**List.sym2_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sym2_eq_nil_iff {xs : List α} : xs.sym2 = [] ↔ xs = []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem sym2_eq_nil_iff {xs : List α} : xs.sym2 = [] ↔ xs = [] := by
  cases xs <;> simp [List.sym2]
/-
**List.left_mem_of_mk_mem_sym2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：left_mem_of_mk_mem_sym2 {xs : List α} {a b : α} (h : s(a, b) in xs.sym2) :
 a in xs
参数：h : s(a, b) in xs.sym2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `List.mem_sym2_cons_iff`：mem_sym2_cons_iff {x : α} {xs : List α} {z : Sym
2 α} : z in (x :: xs).sym2 ↔ z = s(x, x) ∨ (exists y, y in xs ∧ z = s(x, y)) ∨ z
 in xs.sym2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_or_left`：∀ {a b c : Prop}, a ∧ (b ∨ c) ↔ a ∧ b ∨ a ∧ c
· 使用定理 `Sym2.eq_iff`：eq_iff {x y z w : α} : s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ 
x = w ∧ y = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem left_mem_of_mk_mem_sym2 {xs : List α} {a b : α}
    (h : s(a, b) ∈ xs.sym2) : a ∈ xs := by
  induction xs with
  | nil => exact (not_mem_nil h).elim
  | cons x xs ih =>
    rw [mem_cons]
    rw [mem_sym2_cons_iff] at h
    obtain (h | ⟨c, hc, h⟩ | h) := h
    · rw [Sym2.eq_iff, ← and_or_left] at h
      exact .inl h.1
    · rw [Sym2.eq_iff] at h
      obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := h <;> simp [hc]
    · exact .inr <| ih h
/-
**List.right_mem_of_mk_mem_sym2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：right_mem_of_mk_mem_sym2 {xs : List α} {a b : α} (h : s(a, b) in xs.sym2) 
: b in xs
参数：h : s(a, b) in xs.sym2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.left_mem_of_mk_mem_sym2`：left_mem_of_mk_mem_sym2 {xs : List α} {a b
 : α} (h : s(a, b) in xs.sym2) : a in xs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
-/
theorem right_mem_of_mk_mem_sym2 {xs : List α} {a b : α}
    (h : s(a, b) ∈ xs.sym2) : b ∈ xs := by
  rw [Sym2.eq_swap] at h
  exact left_mem_of_mk_mem_sym2 h
/-
**List.mk_mem_sym2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mk_mem_sym2 {xs : List α} {a b : α} (ha : a in xs) (hb : b in xs) : s(a, b
) in xs.sym2
参数：ha : a in xs；hb : b in xs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_sym2_cons_iff`：mem_sym2_cons_iff {x : α} {xs : List α} {z : Sym
2 α} : z in (x :: xs).sym2 ↔ z = s(x, x) ∨ (exists y, y in xs ∧ z = s(x, y)) ∨ z
 in xs.sym2
-/
theorem mk_mem_sym2 {xs : List α} {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) :
    s(a, b) ∈ xs.sym2 := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [mem_sym2_cons_iff]
    grind
/-
**List.mk_mem_sym2_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mk_mem_sym2_iff {xs : List α} {a b : α} : s(a, b) in xs.sym2 ↔ a in xs ∧ b
 in xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.left_mem_of_mk_mem_sym2`：left_mem_of_mk_mem_sym2 {xs : List α} {a b
 : α} (h : s(a, b) in xs.sym2) : a in xs
· 使用定理 `List.right_mem_of_mk_mem_sym2`：right_mem_of_mk_mem_sym2 {xs : List α} {a
 b : α} (h : s(a, b) in xs.sym2) : b in xs
· 使用定理 `List.mk_mem_sym2`：mk_mem_sym2 {xs : List α} {a b : α} (ha : a in xs) (hb
 : b in xs) : s(a, b) in xs.sym2
-/
theorem mk_mem_sym2_iff {xs : List α} {a b : α} :
    s(a, b) ∈ xs.sym2 ↔ a ∈ xs ∧ b ∈ xs := by
  constructor
  · intro h
    exact ⟨left_mem_of_mk_mem_sym2 h, right_mem_of_mk_mem_sym2 h⟩
  · rintro ⟨ha, hb⟩
    exact mk_mem_sym2 ha hb
/-
**List.mem_sym2_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_sym2_iff {xs : List α} {z : Sym2 α} : z in xs.sym2 ↔ forall y in z, y 
in xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sym2_iff {xs : List α} {z : Sym2 α} :
    z ∈ xs.sym2 ↔ ∀ y ∈ z, y ∈ xs := by
  refine z.ind (fun a b => ?_)
  simp [mk_mem_sym2_iff]
/-
**List.setOfPred_mem_sym2** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：setOfPred_mem_sym2 {xs : List α} : {z : Sym2 α | z in xs.sym2} = {x : α | 
x in xs}.sym2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma setOfPred_mem_sym2 {xs : List α} :
    {z : Sym2 α | z ∈ xs.sym2} = {x : α | x ∈ xs}.sym2 :=
  Set.ext fun z ↦ z.ind fun a b => by simp [mk_mem_sym2_iff]

@[deprecated (since := "2026-07-09")] alias setOf_mem_sym2 := setOfPred_mem_sym2
/-
**List.Nodup.sym2** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} {xs : List α}, xs.Nodup → xs.sym2.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sym2.eq_2`：∀ {α : Type u_1} (x_1 : α) (xs : List α), (x_1 :: xs).sy
m2 = List.map (fun y => s(x_1, y)) (x_1 :: xs) ++ xs.sym2
· 使用定理 `List.Nodup.append`：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Nodup → l₂.Nodup 
→ l₁.Disjoint l₂ → (l₁ ++ l₂).Nodup
· 使用定理 `List.Nodup.cons`：∀ {α : Type u} {l : List α} {a : α}, a ∉ l → l.Nodup → 
(a :: l).Nodup
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.nodup_cons`：∀ {α : Type u_1} {a : α} {l : List α}, (a :: l).Nodup ↔
 a ∉ l ∧ l.Nodup
· 使用定理 `List.Nodup.map`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Fu
nction.Injective f → l.Nodup → (List.map f l).Nodup
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.Nodup.of_cons`：∀ {α : Type u} {l : List α} {a : α}, (a :: l).Nodup 
→ l.Nodup
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.left_mem_of_mk_mem_sym2`：left_mem_of_mk_mem_sym2 {xs : List α} {a b
 : α} (h : s(a, b) in xs.sym2) : a in xs
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
protected theorem Nodup.sym2 {xs : List α} (h : xs.Nodup) : xs.sym2.Nodup := by
  induction xs with
  | nil => simp only [List.sym2, nodup_nil]
  | cons x xs ih =>
    rw [List.sym2]
    specialize ih h.of_cons
    rw [nodup_cons] at h
    refine Nodup.append (Nodup.cons ?notmem (h.2.map ?inj)) ih ?disj
    case disj =>
      intro z hz hz'
      simp only [mem_cons, mem_map] at hz
      obtain ⟨_, (rfl | _), rfl⟩ := hz
        <;> simp [left_mem_of_mk_mem_sym2 hz'] at h
    case notmem =>
      intro h'
      simp only [h.1, mem_map, Sym2.eq_iff, true_and, or_self, exists_eq_right] at h'
    case inj =>
      intro a b
      simp only [Sym2.eq_iff, true_and]
      rintro (rfl | ⟨rfl, rfl⟩) <;> rfl
/-
**List.map_mk_sublist_sym2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_mk_sublist_sym2 (x : α) (xs : List α) (h : x in xs) : map (fun y => s(
x, y)) xs <+ xs.sym2
参数：x : α；xs : List α；h : x in xs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.sublist_append_left`：∀ {α : Type u_1} (l₁ l₂ : List α), l₁.Sublist 
(l₁ ++ l₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.singleton_append`：∀ {α : Type u_1} {x : α} {l : List α}, [x] ++ l =
 x :: l
· 使用定理 `List.Sublist.append`：∀ {α : Type u_1} {l₁ l₂ r₁ r₂ : List α}, l₁.Sublist
 l₂ → r₁.Sublist r₂ → (l₁ ++ r₁).Sublist (l₂ ++ r₂)
· 使用定理 `List.singleton_sublist`：∀ {α : Type u_1} {a : α} {l : List α}, [a].Subli
st l ↔ a ∈ l
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
-/
theorem map_mk_sublist_sym2 (x : α) (xs : List α) (h : x ∈ xs) :
    map (fun y ↦ s(x, y)) xs <+ xs.sym2 := by
  induction xs with
  | nil => simp
  | cons x' xs ih =>
    simp only [map_cons, List.sym2, cons_append]
    cases h with
    | head =>
      exact (sublist_append_left _ _).cons_cons _
    | tail _ h =>
      refine .cons _ ?_
      rw [← singleton_append]
      refine .append ?_ (ih h)
      rw [singleton_sublist, mem_map]
      exact ⟨_, h, Sym2.eq_swap⟩
/-
**List.map_mk_disjoint_sym2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_mk_disjoint_sym2 (x : α) (xs : List α) (h : x ∉ xs) : (map (fun y => s
(x, y)) xs).Disjoint xs.sym2
参数：x : α；xs : List α；h : x ∉ xs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem map_mk_disjoint_sym2 (x : α) (xs : List α) (h : x ∉ xs) :
    (map (fun y ↦ s(x, y)) xs).Disjoint xs.sym2 := by
  induction xs with
  | nil => simp
  | cons x' xs ih => aesop (add simp mk_mem_sym2_iff, unfold safe List.Disjoint)
/-
**List.dedup_sym2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_sym2 [DecidableEq α] (xs : List α) : xs.sym2.dedup = xs.dedup.sym2
参数：xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sym2.eq_1`：∀ {α : Type u_1}, [].sym2 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {l : List α} (h : a in
 l) : dedup (a :: l) = dedup l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.mem_append_left`：∀ {α : Type u} {a : α} {as : List α} (bs : List α)
, a ∈ as → a ∈ as ++ bs
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
· 使用定理 `List.Subset.dedup_append_right`：∀ {α : Type u_1} [inst : DecidableEq α] 
{xs ys : List α}, xs ⊆ ys → (xs ++ ys).dedup = ys.dedup
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `List.map_mk_sublist_sym2`：map_mk_sublist_sym2 (x : α) (xs : List α) (h :
 x in xs) : map (fun y => s(x, y)) xs <+ xs.sym2
· 使用定理 `List.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {l : List α} (h 
: a ∉ l) : dedup (a :: l) = a :: dedup l
· 使用定理 `List.sym2.eq_2`：∀ {α : Type u_1} (x_1 : α) (xs : List α), (x_1 :: xs).sy
m2 = List.map (fun y => s(x_1, y)) (x_1 :: xs) ++ xs.sym2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `List.Disjoint.dedup_append`：∀ {α : Type u_1} [inst : DecidableEq α] {xs 
ys : List α}, xs.Disjoint ys → (xs ++ ys).dedup = xs.dedup ++ ys.dedup
（共 33 条，此处仅展示前 30 条）
-/
theorem dedup_sym2 [DecidableEq α] (xs : List α) : xs.sym2.dedup = xs.dedup.sym2 := by
  induction xs with
  | nil => simp only [List.sym2, dedup_nil]
  | cons x xs ih =>
    simp only [List.sym2, map_cons, cons_append]
    obtain hm | hm := Decidable.em (x ∈ xs)
    · rw [dedup_cons_of_mem hm, ← ih, dedup_cons_of_mem,
        List.Subset.dedup_append_right (map_mk_sublist_sym2 _ _ hm).subset]
      refine mem_append_left _ ?_
      rw [mem_map]
      exact ⟨_, hm, Sym2.eq_swap⟩
    · rw [dedup_cons_of_notMem hm, List.sym2, map_cons, ← ih, dedup_cons_of_notMem, cons_append,
        List.Disjoint.dedup_append, dedup_map_of_injective]
      · exact (Sym2.mkEmbedding _).injective
      · exact map_mk_disjoint_sym2 x xs hm
      · simp [hm, mem_sym2_iff]
/-
**List.Perm.sym2** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {xs ys : List α}, xs.Perm ys → xs.sym2.Perm ys.sym2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.Perm.append`：∀ {α : Type u_1} {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → 
t₁.Perm t₂ → (l₁ ++ t₁).Perm (l₂ ++ t₂)
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem Perm.sym2 {xs ys : List α} (h : xs ~ ys) :
    xs.sym2 ~ ys.sym2 := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    simp only [List.sym2, map_cons, cons_append, perm_cons]
    exact (h.map _).append ih
  | swap x y xs =>
    simp only [List.sym2, map_cons, cons_append]
    conv => enter [1, 2, 1]; rw [Sym2.eq_swap]
    -- Explicit permutation to speed up simps that follow.
    refine Perm.trans (Perm.swap ..) (Perm.trans (Perm.cons _ ?_) (Perm.swap ..))
    simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe,
      ← Multiset.coe_add, ← Multiset.singleton_add]
    simp only [add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
/-
**List.Sublist.sym2** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u_1} {xs ys : List α}, xs.Sublist ys → xs.sym2.Sublist ys.sym2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.append`：∀ {α : Type u_1} {l₁ l₂ r₁ r₂ : List α}, l₁.Sublist
 l₂ → r₁.Sublist r₂ → (l₁ ++ r₁).Sublist (l₂ ++ r₂)
· 使用定理 `List.nil_sublist`：∀ {α : Type u_1} (l : List α), [].Sublist l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
-/
protected theorem Sublist.sym2 {xs ys : List α} (h : xs <+ ys) : xs.sym2 <+ ys.sym2 := by
  induction h with
  | slnil => apply slnil
  | cons a h ih =>
    simp only [List.sym2]
    exact Sublist.append (nil_sublist _) ih
  | cons_cons a h ih =>
    simp only [List.sym2, map_cons, cons_append]
    exact cons_cons _ (append (Sublist.map _ h) ih)
/-
**List.Subperm.sym2** 是 Mathlib 中的一个定理，位于命名空间 `List.Subperm`。
形式化陈述：∀ {α : Type u_1} {xs ys : List α}, xs.Subperm ys → xs.sym2.Subperm ys.sym2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Subperm.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Subperm l₂ 
→ l₂.Subperm l₃ → l₁.Subperm l₃
· 使用定理 `List.Perm.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Su
bperm l₂
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.Perm.sym2`：∀ {α : Type u_1} {xs ys : List α}, xs.Perm ys → xs.sym2.
Perm ys.sym2
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.Sublist.sym2`：∀ {α : Type u_1} {xs ys : List α}, xs.Sublist ys → xs
.sym2.Sublist ys.sym2
-/
protected theorem Subperm.sym2 {xs ys : List α} (h : xs <+~ ys) : xs.sym2 <+~ ys.sym2 := by
  obtain ⟨xs', hx, h⟩ := h
  exact hx.sym2.symm.subperm.trans h.sym2.subperm
/-
**List.length_sym2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_sym2 {xs : List α} : xs.sym2.length = Nat.choose (xs.length + 1) 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sym2.eq_2`：∀ {α : Type u_1} (x_1 : α) (xs : List α), (x_1 :: xs).sy
m2 = List.map (fun y => s(x_1, y)) (x_1 :: xs) ++ xs.sym2
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
· 使用定理 `Nat.choose_succ_succ`：choose_succ_succ (n k : Nat) : choose (succ n) (su
cc k) = choose n k + choose n (succ k)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
-/
theorem length_sym2 {xs : List α} : xs.sym2.length = Nat.choose (xs.length + 1) 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.sym2, length_append, length_map, length_cons,
        Nat.choose_succ_succ, ← ih, Nat.choose_one_right]

end Sym2

section Sym

/-- `xs.sym n` is all unordered `n`-tuples from the list `xs` in some order. -/
/-
**List.sym** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (n : ℕ) → List α → List (Sym α n)
参数：n : ℕ；Sym α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`xs.sym n` is all unordered `n`-tuples from the list `xs` in some order.
-/
protected def sym : (n : ℕ) → List α → List (Sym α n)
  | 0, _ => [.nil]
  | _, [] => []
  | n + 1, x :: xs => ((x :: xs).sym n |>.map fun p => x ::ₛ p) ++ xs.sym (n + 1)

variable {xs ys : List α} {n : ℕ}
/-
**List.sym_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sym_one_eq : xs.sym 1 = xs.map (· ::ₛ .nil)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sym.eq_2`：∀ {α : Type u_1} (x : ℕ), (x = 0 → False) → List.sym x []
 = []
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.sym.eq_3`：∀ {α : Type u_1} (n : ℕ) (x_2 : α) (xs : List α),   List.
sym n.succ (x_2 :: xs) = List.map (fun p => x_2 ::ₛ p) (List.sym n (x_2 :: xs)) 
++ …
· 使用定理 `List.sym.eq_1`：∀ {α : Type u_1} (x : List α), List.sym 0 x = [Sym.nil]
· 使用定理 `List.map_singleton`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : α},
 List.map f [a] = [f a]
· 使用定理 `List.singleton_append`：∀ {α : Type u_1} {x : α} {l : List α}, [x] ++ l =
 x :: l
-/
theorem sym_one_eq : xs.sym 1 = xs.map (· ::ₛ .nil) := by
  induction xs with
  | nil => simp only [List.sym, Nat.succ_eq_add_one, Nat.reduceAdd, map_nil]
  | cons x xs ih =>
    rw [map_cons, ← ih, List.sym, List.sym, map_singleton, singleton_append]
/-
**List.sym2_eq_sym_two** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sym2_eq_sym_two : xs.sym2.map (Sym2.equivSym α) = xs.sym 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sym.eq_2`：∀ {α : Type u_1} (x : ℕ), (x = 0 → False) → List.sym x []
 = []
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.sym.eq_3`：∀ {α : Type u_1} (n : ℕ) (x_2 : α) (xs : List α),   List.
sym n.succ (x_2 :: xs) = List.map (fun p => x_2 ::ₛ p) (List.sym n (x_2 :: xs)) 
++ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.sym_one_eq`：sym_one_eq : xs.sym 1 = xs.map (· ::ₛ .nil)
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.sym2.eq_2`：∀ {α : Type u_1} (x_1 : α) (xs : List α), (x_1 :: xs).sy
m2 = List.map (fun y => s(x_1, y)) (x_1 :: xs) ++ xs.sym2
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
-/
theorem sym2_eq_sym_two : xs.sym2.map (Sym2.equivSym α) = xs.sym 2 := by
  induction xs with
  | nil => simp only [List.sym, map_eq_nil_iff, sym2_eq_nil_iff]
  | cons x xs ih =>
    rw [List.sym, ← ih, sym_one_eq, map_map, List.sym2, map_append, map_map]
    rfl
/-
**List.sym_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sym_map {β : Type*} (f : α -> β) (n : Nat) (xs : List α) : (xs.map f).sym 
n = (xs.sym n).map (Sym.map f)
参数：f : α -> β；n : Nat；xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sym_map._unary`：∀ {α : Type u_1} {β : Type u_3} (f : α → β) (_x : (
_ : ℕ) ×' List α),   List.sym _x.1 (List.map f _x.2) = List.map (Sym.map f) (Lis
t.sym _x.…
-/
theorem sym_map {β : Type*} (f : α → β) (n : ℕ) (xs : List α) :
    (xs.map f).sym n = (xs.sym n).map (Sym.map f) :=
  match n, xs with
  | 0, _ => by simp only [List.sym]; rfl
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [map_cons, List.sym, ← map_cons, sym_map f n (x :: xs), sym_map f (n + 1) xs]
    simp only [map_map, List.sym, map_append, append_cancel_right_eq]
    congr
    ext s
    simp only [Function.comp_apply, Sym.map_cons]
/-
**List.Sublist.sym** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u_1} (n : ℕ) {xs ys : List α}, xs.Sublist ys → (List.sym n xs)
.Sublist (List.sym n ys)
参数：n : ℕ；List.sym n xs；List.sym n ys。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.sym._unary`：∀ {α : Type u_1} (_x : (_ : ℕ) ×' (xs : List α)
 ×' (ys : List α) ×' xs.Sublist ys),   (List.sym _x.1 _x.2.1).Sublist (List.sym 
_x.1 _x.2.2.1…
-/
protected theorem Sublist.sym (n : ℕ) {xs ys : List α} (h : xs <+ ys) : xs.sym n <+ ys.sym n :=
  match n, h with
  | 0, _ => by simp [List.sym]
  | n + 1, .slnil => by simp only [refl]
  | n + 1, .cons a h => by
    rw [List.sym, ← nil_append (List.sym (n + 1) xs)]
    apply Sublist.append (nil_sublist _)
    exact h.sym (n + 1)
  | n + 1, .cons_cons a h => by
    rw [List.sym, List.sym]
    apply Sublist.append
    · exact ((cons_cons a h).sym n).map _
    · exact h.sym (n + 1)
/-
**List.sym_sublist_sym_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sym_sublist_sym_cons {a : α} : xs.sym n <+ (a :: xs).sym n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.sym`：∀ {α : Type u_1} (n : ℕ) {xs ys : List α}, xs.Sublist 
ys → (List.sym n xs).Sublist (List.sym n ys)
· 使用定理 `List.sublist_cons_self`：∀ {α : Type u_1} (a : α) (l : List α), l.Sublist
 (a :: l)
-/
theorem sym_sublist_sym_cons {a : α} : xs.sym n <+ (a :: xs).sym n :=
  (sublist_cons_self a xs).sym n
/-
**List.mem_of_mem_of_mem_sym** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_of_mem_of_mem_sym {n : Nat} {xs : List α} {a : α} {z : Sym α n} (ha : 
a in z) (hz : z in xs.sym n) : a in xs
参数：ha : a in z；hz : z in xs.sym n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_of_mem_of_mem_sym._unary`：∀ {α : Type u_1} {a : α} (_x : (n : ℕ
) ×' (xs : List α) ×' (z : Sym α n) ×' (_ : a ∈ z) ×' z ∈ List.sym n xs),   a ∈ 
_x.2.1
-/
theorem mem_of_mem_of_mem_sym {n : ℕ} {xs : List α} {a : α} {z : Sym α n}
    (ha : a ∈ z) (hz : z ∈ xs.sym n) : a ∈ xs :=
  match n, xs with
  | 0, xs => by
    cases Sym.eq_nil_of_card_zero z
    simp at ha
  | n + 1, [] => by simp [List.sym] at hz
  | n + 1, x :: xs => by
    rw [List.sym, mem_append, mem_map] at hz
    obtain ⟨z, hz, rfl⟩ | hz := hz
    · rw [Sym.mem_cons] at ha
      obtain rfl | ha := ha
      · simp
      · exact mem_of_mem_of_mem_sym ha hz
    · rw [mem_cons]
      right
      exact mem_of_mem_of_mem_sym ha hz
/-
**List.first_mem_of_cons_mem_sym** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：first_mem_of_cons_mem_sym {xs : List α} {n : Nat} {a : α} {z : Sym α n} (h
 : a ::ₛ z in xs.sym (n + 1)) : a in xs
参数：h : a ::ₛ z in xs.sym (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_of_mem_of_mem_sym`：mem_of_mem_of_mem_sym {n : Nat} {xs : List α
} {a : α} {z : Sym α n} (ha : a in z) (hz : z in xs.sym n) : a in xs
· 使用定理 `Sym.mem_cons_self`：mem_cons_self (a : α) (s : Sym α n) : a in a ::ₛ s
-/
theorem first_mem_of_cons_mem_sym {xs : List α} {n : ℕ} {a : α} {z : Sym α n}
    (h : a ::ₛ z ∈ xs.sym (n + 1)) : a ∈ xs :=
  mem_of_mem_of_mem_sym (Sym.mem_cons_self a z) h
/-
**List.Nodup.sym** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} (n : ℕ) {xs : List α}, xs.Nodup → (List.sym n xs).Nodup
参数：n : ℕ；List.sym n xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.sym._unary`：∀ {α : Type u_1} (_x : (_ : ℕ) ×' (xs : List α) ×
' xs.Nodup), (List.sym _x.1 _x.2.1).Nodup
-/
protected theorem Nodup.sym (n : ℕ) {xs : List α} (h : xs.Nodup) : (xs.sym n).Nodup :=
  match n, xs with
  | 0, _ => by simp [List.sym]
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [List.sym]
    refine Nodup.append (Nodup.map ?inj (Nodup.sym n h)) (Nodup.sym (n + 1) h.of_cons) ?disj
    case inj =>
      intro z z'
      simp
    case disj =>
      intro z hz hz'
      rw [mem_map] at hz
      obtain ⟨z, _hz, rfl⟩ := hz
      have := first_mem_of_cons_mem_sym hz'
      simp only [nodup_cons, this, not_true_eq_false, false_and] at h
/-
**List.length_sym** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_sym {n : Nat} {xs : List α} : (xs.sym n).length = Nat.multichoose x
s.length n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_sym._unary`：∀ {α : Type u_1} (_x : (_ : ℕ) ×' List α), (List
.sym _x.1 _x.2).length = _x.2.length.multichoose _x.1
-/
theorem length_sym {n : ℕ} {xs : List α} :
    (xs.sym n).length = Nat.multichoose xs.length n :=
  match n, xs with
  | 0, _ => by rw [List.sym, Nat.multichoose]; rfl
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [List.sym, length_append, length_map, length_cons]
    rw [@length_sym n (x :: xs), @length_sym (n + 1) xs]
    rw [Nat.multichoose_succ_succ, length_cons, add_comm]

end Sym

end List

