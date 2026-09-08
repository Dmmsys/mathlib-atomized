/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.Fintype.List
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Fin.Basic

/-!
# Cycles of a list

Lists have an equivalence relation of whether they are rotational permutations of one another.
This relation is defined as `IsRotated`.

Based on this, we define the quotient of lists by the rotation relation, called `Cycle`.

We also define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representable types. For example, the cycle `(2 1 4 3)` will be shown
as `c[2, 1, 4, 3]`. Two equal cycles may be printed differently if their internal representation
is different.

-/

@[expose] public section

assert_not_exists MonoidWithZero

namespace List

variable {α : Type*} [DecidableEq α]

/-- Return the `z` such that `x :: z :: _` appears in `xs`, or `default` if there is no such `z`. -/
/-
**List.nextOr** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → List α → α → α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return the `z` such that `x :: z :: _` appears in `xs`, or `default` if there is
 no such `z`.
-/
def nextOr : ∀ (_ : List α) (_ _ : α), α
  | [], _, default => default
  | [_], _, default => default
  -- Handles the not-found and the wraparound case
  | y :: z :: xs, x, default => if x = y then z else nextOr (z :: xs) x default

@[simp]
/-
**List.nextOr_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nextOr_nil (x d : α) : nextOr [] x d = d
参数：x d : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nextOr_nil (x d : α) : nextOr [] x d = d :=
  rfl

@[simp]
/-
**List.nextOr_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nextOr_singleton (x y d : α) : nextOr [y] x d = d
参数：x y d : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nextOr_singleton (x y d : α) : nextOr [y] x d = d :=
  rfl

@[simp]
/-
**List.nextOr_self_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nextOr_self_cons_cons (xs : List α) (x y d : α) : nextOr (x :: y :: xs) x 
d = y
参数：xs : List α；x y d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem nextOr_self_cons_cons (xs : List α) (x y d : α) : nextOr (x :: y :: xs) x d = y :=
  if_pos rfl
/-
**List.nextOr_cons_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nextOr_cons_of_ne (xs : List α) (y x d : α) (h : x != y) : nextOr (y :: xs
) x d = nextOr xs x d
参数：xs : List α；y x d : α；h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem nextOr_cons_of_ne (xs : List α) (y x d : α) (h : x ≠ y) :
    nextOr (y :: xs) x d = nextOr xs x d := by
  rcases xs with - | ⟨z, zs⟩
  · rfl
  · exact if_neg h

/-- `nextOr` does not depend on the default value, if the next value appears. -/
/-
**List.nextOr_eq_nextOr_of_mem_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nextOr_eq_nextOr_of_mem_dropLast (xs : List α) (x d d' : α) (x_mem : x in 
xs.dropLast) : nextOr xs x d = nextOr xs x d'
参数：xs : List α；x d d' : α；x_mem : x in xs.dropLast。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dropLast_singleton`：∀ {α : Type u_1} {x : α}, [x].dropLast = []
· 使用定理 `List.nextOr_self_cons_cons`：nextOr_self_cons_cons (xs : List α) (x y d :
 α) : nextOr (x :: y :: xs) x d = y
· 使用定理 `List.nextOr.eq_3`：∀ {α : Type u_1} [inst : DecidableEq α] (x x_1 y z : α
) (xs : List α),   (y :: z :: xs).nextOr x x_1 = if x = y then z else (z :: xs).
nextOr…
· 使用定理 `List.dropLast_cons_cons`：∀ {α : Type u_1} {x y : α} {zs : List α}, (x ::
 y :: zs).dropLast = x :: (y :: zs).dropLast
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p

--- 原说明 ---
`nextOr` does not depend on the default value, if the next value appears.
-/
theorem nextOr_eq_nextOr_of_mem_dropLast (xs : List α) (x d d' : α) (x_mem : x ∈ xs.dropLast) :
    nextOr xs x d = nextOr xs x d' := by
  induction xs with
  | nil => cases x_mem
  | cons y ys IH => ?_
  rcases ys with - | ⟨z, zs⟩
  · simp at x_mem
  by_cases h : x = y
  · rw [h, nextOr_self_cons_cons, nextOr_self_cons_cons]
  · rw [nextOr, nextOr, IH]
    simpa [h] using x_mem
/-
**List.mem_of_nextOr_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_of_nextOr_ne {xs : List α} {x d : α} (h : nextOr xs x d != d) : x in x
s
参数：h : nextOr xs x d != d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `List.nextOr_cons_of_ne`：nextOr_cons_of_ne (xs : List α) (y x d : α) (h :
 x != y) : nextOr (y :: xs) x d = nextOr xs x d
-/
theorem mem_of_nextOr_ne {xs : List α} {x d : α} (h : nextOr xs x d ≠ d) : x ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons y ys IH => ?_
  rcases ys with - | ⟨z, zs⟩
  · simp at h
  · by_cases hx : x = y
    · simp [hx]
    · rw [nextOr_cons_of_ne _ _ _ _ hx] at h
      simpa [hx] using IH h
/-
**List.nextOr_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nextOr_concat {xs : List α} {x : α} (d : α) (h : x ∉ xs) : nextOr (xs ++ [
x]) x d = d
参数：d : α；h : x ∉ xs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `List.nextOr_cons_of_ne`：nextOr_cons_of_ne (xs : List α) (y x d : α) (h :
 x != y) : nextOr (y :: xs) x d = nextOr xs x d
-/
theorem nextOr_concat {xs : List α} {x : α} (d : α) (h : x ∉ xs) : nextOr (xs ++ [x]) x d = d := by
  induction xs with
  | nil => simp
  | cons z zs IH =>
    obtain ⟨hz, hzs⟩ := not_or.mp (mt mem_cons.2 h)
    rw [cons_append, nextOr_cons_of_ne _ _ _ _ hz, IH hzs]
/-
**List.nextOr_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nextOr_mem {xs : List α} {x d : α} (hd : d in xs) : nextOr xs x d in xs
参数：hd : d in xs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nextOr.eq_3`：∀ {α : Type u_1} [inst : DecidableEq α] (x x_1 y z : α
) (xs : List α),   (y :: z :: xs).nextOr x x_1 = if x = y then z else (z :: xs).
nextOr…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem nextOr_mem {xs : List α} {x d : α} (hd : d ∈ xs) : nextOr xs x d ∈ xs := by
  revert hd
  suffices ∀ xs' : List α, (∀ x ∈ xs, x ∈ xs') → d ∈ xs' → nextOr xs x d ∈ xs' by
    exact this xs fun _ => id
  intro xs' hxs' hd
  induction xs with
  | nil => exact hd
  | cons y ys ih => ?_
  rcases ys with - | ⟨z, zs⟩
  · exact hd
  rw [nextOr]
  split_ifs with h
  · exact hxs' _ (mem_cons_of_mem _ mem_cons_self)
  · exact ih fun _ h => hxs' _ (mem_cons_of_mem _ h)

/-- Given an element `x : α` of `l : List α` such that `x ∈ l`, get the next
element of `l`. This works from head to tail, (including a check for last element)
so it will match on first hit, ignoring later duplicates.

For example:
* `next [1, 2, 3] 2 _ = 3`
* `next [1, 2, 3] 3 _ = 1`
* `next [1, 2, 3, 2, 4] 2 _ = 3`
* `next [1, 2, 3, 2] 2 _ = 3`
* `next [1, 1, 2, 3, 2] 1 _ = 1`
-/
/-
**List.next** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：next (l : List α) (x : α) (h : x in l) : α
参数：l : List α；x : α；h : x in l。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_pos_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → 0
 < l.length

--- 原说明 ---
Given an element `x : α` of `l : List α` such that `x ∈ l`, get the next
element of `l`. This works from head to tail, (including a check for last elemen
t)
so it will match on first hit, ignoring later duplicates.

For example:
* `next [1, 2, 3] 2 _ = 3`
* `next [1, 2, 3] 3 _ = 1`
* `next [1, 2, 3, 2, 4] 2 _ = 3`
* `next [1, 2, 3, 2] 2 _ = 3`
* `next [1, 1, 2, 3, 2] 1 _ = 1`
-/
def next (l : List α) (x : α) (h : x ∈ l) : α :=
  nextOr l x (l.get ⟨0, length_pos_of_mem h⟩)

/-- Given an element `x : α` of `l : List α` such that `x ∈ l`, get the previous
element of `l`. This works from head to tail, (including a check for last element)
so it will match on first hit, ignoring later duplicates.

* `prev [1, 2, 3] 2 _ = 1`
* `prev [1, 2, 3] 1 _ = 3`
* `prev [1, 2, 3, 2, 4] 2 _ = 1`
* `prev [1, 2, 3, 4, 2] 2 _ = 1`
* `prev [1, 1, 2] 1 _ = 2`
-/
/-
**List.prev** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → (l : List α) → (x : α) → x ∈ l → α
参数：l : List α；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element `x : α` of `l : List α` such that `x ∈ l`, get the previous
element of `l`. This works from head to tail, (including a check for last elemen
t)
so it will match on first hit, ignoring later duplicates.

* `prev [1, 2, 3] 2 _ = 1`
* `prev [1, 2, 3] 1 _ = 3`
* `prev [1, 2, 3, 2, 4] 2 _ = 1`
* `prev [1, 2, 3, 4, 2] 2 _ = 1`
* `prev [1, 1, 2] 1 _ = 2`
-/
def prev : ∀ l : List α, ∀ x ∈ l, α
  | [], _, h => by simp at h
  | [y], _, _ => y
  | y :: z :: xs, x, h =>
    if hx : x = y then getLast (z :: xs) (cons_ne_nil _ _)
    else if x = z then y else prev (z :: xs) x (by simpa [hx] using h)

variable (l : List α) (x : α)

@[simp]
/-
**List.next_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_singleton (x y : α) (h : x in [y]) : next [y] x h = y
参数：x y : α；h : x in [y]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem next_singleton (x y : α) (h : x ∈ [y]) : next [y] x h = y :=
  rfl

@[simp]
/-
**List.prev_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_singleton (x y : α) (h : x in [y]) : prev [y] x h = y
参数：x y : α；h : x in [y]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prev_singleton (x y : α) (h : x ∈ [y]) : prev [y] x h = y :=
  rfl
/-
**List.next_cons_cons_eq'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_cons_cons_eq' (y z : α) (h : x in y :: z :: l) (hx : x = y) : next (y
 :: z :: l) x h = z
参数：y z : α；h : x in y :: z :: l；hx : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_pos_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → 0
 < l.length
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.next.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x 
: α) (h : x ∈ l), l.next x h = l.nextOr x (l.get ⟨0, ⋯⟩)
· 使用定理 `List.nextOr.eq_3`：∀ {α : Type u_1} [inst : DecidableEq α] (x x_1 y z : α
) (xs : List α),   (y :: z :: xs).nextOr x x_1 = if x = y then z else (z :: xs).
nextOr…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem next_cons_cons_eq' (y z : α) (h : x ∈ y :: z :: l) (hx : x = y) :
    next (y :: z :: l) x h = z := by rw [next, nextOr, if_pos hx]

@[simp]
/-
**List.next_cons_cons_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_cons_cons_eq (z : α) (h : x in x :: z :: l) : next (x :: z :: l) x h 
= z
参数：z : α；h : x in x :: z :: l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.next_cons_cons_eq'`：next_cons_cons_eq' (y z : α) (h : x in y :: z :
: l) (hx : x = y) : next (y :: z :: l) x h = z
-/
theorem next_cons_cons_eq (z : α) (h : x ∈ x :: z :: l) : next (x :: z :: l) x h = z :=
  next_cons_cons_eq' l x x z h rfl
/-
**List.next_cons_eq_next_of_mem_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_cons_eq_next_of_mem_dropLast (h : x in l.dropLast) (y : α) (hy : x !=
 y) : next (y :: l) x (mem_cons_of_mem _ <| mem_of_mem_dropLast h) = next l x (m
em_of_mem_dropLast h)
参数：h : x in l.dropLast；y : α；hy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.mem_of_mem_dropLast`：mem_of_mem_dropLast (h : a in l.dropLast) : a 
in l
· 使用定理 `List.length_pos_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → 0
 < l.length
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.next.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x 
: α) (h : x ∈ l), l.next x h = l.nextOr x (l.get ⟨0, ⋯⟩)
· 使用定理 `List.nextOr_cons_of_ne`：nextOr_cons_of_ne (xs : List α) (y x d : α) (h :
 x != y) : nextOr (y :: xs) x d = nextOr xs x d
· 使用定理 `List.nextOr_eq_nextOr_of_mem_dropLast`：nextOr_eq_nextOr_of_mem_dropLast 
(xs : List α) (x d d' : α) (x_mem : x in xs.dropLast) : nextOr xs x d = nextOr x
s x d'
-/
theorem next_cons_eq_next_of_mem_dropLast (h : x ∈ l.dropLast) (y : α) (hy : x ≠ y) :
    next (y :: l) x (mem_cons_of_mem _ <| mem_of_mem_dropLast h) =
      next l x (mem_of_mem_dropLast h) := by
  rwa [next, next, nextOr_cons_of_ne _ _ _ _ hy, nextOr_eq_nextOr_of_mem_dropLast]
/-
**List.next_cons_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_cons_concat (y : α) (hy : x != y) (hx : x ∉ l) (h : x in y :: l ++ [x
]
参数：y : α；hy : x != y；hx : x ∉ l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_pos_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → 0
 < l.length
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.next.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x 
: α) (h : x ∈ l), l.next x h = l.nextOr x (l.get ⟨0, ⋯⟩)
· 使用定理 `List.nextOr_concat`：nextOr_concat {xs : List α} {x : α} (d : α) (h : x ∉
 xs) : nextOr (xs ++ [x]) x d = d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem next_cons_concat (y : α) (hy : x ≠ y) (hx : x ∉ l)
    (h : x ∈ y :: l ++ [x] := mem_append_right _ (mem_singleton_self x)) :
    next (y :: l ++ [x]) x h = y := by
  rw [next, nextOr_concat]
  · simp
  · simp [hy, hx]
/-
**List.next_getLast_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_getLast_cons (h : x in l) (y : α) (h : x in y :: l) (hy : x != y) (hx
 : x = getLast (y :: l) (cons_ne_nil _ _)) (hl : Nodup l) : next (y :: l) x h = 
y
参数：h : x in l；y : α；h : x in y :: l；hy : x != y；hx : x = getLast (y :: l) (cons_
ne_nil _ _)；hl : Nodup l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.length_pos_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → 0
 < l.length
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.next.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x 
: α) (h : x ∈ l), l.next x h = l.nextOr x (l.get ⟨0, ⋯⟩)
· 使用定理 `List.get.eq_1`：∀ {α : Type u} (a : α) (tail : List α) (isLt : 0 < (a :: 
tail).length), (a :: tail).get ⟨0, isLt⟩ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.dropLast_append_getLast`：∀ {α : Type u} {l : List α} (h : l ≠ []), 
l.dropLast ++ [l.getLast h] = l
· 使用定理 `List.nextOr_concat`：nextOr_concat {xs : List α} {x : α} (d : α) (h : x ∉
 xs) : nextOr (xs ++ [x]) x d = d
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.dropLast_singleton`：∀ {α : Type u_1} {x : α}, [x].dropLast = []
· 使用定理 `List.length.eq_2`：∀ {α : Type u_1} (head : α) (tail : List α), (head :: 
tail).length = tail.length + 1
· 使用定理 `Nat.succ_inj`：∀ {a b : ℕ}, a.succ = b.succ ↔ a = b
· 使用定理 `Fin.val_eq_of_eq`：∀ {n : ℕ} {i j : Fin n}, i = j → ↑i = ↑j
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m
· 使用定理 `List.dropLast_cons_cons`：∀ {α : Type u_1} {x y : α} {zs : List α}, (x ::
 y :: zs).dropLast = x :: (y :: zs).dropLast
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_dropLast`：∀ {α : Type u_1} {xs : List α}, xs.dropLast.length
 = xs.length - 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.nodup_iff_injective_get`：nodup_iff_injective_get {l : List α} : Nod
up l ↔ Function.Injective l.get
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem next_getLast_cons (h : x ∈ l) (y : α) (h : x ∈ y :: l) (hy : x ≠ y)
    (hx : x = getLast (y :: l) (cons_ne_nil _ _)) (hl : Nodup l) : next (y :: l) x h = y := by
  rw [next, get, ← dropLast_append_getLast (cons_ne_nil y l), hx, nextOr_concat]
  subst hx
  intro H
  obtain ⟨_ | k, hk, hk'⟩ := getElem_of_mem H
  · grind
  suffices k + 1 = l.length by simp [this] at hk
  rcases l with - | ⟨hd, tl⟩
  · simp at hk
  · rw [nodup_iff_injective_get] at hl
    rw [length, Nat.succ_inj]
    exact Fin.val_eq_of_eq <| @hl ⟨k, Nat.lt_of_succ_lt <| by simpa using hk⟩
      ⟨tl.length, by simp⟩ (by grind)
/-
**List.prev_getLast_cons'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_getLast_cons' (y : α) (hxy : x in y :: l) (hx : x = y) : prev (y :: l
) x hxy = getLast (y :: l) (cons_ne_nil _ _)
参数：y : α；hxy : x in y :: l；hx : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
-/
theorem prev_getLast_cons' (y : α) (hxy : x ∈ y :: l) (hx : x = y) :
    prev (y :: l) x hxy = getLast (y :: l) (cons_ne_nil _ _) := by cases l <;> simp [prev, hx]

@[simp]
/-
**List.prev_getLast_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_getLast_cons (h : x in x :: l) : prev (x :: l) x h = getLast (x :: l)
 (cons_ne_nil _ _)
参数：h : x in x :: l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.prev_getLast_cons'`：prev_getLast_cons' (y : α) (hxy : x in y :: l) 
(hx : x = y) : prev (y :: l) x hxy = getLast (y :: l) (cons_ne_nil _ _)
-/
theorem prev_getLast_cons (h : x ∈ x :: l) :
    prev (x :: l) x h = getLast (x :: l) (cons_ne_nil _ _) :=
  prev_getLast_cons' l x x h rfl
/-
**List.prev_head_eq_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_head_eq_getLast (hl : l != []) : l.prev (l.head hl) (head_mem hl) = l
.getLast hl
参数：hl : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.head_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head h ∈ l
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prev_getLast_cons`：prev_getLast_cons (h : x in x :: l) : prev (x ::
 l) x h = getLast (x :: l) (cons_ne_nil _ _)
-/
theorem prev_head_eq_getLast (hl : l ≠ []) : l.prev (l.head hl) (head_mem hl) = l.getLast hl := by
  cases l with
  | nil => contradiction
  | cons head tail => apply prev_getLast_cons
/-
**List.prev_cons_cons_eq'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_cons_cons_eq' (y z : α) (h : x in y :: z :: l) (hx : x = y) : prev (y
 :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _)
参数：y z : α；h : x in y :: z :: l；hx : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prev.eq_3`：∀ {α : Type u_1} [inst : DecidableEq α] (x y z : α) (xs 
: List α) (x_1 : x ∈ y :: z :: xs),   (y :: z :: xs).prev x x_1 = if hx : x = y 
then…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem prev_cons_cons_eq' (y z : α) (h : x ∈ y :: z :: l) (hx : x = y) :
    prev (y :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _) := by rw [prev, dif_pos hx]
/-
**List.prev_cons_cons_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_cons_cons_eq (z : α) (h : x in x :: z :: l) : prev (x :: z :: l) x h 
= getLast (z :: l) (cons_ne_nil _ _)
参数：z : α；h : x in x :: z :: l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.prev_cons_cons_eq'`：prev_cons_cons_eq' (y z : α) (h : x in y :: z :
: l) (hx : x = y) : prev (y :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _)
-/
theorem prev_cons_cons_eq (z : α) (h : x ∈ x :: z :: l) :
    prev (x :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _) :=
  prev_cons_cons_eq' l x x z h rfl
/-
**List.prev_cons_cons_of_ne'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_cons_cons_of_ne' (y z : α) (h : x in y :: z :: l) (hy : x != y) (hz :
 x = z) : prev (y :: z :: l) x h = y
参数：y z : α；h : x in y :: z :: l；hy : x != y；hz : x = z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prev.eq_3`：∀ {α : Type u_1} [inst : DecidableEq α] (x y z : α) (xs 
: List α) (x_1 : x ∈ y :: z :: xs),   (y :: z :: xs).prev x x_1 = if hx : x = y 
then…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem prev_cons_cons_of_ne' (y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) (hz : x = z) :
    prev (y :: z :: l) x h = y := by
  cases l
  · simp [prev, hz]
  · rw [prev, dif_neg hy, if_pos hz]
/-
**List.prev_cons_cons_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_cons_cons_of_ne (y : α) (h : x in y :: x :: l) (hy : x != y) : prev (
y :: x :: l) x h = y
参数：y : α；h : x in y :: x :: l；hy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.prev_cons_cons_of_ne'`：prev_cons_cons_of_ne' (y z : α) (h : x in y 
:: z :: l) (hy : x != y) (hz : x = z) : prev (y :: z :: l) x h = y
-/
theorem prev_cons_cons_of_ne (y : α) (h : x ∈ y :: x :: l) (hy : x ≠ y) :
    prev (y :: x :: l) x h = y :=
  prev_cons_cons_of_ne' _ _ _ _ _ hy rfl
/-
**List.prev_ne_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_ne_cons_cons (y z : α) (h : x in y :: z :: l) (hy : x != y) (hz : x !
= z) : prev (y :: z :: l) x h = prev (z :: l) x (by simpa [hy] using h)
参数：y z : α；h : x in y :: z :: l；hy : x != y；hz : x != z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.prev.eq_3`：∀ {α : Type u_1} [inst : DecidableEq α] (x y z : α) (xs 
: List α) (x_1 : x ∈ y :: z :: xs),   (y :: z :: xs).prev x x_1 = if hx : x = y 
then…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem prev_ne_cons_cons (y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) (hz : x ≠ z) :
    prev (y :: z :: l) x h = prev (z :: l) x (by simpa [hy] using h) := by
  cases l
  · simp [hy, hz] at h
  · rw [prev, dif_neg hy, if_neg hz]
/-
**List.next_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_mem (h : x in l) : l.next x h in l
参数：h : x in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nextOr_mem`：nextOr_mem {xs : List α} {x d : α} (hd : d in xs) : nex
tOr xs x d in xs
· 使用定理 `List.length_pos_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → 0
 < l.length
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
-/
theorem next_mem (h : x ∈ l) : l.next x h ∈ l :=
  nextOr_mem (get_mem _ _)
/-
**List.prev_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_mem (h : x in l) : l.prev x h in l
参数：h : x in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.prev.congr_simp`：∀ {α : Type u_1} [inst : DecidableEq α] (l l_1 : L
ist α) (e_l : l = l_1) (x x_1 : α) (e_x : x = x_1) (a : x ∈ l),   l.prev x a = l
_1.prev x_…
· 使用定理 `List.prev_cons_cons_eq`：prev_cons_cons_eq (z : α) (h : x in x :: z :: l)
 : prev (x :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _)
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用定理 `List.prev.eq_3`：∀ {α : Type u_1} [inst : DecidableEq α] (x y z : α) (xs 
: List α) (x_1 : x ∈ y :: z :: xs),   (y :: z :: xs).prev x x_1 = if hx : x = y 
then…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem prev_mem (h : x ∈ l) : l.prev x h ∈ l := by
  rcases l with - | ⟨hd, tl⟩
  · simp at h
  induction tl generalizing hd with
  | nil => simp
  | cons hd' tl hl =>
    by_cases hx : x = hd
    · simp only [hx, prev_cons_cons_eq]
      exact mem_cons_of_mem _ (getLast_mem _)
    · rw [prev, dif_neg hx]
      split_ifs with hm
      · exact mem_cons_self
      · exact mem_cons_of_mem _ (hl _ _)
/-
**List.nextOr_eq_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast {l : List α} {a : α} (ha : a
 in l.dropLast) (d : α) : l.nextOr a d = l[l.idxOf a + 1]?
参数：ha : a in l.dropLast；d : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast {l : List α} {a : α} (ha : a ∈ l.dropLast)
    (d : α) : l.nextOr a d = l[l.idxOf a + 1]? := by
  match l with
  | nil => simp at ha
  | [head] => simp at ha
  | x :: y :: tail =>
    rw [getElem?_cons_succ, nextOr]
    split_ifs with hx
    · grind
    rw [idxOf_cons_ne _ <| Ne.symm hx, nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast]
    grind
/-
**List.nextOr_eq_getElem_idxOf_succ_of_mem_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `L
ist`。
形式化陈述：nextOr_eq_getElem_idxOf_succ_of_mem_dropLast {l : List α} {a : α} (ha : a 
in l.dropLast) (d : α) : l.nextOr a d = l[l.idxOf a + 1]'(succ_idxOf_lt_length_o
f_mem_dropLast ha)
参数：ha : a in l.dropLast；d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `List.succ_idxOf_lt_length_of_mem_dropLast`：succ_idxOf_lt_length_of_mem_d
ropLast {l : List α} {a : α} (ha : a in l.dropLast) : l.idxOf a + 1 < l.length
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast`：∀ {α : Type u_1} [in
st : DecidableEq α] {l : List α} {a : α},   a ∈ l.dropLast → ∀ (d : α), some (l.
nextOr a d) = l[List.idxOf a l + 1]?
-/
theorem nextOr_eq_getElem_idxOf_succ_of_mem_dropLast {l : List α} {a : α} (ha : a ∈ l.dropLast)
    (d : α) : l.nextOr a d = l[l.idxOf a + 1]'(succ_idxOf_lt_length_of_mem_dropLast ha) :=
  Option.some_injective _ <| nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast ha d ▸ getElem?_pos ..
/-
**List.nextOr_infix_of_mem_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nextOr_infix_of_mem_dropLast {l : List α} {a : α} (ha : a in l.dropLast) (
d : α) : [a, l.nextOr a d] <:+: l
参数：ha : a in l.dropLast；d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.infix_iff_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁ <:+: l₂
 ↔ ∃ k, l₁.length + k ≤ l₂.length ∧ ∀ (i : ℕ) (h : i < l₁.length), l₂[i + k]? = 
some l₁[i]
· 使用定理 `List.dropLast_prefix`：∀ {α : Type u_1} (l : List α), l.dropLast <+: l
-/
theorem nextOr_infix_of_mem_dropLast {l : List α} {a : α} (ha : a ∈ l.dropLast) (d : α) :
    [a, l.nextOr a d] <:+: l := by
  refine infix_iff_getElem?.mpr ⟨l.idxOf a, ?_, fun i hi ↦ ?_⟩
  · have ⟨_, _⟩ := l.dropLast_prefix
    grind
  by_cases hi₁ : i = 1
  · grind [next, nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast]
  · grind [getElem?_idxOf, mem_of_mem_dropLast]
/-
**List.nextOr_getLast_of_notMem_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nextOr_getLast_of_notMem_dropLast {l : List α} (hl : l != []) (h : l.getLa
st hl ∉ l.dropLast) (d : α) : l.nextOr (l.getLast hl) d = d
参数：hl : l != []；h : l.getLast hl ∉ l.dropLast；d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem nextOr_getLast_of_notMem_dropLast {l : List α} (hl : l ≠ []) (h : l.getLast hl ∉ l.dropLast)
    (d : α) : l.nextOr (l.getLast hl) d = d := by
  match l with
  | nil | [_] => simp
  | x :: y :: tail =>
    unfold nextOr
    split_ifs with h'
    · grind
    apply nextOr_getLast_of_notMem_dropLast
    grind
/-
**List.next_getLast_eq_head_of_notMem_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_getLast_eq_head_of_notMem_dropLast {l : List α} (hl : l != []) (h : l
.getLast hl ∉ l.dropLast) : l.next (l.getLast hl) (getLast_mem hl) = l.head hl
参数：hl : l != []；h : l.getLast hl ∉ l.dropLast。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_pos_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → 0
 < l.length
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.nextOr_getLast_of_notMem_dropLast`：nextOr_getLast_of_notMem_dropLas
t {l : List α} (hl : l != []) (h : l.getLast hl ∉ l.dropLast) (d : α) : l.nextOr
 (l.getLast hl) d = d
-/
theorem next_getLast_eq_head_of_notMem_dropLast {l : List α} (hl : l ≠ [])
    (h : l.getLast hl ∉ l.dropLast) : l.next (l.getLast hl) (getLast_mem hl) = l.head hl :=
  nextOr_getLast_of_notMem_dropLast hl h _ |>.trans <| by grind
/-
**List.next_eq_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_eq_getElem {l : List α} {a : α} (ha : a in l) : l.next a ha = l[(l.id
xOf a + 1) % l.length]'(Nat.mod_lt _ <| by grind)
参数：ha : a in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.succ_idxOf_lt_length_of_mem_dropLast`：succ_idxOf_lt_length_of_mem_d
ropLast {l : List α} {a : α} (ha : a in l.dropLast) : l.idxOf a + 1 < l.length
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nextOr_eq_getElem_idxOf_succ_of_mem_dropLast`：nextOr_eq_getElem_idx
Of_succ_of_mem_dropLast {l : List α} {a : α} (ha : a in l.dropLast) (d : α) : l.
nextOr a d = l[l.idxOf a + 1]'(succ_idx…
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.length_pos_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → 0
 < l.length
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem next_eq_getElem {l : List α} {a : α} (ha : a ∈ l) :
    l.next a ha = l[(l.idxOf a + 1) % l.length]'(Nat.mod_lt _ <| by grind) := by
  have hl := ne_nil_of_mem ha
  by_cases ha' : a ∈ l.dropLast
  · simp [next, nextOr_eq_getElem_idxOf_succ_of_mem_dropLast ha',
      Nat.mod_eq_of_lt <| succ_idxOf_lt_length_of_mem_dropLast ha']
  grind [dropLast_append_getLast, next_getLast_eq_head_of_notMem_dropLast, Nat.mod_self]
/-
**List.next_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi : i < l.length) : l.
next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt _ (i.zero_le.trans_lt
 hi))
参数：l : List α；h : Nodup l；i : Nat；hi : i < l.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi : i < l.length) :
    l.next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt _ (i.zero_le.trans_lt hi)) := by
  grind [next_eq_getElem]
/-
**List.prev_eq_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_eq_getElem?_idxOf_pred_of_ne_head {l : List α} {a : α} (ha : a in l) 
(ha₀ : a != l.head (ne_nil_of_mem ha)) : l.prev a ha = l[l.idxOf a - 1]?
参数：ha : a in l；ha₀ : a != l.head (ne_nil_of_mem ha)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.idxOf_cons_self`：∀ {α : Type u_1} {a : α} [inst : BEq α] [ReflBEq α
] {l : List α}, List.idxOf a (a :: l) = 0
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.prev_getLast_cons`：prev_getLast_cons (h : x in x :: l) : prev (x ::
 l) x h = getLast (x :: l) (cons_ne_nil _ _)
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.prev_eq_getElem_idxOf_pred_of_ne_head`：prev_eq_getElem_idxOf_pred_o
f_ne_head {l : List α} {a : α} (ha : a in l) (ha₀ : a != l.head (ne_nil_of_mem h
a)) : l.prev a ha = l[l.idxOf a …
· 使用定理 `Nat.add_sub_assoc`：∀ {m k : ℕ}, k ≤ m → ∀ (n : ℕ), n + m - k = n + (m - 
k)
· 使用定理 `Nat.sub_add_comm`：∀ {n m k : ℕ}, k ≤ n → n + m - k = n - k + m
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem prev_eq_getElem?_idxOf_pred_of_ne_head {l : List α} {a : α} (ha : a ∈ l)
    (ha₀ : a ≠ l.head (ne_nil_of_mem ha)) : l.prev a ha = l[l.idxOf a - 1]? := by
  match l with
  | nil | [_] => grind
  | x :: y :: tail =>
    have ih := (y :: tail).prev_eq_getElem?_idxOf_pred_of_ne_head (a := a)
    grind [prev]
/-
**List.prev_eq_getElem_idxOf_pred_of_ne_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_eq_getElem_idxOf_pred_of_ne_head {l : List α} {a : α} (ha : a in l) (
ha₀ : a != l.head (ne_nil_of_mem ha)) : l.prev a ha = l[l.idxOf a - 1]'(by grind
 [idxOf_lt_length_of_mem])
参数：ha : a in l；ha₀ : a != l.head (ne_nil_of_mem ha)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prev_eq_getElem?_idxOf_pred_of_ne_head`：∀ {α : Type u_1} [inst : De
cidableEq α] {l : List α} {a : α} (ha : a ∈ l),   a ≠ l.head ⋯ → some (l.prev a 
ha) = l[List.idxOf a l - 1]?
-/
theorem prev_eq_getElem_idxOf_pred_of_ne_head {l : List α} {a : α} (ha : a ∈ l)
    (ha₀ : a ≠ l.head (ne_nil_of_mem ha)) :
    l.prev a ha = l[l.idxOf a - 1]'(by grind [idxOf_lt_length_of_mem]) :=
  Option.some_injective _ <| prev_eq_getElem?_idxOf_pred_of_ne_head ha ha₀ ▸ getElem?_pos ..
/-
**List.prev_infix_of_mem_tail** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_infix_of_mem_tail {l : List α} {a : α} (ha : a in l) (ha₀ : a != l.he
ad (ne_nil_of_mem ha)) : [l.prev a ha, a] <:+: l
参数：ha : a in l；ha₀ : a != l.head (ne_nil_of_mem ha)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `List.idxOf_cons_ne`：idxOf_cons_ne {a b : α} (l : List α) (h : b != a) : 
idxOf a (b :: l) = succ (idxOf a l)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.cons_head_tail`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head 
h :: l.tail = l
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.infix_iff_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁ <:+: l₂
 ↔ ∃ k, l₁.length + k ≤ l₂.length ∧ ∀ (i : ℕ) (h : i < l₁.length), l₂[i + k]? = 
some l₁[i]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prev_infix_of_mem_tail {l : List α} {a : α} (ha : a ∈ l)
    (ha₀ : a ≠ l.head (ne_nil_of_mem ha)) : [l.prev a ha, a] <:+: l := by
  have := cons_head_tail (ne_nil_of_mem ha) ▸ idxOf_cons_ne _ <| Ne.symm ha₀
  refine infix_iff_getElem?.mpr ⟨l.idxOf a - 1, by grind, fun i hi ↦ ?_⟩
  by_cases hi₁ : i = 1
  · subst hi₁
    grind
  grind [prev_eq_getElem?_idxOf_pred_of_ne_head]
/-
**List.prev_eq_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_eq_getElem?_idxOf_pred_of_ne_head {l : List α} {a : α} (ha : a in l) 
(ha₀ : a != l.head (ne_nil_of_mem ha)) : l.prev a ha = l[l.idxOf a - 1]?
参数：ha : a in l；ha₀ : a != l.head (ne_nil_of_mem ha)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.idxOf_cons_self`：∀ {α : Type u_1} {a : α} [inst : BEq α] [ReflBEq α
] {l : List α}, List.idxOf a (a :: l) = 0
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.prev_getLast_cons`：prev_getLast_cons (h : x in x :: l) : prev (x ::
 l) x h = getLast (x :: l) (cons_ne_nil _ _)
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.prev_eq_getElem_idxOf_pred_of_ne_head`：prev_eq_getElem_idxOf_pred_o
f_ne_head {l : List α} {a : α} (ha : a in l) (ha₀ : a != l.head (ne_nil_of_mem h
a)) : l.prev a ha = l[l.idxOf a …
· 使用定理 `Nat.add_sub_assoc`：∀ {m k : ℕ}, k ≤ m → ∀ (n : ℕ), n + m - k = n + (m - 
k)
· 使用定理 `Nat.sub_add_comm`：∀ {n m k : ℕ}, k ≤ n → n + m - k = n - k + m
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem prev_eq_getElem {l : List α} {a : α} (ha : a ∈ l) :
    l.prev a ha = l[(l.idxOf a + (l.length - 1)) % l.length]'(Nat.mod_lt _ <| by grind) := by
  cases l with | nil => grind | cons head tail =>
  by_cases ha₀ : a = head
  · subst ha₀
    simp
    grind
  rw [prev_eq_getElem_idxOf_pred_of_ne_head ha ha₀]
  congr
  rw [← Nat.add_sub_assoc, Nat.sub_add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt]
  all_goals grind
/-
**List.prev_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_getElem (l : List α) (h : Nodup l) (i : Nat) (hi : i < l.length) : l.
prev l[i] (get_mem ..) = l[(i + (l.length - 1)) % l.length]'(Nat.mod_lt _ (by li
a))
参数：l : List α；h : Nodup l；i : Nat；hi : i < l.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prev_getElem (l : List α) (h : Nodup l) (i : Nat) (hi : i < l.length) :
    l.prev l[i] (get_mem ..) = l[(i + (l.length - 1)) % l.length]'(Nat.mod_lt _ (by lia)) := by
  grind [prev_eq_getElem]

@[simp]
/-
**List.next_getLast_eq_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_getLast_eq_head (l : List α) (h : l != []) (hn : l.Nodup) : l.next (l
.getLast h) (getLast_mem h) = l.head h
参数：l : List α；h : l != []；hn : l.Nodup。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.length_pos_iff`：∀ {α : Type u_1} {l : List α}, 0 < l.length ↔ l ≠ [
]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.getLast_eq_getElem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.g
etLast h = l[l.length - 1]
· 使用定理 `List.next.congr_simp`：∀ {α : Type u_1} [inst : DecidableEq α] (l l_1 : L
ist α) (e_l : l = l_1) (x x_1 : α) (e_x : x = x_1) (h : x ∈ l),   l.next x h = l
_1.next x_…
· 使用定理 `List.next_getElem`：next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi
 : i < l.length) : l.next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt 
_ (i.ze…
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.head_eq_getElem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head
 h = l[0]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem next_getLast_eq_head (l : List α) (h : l ≠ []) (hn : l.Nodup) :
    l.next (l.getLast h) (getLast_mem h) = l.head h := by
  have h1 : l.length - 1 + 1 = l.length := by grind [length_pos_iff]
  simp [getLast_eq_getElem h, head_eq_getElem h, next_getElem l hn (l.length - 1) (by grind), h1]
/-
**List.pmap_next_eq_rotate_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pmap_next_eq_rotate_one (h : Nodup l) : (l.pmap l.next fun _ h => h) = l.r
otate 1
参数：h : Nodup l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a
 : α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a},   (List.pmap f l H).length = l
.lengt…
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `List.getElem_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (
a : α) → p a → β) {l : List α} (h : ∀ a ∈ l, p a) {i : ℕ}   (hn : i < (List.pmap
 f l h)…
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `List.getElem_rotate`：getElem_rotate (l : List α) (n : Nat) (k : Nat) (h 
: k < (l.rotate n).length) : (l.rotate n)[k] = l[(k + n) % l.length]'(mod_lt _ (
length_ro…
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
· 使用定理 `List.next_getElem`：next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi
 : i < l.length) : l.next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt 
_ (i.ze…
-/
theorem pmap_next_eq_rotate_one (h : Nodup l) : (l.pmap l.next fun _ h => h) = l.rotate 1 := by
  apply List.ext_getElem
  · simp
  · intros
    rw [getElem_pmap, getElem_rotate, next_getElem _ h]
/-
**List.pmap_prev_eq_rotate_length_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pmap_prev_eq_rotate_length_sub_one (h : Nodup l) : (l.pmap l.prev fun _ h 
=> h) = l.rotate (l.length - 1)
参数：h : Nodup l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a
 : α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a},   (List.pmap f l H).length = l
.lengt…
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `List.getElem_rotate`：getElem_rotate (l : List α) (n : Nat) (k : Nat) (h 
: k < (l.rotate n).length) : (l.rotate n)[k] = l[(k + n) % l.length]'(mod_lt _ (
length_ro…
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `List.getElem_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (
a : α) → p a → β) {l : List α} (h : ∀ a ∈ l, p a) {i : ℕ}   (hn : i < (List.pmap
 f l h)…
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
· 使用定理 `List.prev_getElem`：prev_getElem (l : List α) (h : Nodup l) (i : Nat) (hi
 : i < l.length) : l.prev l[i] (get_mem ..) = l[(i + (l.length - 1)) % l.length]
'(Nat.m…
-/
theorem pmap_prev_eq_rotate_length_sub_one (h : Nodup l) :
    (l.pmap l.prev fun _ h => h) = l.rotate (l.length - 1) := by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    rw [getElem_rotate, getElem_pmap, prev_getElem _ h]
/-
**List.prev_next** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_next (l : List α) (h : Nodup l) (x : α) (hx : x in l) : prev l (next 
l x hx) (next_mem _ _ _) = x
参数：l : List α；h : Nodup l；x : α；hx : x in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.next_mem`：next_mem (h : x in l) : l.next x h in l
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.next_getElem`：next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi
 : i < l.length) : l.next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt 
_ (i.ze…
· 使用定理 `List.prev.congr_simp`：∀ {α : Type u_1} [inst : DecidableEq α] (l l_1 : L
ist α) (e_l : l = l_1) (x x_1 : α) (e_x : x = x_1) (a : x ∈ l),   l.prev x a = l
_1.prev x_…
· 使用定理 `List.prev_getElem`：prev_getElem (l : List α) (h : Nodup l) (i : Nat) (hi
 : i < l.length) : l.prev l[i] (get_mem ..) = l[(i + (l.length - 1)) % l.length]
'(Nat.m…
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prev_next (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    prev l (next l x hx) (next_mem _ _ _) = x := by
  obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
  simp only [next_getElem, prev_getElem, h, Nat.mod_add_mod]
  rcases l with - | ⟨hd, tl⟩
  · simp at hn
  · have : (n + 1 + length tl) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc, add_comm 1, Nat.add_mod_right, Nat.mod_eq_of_lt hn]
    simp only [length_cons, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, this]
/-
**List.next_prev** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_prev (l : List α) (h : Nodup l) (x : α) (hx : x in l) : next l (prev 
l x hx) (prev_mem _ _ _) = x
参数：l : List α；h : Nodup l；x : α；hx : x in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.prev_mem`：prev_mem (h : x in l) : l.prev x h in l
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.prev_getElem`：prev_getElem (l : List α) (h : Nodup l) (i : Nat) (hi
 : i < l.length) : l.prev l[i] (get_mem ..) = l[(i + (l.length - 1)) % l.length]
'(Nat.m…
· 使用定理 `List.next.congr_simp`：∀ {α : Type u_1} [inst : DecidableEq α] (l l_1 : L
ist α) (e_l : l = l_1) (x x_1 : α) (e_x : x = x_1) (h : x ∈ l),   l.next x h = l
_1.next x_…
· 使用定理 `List.next_getElem`：next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi
 : i < l.length) : l.next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt 
_ (i.ze…
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem next_prev (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    next l (prev l x hx) (prev_mem _ _ _) = x := by
  obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
  simp only [next_getElem, prev_getElem, h, Nat.mod_add_mod]
  rcases l with - | ⟨hd, tl⟩
  · simp at hn
  · have : (n + length tl + 1) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc, Nat.add_mod_right, Nat.mod_eq_of_lt hn]
    simp [this]
/-
**List.prev_reverse_eq_next** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prev_reverse_eq_next (l : List α) (h : Nodup l) (x : α) (hx : x in l) : pr
ev l.reverse x (mem_reverse.mpr hx) = next l x hx
参数：l : List α；h : Nodup l；x : α；hx : x in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_reverse`：∀ {α : Type u_1} {x : α} {as : List α}, x ∈ as.reverse
 ↔ x ∈ as
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a
 : α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a},   (List.pmap f l H).length = l
.lengt…
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getElem_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (
a : α) → p a → β) {l : List α} (h : ∀ a ∈ l, p a) {i : ℕ}   (hn : i < (List.pmap
 f l h)…
· 使用定理 `List.getElem_eq_getElem_reverse`：∀ {α : Type u_1} {l : List α} {i : ℕ} (
h : i < l.length), l[i] = l.reverse[l.length - 1 - i]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.prev.congr_simp`：∀ {α : Type u_1} [inst : DecidableEq α] (l l_1 : L
ist α) (e_l : l = l_1) (x x_1 : α) (e_x : x = x_1) (a : x ∈ l),   l.prev x a = l
_1.prev x_…
· 使用定理 `List.pmap_next_eq_rotate_one`：pmap_next_eq_rotate_one (h : Nodup l) : (l
.pmap l.next fun _ h => h) = l.rotate 1
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.pmap_reverse`：∀ {α : Type u_1} {β : Type u_2} {P : α → Prop} {f : (
a : α) → P a → β} {xs : List α} (H : ∀ a ∈ xs.reverse, P a),   List.pmap f xs.re
verse H…
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `List.pmap_prev_eq_rotate_length_sub_one`：pmap_prev_eq_rotate_length_sub_
one (h : Nodup l) : (l.pmap l.prev fun _ h => h) = l.rotate (l.length - 1)
· 使用定理 `List.nodup_reverse`：nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nod
up l
· 使用定理 `List.rotate_reverse`：rotate_reverse (l : List α) (n : Nat) : l.reverse.r
otate n = (l.rotate (l.length - n % l.length)).reverse
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用引理 `Nat.succ_pos'`：succ_pos' : 0 < succ n
· 使用定理 `Nat.sub_sub_self`：∀ {n m : ℕ}, m ≤ n → n - (n - m) = m
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
（共 35 条，此处仅展示前 30 条）
-/
theorem prev_reverse_eq_next (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    prev l.reverse x (mem_reverse.mpr hx) = next l x hx := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  have lpos : 0 < l.length := k.zero_le.trans_lt hk
  have key : l.length - 1 - k < l.length := by lia
  rw [← getElem_pmap l.next (fun _ h => h) (by simpa using hk)]
  simp_rw [getElem_eq_getElem_reverse (l := l), pmap_next_eq_rotate_one _ h]
  rw [← getElem_pmap l.reverse.prev fun _ h => h]
  · simp_rw [pmap_prev_eq_rotate_length_sub_one _ (nodup_reverse.mpr h), rotate_reverse,
      length_reverse, Nat.mod_eq_of_lt (Nat.sub_lt lpos Nat.succ_pos'),
      Nat.sub_sub_self (Nat.succ_le_of_lt lpos)]
    rw [getElem_eq_getElem_reverse]
    · simp [Nat.sub_sub_self (Nat.le_sub_one_of_lt hk)]
  · simpa
/-
**List.next_reverse_eq_prev** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：next_reverse_eq_prev (l : List α) (h : Nodup l) (x : α) (hx : x in l) : ne
xt l.reverse x (mem_reverse.mpr hx) = prev l x hx
参数：l : List α；h : Nodup l；x : α；hx : x in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_reverse`：∀ {α : Type u_1} {x : α} {as : List α}, x ∈ as.reverse
 ↔ x ∈ as
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `List.prev_reverse_eq_next`：prev_reverse_eq_next (l : List α) (h : Nodup 
l) (x : α) (hx : x in l) : prev l.reverse x (mem_reverse.mpr hx) = next l x hx
· 使用定理 `List.nodup_reverse`：nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nod
up l
-/
theorem next_reverse_eq_prev (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    next l.reverse x (mem_reverse.mpr hx) = prev l x hx := by
  convert! (prev_reverse_eq_next l.reverse (nodup_reverse.mpr h) x (mem_reverse.mpr hx)).symm
  exact (reverse_reverse l).symm
/-
**List.isRotated_next_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_next_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx
 : x in l) : l.next x hx = l'.next x (h.mem_iff.mp hx)
参数：h : l ~r l'；hn : Nodup l；hx : x in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.IsRotated.mem_iff`：∀ {α : Type u} {l l' : List α}, l ~r l' → ∀ {a :
 α}, a ∈ l ↔ a ∈ l'
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
· 使用定理 `List.next_getElem`：next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi
 : i < l.length) : l.next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt 
_ (i.ze…
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `List.getElem_eq_getElem_rotate`：getElem_eq_getElem_rotate (l : List α) (
n : Nat) (k : Nat) (hk : k < l.length) : l[k] = ((l.rotate n)[(l.length - n % l.
length + k) % l.leng…
· 使用定理 `List.next.congr_simp`：∀ {α : Type u_1} [inst : DecidableEq α] (l l_1 : L
ist α) (e_l : l = l_1) (x x_1 : α) (e_x : x = x_1) (h : x ∈ l),   l.next x h = l
_1.next x_…
· 使用定理 `List.IsRotated.nodup_iff`：∀ {α : Type u} {l l' : List α}, l ~r l' → (l.N
odup ↔ l'.Nodup)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.add_mod_mod`：∀ (m n k : ℕ), (m + n % k) % k = (m + n) % k
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_rotate`：getElem_rotate (l : List α) (n : Nat) (k : Nat) (h 
: k < (l.rotate n).length) : (l.rotate n)[k] = l[(k + n) % l.length]'(mod_lt _ (
length_ro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isRotated_next_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x ∈ l) :
    l.next x hx = l'.next x (h.mem_iff.mp hx) := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  obtain ⟨n, rfl⟩ := id h
  rw [next_getElem _ hn]
  simp_rw [getElem_eq_getElem_rotate _ n k]
  rw [next_getElem _ (h.nodup_iff.mp hn), getElem_eq_getElem_rotate _ n]
  simp [add_assoc]
/-
**List.isRotated_prev_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_prev_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx
 : x in l) : l.prev x hx = l'.prev x (h.mem_iff.mp hx)
参数：h : l ~r l'；hn : Nodup l；hx : x in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.IsRotated.mem_iff`：∀ {α : Type u} {l l' : List α}, l ~r l' → ∀ {a :
 α}, a ∈ l ↔ a ∈ l'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_reverse`：∀ {α : Type u_1} {x : α} {as : List α}, x ∈ as.reverse
 ↔ x ∈ as
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.next_reverse_eq_prev`：next_reverse_eq_prev (l : List α) (h : Nodup 
l) (x : α) (hx : x in l) : next l.reverse x (mem_reverse.mpr hx) = prev l x hx
· 使用定理 `List.IsRotated.nodup_iff`：∀ {α : Type u} {l l' : List α}, l ~r l' → (l.N
odup ↔ l'.Nodup)
· 使用定理 `List.isRotated_next_eq`：isRotated_next_eq {l l' : List α} (h : l ~r l') 
(hn : Nodup l) {x : α} (hx : x in l) : l.next x hx = l'.next x (h.mem_iff.mp hx)
· 使用定理 `List.IsRotated.reverse`：∀ {α : Type u} {l l' : List α}, l ~r l' → l.reve
rse ~r l'.reverse
· 使用定理 `List.nodup_reverse`：nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nod
up l
-/
theorem isRotated_prev_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x ∈ l) :
    l.prev x hx = l'.prev x (h.mem_iff.mp hx) := by
  rw [← next_reverse_eq_prev _ hn, ← next_reverse_eq_prev _ (h.nodup_iff.mp hn)]
  exact isRotated_next_eq h.reverse (nodup_reverse.mpr hn) _

end List

open List

/-- `Cycle α` is the quotient of `List α` by cyclic permutation.
Duplicates are allowed.
-/
/-
**Cycle** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Cycle (α : Type*) : Type _
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Cycle α` is the quotient of `List α` by cyclic permutation.
Duplicates are allowed.
-/
def Cycle (α : Type*) : Type _ :=
  Quotient (IsRotated.setoid α)

namespace Cycle

variable {α : Type*}

/-- The coercion from `List α` to `Cycle α` -/
/-
**Cycle.ofList** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：{α : Type u_1} → List α → Cycle α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from `List α` to `Cycle α`
-/
@[coe] def ofList : List α → Cycle α :=
  Quot.mk _
/-
**Cycle.** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (List α) (Cycle α) :=
  ⟨ofList⟩

@[simp]
/-
**Cycle.coe_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Cycle α) = (l₂ : Cycle α) ↔ l₁ ~r l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Cycle α) = (l₂ : Cycle α) ↔ l₁ ~r l₂ :=
  @Quotient.eq _ (IsRotated.setoid _) _ _

@[simp]
/-
**Cycle.mk_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：mk_eq_coe (l : List α) : Quot.mk _ l = (l : Cycle α)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_eq_coe (l : List α) : Quot.mk _ l = (l : Cycle α) :=
  rfl

@[simp]
/-
**Cycle.mk''_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：∀ {α : Type u_1} (l : List α), Quotient.mk'' l = ↑l
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem mk''_eq_coe (l : List α) : Quotient.mk'' l = (l : Cycle α) :=
  rfl
/-
**Cycle.coe_cons_eq_coe_append** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：coe_cons_eq_coe_append (l : List α) (a : α) : (↑(a :: l) : Cycle α) = (↑(l
 ++ [a]) : Cycle α)
参数：l : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_cons_succ`：∀ {α : Type u} (l : List α) (a : α) (n : ℕ), (a :
: l).rotate (n + 1) = (l ++ [a]).rotate n
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
-/
theorem coe_cons_eq_coe_append (l : List α) (a : α) :
    (↑(a :: l) : Cycle α) = (↑(l ++ [a]) : Cycle α) :=
  Quot.sound ⟨1, by rw [rotate_cons_succ, rotate_zero]⟩

/-- The unique empty cycle. -/
/-
**Cycle.nil** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：nil : Cycle α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique empty cycle.
-/
def nil : Cycle α :=
  ([] : List α)

@[simp]
/-
**Cycle.coe_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：coe_nil : ↑([] : List α) = @nil α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nil : ↑([] : List α) = @nil α :=
  rfl

@[simp]
/-
**Cycle.coe_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：coe_eq_nil (l : List α) : (l : Cycle α) = nil ↔ l = []
参数：l : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Cycle.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Cycle α) = (l₂ : C
ycle α) ↔ l₁ ~r l₂
· 使用定理 `List.isRotated_nil_iff`：isRotated_nil_iff : l ~r [] ↔ l = []
-/
theorem coe_eq_nil (l : List α) : (l : Cycle α) = nil ↔ l = [] :=
  coe_eq_coe.trans isRotated_nil_iff

/-- For consistency with `EmptyCollection (List α)`. -/
/-
**Cycle.** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For consistency with `EmptyCollection (List α)`.
-/
instance : EmptyCollection (Cycle α) :=
  ⟨nil⟩

@[simp]
/-
**Cycle.empty_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：empty_eq : ∅ = @nil α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_eq : ∅ = @nil α :=
  rfl
/-
**Cycle.** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Cycle α) :=
  ⟨nil⟩

/-- An induction principle for `Cycle`. Use as `induction s`. -/
@[elab_as_elim, induction_eliminator]
/-
**Cycle.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：induction_on {motive : Cycle α -> Prop} (s : Cycle α) (nil : motive nil) (
cons : forall (a) (l : List α), motive ↑l -> motive ↑(a :: l)) : motive s
参数：s : Cycle α；nil : motive nil；cons : forall (a) (l : List α), motive ↑l -> mot
ive ↑(a :: l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
An induction principle for `Cycle`. Use as `induction s`.
-/
theorem induction_on {motive : Cycle α → Prop} (s : Cycle α) (nil : motive nil)
    (cons : ∀ (a) (l : List α), motive ↑l → motive ↑(a :: l)) : motive s :=
  Quotient.inductionOn' s fun l => by
    refine List.recOn l ?_ ?_ <;> simp only [mk''_eq_coe, coe_nil]
    assumption'

/-- For `x : α`, `s : Cycle α`, `x ∈ s` indicates that `x` occurs at least once in `s`. -/
/-
**Cycle.Mem** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：Mem (s : Cycle α) (a : α) : Prop
参数：s : Cycle α；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `x : α`, `s : Cycle α`, `x ∈ s` indicates that `x` occurs at least once in `
s`.
-/
def Mem (s : Cycle α) (a : α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun _ _ e => propext <| e.mem_iff
/-
**Cycle.** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership α (Cycle α) :=
  ⟨Mem⟩

@[simp]
/-
**Cycle.mem_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：mem_coe_iff {a : α} {l : List α} : a in (↑l : Cycle α) ↔ a in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe_iff {a : α} {l : List α} : a ∈ (↑l : Cycle α) ↔ a ∈ l :=
  Iff.rfl

@[simp]
/-
**Cycle.notMem_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：notMem_nil (a : α) : a ∉ nil
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
-/
theorem notMem_nil (a : α) : a ∉ nil :=
  List.not_mem_nil
/-
**Cycle.** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : DecidableEq (Cycle α) := fun s₁ s₂ =>
  Quotient.recOnSubsingleton₂' s₁ s₂ fun _ _ => decidable_of_iff' _ Quotient.eq''
/-
**Cycle.** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] (x : α) (s : Cycle α) : Decidable (x ∈ s) :=
  Quotient.recOnSubsingleton' s fun l => show Decidable (x ∈ l) from inferInstance

/-- Reverse a `s : Cycle α` by reversing the underlying `List`. -/
nonrec def reverse (s : Cycle α) : Cycle α :=
  Quot.map reverse (fun _ _ => IsRotated.reverse) s

@[simp]
/-
**Cycle.reverse_coe** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：reverse_coe (l : List α) : (l : Cycle α).reverse = l.reverse
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverse_coe (l : List α) : (l : Cycle α).reverse = l.reverse :=
  rfl

@[simp]
/-
**Cycle.mem_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：mem_reverse_iff {a : α} {s : Cycle α} : a in s.reverse ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.mem_reverse`：∀ {α : Type u_1} {x : α} {as : List α}, x ∈ as.reverse
 ↔ x ∈ as
-/
theorem mem_reverse_iff {a : α} {s : Cycle α} : a ∈ s.reverse ↔ a ∈ s :=
  Quot.inductionOn s fun _ => mem_reverse

@[simp]
/-
**Cycle.reverse_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：reverse_reverse (s : Cycle α) : s.reverse.reverse = s
参数：s : Cycle α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverse_reverse (s : Cycle α) : s.reverse.reverse = s :=
  Quot.inductionOn s fun _ => by simp

@[simp]
/-
**Cycle.reverse_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：reverse_nil : nil.reverse = @nil α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverse_nil : nil.reverse = @nil α :=
  rfl

/-- The length of the `s : Cycle α`, which is the number of elements, counting duplicates. -/
/-
**Cycle.length** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：length (s : Cycle α) : Nat
参数：s : Cycle α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of the `s : Cycle α`, which is the number of elements, counting dupli
cates.
-/
def length (s : Cycle α) : ℕ :=
  Quot.liftOn s List.length fun _ _ e => e.perm.length_eq

@[simp]
/-
**Cycle.length_coe** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：length_coe (l : List α) : length (l : Cycle α) = l.length
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_coe (l : List α) : length (l : Cycle α) = l.length :=
  rfl

@[simp]
/-
**Cycle.length_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：length_nil : length (@nil α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_nil : length (@nil α) = 0 :=
  rfl

@[simp]
/-
**Cycle.length_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：length_reverse (s : Cycle α) : s.reverse.length = s.length
参数：s : Cycle α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
-/
theorem length_reverse (s : Cycle α) : s.reverse.length = s.length :=
  Quot.inductionOn s fun _ => List.length_reverse

/-- A `s : Cycle α` that is at most one element. -/
/-
**Cycle.Subsingleton** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：Subsingleton (s : Cycle α) : Prop
参数：s : Cycle α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `s : Cycle α` that is at most one element.
-/
def Subsingleton (s : Cycle α) : Prop :=
  s.length ≤ 1
/-
**Cycle.subsingleton_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：subsingleton_nil : Subsingleton (@nil α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem subsingleton_nil : Subsingleton (@nil α) := Nat.zero_le _
/-
**Cycle.length_subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：length_subsingleton_iff {s : Cycle α} : Subsingleton s ↔ length s <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem length_subsingleton_iff {s : Cycle α} : Subsingleton s ↔ length s ≤ 1 :=
  Iff.rfl

@[simp]
/-
**Cycle.subsingleton_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：subsingleton_reverse_iff {s : Cycle α} : s.reverse.Subsingleton ↔ s.Subsin
gleton
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
· 使用定理 `Cycle.length_reverse`：length_reverse (s : Cycle α) : s.reverse.length = 
s.length
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subsingleton_reverse_iff {s : Cycle α} : s.reverse.Subsingleton ↔ s.Subsingleton := by
  simp [length_subsingleton_iff]
/-
**Cycle.Subsingleton.congr** 是 Mathlib 中的一个定理，位于命名空间 `Cycle.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {s : Cycle α}, s.Subsingleton → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y :
 α⦄, y ∈ s → x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem Subsingleton.congr {s : Cycle α} (h : Subsingleton s) :
    ∀ ⦃x⦄ (_hx : x ∈ s) ⦃y⦄ (_hy : y ∈ s), x = y := by
  induction s using Quot.inductionOn with | _ l
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe, le_iff_lt_or_eq, Nat.lt_add_one_iff,
    length_eq_zero_iff, length_eq_one_iff, Nat.not_lt_zero, false_or] at h
  rcases h with (rfl | ⟨z, rfl⟩) <;> simp

/-- A `s : Cycle α` that is made up of at least two unique elements. -/
/-
**Cycle.Nontrivial** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：Nontrivial (s : Cycle α) : Prop
参数：s : Cycle α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `s : Cycle α` that is made up of at least two unique elements.
-/
def Nontrivial (s : Cycle α) : Prop :=
  ∃ x y : α, x ≠ y ∧ x ∈ s ∧ y ∈ s

@[simp]
/-
**Cycle.nontrivial_coe_nodup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：nontrivial_coe_nodup_iff {l : List α} (hl : l.Nodup) : Nontrivial (l : Cyc
le α) ↔ 2 <= l.length
参数：hl : l.Nodup。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.Nontrivial.eq_1`：∀ {α : Type u_1} (s : Cycle α), s.Nontrivial = ∃ 
x y, x ≠ y ∧ x ∈ s ∧ y ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem nontrivial_coe_nodup_iff {l : List α} (hl : l.Nodup) :
    Nontrivial (l : Cycle α) ↔ 2 ≤ l.length := by
  rw [Nontrivial]
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp
  · simp
  · simp only [mem_cons, mem_coe_iff, List.length, Ne, Nat.succ_le_succ_iff,
      Nat.zero_le, iff_true]
    refine ⟨hd, hd', ?_, by simp⟩
    simp only [not_or, mem_cons, nodup_cons] at hl
    exact hl.left.left

@[simp]
/-
**Cycle.nontrivial_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：nontrivial_reverse_iff {s : Cycle α} : s.reverse.Nontrivial ↔ s.Nontrivial
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nontrivial_reverse_iff {s : Cycle α} : s.reverse.Nontrivial ↔ s.Nontrivial := by
  simp [Nontrivial]
/-
**Cycle.length_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：length_nontrivial {s : Cycle α} (h : Nontrivial s) : 2 <= length s
参数：h : Nontrivial s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem length_nontrivial {s : Cycle α} (h : Nontrivial s) : 2 ≤ length s := by
  obtain ⟨x, y, hxy, hx, hy⟩ := h
  induction s using Quot.inductionOn with | _ l
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp at hx
  · simp only [mem_coe_iff, mk_eq_coe, mem_singleton] at hx hy
    simp [hx, hy] at hxy
  · simp [Nat.succ_le_succ_iff]

/-- The `s : Cycle α` contains no duplicates. -/
nonrec def Nodup (s : Cycle α) : Prop :=
  Quot.liftOn s Nodup fun _l₁ _l₂ e => propext <| e.nodup_iff

@[simp]
nonrec theorem nodup_nil : Nodup (@nil α) :=
  nodup_nil

@[simp]
/-
**Cycle.nodup_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：nodup_coe_iff {l : List α} : Nodup (l : Cycle α) ↔ l.Nodup
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nodup_coe_iff {l : List α} : Nodup (l : Cycle α) ↔ l.Nodup :=
  Iff.rfl

@[simp]
/-
**Cycle.nodup_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：nodup_reverse_iff {s : Cycle α} : s.reverse.Nodup ↔ s.Nodup
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.nodup_reverse`：nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nod
up l
-/
theorem nodup_reverse_iff {s : Cycle α} : s.reverse.Nodup ↔ s.Nodup :=
  Quot.inductionOn s fun _ => nodup_reverse
/-
**Cycle.Subsingleton.nodup** 是 Mathlib 中的一个定理，位于命名空间 `Cycle.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {s : Cycle α}, s.Subsingleton → s.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem Subsingleton.nodup {s : Cycle α} (h : Subsingleton s) : Nodup s := by
  induction s using Quot.inductionOn with | _ l
  obtain - | ⟨hd, tl⟩ := l
  · simp
  · have : tl = [] := by simpa [Subsingleton, length_eq_zero_iff, Nat.succ_le_succ_iff] using h
    simp [this]
/-
**Cycle.Nodup.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cycle.Nodup`。
形式化陈述：∀ {α : Type u_1} {s : Cycle α}, s.Nodup → (s.Nontrivial ↔ ¬s.Subsingleton)
参数：s.Nontrivial ↔ ¬s.Subsingleton。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.length_subsingleton_iff`：length_subsingleton_iff {s : Cycle α} : S
ubsingleton s ↔ length s <= 1
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Nodup.nontrivial_iff {s : Cycle α} (h : Nodup s) : Nontrivial s ↔ ¬Subsingleton s := by
  rw [length_subsingleton_iff]
  induction s using Quotient.inductionOn'
  simp only [mk''_eq_coe, nodup_coe_iff] at h
  simp [h, Nat.succ_le_iff]

/-- The `s : Cycle α` as a `Multiset α`.
-/
/-
**Cycle.toMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：toMultiset (s : Cycle α) : Multiset α
参数：s : Cycle α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `s : Cycle α` as a `Multiset α`.
-/
def toMultiset (s : Cycle α) : Multiset α :=
  Quotient.liftOn' s (↑) fun _ _ h => Multiset.coe_eq_coe.mpr h.perm

@[simp]
/-
**Cycle.coe_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：coe_toMultiset (l : List α) : (l : Cycle α).toMultiset = l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMultiset (l : List α) : (l : Cycle α).toMultiset = l :=
  rfl

@[simp]
/-
**Cycle.nil_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：nil_toMultiset : nil.toMultiset = (0 : Multiset α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nil_toMultiset : nil.toMultiset = (0 : Multiset α) :=
  rfl

@[simp]
/-
**Cycle.card_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：card_toMultiset (s : Cycle α) : Multiset.card s.toMultiset = s.length
参数：s : Cycle α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem card_toMultiset (s : Cycle α) : Multiset.card s.toMultiset = s.length :=
  Quotient.inductionOn' s (by simp)

@[simp]
/-
**Cycle.toMultiset_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：toMultiset_eq_nil {s : Cycle α} : s.toMultiset = 0 ↔ s = Cycle.nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem toMultiset_eq_nil {s : Cycle α} : s.toMultiset = 0 ↔ s = Cycle.nil :=
  Quotient.inductionOn' s (by simp)

/-- The lift of `list.map`. -/
/-
**Cycle.map** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：map {β : Type*} (f : α -> β) : Cycle α -> Cycle β
参数：f : α -> β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `List.IsRotated.map`：∀ {α : Type u} {β : Type u_1} {l₁ l₂ : List α}, l₁ ~
r l₂ → ∀ (f : α → β), List.map f l₁ ~r List.map f l₂

--- 原说明 ---
The lift of `list.map`.
-/
def map {β : Type*} (f : α → β) : Cycle α → Cycle β :=
  Quotient.map' (List.map f) fun _ _ h => h.map _

@[simp]
/-
**Cycle.map_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：map_nil {β : Type*} (f : α -> β) : map f nil = nil
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_nil {β : Type*} (f : α → β) : map f nil = nil :=
  rfl

@[simp]
/-
**Cycle.map_coe** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：map_coe {β : Type*} (f : α -> β) (l : List α) : map f ↑l = List.map f l
参数：f : α -> β；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coe {β : Type*} (f : α → β) (l : List α) : map f ↑l = List.map f l :=
  rfl

@[simp]
/-
**Cycle.map_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：map_eq_nil {β : Type*} (f : α -> β) (s : Cycle α) : map f s = nil ↔ s = ni
l
参数：f : α -> β；s : Cycle α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem map_eq_nil {β : Type*} (f : α → β) (s : Cycle α) : map f s = nil ↔ s = nil :=
  Quotient.inductionOn' s (by simp)

@[simp]
/-
**Cycle.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：mem_map {β : Type*} {f : α -> β} {b : β} {s : Cycle α} : b in s.map f ↔ ex
ists a, a in s ∧ f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mem_map {β : Type*} {f : α → β} {b : β} {s : Cycle α} :
    b ∈ s.map f ↔ ∃ a, a ∈ s ∧ f a = b :=
  Quotient.inductionOn' s (by simp)

/-- The `Multiset` of lists that can make the cycle. -/
/-
**Cycle.lists** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：lists (s : Cycle α) : Multiset (List α)
参数：s : Cycle α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Multiset` of lists that can make the cycle.
-/
def lists (s : Cycle α) : Multiset (List α) :=
  Quotient.liftOn' s (fun l => (l.cyclicPermutations : Multiset (List α))) fun l₁ l₂ h => by
    simpa using h.cyclicPermutations.perm

@[simp]
/-
**Cycle.lists_coe** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：lists_coe (l : List α) : lists (l : Cycle α) = ↑l.cyclicPermutations
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lists_coe (l : List α) : lists (l : Cycle α) = ↑l.cyclicPermutations :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Cycle.mem_lists_iff_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：mem_lists_iff_coe_eq {s : Cycle α} {l : List α} : l in s.lists ↔ (l : Cycl
e α) = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.lists.eq_1`：∀ {α : Type u_1} (s : Cycle α), s.lists = Quotient.lif
tOn' s (fun l => ↑l.cyclicPermutations) ⋯
· 使用定理 `Quotient.liftOn'_mk''`：∀ {α : Sort u_1} {φ : Sort u_4} {s₁ : Setoid α} (
f : α → φ) (h : ∀ (a b : α), s₁ a b → f a = f b) (x : α),   (Quotient.mk'' x).li
ftOn' f h =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_lists_iff_coe_eq {s : Cycle α} {l : List α} : l ∈ s.lists ↔ (l : Cycle α) = s :=
  Quotient.inductionOn' s fun l => by
    rw [lists, Quotient.liftOn'_mk'']
    simp

@[simp]
/-
**Cycle.lists_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：lists_nil : lists (@nil α) = {([] : List α)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.nil.eq_1`：∀ {α : Type u_1}, Cycle.nil = ↑[]
· 使用定理 `Cycle.lists_coe`：lists_coe (l : List α) : lists (l : Cycle α) = ↑l.cycli
cPermutations
· 使用定理 `List.cyclicPermutations_nil`：cyclicPermutations_nil : cyclicPermutations
 ([] : List α) = [[]]
· 使用定理 `Multiset.coe_singleton`：coe_singleton (a : α) : ([a] : Multiset α) = {a}
-/
theorem lists_nil : lists (@nil α) = {([] : List α)} := by
  rw [nil, lists_coe, cyclicPermutations_nil, Multiset.coe_singleton]

section Decidable

variable [DecidableEq α]

/-- Auxiliary decidability algorithm for lists that contain at least two unique elements.
-/
/-
**Cycle.decidableNontrivialCoe** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → (l : List α) → Decidable (↑l).Nontrivia
l
参数：l : List α；↑l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary decidability algorithm for lists that contain at least two unique elem
ents.
-/
def decidableNontrivialCoe : ∀ l : List α, Decidable (Nontrivial (l : Cycle α))
  | [] => isFalse (by simp [Nontrivial])
  | [x] => isFalse (by simp [Nontrivial])
  | x :: y :: l =>
    if h : x = y then
      @decidable_of_iff' _ (Nontrivial (x :: l : Cycle α)) (by simp [h, Nontrivial])
        (decidableNontrivialCoe (x :: l))
    else isTrue ⟨x, y, h, by simp, by simp⟩
/-
**Cycle.** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {s : Cycle α} : Decidable (Nontrivial s) :=
  Quot.recOnSubsingleton s decidableNontrivialCoe
/-
**Cycle.** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {s : Cycle α} : Decidable (Nodup s) :=
  Quot.recOnSubsingleton s List.nodupDecidable
/-
**Cycle.fintypeNodupCycle** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
形式化陈述：fintypeNodupCycle [Fintype α] : Fintype { s : Cycle α // s.Nodup }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeNodupCycle [Fintype α] : Fintype { s : Cycle α // s.Nodup } :=
  Fintype.ofSurjective (fun l : { l : List α // l.Nodup } => ⟨l.val, by simpa using l.prop⟩)
    fun ⟨s, hs⟩ => by
    induction s using Quotient.inductionOn' with | _ hs
    exact ⟨⟨_, hs⟩, by simp⟩
/-
**Cycle.fintypeNodupNontrivialCycle** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
形式化陈述：fintypeNodupNontrivialCycle [Fintype α] : Fintype { s : Cycle α // s.Nodup
 ∧ s.Nontrivial }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeNodupNontrivialCycle [Fintype α] :
    Fintype { s : Cycle α // s.Nodup ∧ s.Nontrivial } :=
  Fintype.subtype
    (((Finset.univ : Finset { s : Cycle α // s.Nodup }).map (Function.Embedding.subtype _)).filter
      Cycle.Nontrivial)
    (by simp)

/-- The `s : Cycle α` as a `Finset α`. -/
/-
**Cycle.toFinset** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：toFinset (s : Cycle α) : Finset α
参数：s : Cycle α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `s : Cycle α` as a `Finset α`.
-/
def toFinset (s : Cycle α) : Finset α :=
  s.toMultiset.toFinset

@[simp]
/-
**Cycle.toFinset_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：toFinset_toMultiset (s : Cycle α) : s.toMultiset.toFinset = s.toFinset
参数：s : Cycle α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinset_toMultiset (s : Cycle α) : s.toMultiset.toFinset = s.toFinset :=
  rfl

@[simp]
/-
**Cycle.coe_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：coe_toFinset (l : List α) : (l : Cycle α).toFinset = l.toFinset
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toFinset (l : List α) : (l : Cycle α).toFinset = l.toFinset :=
  rfl

@[simp]
/-
**Cycle.nil_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：nil_toFinset : (@nil α).toFinset = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nil_toFinset : (@nil α).toFinset = ∅ :=
  rfl

@[simp]
/-
**Cycle.toFinset_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：toFinset_eq_nil {s : Cycle α} : s.toFinset = ∅ ↔ s = Cycle.nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem toFinset_eq_nil {s : Cycle α} : s.toFinset = ∅ ↔ s = Cycle.nil :=
  Quotient.inductionOn' s (by simp)

/-- Given a `s : Cycle α` such that `Nodup s`, retrieve the next element after `x ∈ s`. -/
nonrec def next : ∀ (s : Cycle α) (_hs : Nodup s) (x : α) (_hx : x ∈ s), α := fun s =>
  Quot.hrecOn (motive := fun (s : Cycle α) => ∀ (_hs : Cycle.Nodup s) (x : α) (_hx : x ∈ s), α) s
  (fun l _hn x hx => next l x hx) fun l₁ l₂ h =>
    Function.hfunext (propext h.nodup_iff) fun h₁ h₂ _he =>
      Function.hfunext rfl fun x y hxy =>
        Function.hfunext (propext (by rw [eq_of_heq hxy]; simpa [eq_of_heq hxy] using h.mem_iff))
  fun hm hm' he' => heq_of_eq
    (by rw [heq_iff_eq] at hxy; subst x; simpa using isRotated_next_eq h h₁ _)

/-- Given a `s : Cycle α` such that `Nodup s`, retrieve the previous element before `x ∈ s`. -/
nonrec def prev : ∀ (s : Cycle α) (_hs : Nodup s) (x : α) (_hx : x ∈ s), α := fun s =>
  Quot.hrecOn (motive := fun (s : Cycle α) => ∀ (_hs : Cycle.Nodup s) (x : α) (_hx : x ∈ s), α) s
  (fun l _hn x hx => prev l x hx) fun l₁ l₂ h =>
    Function.hfunext (propext h.nodup_iff) fun h₁ h₂ _he =>
      Function.hfunext rfl fun x y hxy =>
        Function.hfunext (propext (by rw [eq_of_heq hxy]; simpa [eq_of_heq hxy] using h.mem_iff))
  fun hm hm' he' => heq_of_eq
    (by rw [heq_iff_eq] at hxy; subst x; simpa using isRotated_prev_eq h h₁ _)

-- `simp` cannot infer the proofs: see `prev_reverse_eq_next'` for `@[simp]` lemma.
nonrec theorem prev_reverse_eq_next (s : Cycle α) : ∀ (hs : Nodup s) (x : α) (hx : x ∈ s),
    s.reverse.prev (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.next hs x hx :=
  Quotient.inductionOn' s prev_reverse_eq_next

@[simp]
nonrec theorem prev_reverse_eq_next' (s : Cycle α) (hs : Nodup s.reverse) (x : α)
    (hx : x ∈ s.reverse) :
    s.reverse.prev hs x hx = s.next (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx) :=
  prev_reverse_eq_next s (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx)

-- `simp` cannot infer the proofs: see `next_reverse_eq_prev'` for `@[simp]` lemma.
/-
**Cycle.next_reverse_eq_prev** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：next_reverse_eq_prev (s : Cycle α) (hs : Nodup s) (x : α) (hx : x in s) : 
s.reverse.next (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.prev hs
 x hx
参数：s : Cycle α；hs : Nodup s；x : α；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cycle.nodup_reverse_iff`：nodup_reverse_iff {s : Cycle α} : s.reverse.Nod
up ↔ s.Nodup
· 使用定理 `Cycle.mem_reverse_iff`：mem_reverse_iff {a : α} {s : Cycle α} : a in s.re
verse ↔ a in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cycle.reverse_reverse`：reverse_reverse (s : Cycle α) : s.reverse.reverse
 = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.prev.congr_simp`：∀ {α : Type u_1} [inst : DecidableEq α] (s s_1 : 
Cycle α) (e_s : s = s_1) (_hs : s.Nodup) (x x_1 : α) (e_x : x = x_1)   (_hx : x 
∈ s), s.pre…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem next_reverse_eq_prev (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) :
    s.reverse.next (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.prev hs x hx := by
  simp [← prev_reverse_eq_next]

@[simp]
/-
**Cycle.next_reverse_eq_prev'** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：next_reverse_eq_prev' (s : Cycle α) (hs : Nodup s.reverse) (x : α) (hx : x
 in s.reverse) : s.reverse.next hs x hx = s.prev (nodup_reverse_iff.mp hs) x (me
m_reverse_iff.mp hx)
参数：s : Cycle α；hs : Nodup s.reverse；x : α；hx : x in s.reverse。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cycle.nodup_reverse_iff`：nodup_reverse_iff {s : Cycle α} : s.reverse.Nod
up ↔ s.Nodup
· 使用定理 `Cycle.mem_reverse_iff`：mem_reverse_iff {a : α} {s : Cycle α} : a in s.re
verse ↔ a in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cycle.reverse_reverse`：reverse_reverse (s : Cycle α) : s.reverse.reverse
 = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.prev.congr_simp`：∀ {α : Type u_1} [inst : DecidableEq α] (s s_1 : 
Cycle α) (e_s : s = s_1) (_hs : s.Nodup) (x x_1 : α) (e_x : x = x_1)   (_hx : x 
∈ s), s.pre…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem next_reverse_eq_prev' (s : Cycle α) (hs : Nodup s.reverse) (x : α) (hx : x ∈ s.reverse) :
    s.reverse.next hs x hx = s.prev (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx) := by
  simp [← prev_reverse_eq_next]

@[simp]
nonrec theorem next_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) : s.next hs x hx ∈ s := by
  induction s using Quot.inductionOn
  apply next_mem; assumption
/-
**Cycle.prev_mem** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：prev_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x in s) : s.prev hs x 
hx in s
参数：s : Cycle α；hs : Nodup s；x : α；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cycle.nodup_reverse_iff`：nodup_reverse_iff {s : Cycle α} : s.reverse.Nod
up ↔ s.Nodup
· 使用定理 `Cycle.mem_reverse_iff`：mem_reverse_iff {a : α} {s : Cycle α} : a in s.re
verse ↔ a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cycle.next_reverse_eq_prev`：next_reverse_eq_prev (s : Cycle α) (hs : Nod
up s) (x : α) (hx : x in s) : s.reverse.next (nodup_reverse_iff.mpr hs) x (mem_r
everse_iff.mpr h…
· 使用定理 `Cycle.next_mem`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Cycle α) (h
s : s.Nodup) (x : α) (hx : x ∈ s), s.next hs x hx ∈ s
-/
theorem prev_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) : s.prev hs x hx ∈ s := by
  rw [← next_reverse_eq_prev, ← mem_reverse_iff]
  apply next_mem

@[simp]
nonrec theorem prev_next (s : Cycle α) : ∀ (hs : Nodup s) (x : α) (hx : x ∈ s),
    s.prev hs (s.next hs x hx) (next_mem s hs x hx) = x :=
  Quotient.inductionOn' s prev_next

@[simp]
nonrec theorem next_prev (s : Cycle α) : ∀ (hs : Nodup s) (x : α) (hx : x ∈ s),
    s.next hs (s.prev hs x hx) (prev_mem s hs x hx) = x :=
  Quotient.inductionOn' s next_prev

end Decidable

/-- We define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representable types. For example, the cycle `(2 1 4 3)` will be shown
as `c[2, 1, 4, 3]`. Two equal cycles may be printed differently if their internal representation
is different.
-/
/-
**Cycle.** 是 Mathlib 中的一个实例，位于命名空间 `Cycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define a representation of concrete cycles, available when viewing them in a 
goal state or
via `#eval`, when over representable types. For example, the cycle `(2 1 4 3)` w
ill be shown
as `c[2, 1, 4, 3]`. Two equal cycles may be printed differently if their interna
l representation
is different.
-/
unsafe instance [Repr α] : Repr (Cycle α) :=
  ⟨fun s _ => "c[" ++ Std.Format.joinSep (s.map repr).lists.unquot.head! ", " ++ "]"⟩

/-- `chain R s` means that `R` holds between adjacent elements of `s`.

`chain R ([a, b, c] : Cycle α) ↔ R a b ∧ R b c ∧ R c a` -/
nonrec def Chain (r : α → α → Prop) (c : Cycle α) : Prop :=
  Quotient.liftOn' c
    (fun l =>
      match l with
      | [] => True
      | a :: m => IsChain r (a :: m ++ [a]))
    fun a b hab =>
    propext <| by
      rcases a with - | ⟨a, l⟩ <;> rcases b with - | ⟨b, m⟩
      · rfl
      · have := isRotated_nil_iff'.1 hab
        contradiction
      · have := isRotated_nil_iff.1 hab
        contradiction
      · dsimp only
        obtain ⟨n, hn⟩ := hab
        induction n generalizing a b l m with
        | zero =>
          simp only [rotate_zero, cons.injEq] at hn
          rw [hn.1, hn.2]
        | succ d hd =>
          rcases l with - | ⟨c, s⟩
          · simp only [rotate_cons_succ, nil_append, rotate_singleton, cons.injEq] at hn
            rw [hn.1, hn.2]
          · rw [Nat.add_comm, ← rotate_rotate, rotate_cons_succ, rotate_zero, cons_append] at hn
            rw [← hd c _ _ _ hn]
            simp [and_comm]

@[simp]
/-
**Cycle.Chain.nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle.Chain`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop), Cycle.Chain r Cycle.nil
参数：r : α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Chain.nil (r : α → α → Prop) : Cycle.Chain r (@nil α) := by trivial

@[simp]
/-
**Cycle.chain_coe_cons** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：chain_coe_cons (r : α -> α -> Prop) (a : α) (l : List α) : Chain r (a :: l
) ↔ List.IsChain r (a :: (l ++ [a]))
参数：r : α -> α -> Prop；a : α；l : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem chain_coe_cons (r : α → α → Prop) (a : α) (l : List α) :
    Chain r (a :: l) ↔ List.IsChain r (a :: (l ++ [a])) :=
  Iff.rfl
/-
**Cycle.chain_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：chain_singleton (r : α -> α -> Prop) (a : α) : Chain r [a] ↔ r a a
参数：r : α -> α -> Prop；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.chain_coe_cons`：chain_coe_cons (r : α -> α -> Prop) (a : α) (l : L
ist α) : Chain r (a :: l) ↔ List.IsChain r (a :: (l ++ [a]))
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `List.isChain_pair`：isChain_pair {x y} : IsChain R [x, y] ↔ R x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem chain_singleton (r : α → α → Prop) (a : α) : Chain r [a] ↔ r a a := by
  rw [chain_coe_cons, nil_append, List.isChain_pair]
/-
**Cycle.chain_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：chain_ne_nil (r : α -> α -> Prop) {l : List α} : forall hl : l != [], Chai
n r l ↔ List.IsChain r (getLast l hl :: l)
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Ne.irrefl`：∀ {α : Sort u} {a : α}, a ≠ a → False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cycle.coe_cons_eq_coe_append`：coe_cons_eq_coe_append (l : List α) (a : α
) : (↑(a :: l) : Cycle α) = (↑(l ++ [a]) : Cycle α)
· 使用定理 `Cycle.chain_coe_cons`：chain_coe_cons (r : α -> α -> Prop) (a : α) (l : L
ist α) : Chain r (a :: l) ↔ List.IsChain r (a :: (l ++ [a]))
· 使用定理 `List.append_ne_nil_of_right_ne_nil`：∀ {α : Type u_1} {t : List α} (s : L
ist α), t ≠ [] → s ++ t ≠ []
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.getLast_append_singleton`：getLast_append_singleton {a : α} (l : Lis
t α) : getLast (l ++ [a]) (append_ne_nil_of_right_ne_nil l (cons_ne_nil a _)) = 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem chain_ne_nil (r : α → α → Prop) {l : List α} :
    ∀ hl : l ≠ [], Chain r l ↔ List.IsChain r (getLast l hl :: l) :=
  l.reverseRecOn (fun hm => hm.irrefl.elim) (by
    intro m a _H _
    rw [← coe_cons_eq_coe_append, chain_coe_cons, getLast_append_singleton])
/-
**Cycle.chain_map** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：chain_map {β : Type*} {r : α -> α -> Prop} (f : β -> α) {s : Cycle β} : Ch
ain r (s.map f) ↔ Chain (fun a b => r (f a) (f b)) s
参数：f : β -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.isChain_cons_map`：isChain_cons_map (f : β -> α) {l : List β} {b : β
} : IsChain R (f b :: map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) (b :: l)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem chain_map {β : Type*} {r : α → α → Prop} (f : β → α) {s : Cycle β} :
    Chain r (s.map f) ↔ Chain (fun a b => r (f a) (f b)) s :=
  Quotient.inductionOn s fun l => by
    rcases l with - | ⟨a, l⟩
    · rfl
    · simp [← concat_eq_append, ← map_concat, List.isChain_cons_map f]
/-
**Cycle.chain_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：chain_range_succ (r : Nat -> Nat -> Prop) (n : Nat) : Chain r (List.range 
n.succ) ↔ r n 0 ∧ forall m < n, r m m.succ
参数：r : Nat -> Nat -> Prop；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cycle.coe_cons_eq_coe_append`：coe_cons_eq_coe_append (l : List α) (a : α
) : (↑(a :: l) : Cycle α) = (↑(l ++ [a]) : Cycle α)
· 使用定理 `Cycle.chain_coe_cons`：chain_coe_cons (r : α -> α -> Prop) (a : α) (l : L
ist α) : Chain r (a :: l) ↔ List.IsChain r (a :: (l ++ [a]))
· 使用定理 `List.isChain_cons_range_succ`：isChain_cons_range_succ (r : Nat -> Nat ->
 Prop) (n a : Nat) : IsChain r (a :: range n.succ) ↔ r a 0 ∧ forall m < n, r m m
.succ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem chain_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) :
    Chain r (List.range n.succ) ↔ r n 0 ∧ ∀ m < n, r m m.succ := by
  rw [range_succ, ← coe_cons_eq_coe_append, chain_coe_cons, ← range_succ, isChain_cons_range_succ]

variable {r : α → α → Prop} {s : Cycle α}
/-
**Cycle.Chain.imp** 是 Mathlib 中的一个定理，位于命名空间 `Cycle.Chain`。
形式化陈述：∀ {α : Type u_1} {s : Cycle α} {r₁ r₂ : α → α → Prop},   (∀ (a b : α), r₁ 
a b → r₂ a b) → Cycle.Chain r₁ s → Cycle.Chain r₂ s
参数：∀ (a b : α), r₁ a b → r₂ a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cycle.induction_on`：induction_on {motive : Cycle α -> Prop} (s : Cycle α
) (nil : motive nil) (cons : forall (a) (l : List α), motive ↑l -> motive ↑(a ::
 l)) : m…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.chain_coe_cons`：chain_coe_cons (r : α -> α -> Prop) (a : α) (l : L
ist α) : Chain r (a :: l) ↔ List.IsChain r (a :: (l ++ [a]))
· 使用定理 `List.IsChain.imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α}, (∀
 ⦃a b : α⦄, R a b → S a b) → List.IsChain R l → List.IsChain S l
-/
theorem Chain.imp {r₁ r₂ : α → α → Prop} (H : ∀ a b, r₁ a b → r₂ a b) (p : Chain r₁ s) :
    Chain r₂ s := by
  induction s
  · trivial
  · rw [chain_coe_cons] at p ⊢
    exact p.imp H

/-- As a function from a relation to a predicate, `chain` is monotonic. -/
/-
**Cycle.chain_mono** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：chain_mono : Monotone (Chain : (α -> α -> Prop) -> Cycle α -> Prop)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cycle.Chain.imp`：∀ {α : Type u_1} {s : Cycle α} {r₁ r₂ : α → α → Prop}, 
  (∀ (a b : α), r₁ a b → r₂ a b) → Cycle.Chain r₁ s → Cycle.Chain r₂ s

--- 原说明 ---
As a function from a relation to a predicate, `chain` is monotonic.
-/
theorem chain_mono : Monotone (Chain : (α → α → Prop) → Cycle α → Prop) := fun _a _b hab _s =>
  Chain.imp hab
/-
**Cycle.chain_of_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：chain_of_pairwise : (forall a in s, forall b in s, r a b) -> Chain r s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cycle.induction_on`：induction_on {motive : Cycle α -> Prop} (s : Cycle α
) (nil : motive nil) (cons : forall (a) (l : List α), motive ↑l -> motive ↑(a ::
 l)) : m…
· 使用定理 `Cycle.Chain.nil`：∀ {α : Type u_1} (r : α → α → Prop), Cycle.Chain r Cycl
e.nil
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Cycle.chain_coe_cons`：chain_coe_cons (r : α -> α -> Prop) (a : α) (l : L
ist α) : Chain r (a :: l) ↔ List.IsChain r (a :: (l ++ [a]))
· 使用定理 `List.Pairwise.isChain`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
 List.Pairwise R l → List.IsChain R l
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.pairwise_append`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List 
α},   List.Pairwise R (l₁ ++ l₂) ↔ List.Pairwise R l₁ ∧ List.Pairwise R l₂ ∧ ∀ a
 ∈ l₁, ∀ b…
· 使用定理 `List.pairwise_of_forall_mem_list`：∀ {α : Type u_1} {l : List α} {r : α →
 α → Prop}, (∀ a ∈ l, ∀ b ∈ l, r a b) → List.Pairwise r l
· 使用定理 `List.pairwise_singleton`：∀ {α : Type u_1} (R : α → α → Prop) (a : α), Li
st.Pairwise R [a]
-/
theorem chain_of_pairwise : (∀ a ∈ s, ∀ b ∈ s, r a b) → Chain r s := by
  induction s with
  | nil => exact fun _ ↦ Cycle.Chain.nil r
  | cons a l => ?_
  intro hs
  have Ha : a ∈ (a :: l : Cycle α) := by simp
  have Hl : ∀ {b} (_hb : b ∈ l), b ∈ (a :: l : Cycle α) := @fun b hb => by simp [hb]
  rw [Cycle.chain_coe_cons]
  apply Pairwise.isChain
  rw [pairwise_cons]
  exact
    ⟨fun b hb => by grind,
      pairwise_append.2
        ⟨pairwise_of_forall_mem_list fun b hb c hc => hs b (Hl hb) c (Hl hc),
          pairwise_singleton r a, fun b hb c hc => by grind⟩⟩
/-
**Cycle.chain_iff_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：chain_iff_pairwise [IsTrans α r] : Chain r s ↔ forall a in s, forall b in 
s, r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cycle.induction_on`：induction_on {motive : Cycle α -> Prop} (s : Cycle α
) (nil : motive nil) (cons : forall (a) (l : List α), motive ↑l -> motive ↑(a ::
 l)) : m…
· 使用定理 `Cycle.notMem_nil`：notMem_nil (a : α) : a ∉ nil
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `List.isChain_iff_pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α} [Trans R R R], List.IsChain R l ↔ List.Pairwise R l
· 使用定理 `Cycle.chain_coe_cons`：chain_coe_cons (r : α -> α -> Prop) (a : α) (l : L
ist α) : Chain r (a :: l) ↔ List.IsChain r (a :: (l ++ [a]))
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `Cycle.chain_of_pairwise`：chain_of_pairwise : (forall a in s, forall b in
 s, r a b) -> Chain r s
-/
theorem chain_iff_pairwise [IsTrans α r] : Chain r s ↔ ∀ a ∈ s, ∀ b ∈ s, r a b :=
  ⟨by
    induction s with
    | nil => exact fun _ b hb ↦ (notMem_nil _ hb).elim
    | cons a l => ?_
    intro hs b hb c hc
    rw [Cycle.chain_coe_cons, List.isChain_iff_pairwise] at hs
    simp only [pairwise_append, pairwise_cons, mem_append, mem_singleton, List.not_mem_nil,
      IsEmpty.forall_iff, imp_true_iff, Pairwise.nil, forall_eq, true_and] at hs
    simp only [mem_coe_iff, mem_cons] at hb hc
    rcases hb with (rfl | hb) <;> rcases hc with (rfl | hc)
    · exact hs.1 c (Or.inr rfl)
    · exact hs.1 c (Or.inl hc)
    · exact hs.2.2 b hb
    · exact _root_.trans (hs.2.2 b hb) (hs.1 c (Or.inl hc)), Cycle.chain_of_pairwise⟩
/-
**Cycle.Chain.eq_nil_of_irrefl** 是 Mathlib 中的一个定理，位于命名空间 `Cycle.Chain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Cycle α} [IsTrans α r] [Std.Irref
l r], Cycle.Chain r s → s = Cycle.nil
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cycle.induction_on`：induction_on {motive : Cycle α -> Prop} (s : Cycle α
) (nil : motive nil) (cons : forall (a) (l : List α), motive ↑l -> motive ↑(a ::
 l)) : m…
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cycle.chain_iff_pairwise`：chain_iff_pairwise [IsTrans α r] : Chain r s ↔
 forall a in s, forall b in s, r a b
-/
theorem Chain.eq_nil_of_irrefl [IsTrans α r] [Std.Irrefl r] (h : Chain r s) : s = Cycle.nil := by
  induction s with
  | nil => rfl
  | cons a l h =>
    have ha : a ∈ a :: l := mem_cons_self
    exact (irrefl_of r a <| chain_iff_pairwise.1 h a ha a ha).elim
/-
**Cycle.Chain.eq_nil_of_well_founded** 是 Mathlib 中的一个定理，位于命名空间 `Cycle.Chain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Cycle α} [IsWellFounded α r], Cyc
le.Chain r s → s = Cycle.nil
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cycle.Chain.eq_nil_of_irrefl`：∀ {α : Type u_1} {r : α → α → Prop} {s : C
ycle α} [IsTrans α r] [Std.Irrefl r], Cycle.Chain r s → s = Cycle.nil
· 使用定理 `Relation.TransGen.instIsTrans`：∀ {α : Type u_1} {r : α → α → Prop}, IsTr
ans α (Relation.TransGen r)
· 使用定理 `Std.instIrreflOfAsymm`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asymm r]
, Std.Irrefl r
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `instIsWellFoundedTransGen`：∀ {α : Type u} (r : α → α → Prop) [i : IsWell
Founded α r], IsWellFounded α (Relation.TransGen r)
· 使用定理 `Cycle.Chain.imp`：∀ {α : Type u_1} {s : Cycle α} {r₁ r₂ : α → α → Prop}, 
  (∀ (a b : α), r₁ a b → r₂ a b) → Cycle.Chain r₁ s → Cycle.Chain r₂ s
-/
theorem Chain.eq_nil_of_well_founded [IsWellFounded α r] (h : Chain r s) : s = Cycle.nil :=
  Chain.eq_nil_of_irrefl <| h.imp fun _ _ => Relation.TransGen.single
/-
**Cycle.forall_eq_of_chain** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：forall_eq_of_chain [IsTrans α r] [Std.Antisymm r] (hs : Chain r s) {a b : 
α} (ha : a in s) (hb : b in s) : a = b
参数：hs : Chain r s；ha : a in s；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `antisymm`：antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.chain_iff_pairwise`：chain_iff_pairwise [IsTrans α r] : Chain r s ↔
 forall a in s, forall b in s, r a b
-/
theorem forall_eq_of_chain [IsTrans α r] [Std.Antisymm r] (hs : Chain r s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : a = b := by
  rw [chain_iff_pairwise] at hs
  exact antisymm (hs a ha b hb) (hs b hb a ha)

end Cycle

