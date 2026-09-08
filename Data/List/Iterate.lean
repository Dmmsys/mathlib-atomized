/-
Copyright (c) 2024 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Defs

/-!
# iterate

Proves various lemmas about `List.iterate`.
-/

public section

variable {α : Type*}

namespace List

@[simp]
/-
**List.length_iterate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_iterate (f : α -> α) (a : α) (n : Nat) : length (iterate f a n) = n
参数：f : α -> α；a : α；n : Nat。
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
theorem length_iterate (f : α → α) (a : α) (n : ℕ) : length (iterate f a n) = n := by
  induction n generalizing a <;> simp [*]

@[simp]
/-
**List.iterate_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：iterate_eq_nil {f : α -> α} {a : α} {n : Nat} : iterate f a n = [] ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_eq_zero_iff`：∀ {α : Type u_1} {l : List α}, l.length = 0 ↔ l
 = []
· 使用定理 `List.length_iterate`：length_iterate (f : α -> α) (a : α) (n : Nat) : len
gth (iterate f a n) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iterate_eq_nil {f : α → α} {a : α} {n : ℕ} : iterate f a n = [] ↔ n = 0 := by
  rw [← length_eq_zero_iff, length_iterate]
/-
**List.getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.
prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem?_iterate (f : α → α) (a : α) :
    ∀ (n i : ℕ), i < n → (iterate f a n)[i]? = f^[i] a
  | n + 1, 0, _ => by simp
  | n + 1, i + 1, h => by simp [getElem?_iterate f (f a) n i (by simpa using h)]

@[simp]
/-
**List.getElem_iterate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_iterate (f : α -> α) (a : α) (n : Nat) (i : Nat) (h : i < (iterate
 f a n).length) : (iterate f a n)[i] = f^[i] a
参数：f : α -> α；a : α；n : Nat；i : Nat；h : i < (iterate f a n).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.getElem_eq_iff`：∀ {α : Type u_1} {x : α} {l : List α} {i : ℕ} (h : 
i < l.length), l[i] = x ↔ l[i]? = some x
· 使用定理 `List.getElem?_iterate`：∀ {α : Type u_1} (f : α → α) (a : α) (n i : ℕ), i
 < n → (List.iterate f a n)[i]? = some (f^[i] a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_iterate`：length_iterate (f : α -> α) (a : α) (n : Nat) : len
gth (iterate f a n) = n
-/
theorem getElem_iterate (f : α → α) (a : α) (n : ℕ) (i : Nat) (h : i < (iterate f a n).length) :
    (iterate f a n)[i] = f^[i] a :=
  (getElem_eq_iff _).2 <| getElem?_iterate _ _ _ _ <| by rwa [length_iterate] at h

@[simp]
/-
**List.mem_iterate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_iterate {f : α -> α} {a : α} {n : Nat} {b : α} : b in iterate f a n ↔ 
exists m < n, b = f^[m] a
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
· 使用定理 `List.getElem_iterate`：getElem_iterate (f : α -> α) (a : α) (n : Nat) (i 
: Nat) (h : i < (iterate f a n).length) : (iterate f a n)[i] = f^[i] a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `List.length_iterate`：length_iterate (f : α -> α) (a : α) (n : Nat) : len
gth (iterate f a n) = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iterate {f : α → α} {a : α} {n : ℕ} {b : α} :
    b ∈ iterate f a n ↔ ∃ m < n, b = f^[m] a := by
  simp [List.mem_iff_get, Fin.exists_iff, eq_comm (b := b)]

@[simp]
/-
**List.range_map_iterate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：range_map_iterate (n : Nat) (f : α -> α) (a : α) : (List.range n).map (f^[
·] a) = List.iterate f a n
参数：n : Nat；f : α -> α；a : α。
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
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `List.length_iterate`：length_iterate (f : α -> α) (a : α) (n : Nat) : len
gth (iterate f a n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getElem_range`：∀ {j n : ℕ} (h : j < (List.range n).length), (List.r
ange n)[j] = j
· 使用定理 `List.getElem_iterate`：getElem_iterate (f : α -> α) (a : α) (n : Nat) (i 
: Nat) (h : i < (iterate f a n).length) : (iterate f a n)[i] = f^[i] a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem range_map_iterate (n : ℕ) (f : α → α) (a : α) :
    (List.range n).map (f^[·] a) = List.iterate f a n := by
  apply List.ext_getElem <;> simp
/-
**List.iterate_add** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：iterate_add (f : α -> α) (a : α) (m n : Nat) : iterate f a (m + n) = itera
te f a m ++ iterate f (f^[m] a) n
参数：f : α -> α；a : α；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.iterate.eq_2`：∀ {α : Type u_1} (f : α → α) (a : α) (n : ℕ), List.it
erate f a n.succ = a :: List.iterate f (f a) n
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Nat.iterate.eq_2`：∀ {α : Sort u} (op : α → α) (x : α) (k : ℕ), op^[k.suc
c] x = op^[k] (op x)
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
-/
theorem iterate_add (f : α → α) (a : α) (m n : ℕ) :
    iterate f a (m + n) = iterate f a m ++ iterate f (f^[m] a) n := by
  induction m generalizing a with
  | zero => simp
  | succ n ih => rw [iterate, add_right_comm, iterate, ih, Nat.iterate, cons_append]
/-
**List.take_iterate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：take_iterate (f : α -> α) (a : α) (m n : Nat) : take m (iterate f a n) = i
terate f a (min m n)
参数：f : α -> α；a : α；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.range_map_iterate`：range_map_iterate (n : Nat) (f : α -> α) (a : α)
 : (List.range n).map (f^[·] a) = List.iterate f a n
· 使用定理 `List.map_take`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.take i l) = List.take i (List.map f l)
· 使用定理 `List.take_range`：∀ {i n : ℕ}, List.take i (List.range n) = List.range (m
in i n)
-/
theorem take_iterate (f : α → α) (a : α) (m n : ℕ) :
    take m (iterate f a n) = iterate f a (min m n) := by
  rw [← range_map_iterate, ← range_map_iterate, ← map_take, take_range]

end List

