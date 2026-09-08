/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Take operations on tuples

We define the `take` operation on `n`-tuples, which restricts a tuple to its first `m` elements.

* `Fin.take`: Given `h : m ≤ n`, `Fin.take m h v` for an `n`-tuple `v = (v 0, ..., v (n - 1))` is
  the `m`-tuple `(v 0, ..., v (m - 1))`.
-/

@[expose] public section

namespace Fin

open Function

variable {n : ℕ} {α : Fin n → Sort*}

section Take

/-- Take the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `m`-tuple. -/
/-
**Fin.take** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：take (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) : (i : Fin m) -> α (c
astLE h i)
参数：m : Nat；h : m <= n；v : (i : Fin n) -> α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `m`-tupl
e.
-/
def take (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) : (i : Fin m) → α (castLE h i) :=
  fun i ↦ v (castLE h i)

@[simp]
/-
**Fin.take_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_apply (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin m) : (
take m h v) i = v (castLE h i)
参数：m : Nat；h : m <= n；v : (i : Fin n) -> α i；i : Fin m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem take_apply (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin m) :
    (take m h v) i = v (castLE h i) := rfl

@[simp]
/-
**Fin.take_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_zero (v : (i : Fin n) -> α i) : take 0 n.zero_le v = fun i => elim0 i
参数：v : (i : Fin n) -> α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem take_zero (v : (i : Fin n) → α i) : take 0 n.zero_le v = fun i ↦ elim0 i := by
  ext i; exact elim0 i

@[simp]
/-
**Fin.take_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_one {α : Fin (n + 1) -> Sort*} (v : (i : Fin (n + 1)) -> α i) : take 
1 (Nat.le_add_left 1 n) v = (fun i => v (castLE (Nat.le_add_left 1 n) i))
参数：n + 1；v : (i : Fin (n + 1)) -> α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem take_one {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    take 1 (Nat.le_add_left 1 n) v = (fun i => v (castLE (Nat.le_add_left 1 n) i)) := by
  ext i
  simp only [take]

@[simp]
/-
**Fin.take_eq_init** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_eq_init {α : Fin (n + 1) -> Sort*} (v : (i : Fin (n + 1)) -> α i) : t
ake n n.le_succ v = init v
参数：n + 1；v : (i : Fin (n + 1)) -> α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem take_eq_init {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    take n n.le_succ v = init v := rfl

@[simp]
/-
**Fin.take_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_eq_self (v : (i : Fin n) -> α i) : take n (le_refl n) v = v
参数：v : (i : Fin n) -> α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem take_eq_self (v : (i : Fin n) → α i) : take n (le_refl n) v = v := by
  ext i
  simp [take]

@[simp]
/-
**Fin.take_take** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_take {m n' : Nat} (h : m <= n') (h' : n' <= n) (v : (i : Fin n) -> α 
i) : take m h (take n' h' v) = take m (Nat.le_trans h h') v
参数：h : m <= n'；h' : n' <= n；v : (i : Fin n) -> α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem take_take {m n' : ℕ} (h : m ≤ n') (h' : n' ≤ n) (v : (i : Fin n) → α i) :
    take m h (take n' h' v) = take m (Nat.le_trans h h') v := rfl

@[simp]
/-
**Fin.take_init** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_init {α : Fin (n + 1) -> Sort*} (m : Nat) (h : m <= n) (v : (i : Fin 
(n + 1)) -> α i) : take m h (init v) = take m (Nat.le_succ_of_le h) v
参数：n + 1；m : Nat；h : m <= n；v : (i : Fin (n + 1)) -> α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem take_init {α : Fin (n + 1) → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin (n + 1)) → α i) :
    take m h (init v) = take m (Nat.le_succ_of_le h) v := rfl
/-
**Fin.take_repeat** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_repeat {α : Type*} {n' : Nat} (m : Nat) (h : m <= n) (a : Fin n' -> α
) : take (m * n') (Nat.mul_le_mul_right n' h) (Fin.repeat n a) = Fin.repeat m a
参数：m : Nat；h : m <= n；a : Fin n' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem take_repeat {α : Type*} {n' : ℕ} (m : ℕ) (h : m ≤ n) (a : Fin n' → α) :
    take (m * n') (Nat.mul_le_mul_right n' h) (Fin.repeat n a) = Fin.repeat m a := by
  ext i
  simp only [take, repeat_apply, modNat, val_castLE]

set_option backward.isDefEq.respectTransparency false in
/-- Taking `m + 1` elements is equal to taking `m` elements and adding the `(m + 1)`th one. -/
/-
**Fin.take_succ_eq_snoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_succ_eq_snoc (m : Nat) (h : m < n) (v : (i : Fin n) -> α i) : take m.
succ h v = snoc (take m h.le v) (v ⟨m, h⟩)
参数：m : Nat；h : m < n；v : (i : Fin n) -> α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i

--- 原说明 ---
Taking `m + 1` elements is equal to taking `m` elements and adding the `(m + 1)`
th one.
-/
theorem take_succ_eq_snoc (m : ℕ) (h : m < n) (v : (i : Fin n) → α i) :
    take m.succ h v = snoc (take m h.le v) (v ⟨m, h⟩) := by
  ext i
  induction m with
  | zero =>
    have h' : i = 0 := by ext; simp
    subst h'
    simp [take, snoc, castLE]
  | succ m _ =>
    induction i using reverseInduction with
    | last => simp [take, snoc]; congr
    | cast i _ => simp

/-- `take` commutes with `update` for indices in the range of `take`. -/
@[simp]
/-
**Fin.take_update_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_update_of_lt (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin
 m) (x : α (castLE h i)) : take m h (update v (castLE h i) x) = update (take m h
 v) i x
参数：m : Nat；h : m <= n；v : (i : Fin n) -> α i；i : Fin m；x : α (castLE h i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a

--- 原说明 ---
`take` commutes with `update` for indices in the range of `take`.
-/
theorem take_update_of_lt (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin m)
    (x : α (castLE h i)) : take m h (update v (castLE h i) x) = update (take m h v) i x := by
  ext j
  by_cases h' : j = i
  · rw [h']
    simp only [take, update_self]
  · have : castLE h j ≠ castLE h i := by simp [h']
    simp only [take, update_of_ne h', update_of_ne this]

/-- `take` is the same after `update` for indices outside the range of `take`. -/
@[simp]
/-
**Fin.take_update_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_update_of_ge (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin
 n) (hi : i >= m) (x : α i) : take m h (update v i x) = take m h v
参数：m : Nat；h : m <= n；v : (i : Fin n) -> α i；i : Fin n；hi : i >= m；x : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ne_of_val_ne`：∀ {n : ℕ} {i j : Fin n}, ↑i ≠ ↑j → i ≠ j
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`take` is the same after `update` for indices outside the range of `take`.
-/
theorem take_update_of_ge (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin n) (hi : i ≥ m)
    (x : α i) : take m h (update v i x) = take m h v := by
  ext j
  have : castLE h j ≠ i := by
    refine ne_of_val_ne ?_
    simp only [val_castLE]
    exact Nat.ne_of_lt (lt_of_lt_of_le j.isLt hi)
  simp only [take, update_of_ne this]

/-- Taking the first `m ≤ n` elements of an `addCases u v`, where `u` is an `n`-tuple, is the same
as taking the first `m` elements of `u`. -/
/-
**Fin.take_addCases_left** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_addCases_left {n' : Nat} {motive : Fin (n + n') -> Sort*} (m : Nat) (
h : m <= n) (u : (i : Fin n) -> motive (castAdd n' i)) (v : (i : Fin n') -> moti
ve (natAdd n i)) : take m (Nat.le_add_right_of_le h) (addCases u v) = take m h u
参数：n + n'；m : Nat；h : m <= n；u : (i : Fin n) -> motive (castAdd n' i)；v : (i : F
in n') -> motive (natAdd n i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.le_add_right_of_le`：∀ {n m k : ℕ}, n ≤ m → n ≤ m + k
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Fin.castAdd_castLT`：∀ {n : ℕ} (m : ℕ) (i : Fin (n + m)) (hi : ↑i < n), F
in.castAdd m (i.castLT hi) = i
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n

--- 原说明 ---
Taking the first `m ≤ n` elements of an `addCases u v`, where `u` is an `n`-tupl
e, is the same
as taking the first `m` elements of `u`.
-/
theorem take_addCases_left {n' : ℕ} {motive : Fin (n + n') → Sort*} (m : ℕ) (h : m ≤ n)
    (u : (i : Fin n) → motive (castAdd n' i)) (v : (i : Fin n') → motive (natAdd n i)) :
      take m (Nat.le_add_right_of_le h) (addCases u v) = take m h u := by
  ext i
  have : i < n := Nat.lt_of_lt_of_le i.isLt h
  simp only [take, addCases, this, val_castLE, ↓reduceDIte]
  congr

/-- Version of `take_addCases_left` that specializes `addCases` to `append`. -/
/-
**Fin.take_append_left** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_append_left {n' : Nat} {α : Sort*} (m : Nat) (h : m <= n) (u : (i : F
in n) -> α) (v : (i : Fin n') -> α) : take m (Nat.le_add_right_of_le h) (append 
u v) = take m h u
参数：m : Nat；h : m <= n；u : (i : Fin n) -> α；v : (i : Fin n') -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.take_addCases_left`：take_addCases_left {n' : Nat} {motive : Fin (n +
 n') -> Sort*} (m : Nat) (h : m <= n) (u : (i : Fin n) -> motive (castAdd n' i))
 (v : (i : F…

--- 原说明 ---
Version of `take_addCases_left` that specializes `addCases` to `append`.
-/
theorem take_append_left {n' : ℕ} {α : Sort*} (m : ℕ) (h : m ≤ n) (u : (i : Fin n) → α)
    (v : (i : Fin n') → α) : take m (Nat.le_add_right_of_le h) (append u v) = take m h u :=
  take_addCases_left m h _ _

set_option backward.isDefEq.respectTransparency false in
/-- Taking the first `n + m` elements of an `addCases u v`, where `v` is a `n'`-tuple and `m ≤ n'`,
is the same as appending `u` with the first `m` elements of `v`. -/
/-
**Fin.take_addCases_right** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_addCases_right {n' : Nat} {motive : Fin (n + n') -> Sort*} (m : Nat) 
(h : m <= n') (u : (i : Fin n) -> motive (castAdd n' i)) (v : (i : Fin n') -> mo
tive (natAdd n i)) : take (n + m) (Nat.add_le_add_left h n) (addCases u v) = add
Cases u (take m h v)
参数：n + n'；m : Nat；h : m <= n'；u : (i : Fin n) -> motive (castAdd n' i)；v : (i : 
Fin n') -> motive (natAdd n i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.add_le_add_left`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), k + n ≤ k + m
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Fin.castAdd_castLT`：∀ {n : ℕ} (m : ℕ) (i : Fin (n + m)) (hi : ↑i < n), F
in.castAdd m (i.castLT hi) = i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eqRec_eq_cast`：∀ {α : Sort u_1} {a : α} {motive : (a' : α) → a = a' → So
rt u_2} (x : motive a ⋯) {a' : α} (e : a = a'),   e ▸ x = cast ⋯ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Taking the first `n + m` elements of an `addCases u v`, where `v` is a `n'`-tupl
e and `m ≤ n'`,
is the same as appending `u` with the first `m` elements of `v`.
-/
theorem take_addCases_right {n' : ℕ} {motive : Fin (n + n') → Sort*} (m : ℕ) (h : m ≤ n')
    (u : (i : Fin n) → motive (castAdd n' i)) (v : (i : Fin n') → motive (natAdd n i)) :
      take (n + m) (Nat.add_le_add_left h n) (addCases u v) = addCases u (take m h v) := by
  ext i
  simp only [take, addCases, val_castLE]
  by_cases h' : i < n
  · simp only [h', ↓reduceDIte]
    congr
  · simp only [h', ↓reduceDIte, subNat, castLE, Fin.cast, eqRec_eq_cast]

/-- Version of `take_addCases_right` that specializes `addCases` to `append`. -/
/-
**Fin.take_append_right** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：take_append_right {n' : Nat} {α : Sort*} (m : Nat) (h : m <= n') (u : (i :
 Fin n) -> α) (v : (i : Fin n') -> α) : take (n + m) (Nat.add_le_add_left h n) (
append u v) = append u (take m h v)
参数：m : Nat；h : m <= n'；u : (i : Fin n) -> α；v : (i : Fin n') -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.take_addCases_right`：take_addCases_right {n' : Nat} {motive : Fin (n
 + n') -> Sort*} (m : Nat) (h : m <= n') (u : (i : Fin n) -> motive (castAdd n' 
i)) (v : (i :…

--- 原说明 ---
Version of `take_addCases_right` that specializes `addCases` to `append`.
-/
theorem take_append_right {n' : ℕ} {α : Sort*} (m : ℕ) (h : m ≤ n') (u : (i : Fin n) → α)
    (v : (i : Fin n') → α) : take (n + m) (Nat.add_le_add_left h n) (append u v)
        = append u (take m h v) :=
  take_addCases_right m h _ _

/-- `Fin.take` intertwines with `List.take` via `List.ofFn`. -/
/-
**Fin.ofFn_take_eq_take_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：ofFn_take_eq_take_ofFn {α : Type*} {m : Nat} (h : m <= n) (v : Fin n -> α)
 : List.ofFn (take m h v) = (List.ofFn v).take m
参数：h : m <= n；v : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.length_take_le'`：∀ {α : Type u_1} (i : ℕ) (l : List α), (List.take 
i l).length ≤ l.length
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `List.getElem_take`：∀ {α : Type u_1} {xs : List α} {j i : ℕ} {h : i < (Li
st.take j xs).length}, (List.take j xs)[i] = xs[i]

--- 原说明 ---
`Fin.take` intertwines with `List.take` via `List.ofFn`.
-/
theorem ofFn_take_eq_take_ofFn {α : Type*} {m : ℕ} (h : m ≤ n) (v : Fin n → α) :
    List.ofFn (take m h v) = (List.ofFn v).take m :=
  List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

/-- Alternative version of `take_eq_take_list_ofFn` with `l : List α` instead of `v : Fin n → α`. -/
/-
**Fin.ofFn_take_get** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：ofFn_take_get {α : Type*} {m : Nat} (l : List α) (h : m <= l.length) : Lis
t.ofFn (take m h l.get) = l.take m
参数：l : List α；h : m <= l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `List.length_take_le'`：∀ {α : Type u_1} (i : ℕ) (l : List α), (List.take 
i l).length ≤ l.length
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `List.getElem_take`：∀ {α : Type u_1} {xs : List α} {j i : ℕ} {h : i < (Li
st.take j xs).length}, (List.take j xs)[i] = xs[i]

--- 原说明 ---
Alternative version of `take_eq_take_list_ofFn` with `l : List α` instead of `v 
: Fin n → α`.
-/
theorem ofFn_take_get {α : Type*} {m : ℕ} (l : List α) (h : m ≤ l.length) :
    List.ofFn (take m h l.get) = l.take m :=
  List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

/-- `Fin.take` intertwines with `List.take` via `List.get`. -/
/-
**Fin.get_take_eq_take_get_comp_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：get_take_eq_take_get_comp_cast {α : Type*} {m : Nat} (l : List α) (h : m <
= l.length) : (l.take m).get = take m h l.get ∘ Fin.cast (List.length_take_of_le
 h)
参数：l : List α；h : m <= l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.length_take_of_le`：∀ {i : ℕ} {α : Type u_1} {l : List α}, i ≤ l.len
gth → (List.take i l).length = i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `List.length_take_le'`：∀ {α : Type u_1} (i : ℕ) (l : List α), (List.take 
i l).length ≤ l.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_take`：∀ {α : Type u_1} {xs : List α} {j i : ℕ} {h : i < (Li
st.take j xs).length}, (List.take j xs)[i] = xs[i]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`Fin.take` intertwines with `List.take` via `List.get`.
-/
theorem get_take_eq_take_get_comp_cast {α : Type*} {m : ℕ} (l : List α) (h : m ≤ l.length) :
    (l.take m).get = take m h l.get ∘ Fin.cast (List.length_take_of_le h) := by
  ext i
  simp only [List.get_eq_getElem, List.getElem_take, comp_apply, take_apply, val_castLE, val_cast]

/-- Alternative version of `take_eq_take_list_get` with `v : Fin n → α` instead of `l : List α`. -/
/-
**Fin.get_take_ofFn_eq_take_comp_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：get_take_ofFn_eq_take_comp_cast {α : Type*} {m : Nat} (v : Fin n -> α) (h 
: m <= n) : ((List.ofFn v).take m).get = take m h v ∘ Fin.cast (by simp [h])
参数：v : Fin n -> α；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.length_take_le'`：∀ {α : Type u_1} (i : ℕ) (l : List α), (List.take 
i l).length ≤ l.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_take`：∀ {α : Type u_1} {xs : List α} {j i : ℕ} {h : i < (Li
st.take j xs).length}, (List.take j xs)[i] = xs[i]
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Alternative version of `take_eq_take_list_get` with `v : Fin n → α` instead of `
l : List α`.
-/
theorem get_take_ofFn_eq_take_comp_cast {α : Type*} {m : ℕ} (v : Fin n → α) (h : m ≤ n) :
    ((List.ofFn v).take m).get = take m h v ∘ Fin.cast (by simp [h]) := by
  ext i
  simp [castLE]

end Take

end Fin

