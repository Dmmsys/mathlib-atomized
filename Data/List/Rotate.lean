/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yakov Pechersky
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Quot

/-!
# List rotation

This file proves basic results about `List.rotate`, the list rotation.

## Main declarations

* `List.IsRotated l₁ l₂`: States that `l₁` is a rotated version of `l₂`.
* `List.cyclicPermutations l`: The list of all cyclic permutants of `l`, up to the length of `l`.

## Tags

rotated, rotation, permutation, cycle
-/

@[expose] public section


universe u

variable {α : Type u}

open Nat Function

namespace List

@[simp]
/-
**List.rotate_mod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_mod (l : List α) (n : Nat) : l.rotate (n % l.length) = l.rotate n
参数：l : List α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `List.splitAt_eq`：∀ {α : Type u_1} {i : ℕ} {l : List α}, List.splitAt i l
 = (List.take i l, List.drop i l)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rotate_mod (l : List α) (n : ℕ) : l.rotate (n % l.length) = l.rotate n := by simp [rotate]

@[simp]
/-
**List.rotate_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_nil (n : Nat) : ([] : List α).rotate n = []
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `List.splitAt_eq`：∀ {α : Type u_1} {i : ℕ} {l : List α}, List.splitAt i l
 = (List.take i l, List.drop i l)
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rotate_nil (n : ℕ) : ([] : List α).rotate n = [] := by simp [rotate]

@[simp]
/-
**List.rotate_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_zero (l : List α) : l.rotate 0 = l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.splitAt_eq`：∀ {α : Type u_1} {i : ℕ} {l : List α}, List.splitAt i l
 = (List.take i l, List.drop i l)
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rotate_zero (l : List α) : l.rotate 0 = l := by simp [rotate]
/-
**List.rotate'_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (n : ℕ), [].rotate' n = []
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate'.eq_1`：∀ {α : Type u_1} (x : ℕ), [].rotate' x = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rotate'_nil (n : ℕ) : ([] : List α).rotate' n = [] := by simp

@[simp]
/-
**List.rotate'_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α), l.rotate' 0 = l
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem rotate'_zero (l : List α) : l.rotate' 0 = l := by cases l <;> rfl
/-
**List.rotate'_cons_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α) (a : α) (n : ℕ), (a :: l).rotate' n.succ = (l 
++ [a]).rotate' n
参数：l : List α；a : α；n : ℕ；a :: l；l ++ [a]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rotate'_cons_succ (l : List α) (a : α) (n : ℕ) :
    (a :: l : List α).rotate' n.succ = (l ++ [a]).rotate' n := by simp [rotate']

@[simp]
/-
**List.length_rotate'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α) (n : ℕ), (l.rotate' n).length = l.length
参数：l : List α；n : ℕ；l.rotate' n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
-/
theorem length_rotate' : ∀ (l : List α) (n : ℕ), (l.rotate' n).length = l.length
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | a :: l, n + 1 => by rw [List.rotate', length_rotate' (l ++ [a]) n]; simp
/-
**List.rotate'_eq_drop_append_take** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {l : List α} {n : ℕ}, n ≤ l.length → l.rotate' n = List.dro
p n l ++ List.take n l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
-/
theorem rotate'_eq_drop_append_take :
    ∀ {l : List α} {n : ℕ}, n ≤ l.length → l.rotate' n = l.drop n ++ l.take n
  | [], n, h => by simp
  | l, 0, h => by simp
  | a :: l, n + 1, h => by
    have hnl : n ≤ l.length := le_of_succ_le_succ h
    have hnl' : n ≤ (l ++ [a]).length := by
      rw [length_append, length_cons, List.length]; exact le_of_succ_le h
    rw [rotate'_cons_succ, rotate'_eq_drop_append_take hnl', drop, take,
        drop_append_of_le_length hnl, take_append_of_le_length hnl]; simp

@[simp]
/-
**List.rotate'_rotate'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α) (n m : ℕ), (l.rotate' n).rotate' m = l.rotate'
 (n + m)
参数：l : List α；n m : ℕ；l.rotate' n；n + m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
-/
theorem rotate'_rotate' : ∀ (l : List α) (n m : ℕ), (l.rotate' n).rotate' m = l.rotate' (n + m)
  | a :: l, 0, m => by simp
  | [], n, m => by simp
  | a :: l, n + 1, m => by
    rw [rotate'_cons_succ, rotate'_rotate' _ n, Nat.add_right_comm, ← rotate'_cons_succ,
      Nat.succ_eq_add_one]

@[simp]
/-
**List.rotate'_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α), l.rotate' l.length = l
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate'_eq_drop_append_take`：∀ {α : Type u} {l : List α} {n : ℕ}, n
 ≤ l.length → l.rotate' n = List.drop n l ++ List.take n l
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.drop_length`：∀ {α : Type u_1} {l : List α}, List.drop l.length l = 
[]
· 使用定理 `List.take_length`：∀ {α : Type u_1} {l : List α}, List.take l.length l = 
l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rotate'_length (l : List α) : rotate' l l.length = l := by
  rw [rotate'_eq_drop_append_take le_rfl]; simp

@[simp]
/-
**List.rotate'_length_mul** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α) (n : ℕ), l.rotate' (l.length * n) = l
参数：l : List α；n : ℕ；l.length * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
-/
theorem rotate'_length_mul (l : List α) : ∀ n : ℕ, l.rotate' (l.length * n) = l
  | 0 => by simp
  | n + 1 =>
    calc
      l.rotate' (l.length * (n + 1)) =
          (l.rotate' (l.length * n)).rotate' (l.rotate' (l.length * n)).length := by
        simp [-rotate'_length, Nat.mul_succ, rotate'_rotate']
      _ = l := by rw [rotate'_length, rotate'_length_mul l n]

@[simp]
/-
**List.rotate'_mod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α) (n : ℕ), l.rotate' (n % l.length) = l.rotate' 
n
参数：l : List α；n : ℕ；n % l.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate'_length_mul`：∀ {α : Type u} (l : List α) (n : ℕ), l.rotate' 
(l.length * n) = l
· 使用定理 `List.rotate'_rotate'`：∀ {α : Type u} (l : List α) (n m : ℕ), (l.rotate' 
n).rotate' m = l.rotate' (n + m)
· 使用定理 `List.length_rotate'`：∀ {α : Type u} (l : List α) (n : ℕ), (l.rotate' n).
length = l.length
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
-/
theorem rotate'_mod (l : List α) (n : ℕ) : l.rotate' (n % l.length) = l.rotate' n :=
  calc l.rotate' (n % l.length)
    _ = (l.rotate' (n % l.length)).rotate'
        ((l.rotate' (n % l.length)).length * (n / l.length)) := by rw [rotate'_length_mul]
    _ = l.rotate' n := by rw [rotate'_rotate', length_rotate', Nat.mod_add_div]
/-
**List.rotate_eq_rotate'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_eq_rotate' (l : List α) (n : Nat) : l.rotate n = l.rotate' n
参数：l : List α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `List.rotate'.eq_1`：∀ {α : Type u_1} (x : ℕ), [].rotate' x = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.rotate'_mod`：∀ {α : Type u} (l : List α) (n : ℕ), l.rotate' (n % l.
length) = l.rotate' n
· 使用定理 `List.rotate'_eq_drop_append_take`：∀ {α : Type u} {l : List α} {n : ℕ}, n
 ≤ l.length → l.rotate' n = List.drop n l ++ List.take n l
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `List.splitAt_eq`：∀ {α : Type u_1} {i : ℕ} {l : List α}, List.splitAt i l
 = (List.take i l, List.drop i l)
-/
theorem rotate_eq_rotate' (l : List α) (n : ℕ) : l.rotate n = l.rotate' n :=
  if h : l.length = 0 then by simp_all [length_eq_zero_iff]
  else by
    rw [← rotate'_mod,
        rotate'_eq_drop_append_take (le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero h)))]
    simp [rotate]
/-
**List.rotate_cons_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α) (a : α) (n : ℕ), (a :: l).rotate (n + 1) = (l 
++ [a]).rotate n
参数：l : List α；a : α；n : ℕ；a :: l；n + 1；l ++ [a]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_rotate'`：rotate_eq_rotate' (l : List α) (n : Nat) : l.rot
ate n = l.rotate' n
· 使用定理 `List.rotate'_cons_succ`：∀ {α : Type u} (l : List α) (a : α) (n : ℕ), (a 
:: l).rotate' n.succ = (l ++ [a]).rotate' n
-/
@[simp] theorem rotate_cons_succ (l : List α) (a : α) (n : ℕ) :
    (a :: l : List α).rotate (n + 1) = (l ++ [a]).rotate n := by
  rw [rotate_eq_rotate', rotate_eq_rotate', rotate'_cons_succ]

@[simp]
/-
**List.mem_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {l : List α} {a : α} {n : ℕ}, a ∈ l.rotate n ↔ a ∈ l
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_rotate : ∀ {l : List α} {a : α} {n : ℕ}, a ∈ l.rotate n ↔ a ∈ l
  | [], _, n => by simp
  | a :: l, _, 0 => by simp
  | a :: l, _, n + 1 => by simp [rotate_cons_succ, mem_rotate, or_comm]

@[simp]
/-
**List.length_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_rotate (l : List α) (n : Nat) : (l.rotate n).length = l.length
参数：l : List α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_rotate'`：rotate_eq_rotate' (l : List α) (n : Nat) : l.rot
ate n = l.rotate' n
· 使用定理 `List.length_rotate'`：∀ {α : Type u} (l : List α) (n : ℕ), (l.rotate' n).
length = l.length
-/
theorem length_rotate (l : List α) (n : ℕ) : (l.rotate n).length = l.length := by
  rw [rotate_eq_rotate', length_rotate']

@[simp]
/-
**List.rotate_replicate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_replicate (a : α) (n : Nat) (k : Nat) : (replicate n a).rotate k = 
replicate n a
参数：a : α；n : Nat；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.eq_replicate_iff`：∀ {α : Type u_1} {a : α} {n : ℕ} {l : List α}, l 
= List.replicate n a ↔ l.length = n ∧ ∀ b ∈ l, b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `List.eq_of_mem_replicate`：∀ {α : Type u_1} {a b : α} {n : ℕ}, b ∈ List.r
eplicate n a → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_rotate`：∀ {α : Type u} {l : List α} {a : α} {n : ℕ}, a ∈ l.rota
te n ↔ a ∈ l
-/
theorem rotate_replicate (a : α) (n : ℕ) (k : ℕ) : (replicate n a).rotate k = replicate n a :=
  eq_replicate_iff.2 ⟨by rw [length_rotate, length_replicate], fun b hb =>
    eq_of_mem_replicate <| mem_rotate.1 hb⟩
/-
**List.rotate_eq_drop_append_take** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_eq_drop_append_take {l : List α} {n : Nat} : n <= l.length -> l.rot
ate n = l.drop n ++ l.take n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_rotate'`：rotate_eq_rotate' (l : List α) (n : Nat) : l.rot
ate n = l.rotate' n
· 使用定理 `List.rotate'_eq_drop_append_take`：∀ {α : Type u} {l : List α} {n : ℕ}, n
 ≤ l.length → l.rotate' n = List.drop n l ++ List.take n l
-/
theorem rotate_eq_drop_append_take {l : List α} {n : ℕ} :
    n ≤ l.length → l.rotate n = l.drop n ++ l.take n := by
  rw [rotate_eq_rotate']; exact rotate'_eq_drop_append_take
/-
**List.rotate_eq_drop_append_take_mod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_eq_drop_append_take_mod {l : List α} {n : Nat} : l.rotate n = l.dro
p (n % l.length) ++ l.take (n % l.length)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.eq_nil_of_length_eq_zero`：∀ {α : Type u_1} {l : List α}, l.length =
 0 → l = []
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.rotate_eq_drop_append_take`：rotate_eq_drop_append_take {l : List α}
 {n : Nat} : n <= l.length -> l.rotate n = l.drop n ++ l.take n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `List.rotate_mod`：rotate_mod (l : List α) (n : Nat) : l.rotate (n % l.len
gth) = l.rotate n
-/
theorem rotate_eq_drop_append_take_mod {l : List α} {n : ℕ} :
    l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length) := by
  rcases l.length.zero_le.eq_or_lt with hl | hl
  · simp [eq_nil_of_length_eq_zero hl.symm]
  rw [← rotate_eq_drop_append_take (n.mod_lt hl).le, rotate_mod]

@[simp]
/-
**List.rotate_append_length_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_append_length_eq (l l' : List α) : (l ++ l').rotate l.length = l' +
+ l
参数：l l' : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_rotate'`：rotate_eq_rotate' (l : List α) (n : Nat) : l.rot
ate n = l.rotate' n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.rotate'_zero`：∀ {α : Type u} (l : List α), l.rotate' 0 = l
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.rotate'.eq_3`：∀ {α : Type u_1} (a : α) (l : List α) (n : ℕ), (a :: 
l).rotate' n.succ = (l ++ [a]).rotate' n
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
-/
theorem rotate_append_length_eq (l l' : List α) : (l ++ l').rotate l.length = l' ++ l := by
  rw [rotate_eq_rotate']
  induction l generalizing l'
  · simp
  · simp_all [rotate']

@[simp]
/-
**List.rotate_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_rotate (l : List α) (n m : Nat) : (l.rotate n).rotate m = l.rotate 
(n + m)
参数：l : List α；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_rotate'`：rotate_eq_rotate' (l : List α) (n : Nat) : l.rot
ate n = l.rotate' n
· 使用定理 `List.rotate'_rotate'`：∀ {α : Type u} (l : List α) (n m : ℕ), (l.rotate' 
n).rotate' m = l.rotate' (n + m)
-/
theorem rotate_rotate (l : List α) (n m : ℕ) : (l.rotate n).rotate m = l.rotate (n + m) := by
  rw [rotate_eq_rotate', rotate_eq_rotate', rotate_eq_rotate', rotate'_rotate']

@[simp]
/-
**List.rotate_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_length (l : List α) : rotate l l.length = l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_rotate'`：rotate_eq_rotate' (l : List α) (n : Nat) : l.rot
ate n = l.rotate' n
· 使用定理 `List.rotate'_length`：∀ {α : Type u} (l : List α), l.rotate' l.length = l
-/
theorem rotate_length (l : List α) : rotate l l.length = l := by
  rw [rotate_eq_rotate', rotate'_length]

@[simp]
/-
**List.rotate_length_mul** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_length_mul (l : List α) (n : Nat) : l.rotate (l.length * n) = l
参数：l : List α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_rotate'`：rotate_eq_rotate' (l : List α) (n : Nat) : l.rot
ate n = l.rotate' n
· 使用定理 `List.rotate'_length_mul`：∀ {α : Type u} (l : List α) (n : ℕ), l.rotate' 
(l.length * n) = l
-/
theorem rotate_length_mul (l : List α) (n : ℕ) : l.rotate (l.length * n) = l := by
  rw [rotate_eq_rotate', rotate'_length_mul]
/-
**List.rotate_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_perm (l : List α) (n : Nat) : l.rotate n ~ l
参数：l : List α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate'`：rotate'_nil (n : Nat) : ([] : List α).rotate' n = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_rotate'`：rotate_eq_rotate' (l : List α) (n : Nat) : l.rot
ate n = l.rotate' n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.rotate'_zero`：∀ {α : Type u} (l : List α), l.rotate' 0 = l
· 使用定理 `List.rotate'_cons_succ`：∀ {α : Type u} (l : List α) (a : α) (n : ℕ), (a 
:: l).rotate' n.succ = (l ++ [a]).rotate' n
· 使用定理 `List.perm_append_singleton`：∀ {α : Type u_1} (a : α) (l : List α), (l ++
 [a]).Perm (a :: l)
-/
theorem rotate_perm (l : List α) (n : ℕ) : l.rotate n ~ l := by
  rw [rotate_eq_rotate']
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · rw [rotate'_cons_succ]
      exact (hn _).trans (perm_append_singleton _ _)

@[simp]
/-
**List.nodup_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_rotate {l : List α} {n : Nat} : Nodup (l.rotate n) ↔ Nodup l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `List.rotate_perm`：rotate_perm (l : List α) (n : Nat) : l.rotate n ~ l
-/
theorem nodup_rotate {l : List α} {n : ℕ} : Nodup (l.rotate n) ↔ Nodup l :=
  (rotate_perm l n).nodup_iff

@[simp]
/-
**List.rotate_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_eq_nil_iff {l : List α} {n : Nat} : l.rotate n = [] ↔ l = []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.rotate_cons_succ`：∀ {α : Type u} (l : List α) (a : α) (n : ℕ), (a :
: l).rotate (n + 1) = (l ++ [a]).rotate n
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem rotate_eq_nil_iff {l : List α} {n : ℕ} : l.rotate n = [] ↔ l = [] := by
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · simp [rotate_cons_succ, hn]
/-
**List.nil_eq_rotate_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nil_eq_rotate_iff {l : List α} {n : Nat} : [] = l.rotate n ↔ [] = l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `List.rotate_eq_nil_iff`：rotate_eq_nil_iff {l : List α} {n : Nat} : l.rot
ate n = [] ↔ l = []
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nil_eq_rotate_iff {l : List α} {n : ℕ} : [] = l.rotate n ↔ [] = l := by
  rw [eq_comm, rotate_eq_nil_iff, eq_comm]

@[simp]
/-
**List.rotate_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_singleton (x : α) (n : Nat) : [x].rotate n = [x]
参数：x : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rotate_replicate`：rotate_replicate (a : α) (n : Nat) (k : Nat) : (r
eplicate n a).rotate k = replicate n a
-/
theorem rotate_singleton (x : α) (n : ℕ) : [x].rotate n = [x] :=
  rotate_replicate x 1 n
/-
**List.zipWith_rotate_distrib** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipWith_rotate_distrib {β γ : Type*} (f : α -> β -> γ) (l : List α) (l' : 
List β) (n : Nat) (h : l.length = l'.length) : (zipWith f l l').rotate n = zipWi
th f (l.rotate n) (l'.rotate n)
参数：f : α -> β -> γ；l : List α；l' : List β；n : Nat；h : l.length = l'.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_drop_append_take_mod`：rotate_eq_drop_append_take_mod {l :
 List α} {n : Nat} : l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length)
· 使用定理 `List.zipWith_append`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β → γ} {l₁ l₁' : List α} {l₂ l₂' : List β},   l₁.length = l₂.length → List.
zipWith f…
· 使用定理 `List.length_drop`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.drop i l)
.length = l.length - i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.drop_zipWith`：∀ {α : Type u_1} {α_1 : Type u_2} {α_2 : Type u_3} {f
 : α → α_1 → α_2} {l : List α} {l' : List α_1} {i : ℕ},   List.drop i (List.zipW
ith f l…
· 使用定理 `List.take_zipWith`：∀ {α : Type u_1} {α_1 : Type u_2} {α_2 : Type u_3} {f
 : α → α_1 → α_2} {l : List α} {l' : List α_1} {i : ℕ},   List.take i (List.zipW
ith f l…
· 使用定理 `List.length_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β → γ} {l₁ : List α} {l₂ : List β},   (List.zipWith f l₁ l₂).length = min l
₁.length …
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
-/
theorem zipWith_rotate_distrib {β γ : Type*} (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)
    (h : l.length = l'.length) :
    (zipWith f l l').rotate n = zipWith f (l.rotate n) (l'.rotate n) := by
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod,
    rotate_eq_drop_append_take_mod, h, zipWith_append, ← drop_zipWith, ←
    take_zipWith, List.length_zipWith, h, min_self]
  rw [length_drop, length_drop, h]
/-
**List.zipWith_rotate_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipWith_rotate_one {β : Type*} (f : α -> α -> β) (x y : α) (l : List α) : 
zipWith f (x :: y :: l) ((x :: y :: l).rotate 1) = f x y :: zipWith f (y :: l) (
l ++ [x])
参数：f : α -> α -> β；x y : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_cons_succ`：∀ {α : Type u} (l : List α) (a : α) (n : ℕ), (a :
: l).rotate (n + 1) = (l ++ [a]).rotate n
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zipWith_rotate_one {β : Type*} (f : α → α → β) (x y : α) (l : List α) :
    zipWith f (x :: y :: l) ((x :: y :: l).rotate 1) = f x y :: zipWith f (y :: l) (l ++ [x]) := by
  simp
/-
**List.getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.
prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem?_rotate {l : List α} {n m : ℕ} (hml : m < l.length) :
    (l.rotate n)[m]? = l[(m + n) % l.length]? := by
  rw [rotate_eq_drop_append_take_mod]
  rcases lt_or_ge m (l.drop (n % l.length)).length with hm | hm
  · rw [getElem?_append_left hm, getElem?_drop, ← add_mod_mod]
    rw [length_drop, Nat.lt_sub_iff_add_lt] at hm
    rw [mod_eq_of_lt hm, Nat.add_comm]
  · have hlt : n % length l < length l := mod_lt _ (m.zero_le.trans_lt hml)
    rw [getElem?_append_right hm, getElem?_take_of_lt, length_drop]
    · congr 1
      rw [length_drop] at hm
      have hm' := Nat.sub_le_iff_le_add'.1 hm
      have : n % length l + m - length l < length l := by
        rw [Nat.sub_lt_iff_lt_add hm']
        exact Nat.add_lt_add hlt hml
      conv_rhs => rw [Nat.add_comm m, ← mod_add_mod, mod_eq_sub_mod hm', mod_eq_of_lt this]
      lia
    · rwa [Nat.sub_lt_iff_lt_add' hm, length_drop, Nat.sub_add_cancel hlt.le]

@[simp]
/-
**List.getElem_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_rotate (l : List α) (n : Nat) (k : Nat) (h : k < (l.rotate n).leng
th) : (l.rotate n)[k] = l[(k + n) % l.length]'(mod_lt _ (length_rotate l n ▸ k.z
ero_le.trans_lt h))
参数：l : List α；n : Nat；k : Nat；h : k < (l.rotate n).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
· 使用定理 `List.getElem?_eq_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), l[i]? = some l[i]
· 使用定理 `List.getElem?_rotate`：∀ {α : Type u} {l : List α} {n m : ℕ}, m < l.lengt
h → (l.rotate n)[m]? = l[(m + n) % l.length]?
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
-/
theorem getElem_rotate (l : List α) (n : ℕ) (k : Nat) (h : k < (l.rotate n).length) :
    (l.rotate n)[k] =
      l[(k + n) % l.length]'(mod_lt _ (length_rotate l n ▸ k.zero_le.trans_lt h)) := by
  rw [← Option.some_inj, ← getElem?_eq_getElem, ← getElem?_eq_getElem, getElem?_rotate]
  exact h.trans_eq (length_rotate _ _)
/-
**List.get_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_rotate (l : List α) (n : Nat) (k : Fin (l.rotate n).length) : (l.rotat
e n).get k = l.get ⟨(k + n) % l.length, mod_lt _ (length_rotate l n ▸ k.pos)⟩
参数：l : List α；n : Nat；k : Fin (l.rotate n).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_rotate`：getElem_rotate (l : List α) (n : Nat) (k : Nat) (h 
: k < (l.rotate n).length) : (l.rotate n)[k] = l[(k + n) % l.length]'(mod_lt _ (
length_ro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_rotate (l : List α) (n : ℕ) (k : Fin (l.rotate n).length) :
    (l.rotate n).get k = l.get ⟨(k + n) % l.length, mod_lt _ (length_rotate l n ▸ k.pos)⟩ := by
  simp [getElem_rotate]

@[simp]
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head?_rotate {l : List α} {n : ℕ} (h : n < l.length) : head? (l.rotate n) = l[n]? := by
  rw [head?_eq_getElem?, getElem?_rotate (n.zero_le.trans_lt h), Nat.zero_add, Nat.mod_eq_of_lt h]
/-
**List.get_rotate_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_rotate_one (l : List α) (k : Fin (l.rotate 1).length) : (l.rotate 1).g
et k = l.get ⟨(k + 1) % l.length, mod_lt _ (length_rotate l 1 ▸ k.pos)⟩
参数：l : List α；k : Fin (l.rotate 1).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.get_rotate`：get_rotate (l : List α) (n : Nat) (k : Fin (l.rotate n)
.length) : (l.rotate n).get k = l.get ⟨(k + n) % l.length, mod_lt _ (length_rota
te l …
-/
theorem get_rotate_one (l : List α) (k : Fin (l.rotate 1).length) :
    (l.rotate 1).get k = l.get ⟨(k + 1) % l.length, mod_lt _ (length_rotate l 1 ▸ k.pos)⟩ :=
  get_rotate l 1 k

-- Allow `l[a]'b` to have a line break between `[a]'` and `b`.
set_option linter.style.whitespace false in
/-- A version of `List.getElem_rotate` that represents `l[k]` in terms of
`(List.rotate l n)[⋯]`, not vice versa. Can be used instead of rewriting `List.getElem_rotate`
from right to left. -/
/-
**List.getElem_eq_getElem_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_eq_getElem_rotate (l : List α) (n : Nat) (k : Nat) (hk : k < l.len
gth) : l[k] = ((l.rotate n)[(l.length - n % l.length + k) % l.length]' ((Nat.mod
_lt _ (k.zero_le.trans_lt hk)).trans_eq (length_rotate _ _).symm))
参数：l : List α；n : Nat；k : Nat；hk : k < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_rotate`：getElem_rotate (l : List α) (n : Nat) (k : Nat) (h 
: k < (l.rotate n).length) : (l.rotate n)[k] = l[(k + n) % l.length]'(mod_lt _ (
length_ro…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fin.eq_of_val_eq`：∀ {n : ℕ} {i j : Fin n}, ↑i = ↑j → i = j
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `Nat.add_mod_mod`：∀ (m n k : ℕ), (m + n % k) % k = (m + n) % k
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.add_mod_left`：∀ (x z : ℕ), (x + z) % x = z % x
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a

--- 原说明 ---
A version of `List.getElem_rotate` that represents `l[k]` in terms of
`(List.rotate l n)[⋯]`, not vice versa. Can be used instead of rewriting `List.g
etElem_rotate`
from right to left.
-/
theorem getElem_eq_getElem_rotate (l : List α) (n : ℕ) (k : Nat) (hk : k < l.length) :
    l[k] = ((l.rotate n)[(l.length - n % l.length + k) % l.length]'
      ((Nat.mod_lt _ (k.zero_le.trans_lt hk)).trans_eq (length_rotate _ _).symm)) := by
  rw [getElem_rotate]
  refine congr_arg l.get (Fin.eq_of_val_eq ?_)
  simp only [mod_add_mod]
  rw [← add_mod_mod, Nat.add_right_comm, Nat.sub_add_cancel, add_mod_left, mod_eq_of_lt]
  exacts [hk, (mod_lt _ (k.zero_le.trans_lt hk)).le]

/-- A version of `List.get_rotate` that represents `List.get l` in terms of
`List.get (List.rotate l n)`, not vice versa. Can be used instead of rewriting `List.get_rotate`
from right to left. -/
/-
**List.get_eq_get_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_eq_get_rotate (l : List α) (n : Nat) (k : Fin l.length) : l.get k = (l
.rotate n).get ⟨(l.length - n % l.length + k) % l.length, (Nat.mod_lt _ (k.1.zer
o_le.trans_lt k.2)).trans_eq (length_rotate _ _).symm⟩
参数：l : List α；n : Nat；k : Fin l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.getElem_rotate`：getElem_rotate (l : List α) (n : Nat) (k : Nat) (h 
: k < (l.rotate n).length) : (l.rotate n)[k] = l[(k + n) % l.length]'(mod_lt _ (
length_ro…
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_eq_getElem_rotate`：getElem_eq_getElem_rotate (l : List α) (
n : Nat) (k : Nat) (hk : k < l.length) : l[k] = ((l.rotate n)[(l.length - n % l.
length + k) % l.leng…

--- 原说明 ---
A version of `List.get_rotate` that represents `List.get l` in terms of
`List.get (List.rotate l n)`, not vice versa. Can be used instead of rewriting `
List.get_rotate`
from right to left.
-/
theorem get_eq_get_rotate (l : List α) (n : ℕ) (k : Fin l.length) :
    l.get k = (l.rotate n).get ⟨(l.length - n % l.length + k) % l.length,
      (Nat.mod_lt _ (k.1.zero_le.trans_lt k.2)).trans_eq (length_rotate _ _).symm⟩ := by
  simpa using getElem_eq_getElem_rotate _ _ _ _
/-
**List.rotate_eq_self_iff_eq_replicate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} [hα : Nonempty α] {l : List α}, (∀ (n : ℕ), l.rotate n = l)
 ↔ ∃ a, l = List.replicate l.length a
参数：∀ (n : ℕ), l.rotate n = l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `List.getElem_replicate`：∀ {α : Type u_1} {a : α} {n i : ℕ} (h : i < (Lis
t.replicate n a).length), (List.replicate n a)[i] = a
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
· 使用定理 `List.getElem?_eq_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), l[i]? = some l[i]
· 使用定理 `List.head?_rotate`：∀ {α : Type u} {l : List α} {n : ℕ}, n < l.length → (
l.rotate n).head? = l[n]?
· 使用定理 `List.head?_cons`：∀ {α : Type u} {a : α} {l : List α}, (a :: l).head? = s
ome a
· 使用定理 `List.rotate_replicate`：rotate_replicate (a : α) (n : Nat) (k : Nat) : (r
eplicate n a).rotate k = replicate n a
-/
theorem rotate_eq_self_iff_eq_replicate [hα : Nonempty α] :
    ∀ {l : List α}, (∀ n, l.rotate n = l) ↔ ∃ a, l = replicate l.length a
  | [] => by simp
  | a :: l => ⟨fun h => ⟨a, ext_getElem length_replicate.symm fun n h₁ h₂ => by
      rw [getElem_replicate, ← Option.some_inj, ← getElem?_eq_getElem, ← head?_rotate h₁, h,
        head?_cons]⟩,
    fun ⟨b, hb⟩ n => by rw [hb, rotate_replicate]⟩
/-
**List.rotate_one_eq_self_iff_eq_replicate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_one_eq_self_iff_eq_replicate [Nonempty α] {l : List α} : l.rotate 1
 = l ↔ exists a : α, l = List.replicate l.length a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.rotate_eq_self_iff_eq_replicate`：∀ {α : Type u} [hα : Nonempty α] {
l : List α}, (∀ (n : ℕ), l.rotate n = l) ↔ ∃ a, l = List.replicate l.length a
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.rotate_rotate`：rotate_rotate (l : List α) (n m : Nat) : (l.rotate n
).rotate m = l.rotate (n + m)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem rotate_one_eq_self_iff_eq_replicate [Nonempty α] {l : List α} :
    l.rotate 1 = l ↔ ∃ a : α, l = List.replicate l.length a :=
  ⟨fun h =>
    rotate_eq_self_iff_eq_replicate.mp fun n =>
      Nat.rec l.rotate_zero (fun n hn => by rwa [Nat.succ_eq_add_one, ← l.rotate_rotate, hn]) n,
    fun h => rotate_eq_self_iff_eq_replicate.mpr h 1⟩
/-
**List.rotate_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_injective (n : Nat) : Function.Injective fun l : List α => l.rotate
 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `List.append_inj`：∀ {α : Type u_1} {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ 
++ t₂ → s₁.length = s₂.length → s₁ = s₂ ∧ t₁ = t₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_drop_append_take_mod`：rotate_eq_drop_append_take_mod {l :
 List α} {n : Nat} : l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_drop`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.drop i l)
.length = l.length - i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
-/
theorem rotate_injective (n : ℕ) : Function.Injective fun l : List α => l.rotate n := by
  rintro l l' (h : l.rotate n = l'.rotate n)
  have hle : l.length = l'.length := (l.length_rotate n).symm.trans (h.symm ▸ l'.length_rotate n)
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod] at h
  obtain ⟨hd, ht⟩ := append_inj h (by simp_all)
  rw [← take_append_drop _ l, ht, hd, take_append_drop]

@[simp]
/-
**List.rotate_eq_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_eq_rotate {l l' : List α} {n : Nat} : l.rotate n = l'.rotate n ↔ l 
= l'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `List.rotate_injective`：rotate_injective (n : Nat) : Function.Injective f
un l : List α => l.rotate n
-/
theorem rotate_eq_rotate {l l' : List α} {n : ℕ} : l.rotate n = l'.rotate n ↔ l = l' :=
  (rotate_injective n).eq_iff
/-
**List.rotate_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_eq_iff {l l' : List α} {n : Nat} : l.rotate n = l' ↔ l = l'.rotate 
(l'.length - n % l'.length)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.rotate_eq_rotate`：rotate_eq_rotate {l l' : List α} {n : Nat} : l.ro
tate n = l'.rotate n ↔ l = l'
· 使用定理 `List.rotate_rotate`：rotate_rotate (l : List α) (n m : Nat) : (l.rotate n
).rotate m = l.rotate (n + m)
· 使用定理 `List.rotate_mod`：rotate_mod (l : List α) (n : Nat) : l.rotate (n % l.len
gth) = l.rotate n
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `List.eq_nil_of_length_eq_zero`：∀ {α : Type u_1} {l : List α}, l.length =
 0 → l = []
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
-/
theorem rotate_eq_iff {l l' : List α} {n : ℕ} :
    l.rotate n = l' ↔ l = l'.rotate (l'.length - n % l'.length) := by
  rw [← @rotate_eq_rotate _ l _ n, rotate_rotate, ← rotate_mod l', add_mod]
  rcases l'.length.zero_le.eq_or_lt with hl | hl
  · rw [eq_nil_of_length_eq_zero hl.symm, rotate_nil]
  · rcases (Nat.zero_le (n % l'.length)).eq_or_lt with hn | hn
    · simp [← hn]
    · rw [mod_eq_of_lt (Nat.sub_lt hl hn), Nat.sub_add_cancel, mod_self, rotate_zero]
      exact (Nat.mod_lt _ hl).le

@[simp]
/-
**List.rotate_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_eq_singleton_iff {l : List α} {n : Nat} {x : α} : l.rotate n = [x] 
↔ l = [x]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_eq_iff`：rotate_eq_iff {l l' : List α} {n : Nat} : l.rotate n
 = l' ↔ l = l'.rotate (l'.length - n % l'.length)
· 使用定理 `List.rotate_singleton`：rotate_singleton (x : α) (n : Nat) : [x].rotate n
 = [x]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rotate_eq_singleton_iff {l : List α} {n : ℕ} {x : α} : l.rotate n = [x] ↔ l = [x] := by
  rw [rotate_eq_iff, rotate_singleton]

@[simp]
/-
**List.singleton_eq_rotate_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：singleton_eq_rotate_iff {l : List α} {n : Nat} {x : α} : [x] = l.rotate n 
↔ [x] = l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `List.rotate_eq_singleton_iff`：rotate_eq_singleton_iff {l : List α} {n : 
Nat} {x : α} : l.rotate n = [x] ↔ l = [x]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem singleton_eq_rotate_iff {l : List α} {n : ℕ} {x : α} : [x] = l.rotate n ↔ [x] = l := by
  rw [eq_comm, rotate_eq_singleton_iff, eq_comm]
/-
**List.reverse_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverse_rotate (l : List α) (n : Nat) : (l.rotate n).reverse = l.reverse.r
otate (l.length - n % l.length)
参数：l : List α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `List.rotate_eq_iff`：rotate_eq_iff {l l' : List α} {n : Nat} : l.rotate n
 = l' ↔ l = l'.rotate (l'.length - n % l'.length)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `List.rotate_cons_succ`：∀ {α : Type u} (l : List α) (a : α) (n : ℕ), (a :
: l).rotate (n + 1) = (l ++ [a]).rotate n
· 使用定理 `List.rotate_rotate`：rotate_rotate (l : List α) (n m : Nat) : (l.rotate n
).rotate m = l.rotate (n + m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
-/
theorem reverse_rotate (l : List α) (n : ℕ) :
    (l.rotate n).reverse = l.reverse.rotate (l.length - n % l.length) := by
  rw [← length_reverse, ← rotate_eq_iff]
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · rw [rotate_cons_succ, ← rotate_rotate, hn]
      simp
/-
**List.rotate_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rotate_reverse (l : List α) (n : Nat) : l.reverse.rotate n = (l.rotate (l.
length - n % l.length)).reverse
参数：l : List α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `List.reverse_rotate`：reverse_rotate (l : List α) (n : Nat) : (l.rotate n
).reverse = l.reverse.rotate (l.length - n % l.length)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.rotate_rotate`：rotate_rotate (l : List α) (n m : Nat) : (l.rotate n
).rotate m = l.rotate (n + m)
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
· 使用定理 `List.splitAt_eq`：∀ {α : Type u_1} {i : ℕ} {l : List α}, List.splitAt i l
 = (List.take i l, List.drop i l)
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `List.rotate_length`：rotate_length (l : List α) : rotate l l.length = l
-/
theorem rotate_reverse (l : List α) (n : ℕ) :
    l.reverse.rotate n = (l.rotate (l.length - n % l.length)).reverse := by
  rw [← reverse_reverse l]
  simp_rw [reverse_rotate, reverse_reverse, rotate_eq_iff, rotate_rotate, length_rotate,
    length_reverse]
  rw [← length_reverse]
  let k := n % l.reverse.length
  rcases hk' : k with - | k'
  · simp_all! [k, length_reverse, ← rotate_rotate]
  · rcases l with - | ⟨x, l⟩
    · simp
    · rw [Nat.mod_eq_of_lt, Nat.sub_add_cancel, rotate_length]
      · exact Nat.sub_le _ _
      · exact Nat.sub_lt (by simp) (by simp_all! [k])

@[simp]
/-
**List.map_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_rotate {β : Type*} (f : α -> β) (l : List α) (n : Nat) : map f (l.rota
te n) = (map f l).rotate n
参数：f : α -> β；l : List α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.rotate_cons_succ`：∀ {α : Type u} (l : List α) (a : α) (n : ℕ), (a :
: l).rotate (n + 1) = (l ++ [a]).rotate n
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem map_rotate {β : Type*} (f : α → β) (l : List α) (n : ℕ) :
    map f (l.rotate n) = (map f l).rotate n := by
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · simp [hn]
/-
**List.Nodup.rotate_congr** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α}, l.Nodup → l ≠ [] → ∀ (i j : ℕ), l.rotate i = 
l.rotate j → i % l.length = j % l.length
参数：i j : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.length_pos_of_ne_nil`：∀ {α : Type u_1} {l : List α}, l ≠ [] → 0 < l
.length
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.head?_rotate`：∀ {α : Type u} {l : List α} {n : ℕ}, n < l.length → (
l.rotate n).head? = l[n]?
· 使用定理 `List.getElem?_eq_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), l[i]? = some l[i]
· 使用定理 `List.Nodup.getElem_inj_iff`：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {i 
: ℕ} {hi : i < l.length} {j : ℕ} {hj : j < l.length}, l[i] = l[j] ↔ i = j
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.rotate_mod`：rotate_mod (l : List α) (n : Nat) : l.rotate (n % l.len
gth) = l.rotate n
-/
theorem Nodup.rotate_congr {l : List α} (hl : l.Nodup) (hn : l ≠ []) (i j : ℕ)
    (h : l.rotate i = l.rotate j) : i % l.length = j % l.length := by
  rw [← rotate_mod l i, ← rotate_mod l j] at h
  simpa only [head?_rotate, mod_lt, length_pos_of_ne_nil hn, getElem?_eq_getElem, Option.some_inj,
    hl.getElem_inj_iff, Fin.ext_iff] using congr_arg head? h
/-
**List.Nodup.rotate_congr_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {i j : ℕ}, l.rotate i = l.rotate 
j ↔ i % l.length = j % l.length ∨ l = []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.Nodup.rotate_congr`：∀ {α : Type u} {l : List α}, l.Nodup → l ≠ [] →
 ∀ (i j : ℕ), l.rotate i = l.rotate j → i % l.length = j % l.length
· 使用定理 `List.rotate_mod`：rotate_mod (l : List α) (n : Nat) : l.rotate (n % l.len
gth) = l.rotate n
-/
theorem Nodup.rotate_congr_iff {l : List α} (hl : l.Nodup) {i j : ℕ} :
    l.rotate i = l.rotate j ↔ i % l.length = j % l.length ∨ l = [] := by
  rcases eq_or_ne l [] with rfl | hn
  · simp
  · simp only [hn, or_false]
    refine ⟨hl.rotate_congr hn _ _, fun h ↦ ?_⟩
    rw [← rotate_mod, h, rotate_mod]
/-
**List.Nodup.rotate_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {n : ℕ}, l.rotate n = l ↔ n % l.l
ength = 0 ∨ l = []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_mod`：∀ (b : ℕ), 0 % b = 0
· 使用定理 `List.Nodup.rotate_congr_iff`：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {i
 j : ℕ}, l.rotate i = l.rotate j ↔ i % l.length = j % l.length ∨ l = []
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Nodup.rotate_eq_self_iff {l : List α} (hl : l.Nodup) {n : ℕ} :
    l.rotate n = l ↔ n % l.length = 0 ∨ l = [] := by
  rw [← zero_mod, ← hl.rotate_congr_iff, rotate_zero]

section IsRotated

variable (l l' : List α)

/-- `IsRotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutations
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`. -/
/-
**List.IsRotated** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：IsRotated : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsRotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutatio
ns
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`.
-/
def IsRotated : Prop :=
  ∃ n, l.rotate n = l'

@[inherit_doc List.IsRotated]
-- This matches the precedence of the infix `~` for `List.Perm`, and of other relation infixes
infixr:50 " ~r " => IsRotated

variable {l l'} {a : α}

@[refl]
/-
**List.IsRotated.refl** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u} (l : List α), l ~r l
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsRotated.refl (l : List α) : l ~r l :=
  ⟨0, by simp⟩

@[symm]
/-
**List.IsRotated.symm** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u} {l l' : List α}, l ~r l' → l' ~r l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_rotate`：rotate_rotate (l : List α) (n m : Nat) : (l.rotate n
).rotate m = l.rotate (n + m)
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `Nat.le_mul_of_pos_left`：∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.rotate_length_mul`：rotate_length_mul (l : List α) (n : Nat) : l.rot
ate (l.length * n) = l
-/
theorem IsRotated.symm (h : l ~r l') : l' ~r l := by
  obtain ⟨n, rfl⟩ := h
  rcases l with - | ⟨hd, tl⟩
  · exists 0
  · use (hd :: tl).length * n - n
    rw [rotate_rotate, Nat.add_sub_cancel', rotate_length_mul]
    exact Nat.le_mul_of_pos_left _ (by simp)
/-
**List.isRotated_comm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_comm : l ~r l' ↔ l' ~r l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsRotated.symm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l' ~r l
-/
theorem isRotated_comm : l ~r l' ↔ l' ~r l :=
  ⟨IsRotated.symm, IsRotated.symm⟩

@[simp]
/-
**List.IsRotated.forall** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u} (l : List α) (n : ℕ), l.rotate n ~r l
参数：l : List α；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsRotated.symm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l' ~r l
-/
protected theorem IsRotated.forall (l : List α) (n : ℕ) : l.rotate n ~r l :=
  IsRotated.symm ⟨n, rfl⟩

@[trans]
/-
**List.IsRotated.trans** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u} {l l' l'' : List α}, l ~r l' → l' ~r l'' → l ~r l''
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_rotate`：rotate_rotate (l : List α) (n m : Nat) : (l.rotate n
).rotate m = l.rotate (n + m)
-/
theorem IsRotated.trans : ∀ {l l' l'' : List α}, l ~r l' → l' ~r l'' → l ~r l''
  | _, _, _, ⟨n, rfl⟩, ⟨m, rfl⟩ => ⟨n + m, by rw [rotate_rotate]⟩
/-
**List.IsRotated.eqv** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u}, Equivalence List.IsRotated
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsRotated.refl`：∀ {α : Type u} (l : List α), l ~r l
· 使用定理 `List.IsRotated.symm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l' ~r l
· 使用定理 `List.IsRotated.trans`：∀ {α : Type u} {l l' l'' : List α}, l ~r l' → l' ~
r l'' → l ~r l''
-/
theorem IsRotated.eqv : Equivalence (@IsRotated α) :=
  Equivalence.mk IsRotated.refl IsRotated.symm IsRotated.trans

/-- The relation `List.IsRotated l l'` forms a `Setoid` of cycles. -/
@[instance_reducible]
/-
**List.IsRotated.setoid** 是 Mathlib 中的一个定义，位于命名空间 `List.IsRotated`。
形式化陈述：(α : Type u_1) → Setoid (List α)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsRotated.eqv`：∀ {α : Type u}, Equivalence List.IsRotated

--- 原说明 ---
The relation `List.IsRotated l l'` forms a `Setoid` of cycles.
-/
def IsRotated.setoid (α : Type*) : Setoid (List α) where
  r := IsRotated
  iseqv := IsRotated.eqv
/-
**List.IsRotated.perm** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u} {l l' : List α}, l ~r l' → l.Perm l'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.rotate_perm`：rotate_perm (l : List α) (n : Nat) : l.rotate n ~ l
-/
theorem IsRotated.perm (h : l ~r l') : l ~ l' :=
  Exists.elim h fun _ hl => hl ▸ (rotate_perm _ _).symm
/-
**List.IsRotated.nodup_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u} {l l' : List α}, l ~r l' → (l.Nodup ↔ l'.Nodup)
参数：l.Nodup ↔ l'.Nodup。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `List.IsRotated.perm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l.Perm l'
-/
theorem IsRotated.nodup_iff (h : l ~r l') : Nodup l ↔ Nodup l' :=
  h.perm.nodup_iff
/-
**List.IsRotated.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u} {l l' : List α}, l ~r l' → ∀ {a : α}, a ∈ l ↔ a ∈ l'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.IsRotated.perm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l.Perm l'
-/
theorem IsRotated.mem_iff (h : l ~r l') {a : α} : a ∈ l ↔ a ∈ l' :=
  h.perm.mem_iff

@[simp]
/-
**List.isRotated_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_nil_iff : l ~r [] ↔ l = []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsRotated.refl`：∀ {α : Type u} (l : List α), l ~r l
-/
theorem isRotated_nil_iff : l ~r [] ↔ l = [] :=
  ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩

@[simp]
/-
**List.isRotated_nil_iff'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_nil_iff' : [] ~r l ↔ [] = l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.isRotated_comm`：isRotated_comm : l ~r l' ↔ l' ~r l
· 使用定理 `List.isRotated_nil_iff`：isRotated_nil_iff : l ~r [] ↔ l = []
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRotated_nil_iff' : [] ~r l ↔ [] = l := by
  rw [isRotated_comm, isRotated_nil_iff, eq_comm]

@[simp]
/-
**List.isRotated_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_singleton_iff {x : α} : l ~r [x] ↔ l = [x]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsRotated.refl`：∀ {α : Type u} (l : List α), l ~r l
-/
theorem isRotated_singleton_iff {x : α} : l ~r [x] ↔ l = [x] :=
  ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩

@[simp]
/-
**List.isRotated_singleton_iff'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_singleton_iff' {x : α} : [x] ~r l ↔ [x] = l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.isRotated_comm`：isRotated_comm : l ~r l' ↔ l' ~r l
· 使用定理 `List.isRotated_singleton_iff`：isRotated_singleton_iff {x : α} : l ~r [x]
 ↔ l = [x]
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRotated_singleton_iff' {x : α} : [x] ~r l ↔ [x] = l := by
  rw [isRotated_comm, isRotated_singleton_iff, eq_comm]
/-
**List.isRotated_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_concat (hd : α) (tl : List α) : (tl ++ [hd]) ~r (hd :: tl)
参数：hd : α；tl : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsRotated.symm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l' ~r l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_cons_succ`：∀ {α : Type u} (l : List α) (a : α) (n : ℕ), (a :
: l).rotate (n + 1) = (l ++ [a]).rotate n
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isRotated_concat (hd : α) (tl : List α) : (tl ++ [hd]) ~r (hd :: tl) :=
  IsRotated.symm ⟨1, by simp⟩
/-
**List.isRotated_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_append : (l ++ l') ~r (l' ++ l)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_append_length_eq`：rotate_append_length_eq (l l' : List α) : 
(l ++ l').rotate l.length = l' ++ l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isRotated_append : (l ++ l') ~r (l' ++ l) :=
  ⟨l.length, by simp⟩
/-
**List.IsRotated.reverse** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u} {l l' : List α}, l ~r l' → l.reverse ~r l'.reverse
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_rotate`：reverse_rotate (l : List α) (n : Nat) : (l.rotate n
).reverse = l.reverse.rotate (l.length - n % l.length)
-/
theorem IsRotated.reverse (h : l ~r l') : l.reverse ~r l'.reverse := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨_, (reverse_rotate _ _).symm⟩
/-
**List.isRotated_reverse_comm_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_reverse_comm_iff : l.reverse ~r l' ↔ l ~r l'.reverse
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `List.IsRotated.reverse`：∀ {α : Type u} {l l' : List α}, l ~r l' → l.reve
rse ~r l'.reverse
-/
theorem isRotated_reverse_comm_iff : l.reverse ~r l' ↔ l ~r l'.reverse := by
  constructor <;>
    · intro h
      simpa using h.reverse

@[simp]
/-
**List.isRotated_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_reverse_iff : l.reverse ~r l'.reverse ↔ l ~r l'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isRotated_reverse_iff : l.reverse ~r l'.reverse ↔ l ~r l' := by
  simp [isRotated_reverse_comm_iff]
/-
**List.isRotated_iff_mod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_iff_mod : l ~r l' ↔ exists n <= l.length, l.rotate n = l'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `List.rotate_mod`：rotate_mod (l : List α) (n : Nat) : l.rotate (n % l.len
gth) = l.rotate n
-/
theorem isRotated_iff_mod : l ~r l' ↔ ∃ n ≤ l.length, l.rotate n = l' := by
  refine ⟨fun h => ?_, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
  obtain ⟨n, rfl⟩ := h
  rcases l with - | ⟨hd, tl⟩
  · simp
  · refine ⟨n % (hd :: tl).length, ?_, rotate_mod _ _⟩
    refine (Nat.mod_lt _ ?_).le
    simp
/-
**List.isRotated_iff_mem_map_range** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_iff_mem_map_range : l ~r l' ↔ l' in (List.range (l.length + 1)).
map l.rotate
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
-/
theorem isRotated_iff_mem_map_range : l ~r l' ↔ l' ∈ (List.range (l.length + 1)).map l.rotate := by
  simp_rw [mem_map, mem_range, isRotated_iff_mod]
  exact
    ⟨fun ⟨n, hn, h⟩ => ⟨n, Nat.lt_succ_of_le hn, h⟩,
      fun ⟨n, hn, h⟩ => ⟨n, Nat.le_of_lt_succ hn, h⟩⟩
/-
**List.IsRotated.map** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u} {β : Type u_1} {l₁ l₂ : List α}, l₁ ~r l₂ → ∀ (f : α → β), 
List.map f l₁ ~r List.map f l₂
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_rotate`：map_rotate {β : Type*} (f : α -> β) (l : List α) (n : N
at) : map f (l.rotate n) = (map f l).rotate n
-/
theorem IsRotated.map {β : Type*} {l₁ l₂ : List α} (h : l₁ ~r l₂) (f : α → β) :
    map f l₁ ~r map f l₂ := by
  obtain ⟨n, rfl⟩ := h
  rw [map_rotate]
  use n
/-
**List.IsRotated.cons_append_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated
`。
形式化陈述：∀ {α : Type u} {l : List α} {a : α}, a :: l ~r l ++ [a]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isRotated_append`：isRotated_append : (l ++ l') ~r (l' ++ l)
-/
lemma IsRotated.cons_append_singleton : a :: l ~r l ++ [a] := by
  simpa using isRotated_append (l := [a])
/-
**List.IsRotated.cons_getLast_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated
`。
形式化陈述：∀ {α : Type u} (L : List α) (hL : L ≠ []), L.getLast hL :: L.dropLast ~r L
参数：L : List α；hL : L ≠ []。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.getLast_append`：∀ {α : Type u_1} {l' l : List α} (h : l ++ l' ≠ [])
,   (l ++ l').getLast h = if h' : l'.isEmpty = true then l.getLast ⋯ else l'.get
Last ⋯
· 使用定理 `List.dropLast_concat`：∀ {α : Type u_1} {l₁ : List α} {b : α}, (l₁ ++ [b]
).dropLast = l₁
· 使用定理 `List.IsRotated.symm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l' ~r l
· 使用定理 `List.isRotated_concat`：isRotated_concat (hd : α) (tl : List α) : (tl ++ 
[hd]) ~r (hd :: tl)
-/
theorem IsRotated.cons_getLast_dropLast
    (L : List α) (hL : L ≠ []) : L.getLast hL :: L.dropLast ~r L := by
  induction L using List.reverseRecOn with
  | nil => simp at hL
  | append_singleton a L _ =>
    simp only [getLast_append, dropLast_concat]
    apply IsRotated.symm
    apply isRotated_concat
/-
**List.IsRotated.dropLast_tail** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u_1} {L : List α} (hL : L ≠ []), L.head hL = L.getLast hL → L.
dropLast ~r L.tail
参数：hL : L ≠ []。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dropLast_nil`：∀ {α : Type u}, [].dropLast = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.dropLast_singleton`：∀ {α : Type u_1} {x : α}, [x].dropLast = []
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
· 使用定理 `List.dropLast_cons_cons`：∀ {α : Type u_1} {x y : α} {zs : List α}, (x ::
 y :: zs).dropLast = x :: (y :: zs).dropLast
-/
theorem IsRotated.dropLast_tail {α}
    {L : List α} (hL : L ≠ []) (hL' : L.head hL = L.getLast hL) : L.dropLast ~r L.tail :=
  match L with
  | [] => by simp
  | [_] => by simp
  | a :: b :: L => by
    simp only [head_cons, ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons] at hL'
    simp [hL', IsRotated.cons_getLast_dropLast]

/-- List of all cyclic permutations of `l`.
The `cyclicPermutations` of a nonempty list `l` will always contain `List.length l` elements.
This implies that under certain conditions, there are duplicates in `List.cyclicPermutations l`.
The `n`th entry is equal to `l.rotate n`, proven in `List.get_cyclicPermutations`.
The proof that every cyclic permutant of `l` is in the list is `List.mem_cyclicPermutations_iff`.

```
     cyclicPermutations [1, 2, 3, 2, 4] =
       [[1, 2, 3, 2, 4], [2, 3, 2, 4, 1], [3, 2, 4, 1, 2],
        [2, 4, 1, 2, 3], [4, 1, 2, 3, 2]]
``` -/
/-
**List.cyclicPermutations** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u} → List α → List (List α)
参数：List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
List of all cyclic permutations of `l`.
The `cyclicPermutations` of a nonempty list `l` will always contain `List.length
 l` elements.
This implies that under certain conditions, there are duplicates in `List.cyclic
Permutations l`.
The `n`th entry is equal to `l.rotate n`, proven in `List.get_cyclicPermutations
`.
The proof that every cyclic permutant of `l` is in the list is `List.mem_cyclicP
ermutations_iff`.

```
     cyclicPermutations [1, 2, 3, 2, 4] =
       [[1, 2, 3, 2, 4], [2, 3, 2, 4, 1], [3, 2, 4, 1, 2],
        [2, 4, 1, 2, 3], [4, 1, 2, 3, 2]]
```
-/
def cyclicPermutations : List α → List (List α)
  | [] => [[]]
  | l@(_ :: _) => dropLast (zipWith (· ++ ·) (tails l) (inits l))

@[simp]
/-
**List.cyclicPermutations_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cyclicPermutations_nil : cyclicPermutations ([] : List α) = [[]]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cyclicPermutations_nil : cyclicPermutations ([] : List α) = [[]] :=
  rfl
/-
**List.cyclicPermutations_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cyclicPermutations_cons (x : α) (l : List α) : cyclicPermutations (x :: l)
 = dropLast (zipWith (· ++ ·) (tails (x :: l)) (inits (x :: l)))
参数：x : α；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cyclicPermutations_cons (x : α) (l : List α) :
    cyclicPermutations (x :: l) = dropLast (zipWith (· ++ ·) (tails (x :: l)) (inits (x :: l))) :=
  rfl
/-
**List.cyclicPermutations_of_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cyclicPermutations_of_ne_nil (l : List α) (h : l != []) : cyclicPermutatio
ns l = dropLast (zipWith (· ++ ·) (tails l) (inits l))
参数：l : List α；h : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.exists_cons_of_ne_nil`：∀ {α : Type u_1} {l : List α}, l ≠ [] → ∃ b 
l', l = b :: l'
· 使用定理 `List.cyclicPermutations_cons`：cyclicPermutations_cons (x : α) (l : List 
α) : cyclicPermutations (x :: l) = dropLast (zipWith (· ++ ·) (tails (x :: l)) (
inits (x :: l)))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cyclicPermutations_of_ne_nil (l : List α) (h : l ≠ []) :
    cyclicPermutations l = dropLast (zipWith (· ++ ·) (tails l) (inits l)) := by
  obtain ⟨hd, tl, rfl⟩ := exists_cons_of_ne_nil h
  exact cyclicPermutations_cons _ _
/-
**List.length_cyclicPermutations_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_cyclicPermutations_cons (x : α) (l : List α) : length (cyclicPermut
ations (x :: l)) = length l + 1
参数：x : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.length_dropLast`：∀ {α : Type u_1} {xs : List α}, xs.dropLast.length
 = xs.length - 1
· 使用定理 `List.length_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β → γ} {l₁ : List α} {l₂ : List β},   (List.zipWith f l₁ l₂).length = min l
₁.length …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_tails`：length_tails (l : List α) : length (tails l) = length
 l + 1
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_inits`：length_inits (l : List α) : length (inits l) = length
 l + 1
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_cyclicPermutations_cons (x : α) (l : List α) :
    length (cyclicPermutations (x :: l)) = length l + 1 := by simp [cyclicPermutations_cons]

@[simp]
/-
**List.length_cyclicPermutations_of_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_cyclicPermutations_of_ne_nil (l : List α) (h : l != []) : length (c
yclicPermutations l) = length l
参数：l : List α；h : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.cyclicPermutations_of_ne_nil`：cyclicPermutations_of_ne_nil (l : Lis
t α) (h : l != []) : cyclicPermutations l = dropLast (zipWith (· ++ ·) (tails l)
 (inits l))
· 使用定理 `List.length_dropLast`：∀ {α : Type u_1} {xs : List α}, xs.dropLast.length
 = xs.length - 1
· 使用定理 `List.length_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β → γ} {l₁ : List α} {l₂ : List β},   (List.zipWith f l₁ l₂).length = min l
₁.length …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_tails`：length_tails (l : List α) : length (tails l) = length
 l + 1
· 使用定理 `List.length_inits`：length_inits (l : List α) : length (inits l) = length
 l + 1
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_cyclicPermutations_of_ne_nil (l : List α) (h : l ≠ []) :
    length (cyclicPermutations l) = length l := by simp [cyclicPermutations_of_ne_nil _ h]

@[simp]
/-
**List.cyclicPermutations_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α), l.cyclicPermutations ≠ []
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_cyclicPermutations_of_ne_nil`：length_cyclicPermutations_of_n
e_nil (l : List α) (h : l != []) : length (cyclicPermutations l) = length l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cyclicPermutations_ne_nil : ∀ l : List α, cyclicPermutations l ≠ []
  | a::l, h => by simpa using congr_arg length h

@[simp]
/-
**List.getElem_cyclicPermutations** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_cyclicPermutations (l : List α) (n : Nat) (h : n < length (cyclicP
ermutations l)) : (cyclicPermutations l)[n] = l.rotate n
参数：l : List α；n : Nat；h : n < length (cyclicPermutations l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_singleton`：∀ {α : Type u_1} {a : α} {i : ℕ} (h : i < 1), [a
][i] = a
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `List.length_dropLast`：∀ {α : Type u_1} {xs : List α}, xs.dropLast.length
 = xs.length - 1
· 使用定理 `List.getElem_dropLast`：∀ {α : Type u_1} {xs : List α} {i : ℕ} (h : i < x
s.dropLast.length), xs.dropLast[i] = xs[i]
· 使用定理 `List.lt_length_left_of_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β},   i < (List.zipWith f
 l l').length → i < …
· 使用定理 `List.lt_length_right_of_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β},   i < (List.zipWith 
f l l').length → i < …
· 使用定理 `List.getElem_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f 
: α → β → γ} {l : List α} {l' : List β} {i : ℕ}   {h : i < (List.zipWith f l l')
.length}, …
· 使用定理 `List.getElem_tails`：getElem_tails (l : List α) (n : Nat) (h : n < (tails
 l).length) : (tails l)[n] = l.drop n
· 使用定理 `List.getElem_inits`：getElem_inits (l : List α) (n : Nat) (h : n < length
 (inits l)) : (inits l)[n] = l.take n
· 使用定理 `List.rotate_eq_drop_append_take`：rotate_eq_drop_append_take {l : List α}
 {n : Nat} : n <= l.length -> l.rotate n = l.drop n ++ l.take n
· 使用定理 `List.length_cyclicPermutations_of_ne_nil`：length_cyclicPermutations_of_n
e_nil (l : List α) (h : l != []) : length (cyclicPermutations l) = length l
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem getElem_cyclicPermutations (l : List α) (n : Nat) (h : n < length (cyclicPermutations l)) :
    (cyclicPermutations l)[n] = l.rotate n := by
  cases l with
  | nil => simp
  | cons a l =>
    simp only [cyclicPermutations_cons, getElem_dropLast, getElem_zipWith, getElem_tails,
      getElem_inits]
    rw [rotate_eq_drop_append_take (by simpa using h.le)]
/-
**List.get_cyclicPermutations** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_cyclicPermutations (l : List α) (n : Fin (length (cyclicPermutations l
))) : (cyclicPermutations l).get n = l.rotate n
参数：l : List α；n : Fin (length (cyclicPermutations l))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_cyclicPermutations`：getElem_cyclicPermutations (l : List α)
 (n : Nat) (h : n < length (cyclicPermutations l)) : (cyclicPermutations l)[n] =
 l.rotate n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_cyclicPermutations (l : List α) (n : Fin (length (cyclicPermutations l))) :
    (cyclicPermutations l).get n = l.rotate n := by
  simp

@[simp]
/-
**List.head_cyclicPermutations** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head_cyclicPermutations (l : List α) : (cyclicPermutations l).head (cyclic
Permutations_ne_nil l) = l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_pos_of_ne_nil`：∀ {α : Type u_1} {l : List α}, l ≠ [] → 0 < l
.length
· 使用定理 `List.cyclicPermutations_ne_nil`：∀ {α : Type u} (l : List α), l.cyclicPer
mutations ≠ []
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_pos_iff`：∀ {α : Type u_1} {l : List α}, 0 < l.length ↔ l ≠ [
]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.get_mk_zero`：∀ {α : Type u_1} {l : List α} (h : 0 < l.length), l.ge
t ⟨0, h⟩ = l.head ⋯
· 使用定理 `List.get_cyclicPermutations`：get_cyclicPermutations (l : List α) (n : Fi
n (length (cyclicPermutations l))) : (cyclicPermutations l).get n = l.rotate n
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
-/
theorem head_cyclicPermutations (l : List α) :
    (cyclicPermutations l).head (cyclicPermutations_ne_nil l) = l := by
  have h : 0 < length (cyclicPermutations l) := length_pos_of_ne_nil (cyclicPermutations_ne_nil _)
  rw [← get_mk_zero h, get_cyclicPermutations, Fin.val_mk, rotate_zero]

@[simp]
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head?_cyclicPermutations (l : List α) : (cyclicPermutations l).head? = l := by
  rw [head?_eq_some_head (cyclicPermutations_ne_nil l), head_cyclicPermutations]
/-
**List.cyclicPermutations_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cyclicPermutations_injective : Function.Injective (@cyclicPermutations α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.head?_cyclicPermutations`：∀ {α : Type u} (l : List α), l.cyclicPerm
utations.head? = some l
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cyclicPermutations_injective : Function.Injective (@cyclicPermutations α) := fun l l' h ↦ by
  simpa using congr_arg head? h

@[simp]
/-
**List.cyclicPermutations_inj** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cyclicPermutations_inj {l l' : List α} : cyclicPermutations l = cyclicPerm
utations l' ↔ l = l'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `List.cyclicPermutations_injective`：cyclicPermutations_injective : Functi
on.Injective (@cyclicPermutations α)
-/
theorem cyclicPermutations_inj {l l' : List α} :
    cyclicPermutations l = cyclicPermutations l' ↔ l = l' :=
  cyclicPermutations_injective.eq_iff
/-
**List.length_mem_cyclicPermutations** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_mem_cyclicPermutations (l : List α) (h : l' in cyclicPermutations l
) : length l' = length l
参数：l : List α；h : l' in cyclicPermutations l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.get_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ n, l.g
et n = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_cyclicPermutations`：getElem_cyclicPermutations (l : List α)
 (n : Nat) (h : n < length (cyclicPermutations l)) : (cyclicPermutations l)[n] =
 l.rotate n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem length_mem_cyclicPermutations (l : List α) (h : l' ∈ cyclicPermutations l) :
    length l' = length l := by
  obtain ⟨k, hk, rfl⟩ := get_of_mem h
  simp
/-
**List.mem_cyclicPermutations_self** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_cyclicPermutations_self (l : List α) : l in cyclicPermutations l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.cyclicPermutations_ne_nil`：∀ {α : Type u} (l : List α), l.cyclicPer
mutations ≠ []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.head_cyclicPermutations`：head_cyclicPermutations (l : List α) : (cy
clicPermutations l).head (cyclicPermutations_ne_nil l) = l
· 使用定理 `List.head_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head h ∈ l
-/
theorem mem_cyclicPermutations_self (l : List α) : l ∈ cyclicPermutations l := by
  simpa using head_mem (cyclicPermutations_ne_nil l)

@[simp]
/-
**List.cyclicPermutations_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cyclicPermutations_rotate (l : List α) (k : Nat) : (l.rotate k).cyclicPerm
utations = l.cyclicPermutations.rotate k
参数：l : List α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `List.rotate_singleton`：rotate_singleton (x : α) (n : Nat) : [x].rotate n
 = [x]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_cyclicPermutations_of_ne_nil`：length_cyclicPermutations_of_n
e_nil (l : List α) (h : l != []) : length (cyclicPermutations l) = length l
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用定理 `List.get_rotate`：get_rotate (l : List α) (n : Nat) (k : Fin (l.rotate n)
.length) : (l.rotate n).get k = l.get ⟨(k + n) % l.length, mod_lt _ (length_rota
te l …
· 使用定理 `List.get_cyclicPermutations`：get_cyclicPermutations (l : List α) (n : Fi
n (length (cyclicPermutations l))) : (cyclicPermutations l).get n = l.rotate n
· 使用定理 `List.rotate_rotate`：rotate_rotate (l : List α) (n m : Nat) : (l.rotate n
).rotate m = l.rotate (n + m)
· 使用定理 `List.rotate_mod`：rotate_mod (l : List α) (n : Nat) : l.rotate (n % l.len
gth) = l.rotate n
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `List.getElem_singleton`：∀ {α : Type u_1} {a : α} {i : ℕ} (h : i < 1), [a
][i] = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.getElem_cyclicPermutations`：getElem_cyclicPermutations (l : List α)
 (n : Nat) (h : n < length (cyclicPermutations l)) : (cyclicPermutations l)[n] =
 l.rotate n
-/
theorem cyclicPermutations_rotate (l : List α) (k : ℕ) :
    (l.rotate k).cyclicPermutations = l.cyclicPermutations.rotate k := by
  have : (l.rotate k).cyclicPermutations.length = length (l.cyclicPermutations.rotate k) := by
    cases l
    · simp
    · rw [length_cyclicPermutations_of_ne_nil] <;> simp
  refine ext_get this fun n hn hn' => ?_
  rw [get_rotate, get_cyclicPermutations, rotate_rotate, ← rotate_mod, Nat.add_comm]
  cases l <;> simp

@[simp]
/-
**List.mem_cyclicPermutations_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_cyclicPermutations_iff : l in cyclicPermutations l' ↔ l ~r l'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.get_cyclicPermutations`：get_cyclicPermutations (l : List α) (n : Fi
n (length (cyclicPermutations l))) : (cyclicPermutations l).get n = l.rotate n
· 使用定理 `List.IsRotated.forall`：∀ {α : Type u} (l : List α) (n : ℕ), l.rotate n ~
r l
· 使用定理 `List.cyclicPermutations_rotate`：cyclicPermutations_rotate (l : List α) (
k : Nat) : (l.rotate k).cyclicPermutations = l.cyclicPermutations.rotate k
· 使用定理 `List.mem_rotate`：∀ {α : Type u} {l : List α} {a : α} {n : ℕ}, a ∈ l.rota
te n ↔ a ∈ l
· 使用定理 `List.mem_cyclicPermutations_self`：mem_cyclicPermutations_self (l : List 
α) : l in cyclicPermutations l
-/
theorem mem_cyclicPermutations_iff : l ∈ cyclicPermutations l' ↔ l ~r l' := by
  constructor
  · simp_rw [mem_iff_get, get_cyclicPermutations]
    rintro ⟨k, rfl⟩
    exact .forall _ _
  · rintro ⟨k, rfl⟩
    rw [cyclicPermutations_rotate, mem_rotate]
    apply mem_cyclicPermutations_self

@[simp]
/-
**List.cyclicPermutations_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cyclicPermutations_eq_nil_iff {l : List α} : cyclicPermutations l = [[]] ↔
 l = []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `List.cyclicPermutations_injective`：cyclicPermutations_injective : Functi
on.Injective (@cyclicPermutations α)
-/
theorem cyclicPermutations_eq_nil_iff {l : List α} : cyclicPermutations l = [[]] ↔ l = [] :=
  cyclicPermutations_injective.eq_iff' rfl

@[simp]
/-
**List.cyclicPermutations_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cyclicPermutations_eq_singleton_iff {l : List α} {x : α} : cyclicPermutati
ons l = [[x]] ↔ l = [x]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `List.cyclicPermutations_injective`：cyclicPermutations_injective : Functi
on.Injective (@cyclicPermutations α)
-/
theorem cyclicPermutations_eq_singleton_iff {l : List α} {x : α} :
    cyclicPermutations l = [[x]] ↔ l = [x] :=
  cyclicPermutations_injective.eq_iff' rfl

/-- If a `l : List α` is `Nodup l`, then all of its cyclic permutants are distinct. -/
/-
**List.Nodup.cyclicPermutations** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α}, l.Nodup → l.cyclicPermutations.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.nodup_iff_injective_get`：nodup_iff_injective_get {l : List α} : Nod
up l ↔ Function.Injective l.get
· 使用定理 `Fin.mk.injEq`：∀ {n : ℕ} (val : ℕ) (isLt : val < n) (val_1 : ℕ) (isLt_1 :
 val_1 < n), (⟨val, isLt⟩ = ⟨val_1, isLt_1⟩) = (val = val_1)
· 使用定理 `List.getElem_cyclicPermutations`：getElem_cyclicPermutations (l : List α)
 (n : Nat) (h : n < length (cyclicPermutations l)) : (cyclicPermutations l)[n] =
 l.rotate n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.Nodup.rotate_congr_iff`：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {i
 j : ℕ}, l.rotate i = l.rotate j ↔ i % l.length = j % l.length ∨ l = []
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `List.length_cyclicPermutations_of_ne_nil`：length_cyclicPermutations_of_n
e_nil (l : List α) (h : l != []) : length (cyclicPermutations l) = length l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p

--- 原说明 ---
If a `l : List α` is `Nodup l`, then all of its cyclic permutants are distinct.
-/
protected theorem Nodup.cyclicPermutations {l : List α} (hn : Nodup l) :
    Nodup (cyclicPermutations l) := by
  rcases eq_or_ne l [] with rfl | hl
  · simp
  · rw [nodup_iff_injective_get]
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only [length_cyclicPermutations_of_ne_nil l hl] at hi hj
    simpa [hn.rotate_congr_iff, mod_eq_of_lt, *] using h
/-
**List.IsRotated.cyclicPermutations** 是 Mathlib 中的一个定理，位于命名空间 `List.IsRotated`。
形式化陈述：∀ {α : Type u} {l l' : List α}, l ~r l' → l.cyclicPermutations ~r l'.cycli
cPermutations
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.cyclicPermutations_rotate`：cyclicPermutations_rotate (l : List α) (
k : Nat) : (l.rotate k).cyclicPermutations = l.cyclicPermutations.rotate k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem IsRotated.cyclicPermutations {l l' : List α} (h : l ~r l') :
    l.cyclicPermutations ~r l'.cyclicPermutations := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by simp⟩

@[simp]
/-
**List.isRotated_cyclicPermutations_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isRotated_cyclicPermutations_iff {l l' : List α} : l.cyclicPermutations ~r
 l'.cyclicPermutations ↔ l ~r l'
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isRotated_cyclicPermutations_iff {l l' : List α} :
    l.cyclicPermutations ~r l'.cyclicPermutations ↔ l ~r l' := by
  simp only [IsRotated, ← cyclicPermutations_rotate, cyclicPermutations_inj]

section Decidable

variable [DecidableEq α]

/-
**List.isRotatedDecidable** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：isRotatedDecidable (l l' : List α) : Decidable (l ~r l')
参数：l l' : List α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isRotated_iff_mem_map_range`：isRotated_iff_mem_map_range : l ~r l' 
↔ l' in (List.range (l.length + 1)).map l.rotate
-/
instance isRotatedDecidable (l l' : List α) : Decidable (l ~r l') :=
  decidable_of_iff' _ isRotated_iff_mem_map_range
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {l l' : List α} : Decidable (IsRotated.setoid α l l') :=
  List.isRotatedDecidable _ _

end Decidable

end IsRotated

end List

