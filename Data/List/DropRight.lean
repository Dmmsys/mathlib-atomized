/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Data.List.Basic

/-!

# Dropping or taking from lists on the right

Taking or removing element from the tail end of a list

## Main definitions

- `rdrop n`: drop `n : ℕ` elements from the tail
- `rtake n`: take `n : ℕ` elements from the tail
- `rdropWhile p`: remove all the elements from the tail of a list until it finds the first element
  for which `p : α → Bool` returns false. This element and everything before is returned.
- `rtakeWhile p`:  Returns the longest terminal segment of a list for which `p : α → Bool` returns
  true.

## Implementation detail

The two predicate-based methods operate by performing the regular "from-left" operation on
`List.reverse`, followed by another `List.reverse`, so they are not the most performant.
The other two rely on `List.length l` so they still traverse the list twice. One could construct
another function that takes a `L : ℕ` and use `L - n`. Under a proof condition that
`L = l.length`, the function would do the right thing.

-/

@[expose] public section

-- Make sure we don't import algebra
assert_not_exists Monoid

variable {α : Type*} (p : α → Bool) (l : List α) (n : ℕ)

namespace List

/-- Drop `n` elements from the tail end of a list. -/
/-
**List.rdrop** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：rdrop : List α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Drop `n` elements from the tail end of a list.
-/
def rdrop : List α :=
  l.take (l.length - n)

@[simp]
/-
**List.rdrop_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdrop_nil : rdrop ([] : List α) n = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rdrop_nil : rdrop ([] : List α) n = [] := by simp [rdrop]

@[simp]
/-
**List.rdrop_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdrop_zero : rdrop l 0 = l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.take_length`：∀ {α : Type u_1} {l : List α}, List.take l.length l = 
l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rdrop_zero : rdrop l 0 = l := by simp [rdrop]
/-
**List.rdrop_eq_reverse_drop_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdrop_eq_reverse_drop_reverse : l.rdrop n = reverse (l.reverse.drop n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rdrop.eq_1`：∀ {α : Type u_1} (l : List α) (n : ℕ), l.rdrop n = List
.take (l.length - n) l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `List.take_length_add_append`：∀ {α : Type u_1} {l₁ l₂ : List α} (i : ℕ), 
List.take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ List.take i l₂
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `List.take_append`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, List.take i
 (l₁ ++ l₂) = List.take i l₁ ++ List.take (i - l₁.length) l₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
-/
theorem rdrop_eq_reverse_drop_reverse : l.rdrop n = reverse (l.reverse.drop n) := by
  rw [rdrop]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton xs x IH =>
    cases n
    · simp [take_length_add_append]
    · simp [take_append, IH]

@[simp]
/-
**List.rdrop_concat_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdrop_concat_succ (x : α) : rdrop (l ++ [x]) (n + 1) = rdrop l n
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rdrop_eq_reverse_drop_reverse`：rdrop_eq_reverse_drop_reverse : l.rd
rop n = reverse (l.reverse.drop n)
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rdrop_concat_succ (x : α) : rdrop (l ++ [x]) (n + 1) = rdrop l n := by
  simp [rdrop_eq_reverse_drop_reverse]

/-- Take `n` elements from the tail end of a list. -/
/-
**List.rtake** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：rtake : List α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take `n` elements from the tail end of a list.
-/
def rtake : List α :=
  l.drop (l.length - n)

@[simp]
/-
**List.rtake_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtake_nil : rtake ([] : List α) n = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rtake_nil : rtake ([] : List α) n = [] := by simp [rtake]

@[simp]
/-
**List.rtake_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtake_zero : rtake l 0 = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.drop_length`：∀ {α : Type u_1} {l : List α}, List.drop l.length l = 
[]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rtake_zero : rtake l 0 = [] := by simp [rtake]
/-
**List.rtake_eq_reverse_take_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtake_eq_reverse_take_reverse : l.rtake n = reverse (l.reverse.take n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rtake.eq_1`：∀ {α : Type u_1} (l : List α) (n : ℕ), l.rtake n = List
.drop (l.length - n) l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.drop_length`：∀ {α : Type u_1} {l : List α}, List.drop l.length l = 
[]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `List.drop_append`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, List.drop i
 (l₁ ++ l₂) = List.drop i l₁ ++ List.drop (i - l₁.length) l₂
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
-/
theorem rtake_eq_reverse_take_reverse : l.rtake n = reverse (l.reverse.take n) := by
  rw [rtake]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton xs x IH =>
    cases n
    · exact drop_length
    · simp [drop_append, IH]

@[simp]
/-
**List.rtake_concat_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtake_concat_succ (x : α) : rtake (l ++ [x]) (n + 1) = rtake l n ++ [x]
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rtake_eq_reverse_take_reverse`：rtake_eq_reverse_take_reverse : l.rt
ake n = reverse (l.reverse.take n)
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rtake_concat_succ (x : α) : rtake (l ++ [x]) (n + 1) = rtake l n ++ [x] := by
  simp [rtake_eq_reverse_take_reverse]

/-- Drop elements from the tail end of a list that satisfy `p : α → Bool`.
Implemented naively via `List.reverse` -/
/-
**List.rdropWhile** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：rdropWhile : List α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Drop elements from the tail end of a list that satisfy `p : α → Bool`.
Implemented naively via `List.reverse`
-/
def rdropWhile : List α :=
  reverse (l.reverse.dropWhile p)

@[simp]
/-
**List.rdropWhile_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_nil : rdropWhile p ([] : List α) = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rdropWhile_nil : rdropWhile p ([] : List α) = [] := by simp [rdropWhile]
/-
**List.rdropWhile_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_concat (x : α) : rdropWhile p (l ++ [x]) = if p x then rdropWhi
le p l else l ++ [x]
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_singleton`：∀ {α : Type u_1} {a : α}, [a].reverse = [a]
· 使用定理 `List.dropWhile.eq_2`：∀ {α : Type u} (p : α → Bool) (a : α) (as : List α)
,   List.dropWhile p (a :: as) =     match p a with     | true => List.dropWhile
 p as    …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
theorem rdropWhile_concat (x : α) :
    rdropWhile p (l ++ [x]) = if p x then rdropWhile p l else l ++ [x] := by
  simp only [rdropWhile, dropWhile, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h <;> simp [h]

@[simp]
/-
**List.rdropWhile_concat_pos** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_concat_pos (x : α) (h : p x) : rdropWhile p (l ++ [x]) = rdropW
hile p l
参数：x : α；h : p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rdropWhile_concat`：rdropWhile_concat (x : α) : rdropWhile p (l ++ [
x]) = if p x then rdropWhile p l else l ++ [x]
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem rdropWhile_concat_pos (x : α) (h : p x) : rdropWhile p (l ++ [x]) = rdropWhile p l := by
  rw [rdropWhile_concat, if_pos h]

@[simp]
/-
**List.rdropWhile_concat_neg** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_concat_neg (x : α) (h : ¬p x) : rdropWhile p (l ++ [x]) = l ++ 
[x]
参数：x : α；h : ¬p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rdropWhile_concat`：rdropWhile_concat (x : α) : rdropWhile p (l ++ [
x]) = if p x then rdropWhile p l else l ++ [x]
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem rdropWhile_concat_neg (x : α) (h : ¬p x) : rdropWhile p (l ++ [x]) = l ++ [x] := by
  rw [rdropWhile_concat, if_neg h]
/-
**List.rdropWhile_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_singleton (x : α) : rdropWhile p [x] = if p x then [] else [x]
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `List.rdropWhile_concat`：rdropWhile_concat (x : α) : rdropWhile p (l ++ [
x]) = if p x then rdropWhile p l else l ++ [x]
· 使用定理 `List.rdropWhile_nil`：rdropWhile_nil : rdropWhile p ([] : List α) = []
-/
theorem rdropWhile_singleton (x : α) : rdropWhile p [x] = if p x then [] else [x] := by
  rw [← nil_append [x], rdropWhile_concat, rdropWhile_nil]
/-
**List.rdropWhile_last_not** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_last_not (hl : l.rdropWhile p != []) : ¬p ((rdropWhile p l).get
Last hl)
参数：hl : l.rdropWhile p != []。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getLast_reverse`：∀ {α : Type u_1} {l : List α} (h : l.reverse ≠ [])
, l.reverse.getLast h = l.head ⋯
· 使用定理 `List.head_dropWhile_not`：∀ {α : Type u_1} (p : α → Bool) {l : List α} (w
 : List.dropWhile p l ≠ []), p ((List.dropWhile p l).head w) = false
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem rdropWhile_last_not (hl : l.rdropWhile p ≠ []) : ¬p ((rdropWhile p l).getLast hl) := by
  simp_rw [rdropWhile]
  rw [getLast_reverse, head_dropWhile_not p]
  simp
/-
**List.rdropWhile_prefix** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_prefix : l.rdropWhile p <+: l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_suffix`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.reverse <:+ l
₂.reverse ↔ l₁ <+: l₂
· 使用定理 `List.rdropWhile.eq_1`：∀ {α : Type u_1} (p : α → Bool) (l : List α), List
.rdropWhile p l = (List.dropWhile p l.reverse).reverse
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `List.dropWhile_suffix`：∀ {α : Type u_1} {l : List α} (p : α → Bool), Lis
t.dropWhile p l <:+ l
-/
theorem rdropWhile_prefix : l.rdropWhile p <+: l := by
  rw [← reverse_suffix, rdropWhile, reverse_reverse]
  exact dropWhile_suffix _

variable {p} {l}

@[simp]
/-
**List.rdropWhile_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_eq_nil_iff : rdropWhile p l = [] ↔ forall x in l, p x
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rdropWhile_eq_nil_iff : rdropWhile p l = [] ↔ ∀ x ∈ l, p x := by simp [rdropWhile]

@[simp]
/-
**List.rdropWhile_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_eq_self_iff : rdropWhile p l = l ↔ forall hl : l != [], ¬p (l.g
etLast hl)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.sub_one_sub_lt_of_lt`：∀ {a b : ℕ}, a < b → b - 1 - a < b
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getElem_reverse`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i < l.r
everse.length), l.reverse[i] = l[l.length - 1 - i]
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `List.getLast_eq_getElem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.g
etLast h = l[l.length - 1]
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rdropWhile_eq_self_iff : rdropWhile p l = l ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) := by
  simp [rdropWhile, reverse_eq_iff, getLast_eq_getElem, Nat.pos_iff_ne_zero]

variable (p) (l)
/-
**List.dropWhile_idempotent** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dropWhile_idempotent : dropWhile p (dropWhile p l) = dropWhile p l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dropWhile_get_zero_not`：dropWhile_get_zero_not (l : List α) (hl : 0
 < (l.dropWhile p).length) : ¬p ((l.dropWhile p).get ⟨0, hl⟩)
-/
theorem dropWhile_idempotent : dropWhile p (dropWhile p l) = dropWhile p l := by
  simp only [dropWhile_eq_self_iff]
  exact fun h => dropWhile_get_zero_not p l h
/-
**List.rdropWhile_idempotent** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_idempotent : rdropWhile p (rdropWhile p l) = rdropWhile p l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.rdropWhile_eq_self_iff`：rdropWhile_eq_self_iff : rdropWhile p l = l
 ↔ forall hl : l != [], ¬p (l.getLast hl)
· 使用定理 `List.rdropWhile_last_not`：rdropWhile_last_not (hl : l.rdropWhile p != []
) : ¬p ((rdropWhile p l).getLast hl)
-/
theorem rdropWhile_idempotent : rdropWhile p (rdropWhile p l) = rdropWhile p l :=
  rdropWhile_eq_self_iff.mpr (rdropWhile_last_not _ _)
/-
**List.rdropWhile_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_reverse : l.reverse.rdropWhile p = (l.dropWhile p).reverse
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem rdropWhile_reverse : l.reverse.rdropWhile p = (l.dropWhile p).reverse := by
  simp_rw [rdropWhile, reverse_reverse]

/-- Take elements from the tail end of a list that satisfy `p : α → Bool`.
Implemented naively via `List.reverse` -/
/-
**List.rtakeWhile** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：rtakeWhile : List α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take elements from the tail end of a list that satisfy `p : α → Bool`.
Implemented naively via `List.reverse`
-/
def rtakeWhile : List α :=
  reverse (l.reverse.takeWhile p)

@[simp]
/-
**List.rtakeWhile_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtakeWhile_nil : rtakeWhile p ([] : List α) = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rtakeWhile_nil : rtakeWhile p ([] : List α) = [] := by simp [rtakeWhile]
/-
**List.rtakeWhile_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtakeWhile_concat (x : α) : rtakeWhile p (l ++ [x]) = if p x then rtakeWhi
le p l ++ [x] else []
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_singleton`：∀ {α : Type u_1} {a : α}, [a].reverse = [a]
· 使用定理 `List.takeWhile.eq_2`：∀ {α : Type u} (p : α → Bool) (a : α) (as : List α)
,   List.takeWhile p (a :: as) =     match p a with     | true => a :: List.take
While p a…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
-/
theorem rtakeWhile_concat (x : α) :
    rtakeWhile p (l ++ [x]) = if p x then rtakeWhile p l ++ [x] else [] := by
  simp only [rtakeWhile, takeWhile, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h <;> simp [h]

@[simp]
/-
**List.rtakeWhile_concat_pos** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtakeWhile_concat_pos (x : α) (h : p x) : rtakeWhile p (l ++ [x]) = rtakeW
hile p l ++ [x]
参数：x : α；h : p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rtakeWhile_concat`：rtakeWhile_concat (x : α) : rtakeWhile p (l ++ [
x]) = if p x then rtakeWhile p l ++ [x] else []
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem rtakeWhile_concat_pos (x : α) (h : p x) :
    rtakeWhile p (l ++ [x]) = rtakeWhile p l ++ [x] := by rw [rtakeWhile_concat, if_pos h]

@[simp]
/-
**List.rtakeWhile_concat_neg** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtakeWhile_concat_neg (x : α) (h : ¬p x) : rtakeWhile p (l ++ [x]) = []
参数：x : α；h : ¬p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rtakeWhile_concat`：rtakeWhile_concat (x : α) : rtakeWhile p (l ++ [
x]) = if p x then rtakeWhile p l ++ [x] else []
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem rtakeWhile_concat_neg (x : α) (h : ¬p x) : rtakeWhile p (l ++ [x]) = [] := by
  rw [rtakeWhile_concat, if_neg h]
/-
**List.rtakeWhile_suffix** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtakeWhile_suffix : l.rtakeWhile p <:+ l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_prefix`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.reverse <+: l
₂.reverse ↔ l₁ <:+ l₂
· 使用定理 `List.rtakeWhile.eq_1`：∀ {α : Type u_1} (p : α → Bool) (l : List α), List
.rtakeWhile p l = (List.takeWhile p l.reverse).reverse
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `List.takeWhile_prefix`：∀ {α : Type u_1} {l : List α} (p : α → Bool), Lis
t.takeWhile p l <+: l
-/
theorem rtakeWhile_suffix : l.rtakeWhile p <:+ l := by
  rw [← reverse_prefix, rtakeWhile, reverse_reverse]
  exact takeWhile_prefix _

variable {p} {l}

@[simp]
/-
**List.rtakeWhile_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtakeWhile_eq_self_iff : rtakeWhile p l = l ↔ forall x in l, p x
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rtakeWhile_eq_self_iff : rtakeWhile p l = l ↔ ∀ x ∈ l, p x := by
  simp [rtakeWhile, reverse_eq_iff]

@[simp]
/-
**List.rtakeWhile_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtakeWhile_eq_nil_iff : rtakeWhile p l = [] ↔ forall hl : l != [], ¬p (l.g
etLast hl)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.getLast_append_of_ne_nil`：∀ {α : Type u_1} {l' l : List α} (h₁ : l 
++ l' ≠ []) (h₂ : l' ≠ []), (l ++ l').getLast h₁ = l'.getLast h₂
-/
theorem rtakeWhile_eq_nil_iff : rtakeWhile p l = [] ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) := by
  induction l using List.reverseRecOn <;> simp [rtakeWhile]
/-
**List.mem_rtakeWhile_imp** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_rtakeWhile_imp {x : α} (hx : x in rtakeWhile p l) : p x
参数：hx : x in rtakeWhile p l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_takeWhile_imp`：mem_takeWhile_imp {x : α} (hx : x in takeWhile p
 l) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_reverse`：∀ {α : Type u_1} {x : α} {as : List α}, x ∈ as.reverse
 ↔ x ∈ as
· 使用定理 `List.rtakeWhile.eq_1`：∀ {α : Type u_1} (p : α → Bool) (l : List α), List
.rtakeWhile p l = (List.takeWhile p l.reverse).reverse
-/
theorem mem_rtakeWhile_imp {x : α} (hx : x ∈ rtakeWhile p l) : p x := by
  rw [rtakeWhile, mem_reverse] at hx
  exact mem_takeWhile_imp hx
/-
**List.rtakeWhile_idempotent** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtakeWhile_idempotent (p : α -> Bool) (l : List α) : rtakeWhile p (rtakeWh
ile p l) = rtakeWhile p l
参数：p : α -> Bool；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.rtakeWhile_eq_self_iff`：rtakeWhile_eq_self_iff : rtakeWhile p l = l
 ↔ forall x in l, p x
· 使用定理 `List.mem_rtakeWhile_imp`：mem_rtakeWhile_imp {x : α} (hx : x in rtakeWhil
e p l) : p x
-/
theorem rtakeWhile_idempotent (p : α → Bool) (l : List α) :
    rtakeWhile p (rtakeWhile p l) = rtakeWhile p l :=
  rtakeWhile_eq_self_iff.mpr fun _ => mem_rtakeWhile_imp
/-
**List.rtakeWhile_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rtakeWhile_reverse : l.reverse.rtakeWhile p = (l.takeWhile p).reverse
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem rtakeWhile_reverse : l.reverse.rtakeWhile p = (l.takeWhile p).reverse := by
  simp_rw [rtakeWhile, reverse_reverse]

@[simp]
/-
**List.rdropWhile_append_rtakeWhile** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rdropWhile_append_rtakeWhile : l.rdropWhile p ++ l.rtakeWhile p = l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.takeWhile_append_dropWhile`：∀ {α : Type u_1} {p : α → Bool} {l : Li
st α}, List.takeWhile p l ++ List.dropWhile p l = l
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
theorem rdropWhile_append_rtakeWhile :
    l.rdropWhile p ++ l.rtakeWhile p = l := by
  simp only [rdropWhile, rtakeWhile]
  rw [← List.reverse_append, takeWhile_append_dropWhile, reverse_reverse]
/-
**List.rdrop_add** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：rdrop_add (i j : Nat) : (l.rdrop i).rdrop j = l.rdrop (i + j)
参数：i j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.rdrop_eq_reverse_drop_reverse`：rdrop_eq_reverse_drop_reverse : l.rd
rop n = reverse (l.reverse.drop n)
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.drop_drop`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.drop j l) = List.drop (j + i) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rdrop_add (i j : ℕ) : (l.rdrop i).rdrop j = l.rdrop (i + j) := by
  simp_rw [rdrop_eq_reverse_drop_reverse, reverse_reverse, drop_drop]

@[simp]
/-
**List.rdrop_append_length** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：rdrop_append_length {l₁ l₂ : List α} : List.rdrop (l₁ ++ l₂) (List.length 
l₂) = l₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rdrop_eq_reverse_drop_reverse`：rdrop_eq_reverse_drop_reverse : l.rd
rop n = reverse (l.reverse.drop n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.drop_left`：∀ {α : Type u_1} {l₁ l₂ : List α}, List.drop l₁.length (
l₁ ++ l₂) = l₂
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
lemma rdrop_append_length {l₁ l₂ : List α} :
    List.rdrop (l₁ ++ l₂) (List.length l₂) = l₁ := by
  rw [rdrop_eq_reverse_drop_reverse, ← length_reverse,
      reverse_append, drop_left, reverse_reverse]
/-
**List.rdrop_append_of_le_length** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：rdrop_append_of_le_length {l₁ l₂ : List α} (k : Nat) : k <= length l₂ -> L
ist.rdrop (l₁ ++ l₂) k = l₁ ++ List.rdrop l₂ k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rdrop_eq_reverse_drop_reverse`：rdrop_eq_reverse_drop_reverse : l.rd
rop n = reverse (l.reverse.drop n)
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.drop_append_of_le_length`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}
, i ≤ l₁.length → List.drop i (l₁ ++ l₂) = List.drop i l₁ ++ l₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
lemma rdrop_append_of_le_length {l₁ l₂ : List α} (k : ℕ) :
    k ≤ length l₂ → List.rdrop (l₁ ++ l₂) k = l₁ ++ List.rdrop l₂ k := by
  intro hk
  rw [← length_reverse] at hk
  rw [rdrop_eq_reverse_drop_reverse, reverse_append, drop_append_of_le_length hk,
    reverse_append, reverse_reverse, ← rdrop_eq_reverse_drop_reverse]

@[simp]
/-
**List.rdrop_append_length_add** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：rdrop_append_length_add {l₁ l₂ : List α} (k : Nat) : List.rdrop (l₁ ++ l₂)
 (length l₂ + k) = List.rdrop l₁ k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `List.rdrop_add`：rdrop_add (i j : Nat) : (l.rdrop i).rdrop j = l.rdrop (i
 + j)
· 使用引理 `List.rdrop_append_length`：rdrop_append_length {l₁ l₂ : List α} : List.rd
rop (l₁ ++ l₂) (List.length l₂) = l₁
-/
lemma rdrop_append_length_add {l₁ l₂ : List α} (k : ℕ) :
    List.rdrop (l₁ ++ l₂) (length l₂ + k) = List.rdrop l₁ k := by
  rw [← rdrop_add, rdrop_append_length]

end List

