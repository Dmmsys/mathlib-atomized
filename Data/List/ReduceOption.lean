/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Anthony DeRossi
-/
module

public import Mathlib.Data.List.Basic

/-!
# Properties of `List.reduceOption`

In this file we prove basic lemmas about `List.reduceOption`.
-/

public section

namespace List

variable {α β : Type*}

@[simp]
/-
**List.reduceOption_cons_of_some** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_cons_of_some (x : α) (l : List (Option α)) : reduceOption (so
me x :: l) = x :: l.reduceOption
参数：x : α；l : List (Option α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filterMap_congr`：filterMap_congr {f g : α -> Option β} {l : List α}
 (h : forall x in l, f x = g x) : l.filterMap f = l.filterMap g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reduceOption_cons_of_some (x : α) (l : List (Option α)) :
    reduceOption (some x :: l) = x :: l.reduceOption := by
  simp only [reduceOption, filterMap, id]

@[simp]
/-
**List.reduceOption_cons_of_none** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_cons_of_none (l : List (Option α)) : reduceOption (none :: l)
 = l.reduceOption
参数：l : List (Option α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filterMap_congr`：filterMap_congr {f g : α -> Option β} {l : List α}
 (h : forall x in l, f x = g x) : l.filterMap f = l.filterMap g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reduceOption_cons_of_none (l : List (Option α)) :
    reduceOption (none :: l) = l.reduceOption := by simp only [reduceOption, filterMap, id]

@[simp]
/-
**List.reduceOption_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_nil : @reduceOption α [] = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reduceOption_nil : @reduceOption α [] = [] :=
  rfl

@[simp]
/-
**List.reduceOption_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_map {l : List (Option α)} {f : α -> β} : reduceOption (map (O
ption.map f) l) = map f (reduceOption l)
参数：Option α。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.reduceOption_cons_of_none`：reduceOption_cons_of_none (l : List (Opt
ion α)) : reduceOption (none :: l) = l.reduceOption
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reduceOption_cons_of_some`：reduceOption_cons_of_some (x : α) (l : L
ist (Option α)) : reduceOption (some x :: l) = x :: l.reduceOption
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem reduceOption_map {l : List (Option α)} {f : α → β} :
    reduceOption (map (Option.map f) l) = map f (reduceOption l) := by
  induction l with
  | nil => simp only [reduceOption_nil, map_nil]
  | cons hd tl hl =>
    cases hd <;> simpa [Option.map_some, map, eq_self_iff_true, reduceOption_cons_of_some] using hl
/-
**List.reduceOption_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_append (l l' : List (Option α)) : (l ++ l').reduceOption = l.
reduceOption ++ l'.reduceOption
参数：l l' : List (Option α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.filterMap_append`：∀ {α : Type u_1} {β : Type u_2} {l l' : List α} {
f : α → Option β},   List.filterMap f (l ++ l') = List.filterMap f l ++ List.fil
terMap f l'
-/
theorem reduceOption_append (l l' : List (Option α)) :
    (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption :=
  filterMap_append

@[simp]
/-
**List.reduceOption_replicate_none** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_replicate_none {n : Nat} : (replicate n (@none α)).reduceOpti
on = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filterMap_replicate_of_none`：∀ {α : Type u_1} {β : Type u_2} {a : α
} {n : ℕ} {f : α → Option β},   f a = none → List.filterMap f (List.replicate n 
a) = []
· 使用定理 `id_def`：∀ {α : Sort u} (a : α), id a = a
-/
theorem reduceOption_replicate_none {n : ℕ} : (replicate n (@none α)).reduceOption = [] := by
  dsimp [reduceOption]
  rw [filterMap_replicate_of_none (id_def _)]
/-
**List.reduceOption_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_eq_nil_iff (l : List (Option α)) : l.reduceOption = [] ↔ exis
ts n, l = replicate n none
参数：l : List (Option α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filterMap_eq_nil_iff`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → Op
tion α_1} {l : List α}, List.filterMap f l = [] ↔ ∀ a ∈ l, f a = none
· 使用定理 `List.eq_replicate_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, (∀ b ∈ 
l, b = a) → l = List.replicate l.length a
-/
theorem reduceOption_eq_nil_iff (l : List (Option α)) :
    l.reduceOption = [] ↔ ∃ n, l = replicate n none := by
  dsimp [reduceOption]
  rw [filterMap_eq_nil_iff]
  constructor
  · intro h
    exact ⟨l.length, eq_replicate_of_mem h⟩
  · grind
/-
**List.reduceOption_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_eq_singleton_iff (l : List (Option α)) (a : α) : l.reduceOpti
on = [a] ↔ exists m n, l = replicate m none ++ some a :: replicate n none
参数：l : List (Option α)；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filterMap_eq_cons_iff`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → O
ption α_1} {l : List α} {b : α_1} {bs : List α_1},   List.filterMap f l = b :: b
s ↔     ∃ l₁ a l…
· 使用定理 `List.eq_replicate_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, (∀ b ∈ 
l, b = a) → l = List.replicate l.length a
· 使用定理 `List.filterMap_eq_nil_iff`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → Op
tion α_1} {l : List α}, List.filterMap f l = [] ↔ ∀ a ∈ l, f a = none
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.filterMap_congr`：filterMap_congr {f g : α -> Option β} {l : List α}
 (h : forall x in l, f x = g x) : l.filterMap f = l.filterMap g
· 使用定理 `List.filterMap_append`：∀ {α : Type u_1} {β : Type u_2} {l l' : List α} {
f : α → Option β},   List.filterMap f (l ++ l') = List.filterMap f l ++ List.fil
terMap f l'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.filterMap_replicate_of_none`：∀ {α : Type u_1} {β : Type u_2} {a : α
} {n : ℕ} {f : α → Option β},   f a = none → List.filterMap f (List.replicate n 
a) = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.filterMap_cons_some`：∀ {α : Type u_1} {β : Type u_2} {f : α → Optio
n β} {a : α} {l : List α} {b : β},   f a = some b → List.filterMap f (a :: l) = 
b :: List.filt…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
theorem reduceOption_eq_singleton_iff (l : List (Option α)) (a : α) :
    l.reduceOption = [a] ↔ ∃ m n, l = replicate m none ++ some a :: replicate n none := by
  dsimp [reduceOption]
  constructor
  · intro h
    rw [filterMap_eq_cons_iff] at h
    obtain ⟨l₁, _, l₂, h, hl₁, ⟨⟩, hl₂⟩ := h
    rw [filterMap_eq_nil_iff] at hl₂
    apply eq_replicate_of_mem at hl₁
    apply eq_replicate_of_mem at hl₂
    rw [h, hl₁, hl₂]
    use l₁.length, l₂.length
  · intro ⟨_, _, h⟩
    simp only [h, filterMap_append, filterMap_cons_some, filterMap_replicate_of_none, id_eq,
      nil_append, Option.some.injEq]
/-
**List.reduceOption_eq_append_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_eq_append_iff (l : List (Option α)) (l'₁ l'₂ : List α) : l.re
duceOption = l'₁ ++ l'₂ ↔ exists l₁ l₂, l = l₁ ++ l₂ ∧ l₁.reduceOption = l'₁ ∧ l
₂.reduceOption = l'₂
参数：l : List (Option α)；l'₁ l'₂ : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.filterMap_eq_append_iff`：∀ {α : Type u_1} {β : Type u_2} {l : List 
α} {L₁ L₂ : List β} {f : α → Option β},   List.filterMap f l = L₁ ++ L₂ ↔ ∃ l₁ l
₂, l = l₁ ++ l₂ ∧ …
-/
theorem reduceOption_eq_append_iff (l : List (Option α)) (l'₁ l'₂ : List α) :
    l.reduceOption = l'₁ ++ l'₂ ↔
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.reduceOption = l'₁ ∧ l₂.reduceOption = l'₂ := by
  dsimp [reduceOption]
  exact filterMap_eq_append_iff
/-
**List.reduceOption_eq_concat_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_eq_concat_iff (l : List (Option α)) (l' : List α) (a : α) : l
.reduceOption = l'.concat a ↔ exists l₁ l₂, l = l₁ ++ some a :: l₂ ∧ l₁.reduceOp
tion = l' ∧ l₂.reduceOption = []
参数：l : List (Option α)；l' : List α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.reduceOption_eq_append_iff`：reduceOption_eq_append_iff (l : List (O
ption α)) (l'₁ l'₂ : List α) : l.reduceOption = l'₁ ++ l'₂ ↔ exists l₁ l₂, l = l
₁ ++ l₂ ∧ l₁.reduceOp…
· 使用定理 `List.reduceOption_eq_singleton_iff`：reduceOption_eq_singleton_iff (l : L
ist (Option α)) (a : α) : l.reduceOption = [a] ↔ exists m n, l = replicate m non
e ++ some a :: replicate…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.reduceOption_append`：reduceOption_append (l l' : List (Option α)) :
 (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.reduceOption_replicate_none`：reduceOption_replicate_none {n : Nat} 
: (replicate n (@none α)).reduceOption = []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `List.reduceOption_cons_of_some`：reduceOption_cons_of_some (x : α) (l : L
ist (Option α)) : reduceOption (some x :: l) = x :: l.reduceOption
-/
theorem reduceOption_eq_concat_iff (l : List (Option α)) (l' : List α) (a : α) :
    l.reduceOption = l'.concat a ↔
      ∃ l₁ l₂, l = l₁ ++ some a :: l₂ ∧ l₁.reduceOption = l' ∧ l₂.reduceOption = [] := by
  rw [concat_eq_append]
  constructor
  · intro h
    rw [reduceOption_eq_append_iff] at h
    obtain ⟨l₁, _, h, hl₁, hl₂⟩ := h
    rw [reduceOption_eq_singleton_iff] at hl₂
    obtain ⟨m, n, hl₂⟩ := hl₂
    use l₁ ++ replicate m none, replicate n none
    simp_rw [h, reduceOption_append, reduceOption_replicate_none, append_assoc, append_nil, hl₁,
      hl₂, and_self]
  · intro ⟨_, _, h, hl₁, hl₂⟩
    rw [h, reduceOption_append, reduceOption_cons_of_some, hl₁, hl₂]
/-
**List.reduceOption_length_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_length_eq {l : List (Option α)} : l.reduceOption.length = (l.
filter Option.isSome).length
参数：Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reduceOption_cons_of_none`：reduceOption_cons_of_none (l : List (Opt
ion α)) : reduceOption (none :: l) = l.reduceOption
· 使用定理 `List.filter_cons_of_neg`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, ¬p a = true → List.filter p (a :: l) = List.filter p l
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reduceOption_cons_of_some`：reduceOption_cons_of_some (x : α) (l : L
ist (Option α)) : reduceOption (some x :: l) = x :: l.reduceOption
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.filter_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, p a = true → List.filter p (a :: l) = a :: List.filter p l
-/
theorem reduceOption_length_eq {l : List (Option α)} :
    l.reduceOption.length = (l.filter Option.isSome).length := by
  induction l with
  | nil => simp_rw [reduceOption_nil, filter_nil, length]
  | cons hd tl hl => cases hd <;> simp [hl]
/-
**List.length_eq_reduceOption_length_add_filter_none** 是 Mathlib 中的一个定理，位于命名空间 `
List`。
形式化陈述：length_eq_reduceOption_length_add_filter_none {l : List (Option α)} : l.le
ngth = l.reduceOption.length + (l.filter Option.isNone).length
参数：Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.reduceOption_length_eq`：reduceOption_length_eq {l : List (Option α)
} : l.reduceOption.length = (l.filter Option.isSome).length
· 使用定理 `List.length_eq_length_filter_add`：length_eq_length_filter_add {l : List 
(α)} (f : α -> Bool) : l.length = (l.filter f).length + (l.filter (!f ·)).length
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.not_isSome`：∀ {α : Type u_1} (a : Option α), (!a.isSome) = a.isNo
ne
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_eq_reduceOption_length_add_filter_none {l : List (Option α)} :
    l.length = l.reduceOption.length + (l.filter Option.isNone).length := by
  simp_rw [reduceOption_length_eq, l.length_eq_length_filter_add Option.isSome, Option.not_isSome]
/-
**List.reduceOption_length_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_length_le (l : List (Option α)) : l.reduceOption.length <= l.
length
参数：l : List (Option α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_eq_reduceOption_length_add_filter_none`：length_eq_reduceOpti
on_length_add_filter_none {l : List (Option α)} : l.length = l.reduceOption.leng
th + (l.filter Option.isNone).length
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem reduceOption_length_le (l : List (Option α)) : l.reduceOption.length ≤ l.length := by
  rw [length_eq_reduceOption_length_add_filter_none]
  apply Nat.le_add_right
/-
**List.reduceOption_length_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_length_eq_iff {l : List (Option α)} : l.reduceOption.length =
 l.length ↔ forall x in l, Option.isSome x
参数：Option α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reduceOption_length_eq`：reduceOption_length_eq {l : List (Option α)
} : l.reduceOption.length = (l.filter Option.isSome).length
· 使用定理 `List.length_filter_eq_length_iff`：∀ {α : Type u_1} {p : α → Bool} {l : L
ist α}, (List.filter p l).length = l.length ↔ ∀ a ∈ l, p a = true
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem reduceOption_length_eq_iff {l : List (Option α)} :
    l.reduceOption.length = l.length ↔ ∀ x ∈ l, Option.isSome x := by
  rw [reduceOption_length_eq, List.length_filter_eq_length_iff]
/-
**List.reduceOption_length_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_length_lt_iff {l : List (Option α)} : l.reduceOption.length <
 l.length ↔ none in l
参数：Option α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_iff_le_and_ne`：∀ {m n : ℕ}, m < n ↔ m ≤ n ∧ m ≠ n
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `List.reduceOption_length_le`：reduceOption_length_le (l : List (Option α)
) : l.reduceOption.length <= l.length
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `List.reduceOption_length_eq_iff`：reduceOption_length_eq_iff {l : List (O
ption α)} : l.reduceOption.length = l.length ↔ forall x in l, Option.isSome x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem reduceOption_length_lt_iff {l : List (Option α)} :
    l.reduceOption.length < l.length ↔ none ∈ l := by
  rw [Nat.lt_iff_le_and_ne, and_iff_right (reduceOption_length_le l), Ne,
    reduceOption_length_eq_iff]
  induction l
  · simp
  · grind [cases Option]
/-
**List.reduceOption_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_singleton (x : Option α) : [x].reduceOption = x.toList
参数：x : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem reduceOption_singleton (x : Option α) : [x].reduceOption = x.toList := by cases x <;> rfl
/-
**List.reduceOption_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_concat (l : List (Option α)) (x : Option α) : (l.concat x).re
duceOption = l.reduceOption ++ x.toList
参数：l : List (Option α)；x : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.reduceOption_cons_of_none`：reduceOption_cons_of_none (l : List (Opt
ion α)) : reduceOption (none :: l) = l.reduceOption
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.reduceOption_cons_of_some`：reduceOption_cons_of_some (x : α) (l : L
ist (Option α)) : reduceOption (some x :: l) = x :: l.reduceOption
· 使用定理 `List.reduceOption_append`：reduceOption_append (l l' : List (Option α)) :
 (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem reduceOption_concat (l : List (Option α)) (x : Option α) :
    (l.concat x).reduceOption = l.reduceOption ++ x.toList := by
  induction l generalizing x with
  | nil => cases x <;> simp [Option.toList]
  | cons hd tl hl =>
    simp only [concat_eq_append, reduceOption_append] at hl
    cases hd <;> simp [hl, reduceOption_append]
/-
**List.reduceOption_concat_of_some** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_concat_of_some (l : List (Option α)) (x : α) : (l.concat (som
e x)).reduceOption = l.reduceOption.concat x
参数：l : List (Option α)；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.reduceOption_append`：reduceOption_append (l l' : List (Option α)) :
 (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption
· 使用定理 `List.reduceOption_cons_of_some`：reduceOption_cons_of_some (x : α) (l : L
ist (Option α)) : reduceOption (some x :: l) = x :: l.reduceOption
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reduceOption_concat_of_some (l : List (Option α)) (x : α) :
    (l.concat (some x)).reduceOption = l.reduceOption.concat x := by
  simp only [reduceOption_nil, concat_eq_append, reduceOption_append, reduceOption_cons_of_some]
/-
**List.reduceOption_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_mem_iff {l : List (Option α)} {x : α} : x in l.reduceOption ↔
 some x in l
参数：Option α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filterMap_congr`：filterMap_congr {f g : α -> Option β} {l : List α}
 (h : forall x in l, f x = g x) : l.filterMap f = l.filterMap g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem reduceOption_mem_iff {l : List (Option α)} {x : α} : x ∈ l.reduceOption ↔ some x ∈ l := by
  simp only [reduceOption, id, mem_filterMap, exists_eq_right]
/-
**List.reduceOption_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reduceOption_getElem?_iff {l : List (Option α)} {x : α} : (exists i : Nat,
 l[i]? = some (some x)) ↔ exists i : Nat, l.reduceOption[i]? = some x
参数：Option α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reduceOption_getElem?_iff {l : List (Option α)} {x : α} :
    (∃ i : ℕ, l[i]? = some (some x)) ↔ ∃ i : ℕ, l.reduceOption[i]? = some x := by
  rw [← mem_iff_getElem?, ← mem_iff_getElem?, reduceOption_mem_iff]

end List

