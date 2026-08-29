/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Data.Stream.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Common

/-!
# Streams a.k.a. infinite lists a.k.a. infinite sequences
-/

@[expose] public section

open Nat Function Option

namespace Stream'

universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}
variable (m n : Nat) (x y : List α) (a b : Stream' α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Stream' α)
  body: ⟨Stream'.const default⟩

中文:
实例 [可居
  签名: α] : 可居 (Stream' α)
  定义体: ⟨Stream'.const default⟩

Depends on / 依赖: Stream
-/
instance [Inhabited α] : Inhabited (Stream' α) :=
  ⟨Stream'.const default⟩

/--
theorem `eta` / 定理 `eta`

English:
theorem eta
  given: (s : Stream' α)
  statement: head s :: tail s = s
  proof: funext fun i => by cases i <;> rfl

中文:
定理 eta
  条件: (s : Stream' α)
  结论: head s :: tail s = s
  证明: funext fun i => by cases i <;> rfl
-/
@[simp] protected theorem eta (s : Stream' α) : head s :: tail s = s :=
  funext fun i => by cases i <;> rfl

/-- Alias for `Stream'.eta` to match `List` API. -/
alias cons_head_tail := Stream'.eta

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s₁ s₂ : Stream' α}
  statement: (forall n, get s₁ n = get s₂ n) -> s₁ = s₂
  proof: fun h => funext h

@[simp]

中文:
定理 ext
  条件: {s₁ s₂ : Stream' α}
  结论: (对任意 n, get s₁ n = get s₂ n) -> s₁ = s₂
  证明: fun h => funext h

@[simp]
-/
protected theorem ext {s₁ s₂ : Stream' α} : (forall n, get s₁ n = get s₂ n) -> s₁ = s₂ :=
  fun h => funext h

@[simp]
/--
theorem `get_zero_cons` / 定理 `get_zero_cons`

English:
theorem get_zero_cons
  given: (a : α) (s : Stream' α)
  statement: get (a::s) 0 = a
  proof: rfl

@[simp]

中文:
定理 get_zero_cons
  条件: (a : α) (s : Stream' α)
  结论: get (a::s) 0 = a
  证明: rfl

@[simp]
-/
theorem get_zero_cons (a : α) (s : Stream' α) : get (a::s) 0 = a :=
  rfl

@[simp]
/--
theorem `head_cons` / 定理 `head_cons`

English:
theorem head_cons
  given: (a : α) (s : Stream' α)
  statement: head (a::s) = a
  proof: rfl

@[simp]

中文:
定理 head_cons
  条件: (a : α) (s : Stream' α)
  结论: head (a::s) = a
  证明: rfl

@[simp]

Depends on / 依赖: Group.IsSolvable, IsNilpotent, IsNilpotent.to_isSolvable, IsSolvable, derived_le_lower_central, eq_bot_iff, nilpotent_iff_lowerCentralSeries, to_isSolvable
-/
theorem head_cons (a : α) (s : Stream' α) : head (a::s) = a :=
  rfl

@[simp]
/--
theorem `tail_cons` / 定理 `tail_cons`

English:
theorem tail_cons
  given: (a : α) (s : Stream' α)
  statement: tail (a::s) = s
  proof: rfl

@[simp]

中文:
定理 tail_cons
  条件: (a : α) (s : Stream' α)
  结论: tail (a::s) = s
  证明: rfl

@[simp]
-/
theorem tail_cons (a : α) (s : Stream' α) : tail (a::s) = s :=
  rfl

@[simp]
/--
theorem `get_drop` / 定理 `get_drop`

English:
theorem get_drop
  given: (n m : Nat) (s : Stream' α)
  statement: get (drop m s) n = get s (m + n)
  proof: by
  rw [Nat.add_comm]
  rfl

中文:
定理 get_drop
  条件: (n m : 自然数) (s : Stream' α)
  结论: get (drop m s) n = get s (m + n)
  证明: by
  rw [Nat.add_comm]
  rfl

Depends on / 依赖: Nat.add_comm, add_comm
-/
theorem get_drop (n m : Nat) (s : Stream' α) : get (drop m s) n = get s (m + n) := by
  rw [Nat.add_comm]
  rfl

/--
theorem `tail_eq_drop` / 定理 `tail_eq_drop`

English:
theorem tail_eq_drop
  given: (s : Stream' α)
  statement: tail s = drop 1 s
  proof: rfl

@[simp]

中文:
定理 tail_eq_drop
  条件: (s : Stream' α)
  结论: tail s = drop 1 s
  证明: rfl

@[simp]
-/
theorem tail_eq_drop (s : Stream' α) : tail s = drop 1 s :=
  rfl

@[simp]
/--
theorem `drop_drop` / 定理 `drop_drop`

English:
theorem drop_drop
  given: (n m : Nat) (s : Stream' α)
  statement: drop n (drop m s) = drop (m + n) s
  proof: by
  ext; simp [Nat.add_assoc]

中文:
定理 drop_drop
  条件: (n m : 自然数) (s : Stream' α)
  结论: drop n (drop m s) = drop (m + n) s
  证明: by
  ext; simp [Nat.add_assoc]

Depends on / 依赖: Nat.add_assoc, add_assoc
-/
theorem drop_drop (n m : Nat) (s : Stream' α) : drop n (drop m s) = drop (m + n) s := by
  ext; simp [Nat.add_assoc]

/--
theorem `get_tail` / 定理 `get_tail`

English:
theorem get_tail
  given: {n : Nat} {s : Stream' α}
  statement: s.tail.get n = s.get (n + 1)
  proof: rfl

中文:
定理 get_tail
  条件: {n : 自然数} {s : Stream' α}
  结论: s.tail.get n = s.get (n + 1)
  证明: rfl
-/
@[simp] theorem get_tail {n : Nat} {s : Stream' α} : s.tail.get n = s.get (n + 1) := rfl

/--
theorem `tail_drop'` / 定理 `tail_drop'`

English:
theorem tail_drop'
  given: {i : Nat} {s : Stream' α}
  statement: tail (drop i s) = s.drop (i + 1)
  proof: by
  ext; simp [Nat.add_comm, Nat.add_left_comm]

中文:
定理 tail_drop'
  条件: {i : 自然数} {s : Stream' α}
  结论: tail (drop i s) = s.drop (i + 1)
  证明: by
  ext; simp [Nat.add_comm, Nat.add_left_comm]
-/
@[simp] theorem tail_drop' {i : Nat} {s : Stream' α} : tail (drop i s) = s.drop (i + 1) := by
  ext; simp [Nat.add_comm, Nat.add_left_comm]

/--
theorem `drop_tail'` / 定理 `drop_tail'`

English:
theorem drop_tail'
  given: {i : Nat} {s : Stream' α}
  statement: drop i (tail s) = s.drop (i + 1)
  proof: rfl

中文:
定理 drop_tail'
  条件: {i : 自然数} {s : Stream' α}
  结论: drop i (tail s) = s.drop (i + 1)
  证明: rfl
-/
@[simp] theorem drop_tail' {i : Nat} {s : Stream' α} : drop i (tail s) = s.drop (i + 1) := rfl

/--
theorem `tail_drop` / 定理 `tail_drop`

English:
theorem tail_drop
  given: (n : Nat) (s : Stream' α)
  statement: tail (drop n s) = drop n (tail s)
  proof: by simp

中文:
定理 tail_drop
  条件: (n : 自然数) (s : Stream' α)
  结论: tail (drop n s) = drop n (tail s)
  证明: by simp
-/
theorem tail_drop (n : Nat) (s : Stream' α) : tail (drop n s) = drop n (tail s) := by simp

/--
theorem `get_succ` / 定理 `get_succ`

English:
theorem get_succ
  given: (n : Nat) (s : Stream' α)
  statement: get s (succ n) = get (tail s) n
  proof: rfl

@[simp]

中文:
定理 get_succ
  条件: (n : 自然数) (s : Stream' α)
  结论: get s (succ n) = get (tail s) n
  证明: rfl

@[simp]
-/
theorem get_succ (n : Nat) (s : Stream' α) : get s (succ n) = get (tail s) n :=
  rfl

@[simp]
/--
theorem `get_succ_cons` / 定理 `get_succ_cons`

English:
theorem get_succ_cons
  given: (n : Nat) (s : Stream' α) (x : α)
  statement: get (x :: s) n.succ = get s n
  proof: rfl

中文:
定理 get_succ_cons
  条件: (n : 自然数) (s : Stream' α) (x : α)
  结论: get (x :: s) n.succ = get s n
  证明: rfl
-/
theorem get_succ_cons (n : Nat) (s : Stream' α) (x : α) : get (x :: s) n.succ = get s n :=
  rfl

/--
lemma `get_cons_append_zero` / 引理 `get_cons_append_zero`

English:
lemma get_cons_append_zero
  given: {a : α} {x : List α} {s : Stream' α}
  proof: rfl

中文:
引理 get_cons_append_zero
  条件: {a : α} {x : 列表 α} {s : Stream' α}
  证明: rfl
-/
@[simp] lemma get_cons_append_zero {a : α} {x : List α} {s : Stream' α} :
    (a :: x ++ₛ s).get 0 = a := rfl

/--
lemma `append_eq_cons` / 引理 `append_eq_cons`

English:
lemma append_eq_cons
  given: {a : α} {as : Stream' α}
  statement: [a] ++ₛ as = a :: as
  proof: rfl

中文:
引理 append_eq_cons
  条件: {a : α} {as : Stream' α}
  结论: [a] ++ₛ as = a :: as
  证明: rfl
-/
@[simp] lemma append_eq_cons {a : α} {as : Stream' α} : [a] ++ₛ as = a :: as := rfl

/--
theorem `drop_zero` / 定理 `drop_zero`

English:
theorem drop_zero
  given: {s : Stream' α}
  statement: s.drop 0 = s
  proof: rfl

中文:
定理 drop_zero
  条件: {s : Stream' α}
  结论: s.drop 0 = s
  证明: rfl
-/
@[simp] theorem drop_zero {s : Stream' α} : s.drop 0 = s := rfl

/--
theorem `drop_succ` / 定理 `drop_succ`

English:
theorem drop_succ
  given: (n : Nat) (s : Stream' α)
  statement: drop (succ n) s = drop n (tail s)
  proof: rfl

中文:
定理 drop_succ
  条件: (n : 自然数) (s : Stream' α)
  结论: drop (succ n) s = drop n (tail s)
  证明: rfl
-/
theorem drop_succ (n : Nat) (s : Stream' α) : drop (succ n) s = drop n (tail s) :=
  rfl

/--
theorem `head_drop` / 定理 `head_drop`

English:
theorem head_drop
  given: (a : Stream' α) (n : Nat)
  statement: (a.drop n).head = a.get n
  proof: by simp

中文:
定理 head_drop
  条件: (a : Stream' α) (n : 自然数)
  结论: (a.drop n).head = a.get n
  证明: by simp
-/
theorem head_drop (a : Stream' α) (n : Nat) : (a.drop n).head = a.get n := by simp

/--
theorem `cons_injective2` / 定理 `cons_injective2`

English:
theorem cons_injective2
  statement: Function.Injective2 (cons : α -> Stream' α -> Stream' α)
  proof: fun x y s t h =>
  ⟨by rw [← get_zero_cons x s, h, get_zero_cons],
    Stream'.ext fun n => by rw [← get_succ_cons n _ x, h, get_succ_cons]⟩

中文:
定理 cons_injective2
  结论: 函数.Injective2 (cons : α -> Stream' α -> Stream' α)
  证明: fun x y s t h =>
  ⟨by rw [← get_zero_cons x s, h, get_zero_cons],
    Stream'.ext fun n => by rw [← get_succ_cons n _ x, h, get_succ_cons]⟩
-/
theorem cons_injective2 : Function.Injective2 (cons : α -> Stream' α -> Stream' α) := fun x y s t h =>
  ⟨by rw [← get_zero_cons x s, h, get_zero_cons],
    Stream'.ext fun n => by rw [← get_succ_cons n _ x, h, get_succ_cons]⟩

/--
theorem `cons_injective_left` / 定理 `cons_injective_left`

English:
theorem cons_injective_left
  given: (s : Stream' α)
  statement: Function.Injective fun x => cons x s
  proof: cons_injective2.left _

中文:
定理 cons_injective_left
  条件: (s : Stream' α)
  结论: 函数.单射 fun x => cons x s
  证明: cons_injective2.left _

Depends on / 依赖: cons_injective2, cons_injective2.left
-/
theorem cons_injective_left (s : Stream' α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _

/--
theorem `cons_injective_right` / 定理 `cons_injective_right`

English:
theorem cons_injective_right
  given: (x : α)
  statement: Function.Injective (cons x)
  proof: cons_injective2.right _

中文:
定理 cons_injective_right
  条件: (x : α)
  结论: 函数.单射 (cons x)
  证明: cons_injective2.right _

Depends on / 依赖: cons_injective2, cons_injective2.right
-/
theorem cons_injective_right (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _

/--
theorem `all_def` / 定理 `all_def`

English:
theorem all_def
  given: (p : α -> Prop) (s : Stream' α)
  statement: All p s = forall n, p (get s n)
  proof: rfl

中文:
定理 all_def
  条件: (p : α -> 命题) (s : Stream' α)
  结论: All p s = 对任意 n, p (get s n)
  证明: rfl
-/
theorem all_def (p : α -> Prop) (s : Stream' α) : All p s = forall n, p (get s n) :=
  rfl

/--
theorem `any_def` / 定理 `any_def`

English:
theorem any_def
  given: (p : α -> Prop) (s : Stream' α)
  statement: Any p s = exists n, p (get s n)
  proof: rfl

@[simp]

中文:
定理 any_def
  条件: (p : α -> 命题) (s : Stream' α)
  结论: Any p s = 存在 n, p (get s n)
  证明: rfl

@[simp]
-/
theorem any_def (p : α -> Prop) (s : Stream' α) : Any p s = exists n, p (get s n) :=
  rfl

@[simp]
/--
theorem `mem_cons` / 定理 `mem_cons`

English:
theorem mem_cons
  given: (a : α) (s : Stream' α)
  statement: a in a::s
  proof: Exists.intro 0 rfl

中文:
定理 mem_cons
  条件: (a : α) (s : Stream' α)
  结论: a in a::s
  证明: Exists.intro 0 rfl

Depends on / 依赖: Exists, Exists.intro
-/
theorem mem_cons (a : α) (s : Stream' α) : a in a::s :=
  Exists.intro 0 rfl

/--
theorem `mem_cons_of_mem` / 定理 `mem_cons_of_mem`

English:
theorem mem_cons_of_mem
  given: {a : α} {s : Stream' α} (b : α)
  statement: a in s -> a in b::s
  proof: fun ⟨n, h⟩ =>
  Exists.intro (succ n) (by rw [get_succ, tail_cons, h])

中文:
定理 mem_cons_of_mem
  条件: {a : α} {s : Stream' α} (b : α)
  结论: a in s -> a in b::s
  证明: fun ⟨n, h⟩ =>
  Exists.intro (succ n) (by rw [get_succ, tail_cons, h])
-/
theorem mem_cons_of_mem {a : α} {s : Stream' α} (b : α) : a in s -> a in b::s := fun ⟨n, h⟩ =>
  Exists.intro (succ n) (by rw [get_succ, tail_cons, h])

/--
theorem `eq_or_mem_of_mem_cons` / 定理 `eq_or_mem_of_mem_cons`

English:
theorem eq_or_mem_of_mem_cons
  given: {a b : α} {s : Stream' α}
  statement: (a in b::s) -> a = b ∨ a in s
  proof: fun ⟨n, h⟩ => by
  rcases n with - | n'
  · left
    exact h
  · right
    rw [get_succ]; rw [tail_cons] at h
    exact ⟨n', h⟩

中文:
定理 eq_or_mem_of_mem_cons
  条件: {a b : α} {s : Stream' α}
  结论: (a in b::s) -> a = b ∨ a in s
  证明: fun ⟨n, h⟩ => by
  rcases n with - | n'
  · left
    exact h
  · right
    rw [get_succ]; rw [tail_cons] at h
    exact ⟨n', h⟩

Depends on / 依赖: get_succ, tail_cons
-/
theorem eq_or_mem_of_mem_cons {a b : α} {s : Stream' α} : (a in b::s) -> a = b ∨ a in s :=
    fun ⟨n, h⟩ => by
  rcases n with - | n'
  · left
    exact h
  · right
    rw [get_succ]; rw [tail_cons] at h
    exact ⟨n', h⟩

/--
theorem `mem_of_get_eq` / 定理 `mem_of_get_eq`

English:
theorem mem_of_get_eq
  given: {n : Nat} {s : Stream' α} {a : α}
  statement: a = get s n -> a in s
  proof: fun h =>
  Exists.intro n h

中文:
定理 mem_of_get_eq
  条件: {n : 自然数} {s : Stream' α} {a : α}
  结论: a = get s n -> a in s
  证明: fun h =>
  Exists.intro n h
-/
theorem mem_of_get_eq {n : Nat} {s : Stream' α} {a : α} : a = get s n -> a in s := fun h =>
  Exists.intro n h

/--
theorem `mem_iff_exists_get_eq` / 定理 `mem_iff_exists_get_eq`

English:
theorem mem_iff_exists_get_eq
  given: {s : Stream' α} {a : α}
  statement: a in s ↔ exists n, a = s.get n where
  proof: by simp [Membership.mem, any_def]
  mpr h := mem_of_get_eq h.choose_spec

中文:
定理 mem_iff_存在_get_eq
  条件: {s : Stream' α} {a : α}
  结论: a in s ↔ 存在 n, a = s.get n where
  证明: by simp [Membership.mem, any_def]
  mpr h := mem_of_get_eq h.choose_spec

Depends on / 依赖: Membership, Membership.mem, any_def, choose_spec, h.choose_spec, mem_of_get_eq
-/
theorem mem_iff_exists_get_eq {s : Stream' α} {a : α} : a in s ↔ exists n, a = s.get n where
  mp := by simp [Membership.mem, any_def]
  mpr h := mem_of_get_eq h.choose_spec

section Map

variable (f : α -> β)

/--
theorem `drop_map` / 定理 `drop_map`

English:
theorem drop_map
  given: (n : Nat) (s : Stream' α)
  statement: drop n (map f s) = map f (drop n s)
  proof: Stream'.ext fun _ => rfl

@[simp]

中文:
定理 drop_map
  条件: (n : 自然数) (s : Stream' α)
  结论: drop n (map f s) = map f (drop n s)
  证明: Stream'.ext fun _ => rfl

@[simp]

Depends on / 依赖: Stream
-/
theorem drop_map (n : Nat) (s : Stream' α) : drop n (map f s) = map f (drop n s) :=
  Stream'.ext fun _ => rfl

@[simp]
/--
theorem `get_map` / 定理 `get_map`

English:
theorem get_map
  given: (n : Nat) (s : Stream' α)
  statement: get (map f s) n = f (get s n)
  proof: rfl

中文:
定理 get_map
  条件: (n : 自然数) (s : Stream' α)
  结论: get (map f s) n = f (get s n)
  证明: rfl
-/
theorem get_map (n : Nat) (s : Stream' α) : get (map f s) n = f (get s n) :=
  rfl

/--
theorem `tail_map` / 定理 `tail_map`

English:
theorem tail_map
  given: (s : Stream' α)
  statement: tail (map f s) = map f (tail s)
  proof: rfl

@[simp]

中文:
定理 tail_map
  条件: (s : Stream' α)
  结论: tail (map f s) = map f (tail s)
  证明: rfl

@[simp]
-/
theorem tail_map (s : Stream' α) : tail (map f s) = map f (tail s) := rfl

@[simp]
/--
theorem `head_map` / 定理 `head_map`

English:
theorem head_map
  given: (s : Stream' α)
  statement: head (map f s) = f (head s)
  proof: rfl

中文:
定理 head_map
  条件: (s : Stream' α)
  结论: head (map f s) = f (head s)
  证明: rfl
-/
theorem head_map (s : Stream' α) : head (map f s) = f (head s) :=
  rfl

/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  given: (s : Stream' α)
  statement: map f s = f (head s)::map f (tail s)
  proof: by
  rw [← Stream'.eta (map f s)]; rw [tail_map]; rw [head_map]

中文:
定理 map_eq
  条件: (s : Stream' α)
  结论: map f s = f (head s)::map f (tail s)
  证明: by
  rw [← Stream'.eta (map f s)]; rw [tail_map]; rw [head_map]

Depends on / 依赖: Stream, head_map, tail_map
-/
theorem map_eq (s : Stream' α) : map f s = f (head s)::map f (tail s) := by
  rw [← Stream'.eta (map f s)]; rw [tail_map]; rw [head_map]

/--
theorem `map_cons` / 定理 `map_cons`

English:
theorem map_cons
  given: (a : α) (s : Stream' α)
  statement: map f (a::s) = f a::map f s
  proof: by
  rw [← Stream'.eta (map f (a::s))]; rw [map_eq]; rfl

@[simp]

中文:
定理 map_cons
  条件: (a : α) (s : Stream' α)
  结论: map f (a::s) = f a::map f s
  证明: by
  rw [← Stream'.eta (map f (a::s))]; rw [map_eq]; rfl

@[simp]

Depends on / 依赖: Stream, map_eq
-/
theorem map_cons (a : α) (s : Stream' α) : map f (a::s) = f a::map f s := by
  rw [← Stream'.eta (map f (a::s))]; rw [map_eq]; rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (s : Stream' α)
  statement: map id s = s
  proof: rfl

@[simp]

中文:
定理 map_id
  条件: (s : Stream' α)
  结论: map id s = s
  证明: rfl

@[simp]
-/
theorem map_id (s : Stream' α) : map id s = s :=
  rfl

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : β -> δ) (f : α -> β) (s : Stream' α)
  statement: map g (map f s) = map (g ∘ f) s
  proof: rfl

@[simp]

中文:
定理 map_map
  条件: (g : β -> δ) (f : α -> β) (s : Stream' α)
  结论: map g (map f s) = map (g ∘ f) s
  证明: rfl

@[simp]
-/
theorem map_map (g : β -> δ) (f : α -> β) (s : Stream' α) : map g (map f s) = map (g ∘ f) s :=
  rfl

@[simp]
/--
theorem `map_tail` / 定理 `map_tail`

English:
theorem map_tail
  given: (s : Stream' α)
  statement: map f (tail s) = tail (map f s)
  proof: rfl

中文:
定理 map_tail
  条件: (s : Stream' α)
  结论: map f (tail s) = tail (map f s)
  证明: rfl
-/
theorem map_tail (s : Stream' α) : map f (tail s) = tail (map f s) :=
  rfl

/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {a : α} {s : Stream' α}
  statement: a in s -> f a in map f s
  proof: fun ⟨n, h⟩ =>
  Exists.intro n (by rw [get_map, h])

中文:
定理 mem_map
  条件: {a : α} {s : Stream' α}
  结论: a in s -> f a in map f s
  证明: fun ⟨n, h⟩ =>
  Exists.intro n (by rw [get_map, h])
-/
theorem mem_map {a : α} {s : Stream' α} : a in s -> f a in map f s := fun ⟨n, h⟩ =>
  Exists.intro n (by rw [get_map, h])

/--
theorem `exists_of_mem_map` / 定理 `exists_of_mem_map`

English:
theorem exists_of_mem_map
  given: {f} {b : β} {s : Stream' α}
  statement: b in map f s -> exists a, a in s ∧ f a = b
  proof: fun ⟨n, h⟩ => ⟨get s n, ⟨n, rfl⟩, h.symm⟩

中文:
定理 存在_of_mem_map
  条件: {f} {b : β} {s : Stream' α}
  结论: b in map f s -> 存在 a, a in s ∧ f a = b
  证明: fun ⟨n, h⟩ => ⟨get s n, ⟨n, rfl⟩, h.symm⟩

Depends on / 依赖: h.symm
-/
theorem exists_of_mem_map {f} {b : β} {s : Stream' α} : b in map f s -> exists a, a in s ∧ f a = b :=
  fun ⟨n, h⟩ => ⟨get s n, ⟨n, rfl⟩, h.symm⟩

end Map

section Zip

variable (f : α -> β -> δ)

/--
theorem `drop_zip` / 定理 `drop_zip`

English:
theorem drop_zip
  given: (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β)
  proof: Stream'.ext fun _ => rfl

@[simp]

中文:
定理 drop_zip
  条件: (n : 自然数) (s₁ : Stream' α) (s₂ : Stream' β)
  证明: Stream'.ext fun _ => rfl

@[simp]

Depends on / 依赖: Stream
-/
theorem drop_zip (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β) :
    drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
  Stream'.ext fun _ => rfl

@[simp]
/--
theorem `get_zip` / 定理 `get_zip`

English:
theorem get_zip
  given: (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β)
  proof: rfl

中文:
定理 get_zip
  条件: (n : 自然数) (s₁ : Stream' α) (s₂ : Stream' β)
  证明: rfl
-/
theorem get_zip (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β) :
    get (zip f s₁ s₂) n = f (get s₁ n) (get s₂ n) :=
  rfl

/--
theorem `head_zip` / 定理 `head_zip`

English:
theorem head_zip
  given: (s₁ : Stream' α) (s₂ : Stream' β)
  statement: head (zip f s₁ s₂) = f (head s₁) (head s₂)
  proof: rfl

中文:
定理 head_zip
  条件: (s₁ : Stream' α) (s₂ : Stream' β)
  结论: head (zip f s₁ s₂) = f (head s₁) (head s₂)
  证明: rfl
-/
theorem head_zip (s₁ : Stream' α) (s₂ : Stream' β) : head (zip f s₁ s₂) = f (head s₁) (head s₂) :=
  rfl

/--
theorem `tail_zip` / 定理 `tail_zip`

English:
theorem tail_zip
  given: (s₁ : Stream' α) (s₂ : Stream' β)
  proof: rfl

中文:
定理 tail_zip
  条件: (s₁ : Stream' α) (s₂ : Stream' β)
  证明: rfl
-/
theorem tail_zip (s₁ : Stream' α) (s₂ : Stream' β) :
    tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) :=
  rfl

/--
theorem `zip_eq` / 定理 `zip_eq`

English:
theorem zip_eq
  given: (s₁ : Stream' α) (s₂ : Stream' β)
  proof: by
  rw [← Stream'.eta (zip f s₁ s₂)]; rfl

@[simp]

中文:
定理 zip_eq
  条件: (s₁ : Stream' α) (s₂ : Stream' β)
  证明: by
  rw [← Stream'.eta (zip f s₁ s₂)]; rfl

@[simp]

Depends on / 依赖: Stream
-/
theorem zip_eq (s₁ : Stream' α) (s₂ : Stream' β) :
    zip f s₁ s₂ = f (head s₁) (head s₂)::zip f (tail s₁) (tail s₂) := by
  rw [← Stream'.eta (zip f s₁ s₂)]; rfl

@[simp]
/--
theorem `get_enum` / 定理 `get_enum`

English:
theorem get_enum
  given: (s : Stream' α) (n : Nat)
  statement: get (enum s) n = (n, s.get n)
  proof: rfl

中文:
定理 get_enum
  条件: (s : Stream' α) (n : 自然数)
  结论: get (enum s) n = (n, s.get n)
  证明: rfl
-/
theorem get_enum (s : Stream' α) (n : Nat) : get (enum s) n = (n, s.get n) :=
  rfl

/--
theorem `enum_eq_zip` / 定理 `enum_eq_zip`

English:
theorem enum_eq_zip
  given: (s : Stream' α)
  statement: enum s = zip Prod.mk nats s
  proof: rfl

中文:
定理 enum_eq_zip
  条件: (s : Stream' α)
  结论: enum s = zip 积类型.mk nats s
  证明: rfl
-/
theorem enum_eq_zip (s : Stream' α) : enum s = zip Prod.mk nats s :=
  rfl

end Zip

@[simp]
/--
theorem `mem_const` / 定理 `mem_const`

English:
theorem mem_const
  given: (a : α)
  statement: a in const a
  proof: Exists.intro 0 rfl

中文:
定理 mem_const
  条件: (a : α)
  结论: a in const a
  证明: Exists.intro 0 rfl

Depends on / 依赖: Exists, Exists.intro
-/
theorem mem_const (a : α) : a in const a :=
  Exists.intro 0 rfl

/--
theorem `const_eq` / 定理 `const_eq`

English:
theorem const_eq
  given: (a : α)
  statement: const a = a::const a
  proof: by
  apply Stream'.ext; intro n
  cases n <;> rfl

@[simp]

中文:
定理 const_eq
  条件: (a : α)
  结论: const a = a::const a
  证明: by
  apply Stream'.ext; intro n
  cases n <;> rfl

@[simp]

Depends on / 依赖: Stream
-/
theorem const_eq (a : α) : const a = a::const a := by
  apply Stream'.ext; intro n
  cases n <;> rfl

@[simp]
/--
theorem `tail_const` / 定理 `tail_const`

English:
theorem tail_const
  given: (a : α)
  statement: tail (const a) = const a
  proof: suffices tail (a::const a) = const a by rwa [← const_eq] at this
  rfl

@[simp]

中文:
定理 tail_const
  条件: (a : α)
  结论: tail (const a) = const a
  证明: suffices tail (a::const a) = const a by rwa [← const_eq] at this
  rfl

@[simp]

Depends on / 依赖: const_eq
-/
theorem tail_const (a : α) : tail (const a) = const a :=
  suffices tail (a::const a) = const a by rwa [← const_eq] at this
  rfl

@[simp]
/--
theorem `map_const` / 定理 `map_const`

English:
theorem map_const
  given: (f : α -> β) (a : α)
  statement: map f (const a) = const (f a)
  proof: rfl

@[simp]

中文:
定理 map_const
  条件: (f : α -> β) (a : α)
  结论: map f (const a) = const (f a)
  证明: rfl

@[simp]
-/
theorem map_const (f : α -> β) (a : α) : map f (const a) = const (f a) :=
  rfl

@[simp]
/--
theorem `get_const` / 定理 `get_const`

English:
theorem get_const
  given: (n : Nat) (a : α)
  statement: get (const a) n = a
  proof: rfl

@[simp]

中文:
定理 get_const
  条件: (n : 自然数) (a : α)
  结论: get (const a) n = a
  证明: rfl

@[simp]
-/
theorem get_const (n : Nat) (a : α) : get (const a) n = a :=
  rfl

@[simp]
/--
theorem `drop_const` / 定理 `drop_const`

English:
theorem drop_const
  given: (n : Nat) (a : α)
  statement: drop n (const a) = const a
  proof: Stream'.ext fun _ => rfl

@[simp]

中文:
定理 drop_const
  条件: (n : 自然数) (a : α)
  结论: drop n (const a) = const a
  证明: Stream'.ext fun _ => rfl

@[simp]

Depends on / 依赖: Stream
-/
theorem drop_const (n : Nat) (a : α) : drop n (const a) = const a :=
  Stream'.ext fun _ => rfl

@[simp]
/--
theorem `head_iterate` / 定理 `head_iterate`

English:
theorem head_iterate
  given: (f : α -> α) (a : α)
  statement: head (iterate f a) = a
  proof: rfl

中文:
定理 head_iterate
  条件: (f : α -> α) (a : α)
  结论: head (iterate f a) = a
  证明: rfl
-/
theorem head_iterate (f : α -> α) (a : α) : head (iterate f a) = a :=
  rfl

/--
theorem `get_succ_iterate'` / 定理 `get_succ_iterate'`

English:
theorem get_succ_iterate'
  given: (n : Nat) (f : α -> α) (a : α)
  proof: rfl

中文:
定理 get_succ_iterate'
  条件: (n : 自然数) (f : α -> α) (a : α)
  证明: rfl
-/
theorem get_succ_iterate' (n : Nat) (f : α -> α) (a : α) :
    get (iterate f a) (succ n) = f (get (iterate f a) n) := rfl

/--
theorem `tail_iterate` / 定理 `tail_iterate`

English:
theorem tail_iterate
  given: (f : α -> α) (a : α)
  statement: tail (iterate f a) = iterate f (f a)
  proof: by
  ext n
  rw [get_tail]
  induction n with
  | zero => rfl
  | succ n ih => rw [get_succ_iterate', ih, get_succ_iterate']

中文:
定理 tail_iterate
  条件: (f : α -> α) (a : α)
  结论: tail (iterate f a) = iterate f (f a)
  证明: by
  ext n
  rw [get_tail]
  induction n with
  | zero => rfl
  | succ n ih => rw [get_succ_iterate', ih, get_succ_iterate']

Depends on / 依赖: get_succ_iterate, get_tail
-/
theorem tail_iterate (f : α -> α) (a : α) : tail (iterate f a) = iterate f (f a) := by
  ext n
  rw [get_tail]
  induction n with
  | zero => rfl
  | succ n ih => rw [get_succ_iterate', ih, get_succ_iterate']

/--
theorem `iterate_eq` / 定理 `iterate_eq`

English:
theorem iterate_eq
  given: (f : α -> α) (a : α)
  statement: iterate f a = a::iterate f (f a)
  proof: by
  rw [← Stream'.eta (iterate f a)]
  rw [tail_iterate]; rfl

@[simp]

中文:
定理 iterate_eq
  条件: (f : α -> α) (a : α)
  结论: iterate f a = a::iterate f (f a)
  证明: by
  rw [← Stream'.eta (iterate f a)]
  rw [tail_iterate]; rfl

@[simp]

Depends on / 依赖: Stream, iterate, tail_iterate
-/
theorem iterate_eq (f : α -> α) (a : α) : iterate f a = a::iterate f (f a) := by
  rw [← Stream'.eta (iterate f a)]
  rw [tail_iterate]; rfl

@[simp]
/--
theorem `get_zero_iterate` / 定理 `get_zero_iterate`

English:
theorem get_zero_iterate
  given: (f : α -> α) (a : α)
  statement: get (iterate f a) 0 = a
  proof: rfl

中文:
定理 get_zero_iterate
  条件: (f : α -> α) (a : α)
  结论: get (iterate f a) 0 = a
  证明: rfl
-/
theorem get_zero_iterate (f : α -> α) (a : α) : get (iterate f a) 0 = a :=
  rfl

/--
theorem `get_succ_iterate` / 定理 `get_succ_iterate`

English:
theorem get_succ_iterate
  given: (n : Nat) (f : α -> α) (a : α)
  proof: by rw [get_succ, tail_iterate]

中文:
定理 get_succ_iterate
  条件: (n : 自然数) (f : α -> α) (a : α)
  证明: by rw [get_succ, tail_iterate]

Depends on / 依赖: get_succ, tail_iterate
-/
theorem get_succ_iterate (n : Nat) (f : α -> α) (a : α) :
    get (iterate f a) (succ n) = get (iterate f (f a)) n := by rw [get_succ, tail_iterate]

section Bisim

variable (R : Stream' α -> Stream' α -> Prop)

/-- equivalence relation -/
local infixl:50 " ~ " => R

/--
Definition of `IsBisimulation` / `IsBisimulation` 的定义

English:
definition IsBisimulation
  body: forall ⦃s₁ s₂⦄, s₁ ~ s₂ ->
      head s₁ = head s₂ ∧ tail s₁ ~ tail s₂

中文:
定义 是Bisimulation
  定义体: forall ⦃s₁ s₂⦄, s₁ ~ s₂ ->
      head s₁ = head s₂ ∧ tail s₁ ~ tail s₂
-/
def IsBisimulation :=
  forall ⦃s₁ s₂⦄, s₁ ~ s₂ ->
      head s₁ = head s₂ ∧ tail s₁ ~ tail s₂

/--
theorem `get_of_bisim` / 定理 `get_of_bisim`

English:
theorem get_of_bisim
  given: (bisim : IsBisimulation R) {s₁ s₂}

中文:
定理 get_of_bisim
  条件: (bisim : 是Bisimulation R) {s₁ s₂}
-/
theorem get_of_bisim (bisim : IsBisimulation R) {s₁ s₂} :
    forall n, s₁ ~ s₂ -> get s₁ n = get s₂ n ∧ drop (n + 1) s₁ ~ drop (n + 1) s₂
  | 0, h => bisim h
  | n + 1, h =>
    match bisim h with
    | ⟨_, trel⟩ => get_of_bisim bisim n trel

-- If two streams are bisimilar, then they are equal
/--
theorem `eq_of_bisim` / 定理 `eq_of_bisim`

English:
theorem eq_of_bisim
  given: (bisim : IsBisimulation R) {s₁ s₂}
  statement: s₁ ~ s₂ -> s₁ = s₂
  proof: fun r =>
  Stream'.ext fun n => And.left (get_of_bisim R bisim n r)

中文:
定理 eq_of_bisim
  条件: (bisim : 是Bisimulation R) {s₁ s₂}
  结论: s₁ ~ s₂ -> s₁ = s₂
  证明: fun r =>
  Stream'.ext fun n => And.left (get_of_bisim R bisim n r)
-/
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} : s₁ ~ s₂ -> s₁ = s₂ := fun r =>
  Stream'.ext fun n => And.left (get_of_bisim R bisim n r)

end Bisim

/--
theorem `bisim_simple` / 定理 `bisim_simple`

English:
theorem bisim_simple
  given: (s₁ s₂ : Stream' α)
  proof: fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by grind)
    (And.intro hh (And.intro ht₁ ht₂))

中文:
定理 bisim_simple
  条件: (s₁ s₂ : Stream' α)
  证明: fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by grind)
    (And.intro hh (And.intro ht₁ ht₂))
-/
theorem bisim_simple (s₁ s₂ : Stream' α) :
    head s₁ = head s₂ -> s₁ = tail s₁ -> s₂ = tail s₂ -> s₁ = s₂ := fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by grind)
    (And.intro hh (And.intro ht₁ ht₂))

/--
theorem `coinduction` / 定理 `coinduction`

English:
theorem coinduction
  given: {s₁ s₂ : Stream' α}
  proof: fun hh ht =>
  eq_of_bisim
    (fun s₁ s₂ =>
      head s₁ = head s₂ ∧
        forall (β : Type u) (fr : Stream' α -> β), fr s₁ = fr s₂ -> fr (tail s₁) = fr (tail s₂))
    (fun s₁ s₂ h =>
      have h₁ : head s₁ = head s₂ := And.left h
      have h₂ : head (tail s₁) = head (tail s₂) := And.right h α

中文:
定理 coinduction
  条件: {s₁ s₂ : Stream' α}
  证明: fun hh ht =>
  eq_of_bisim
    (fun s₁ s₂ =>
      head s₁ = head s₂ ∧
        forall (β : Type u) (fr : Stream' α -> β), fr s₁ = fr s₂ -> fr (tail s₁) = fr (tail s₂))
    (fun s₁ s₂ h =>
      have h₁ : head s₁ = head s₂ := And.left h
      have h₂ : head (tail s₁) = head (tail s₂) := And.right h α

Depends on / 依赖: And.intro, And.left, And.right, Stream, eq_of_bisim
-/
theorem coinduction {s₁ s₂ : Stream' α} :
    head s₁ = head s₂ ->
      (forall (β : Type u) (fr : Stream' α -> β),
      fr s₁ = fr s₂ -> fr (tail s₁) = fr (tail s₂)) -> s₁ = s₂ :=
  fun hh ht =>
  eq_of_bisim
    (fun s₁ s₂ =>
      head s₁ = head s₂ ∧
        forall (β : Type u) (fr : Stream' α -> β), fr s₁ = fr s₂ -> fr (tail s₁) = fr (tail s₂))
    (fun s₁ s₂ h =>
      have h₁ : head s₁ = head s₂ := And.left h
      have h₂ : head (tail s₁) = head (tail s₂) := And.right h α (@head α) h₁
      have h₃ :
        forall (β : Type u) (fr : Stream' α -> β),
          fr (tail s₁) = fr (tail s₂) -> fr (tail (tail s₁)) = fr (tail (tail s₂)) :=
        fun β fr => And.right h β fun s => fr (tail s)
      And.intro h₁ (And.intro h₂ h₃))
    (And.intro hh ht)

@[simp]
/--
theorem `iterate_id` / 定理 `iterate_id`

English:
theorem iterate_id
  given: (a : α)
  statement: iterate id a = const a
  proof: coinduction rfl fun β fr ch => by rw [tail_iterate, tail_const]; exact ch

中文:
定理 iterate_id
  条件: (a : α)
  结论: iterate id a = const a
  证明: coinduction rfl fun β fr ch => by rw [tail_iterate, tail_const]; exact ch

Depends on / 依赖: coinduction, tail_const, tail_iterate
-/
theorem iterate_id (a : α) : iterate id a = const a :=
  coinduction rfl fun β fr ch => by rw [tail_iterate, tail_const]; exact ch

/--
theorem `map_iterate` / 定理 `map_iterate`

English:
theorem map_iterate
  given: (f : α -> α) (a : α)
  statement: iterate f (f a) = map f (iterate f a)
  proof: by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold map iterate get
    rw [map]; rw [get] at ih
    rw [iterate]
    exact congrArg f ih

中文:
定理 map_iterate
  条件: (f : α -> α) (a : α)
  结论: iterate f (f a) = map f (iterate f a)
  证明: by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold map iterate get
    rw [map]; rw [get] at ih
    rw [iterate]
    exact congrArg f ih

Depends on / 依赖: iterate
-/
theorem map_iterate (f : α -> α) (a : α) : iterate f (f a) = map f (iterate f a) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold map iterate get
    rw [map]; rw [get] at ih
    rw [iterate]
    exact congrArg f ih

section Corec

/--
theorem `corec_def` / 定理 `corec_def`

English:
theorem corec_def
  given: (f : α -> β) (g : α -> α) (a : α)
  statement: corec f g a = map f (iterate g a)
  proof: rfl

中文:
定理 corec_def
  条件: (f : α -> β) (g : α -> α) (a : α)
  结论: corec f g a = map f (iterate g a)
  证明: rfl
-/
theorem corec_def (f : α -> β) (g : α -> α) (a : α) : corec f g a = map f (iterate g a) :=
  rfl

/--
theorem `corec_eq` / 定理 `corec_eq`

English:
theorem corec_eq
  given: (f : α -> β) (g : α -> α) (a : α)
  statement: corec f g a = f a :: corec f g (g a)
  proof: by
  rw [corec_def]; rw [map_eq]; rw [head_iterate]; rw [tail_iterate]; rfl

中文:
定理 corec_eq
  条件: (f : α -> β) (g : α -> α) (a : α)
  结论: corec f g a = f a :: corec f g (g a)
  证明: by
  rw [corec_def]; rw [map_eq]; rw [head_iterate]; rw [tail_iterate]; rfl

Depends on / 依赖: corec_def, head_iterate, map_eq, tail_iterate
-/
theorem corec_eq (f : α -> β) (g : α -> α) (a : α) : corec f g a = f a :: corec f g (g a) := by
  rw [corec_def]; rw [map_eq]; rw [head_iterate]; rw [tail_iterate]; rfl

/--
theorem `corec_id_id_eq_const` / 定理 `corec_id_id_eq_const`

English:
theorem corec_id_id_eq_const
  given: (a : α)
  statement: corec id id a = const a
  proof: by
  rw [corec_def]; rw [map_id]; rw [iterate_id]

中文:
定理 corec_id_id_eq_const
  条件: (a : α)
  结论: corec id id a = const a
  证明: by
  rw [corec_def]; rw [map_id]; rw [iterate_id]

Depends on / 依赖: corec_def, iterate_id, map_id
-/
theorem corec_id_id_eq_const (a : α) : corec id id a = const a := by
  rw [corec_def]; rw [map_id]; rw [iterate_id]

/--
theorem `corec_id_f_eq_iterate` / 定理 `corec_id_f_eq_iterate`

English:
theorem corec_id_f_eq_iterate
  given: (f : α -> α) (a : α)
  statement: corec id f a = iterate f a
  proof: rfl

中文:
定理 corec_id_f_eq_iterate
  条件: (f : α -> α) (a : α)
  结论: corec id f a = iterate f a
  证明: rfl
-/
theorem corec_id_f_eq_iterate (f : α -> α) (a : α) : corec id f a = iterate f a :=
  rfl

end Corec

section Corec'

/--
theorem `corec'_eq` / 定理 `corec'_eq`

English:
theorem corec'_eq
  given: (f : α -> β × α) (a : α)
  statement: corec' f a = (f a).1 :: corec' f (f a).2
  proof: corec_eq _ _ _

中文:
定理 corec'_eq
  条件: (f : α -> β × α) (a : α)
  结论: corec' f a = (f a).1 :: corec' f (f a).2
  证明: corec_eq _ _ _
-/
theorem corec'_eq (f : α -> β × α) (a : α) : corec' f a = (f a).1 :: corec' f (f a).2 :=
  corec_eq _ _ _

end Corec'

/--
theorem `unfolds_eq` / 定理 `unfolds_eq`

English:
theorem unfolds_eq
  given: (g : α -> β) (f : α -> α) (a : α)
  statement: unfolds g f a = g a :: unfolds g f (f a)
  proof: by
  unfold unfolds; rw [corec_eq]

中文:
定理 unfolds_eq
  条件: (g : α -> β) (f : α -> α) (a : α)
  结论: unfolds g f a = g a :: unfolds g f (f a)
  证明: by
  unfold unfolds; rw [corec_eq]

Depends on / 依赖: corec_eq, unfolds
-/
theorem unfolds_eq (g : α -> β) (f : α -> α) (a : α) : unfolds g f a = g a :: unfolds g f (f a) := by
  unfold unfolds; rw [corec_eq]

/--
theorem `get_unfolds_head_tail` / 定理 `get_unfolds_head_tail`

English:
theorem get_unfolds_head_tail
  given: (n : Nat) (s : Stream' α)
  statement: get (unfolds head tail s) n = get s n
  proof: by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, get_succ, unfolds_eq, tail_cons, ih]

中文:
定理 get_unfolds_head_tail
  条件: (n : 自然数) (s : Stream' α)
  结论: get (unfolds head tail s) n = get s n
  证明: by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, get_succ, unfolds_eq, tail_cons, ih]

Depends on / 依赖: generalizing, get_succ, tail_cons, unfolds_eq
-/
theorem get_unfolds_head_tail (n : Nat) (s : Stream' α) : get (unfolds head tail s) n = get s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, get_succ, unfolds_eq, tail_cons, ih]

/--
theorem `unfolds_head_eq` / 定理 `unfolds_head_eq`

English:
theorem unfolds_head_eq
  statement: forall s : Stream' α, unfolds head tail s = s
  proof: fun s =>
  Stream'.ext fun n => get_unfolds_head_tail n s

中文:
定理 unfolds_head_eq
  结论: 对任意 s : Stream' α, unfolds head tail s = s
  证明: fun s =>
  Stream'.ext fun n => get_unfolds_head_tail n s
-/
theorem unfolds_head_eq : forall s : Stream' α, unfolds head tail s = s := fun s =>
  Stream'.ext fun n => get_unfolds_head_tail n s

/--
theorem `interleave_eq` / 定理 `interleave_eq`

English:
theorem interleave_eq
  given: (s₁ s₂ : Stream' α)
  statement: s₁ ⋈ s₂ = head s₁::head s₂::(tail s₁ ⋈ tail s₂)
  proof: by
  let t := tail s₁ ⋈ tail s₂
  change s₁ ⋈ s₂ = head s₁::head s₂::t
  unfold interleave; unfold corecOn; rw [corec_eq]; dsimp; rw [corec_eq]; rfl

中文:
定理 interleave_eq
  条件: (s₁ s₂ : Stream' α)
  结论: s₁ ⋈ s₂ = head s₁::head s₂::(tail s₁ ⋈ tail s₂)
  证明: by
  let t := tail s₁ ⋈ tail s₂
  change s₁ ⋈ s₂ = head s₁::head s₂::t
  unfold interleave; unfold corecOn; rw [corec_eq]; dsimp; rw [corec_eq]; rfl

Depends on / 依赖: corecOn, corec_eq, interleave
-/
theorem interleave_eq (s₁ s₂ : Stream' α) : s₁ ⋈ s₂ = head s₁::head s₂::(tail s₁ ⋈ tail s₂) := by
  let t := tail s₁ ⋈ tail s₂
  change s₁ ⋈ s₂ = head s₁::head s₂::t
  unfold interleave; unfold corecOn; rw [corec_eq]; dsimp; rw [corec_eq]; rfl

/--
theorem `tail_interleave` / 定理 `tail_interleave`

English:
theorem tail_interleave
  given: (s₁ s₂ : Stream' α)
  statement: tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁
  proof: by
  unfold interleave corecOn; rw [corec_eq]; rfl

中文:
定理 tail_interleave
  条件: (s₁ s₂ : Stream' α)
  结论: tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁
  证明: by
  unfold interleave corecOn; rw [corec_eq]; rfl

Depends on / 依赖: corecOn, corec_eq, interleave
-/
theorem tail_interleave (s₁ s₂ : Stream' α) : tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁ := by
  unfold interleave corecOn; rw [corec_eq]; rfl

/--
theorem `interleave_tail_tail` / 定理 `interleave_tail_tail`

English:
theorem interleave_tail_tail
  given: (s₁ s₂ : Stream' α)
  statement: tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂))
  proof: by
  rw [interleave_eq s₁ s₂]; rfl

中文:
定理 interleave_tail_tail
  条件: (s₁ s₂ : Stream' α)
  结论: tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂))
  证明: by
  rw [interleave_eq s₁ s₂]; rfl

Depends on / 依赖: interleave_eq
-/
theorem interleave_tail_tail (s₁ s₂ : Stream' α) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) := by
  rw [interleave_eq s₁ s₂]; rfl

/--
theorem `get_interleave_left` / 定理 `get_interleave_left`

English:
theorem get_interleave_left
  statement: forall (n : Nat) (s₁ s₂ : Stream' α),

中文:
定理 get_interleave_left
  结论: 对任意 (n : 自然数) (s₁ s₂ : Stream' α),
-/
theorem get_interleave_left : forall (n : Nat) (s₁ s₂ : Stream' α),
    get (s₁ ⋈ s₂) (2 * n) = get s₁ n
  | 0, _, _ => rfl
  | n + 1, s₁, s₂ => by
    change get (s₁ ⋈ s₂) (succ (succ (2 * n))) = get s₁ (succ n)
    rw [get_succ]; rw [get_succ]; rw [interleave_eq]; rw [tail_cons]; rw [tail_cons]
    rw [get_interleave_left n (tail s₁) (tail s₂)]
    rfl

/--
theorem `get_interleave_right` / 定理 `get_interleave_right`

English:
theorem get_interleave_right
  statement: forall (n : Nat) (s₁ s₂ : Stream' α),

中文:
定理 get_interleave_right
  结论: 对任意 (n : 自然数) (s₁ s₂ : Stream' α),
-/
theorem get_interleave_right : forall (n : Nat) (s₁ s₂ : Stream' α),
    get (s₁ ⋈ s₂) (2 * n + 1) = get s₂ n
  | 0, _, _ => rfl
  | n + 1, s₁, s₂ => by
    change get (s₁ ⋈ s₂) (succ (succ (2 * n + 1))) = get s₂ (succ n)
    rw [get_succ]; rw [get_succ]; rw [interleave_eq]; rw [tail_cons]; rw [tail_cons]; rw [get_interleave_right n (tail s₁) (tail s₂)]
    rfl

/--
theorem `mem_interleave_left` / 定理 `mem_interleave_left`

English:
theorem mem_interleave_left
  given: {a : α} {s₁ : Stream' α} (s₂ : Stream' α)
  statement: a in s₁ -> a in s₁ ⋈ s₂
  proof: fun ⟨n, h⟩ => Exists.intro (2 * n) (by rw [h, get_interleave_left])

中文:
定理 mem_interleave_left
  条件: {a : α} {s₁ : Stream' α} (s₂ : Stream' α)
  结论: a in s₁ -> a in s₁ ⋈ s₂
  证明: fun ⟨n, h⟩ => Exists.intro (2 * n) (by rw [h, get_interleave_left])

Depends on / 依赖: Exists, Exists.intro, get_interleave_left
-/
theorem mem_interleave_left {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a in s₁ -> a in s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n) (by rw [h, get_interleave_left])

/--
theorem `mem_interleave_right` / 定理 `mem_interleave_right`

English:
theorem mem_interleave_right
  given: {a : α} {s₁ : Stream' α} (s₂ : Stream' α)
  statement: a in s₂ -> a in s₁ ⋈ s₂
  proof: fun ⟨n, h⟩ => Exists.intro (2 * n + 1) (by rw [h, get_interleave_right])

中文:
定理 mem_interleave_right
  条件: {a : α} {s₁ : Stream' α} (s₂ : Stream' α)
  结论: a in s₂ -> a in s₁ ⋈ s₂
  证明: fun ⟨n, h⟩ => Exists.intro (2 * n + 1) (by rw [h, get_interleave_right])

Depends on / 依赖: Exists, Exists.intro, get_interleave_right
-/
theorem mem_interleave_right {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a in s₂ -> a in s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n + 1) (by rw [h, get_interleave_right])

/--
theorem `odd_eq` / 定理 `odd_eq`

English:
theorem odd_eq
  given: (s : Stream' α)
  statement: odd s = even (tail s)
  proof: rfl

@[simp]

中文:
定理 odd_eq
  条件: (s : Stream' α)
  结论: odd s = even (tail s)
  证明: rfl

@[simp]
-/
theorem odd_eq (s : Stream' α) : odd s = even (tail s) :=
  rfl

@[simp]
/--
theorem `head_even` / 定理 `head_even`

English:
theorem head_even
  given: (s : Stream' α)
  statement: head (even s) = head s
  proof: rfl

中文:
定理 head_even
  条件: (s : Stream' α)
  结论: head (even s) = head s
  证明: rfl
-/
theorem head_even (s : Stream' α) : head (even s) = head s :=
  rfl

/--
theorem `tail_even` / 定理 `tail_even`

English:
theorem tail_even
  given: (s : Stream' α)
  statement: tail (even s) = even (tail (tail s))
  proof: by
  unfold even
  rw [corec_eq]
  rfl

中文:
定理 tail_even
  条件: (s : Stream' α)
  结论: tail (even s) = even (tail (tail s))
  证明: by
  unfold even
  rw [corec_eq]
  rfl

Depends on / 依赖: corec_eq
-/
theorem tail_even (s : Stream' α) : tail (even s) = even (tail (tail s)) := by
  unfold even
  rw [corec_eq]
  rfl

/--
theorem `even_cons_cons` / 定理 `even_cons_cons`

English:
theorem even_cons_cons
  given: (a₁ a₂ : α) (s : Stream' α)
  statement: even (a₁::a₂::s) = a₁::even s
  proof: by
  unfold even
  rw [corec_eq]; rfl

中文:
定理 even_cons_cons
  条件: (a₁ a₂ : α) (s : Stream' α)
  结论: even (a₁::a₂::s) = a₁::even s
  证明: by
  unfold even
  rw [corec_eq]; rfl

Depends on / 依赖: corec_eq
-/
theorem even_cons_cons (a₁ a₂ : α) (s : Stream' α) : even (a₁::a₂::s) = a₁::even s := by
  unfold even
  rw [corec_eq]; rfl

/--
theorem `even_tail` / 定理 `even_tail`

English:
theorem even_tail
  given: (s : Stream' α)
  statement: even (tail s) = odd s
  proof: rfl

中文:
定理 even_tail
  条件: (s : Stream' α)
  结论: even (tail s) = odd s
  证明: rfl
-/
theorem even_tail (s : Stream' α) : even (tail s) = odd s :=
  rfl

/--
theorem `even_interleave` / 定理 `even_interleave`

English:
theorem even_interleave
  given: (s₁ s₂ : Stream' α)
  statement: even (s₁ ⋈ s₂) = s₁
  proof: eq_of_bisim (fun s₁' s₁ => exists s₂, s₁' = even (s₁ ⋈ s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ => by
      rw [h₁]
      constructor
      · rfl
      · exact ⟨tail s₂, by rw [interleave_eq, even_cons_cons, tail_cons]⟩)
    (Exists.intro s₂ rfl)

中文:
定理 even_interleave
  条件: (s₁ s₂ : Stream' α)
  结论: even (s₁ ⋈ s₂) = s₁
  证明: eq_of_bisim (fun s₁' s₁ => exists s₂, s₁' = even (s₁ ⋈ s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ => by
      rw [h₁]
      constructor
      · rfl
      · exact ⟨tail s₂, by rw [interleave_eq, even_cons_cons, tail_cons]⟩)
    (Exists.intro s₂ rfl)

Depends on / 依赖: Exists, Exists.intro, eq_of_bisim, even_cons_cons, interleave_eq, tail_cons
-/
theorem even_interleave (s₁ s₂ : Stream' α) : even (s₁ ⋈ s₂) = s₁ :=
  eq_of_bisim (fun s₁' s₁ => exists s₂, s₁' = even (s₁ ⋈ s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ => by
      rw [h₁]
      constructor
      · rfl
      · exact ⟨tail s₂, by rw [interleave_eq, even_cons_cons, tail_cons]⟩)
    (Exists.intro s₂ rfl)

/--
theorem `interleave_even_odd` / 定理 `interleave_even_odd`

English:
theorem interleave_even_odd
  given: (s₁ : Stream' α)
  statement: even s₁ ⋈ odd s₁ = s₁
  proof: eq_of_bisim (fun s' s => s' = even s ⋈ odd s)
    (fun s' s (h : s' = even s ⋈ odd s) => by
      rw [h]; constructor
      · rfl
      · simp [odd_eq, odd_eq, tail_interleave, tail_even])
    rfl

中文:
定理 interleave_even_odd
  条件: (s₁ : Stream' α)
  结论: even s₁ ⋈ odd s₁ = s₁
  证明: eq_of_bisim (fun s' s => s' = even s ⋈ odd s)
    (fun s' s (h : s' = even s ⋈ odd s) => by
      rw [h]; constructor
      · rfl
      · simp [odd_eq, odd_eq, tail_interleave, tail_even])
    rfl

Depends on / 依赖: eq_of_bisim, odd_eq, tail_even, tail_interleave
-/
theorem interleave_even_odd (s₁ : Stream' α) : even s₁ ⋈ odd s₁ = s₁ :=
  eq_of_bisim (fun s' s => s' = even s ⋈ odd s)
    (fun s' s (h : s' = even s ⋈ odd s) => by
      rw [h]; constructor
      · rfl
      · simp [odd_eq, odd_eq, tail_interleave, tail_even])
    rfl

/--
theorem `get_even` / 定理 `get_even`

English:
theorem get_even
  statement: forall (n : Nat) (s : Stream' α), get (even s) n = get s (2 * n)

中文:
定理 get_even
  结论: 对任意 (n : 自然数) (s : Stream' α), get (even s) n = get s (2 * n)
-/
theorem get_even : forall (n : Nat) (s : Stream' α), get (even s) n = get s (2 * n)
  | 0, _ => rfl
  | succ n, s => by
    change get (even s) (succ n) = get s (succ (succ (2 * n)))
    rw [get_succ]; rw [get_succ]; rw [tail_even]; rw [get_even n]; rfl

/--
theorem `get_odd` / 定理 `get_odd`

English:
theorem get_odd
  statement: forall (n : Nat) (s : Stream' α), get (odd s) n = get s (2 * n + 1)
  proof: fun n s => by
  rw [odd_eq]; rw [get_even]; rfl

中文:
定理 get_odd
  结论: 对任意 (n : 自然数) (s : Stream' α), get (odd s) n = get s (2 * n + 1)
  证明: fun n s => by
  rw [odd_eq]; rw [get_even]; rfl

Depends on / 依赖: get_even, odd_eq
-/
theorem get_odd : forall (n : Nat) (s : Stream' α), get (odd s) n = get s (2 * n + 1) := fun n s => by
  rw [odd_eq]; rw [get_even]; rfl

/--
theorem `mem_of_mem_even` / 定理 `mem_of_mem_even`

English:
theorem mem_of_mem_even
  given: (a : α) (s : Stream' α)
  statement: a in even s -> a in s
  proof: fun ⟨n, h⟩ =>
  Exists.intro (2 * n) (by rw [h, get_even])

中文:
定理 mem_of_mem_even
  条件: (a : α) (s : Stream' α)
  结论: a in even s -> a in s
  证明: fun ⟨n, h⟩ =>
  Exists.intro (2 * n) (by rw [h, get_even])
-/
theorem mem_of_mem_even (a : α) (s : Stream' α) : a in even s -> a in s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n) (by rw [h, get_even])

/--
theorem `mem_of_mem_odd` / 定理 `mem_of_mem_odd`

English:
theorem mem_of_mem_odd
  given: (a : α) (s : Stream' α)
  statement: a in odd s -> a in s
  proof: fun ⟨n, h⟩ =>
  Exists.intro (2 * n + 1) (by rw [h, get_odd])

中文:
定理 mem_of_mem_odd
  条件: (a : α) (s : Stream' α)
  结论: a in odd s -> a in s
  证明: fun ⟨n, h⟩ =>
  Exists.intro (2 * n + 1) (by rw [h, get_odd])
-/
theorem mem_of_mem_odd (a : α) (s : Stream' α) : a in odd s -> a in s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n + 1) (by rw [h, get_odd])

/--
theorem `nil_append_stream` / 定理 `nil_append_stream`

English:
theorem nil_append_stream
  given: (s : Stream' α)
  statement: appendStream' [] s = s
  proof: rfl

中文:
定理 nil_append_stream
  条件: (s : Stream' α)
  结论: appendStream' [] s = s
  证明: rfl
-/
@[simp] theorem nil_append_stream (s : Stream' α) : appendStream' [] s = s :=
  rfl

/--
theorem `cons_append_stream` / 定理 `cons_append_stream`

English:
theorem cons_append_stream
  given: (a : α) (l : List α) (s : Stream' α)
  proof: rfl

中文:
定理 cons_append_stream
  条件: (a : α) (l : 列表 α) (s : Stream' α)
  证明: rfl
-/
theorem cons_append_stream (a : α) (l : List α) (s : Stream' α) :
    appendStream' (a::l) s = a::appendStream' l s :=
  rfl

/--
theorem `append_append_stream` / 定理 `append_append_stream`

English:
theorem append_append_stream
  statement: forall (l₁ l₂ : List α) (s : Stream' α),

中文:
定理 append_append_stream
  结论: 对任意 (l₁ l₂ : 列表 α) (s : Stream' α),
-/
@[simp] theorem append_append_stream : forall (l₁ l₂ : List α) (s : Stream' α),
    l₁ ++ l₂ ++ₛ s = l₁ ++ₛ (l₂ ++ₛ s)
  | [], _, _ => rfl
  | List.cons a l₁, l₂, s => by
    rw [List.cons_append]; rw [cons_append_stream]; rw [cons_append_stream]; rw [append_append_stream l₁]

/--
lemma `get_append_left` / 引理 `get_append_left`

English:
lemma get_append_left
  given: (h : n < x.length)
  statement: (x ++ₛ a).get n = x[n]
  proof: by
  induction x generalizing n with
  | nil => simp at h
  | cons b x ih =>
    rcases n with (_ | n)
    · simp
    · simp [ih n (by simpa using h), cons_append_stream]

中文:
引理 get_append_left
  条件: (h : n < x.length)
  结论: (x ++ₛ a).get n = x[n]
  证明: by
  induction x generalizing n with
  | nil => simp at h
  | cons b x ih =>
    rcases n with (_ | n)
    · simp
    · simp [ih n (by simpa using h), cons_append_stream]

Depends on / 依赖: cons_append_stream, generalizing
-/
lemma get_append_left (h : n < x.length) : (x ++ₛ a).get n = x[n] := by
  induction x generalizing n with
  | nil => simp at h
  | cons b x ih =>
    rcases n with (_ | n)
    · simp
    · simp [ih n (by simpa using h), cons_append_stream]

/--
lemma `get_append_right` / 引理 `get_append_right`

English:
lemma get_append_right
  statement: (x ++ₛ a).get (x.length + n) = a.get n
  proof: by
  induction x <;> simp [Nat.succ_add, *, cons_append_stream]

中文:
引理 get_append_right
  结论: (x ++ₛ a).get (x.length + n) = a.get n
  证明: by
  induction x <;> simp [Nat.succ_add, *, cons_append_stream]
-/
@[simp] lemma get_append_right : (x ++ₛ a).get (x.length + n) = a.get n := by
  induction x <;> simp [Nat.succ_add, *, cons_append_stream]

/--
lemma `get_append_length` / 引理 `get_append_length`

English:
lemma get_append_length
  statement: (x ++ₛ a).get x.length = a.get 0
  proof: get_append_right 0 x a

中文:
引理 get_append_length
  结论: (x ++ₛ a).get x.length = a.get 0
  证明: get_append_right 0 x a
-/
@[simp] lemma get_append_length : (x ++ₛ a).get x.length = a.get 0 := get_append_right 0 x a

/--
lemma `append_right_injective` / 引理 `append_right_injective`

English:
lemma append_right_injective
  given: (h : x ++ₛ a = x ++ₛ b)
  statement: a = b
  proof: by
  ext n; replace h := congr_arg (fun a => a.get (x.length + n)) h; simpa using h

中文:
引理 append_right_injective
  条件: (h : x ++ₛ a = x ++ₛ b)
  结论: a = b
  证明: by
  ext n; replace h := congr_arg (fun a => a.get (x.length + n)) h; simpa using h

Depends on / 依赖: a.get, congr_arg, length, replace, x.length
-/
lemma append_right_injective (h : x ++ₛ a = x ++ₛ b) : a = b := by
  ext n; replace h := congr_arg (fun a => a.get (x.length + n)) h; simpa using h

/--
lemma `append_right_inj` / 引理 `append_right_inj`

English:
lemma append_right_inj
  statement: x ++ₛ a = x ++ₛ b ↔ a = b
  proof: ⟨append_right_injective x a b, by simp +contextual⟩

中文:
引理 append_right_inj
  结论: x ++ₛ a = x ++ₛ b ↔ a = b
  证明: ⟨append_right_injective x a b, by simp +contextual⟩
-/
@[simp] lemma append_right_inj : x ++ₛ a = x ++ₛ b ↔ a = b :=
  ⟨append_right_injective x a b, by simp +contextual⟩

/--
lemma `append_left_injective` / 引理 `append_left_injective`

English:
lemma append_left_injective
  given: (h : x ++ₛ a = y ++ₛ b) (hl : x.length = y.length)
  statement: x = y
  proof: by
  apply List.ext_getElem hl
  intros
  rw [← get_append_left]; rw [← get_append_left]; rw [h]

中文:
引理 append_left_injective
  条件: (h : x ++ₛ a = y ++ₛ b) (hl : x.length = y.length)
  结论: x = y
  证明: by
  apply List.ext_getElem hl
  intros
  rw [← get_append_left]; rw [← get_append_left]; rw [h]

Depends on / 依赖: List.ext_getElem, ext_getElem, get_append_left, intros
-/
lemma append_left_injective (h : x ++ₛ a = y ++ₛ b) (hl : x.length = y.length) : x = y := by
  apply List.ext_getElem hl
  intros
  rw [← get_append_left]; rw [← get_append_left]; rw [h]

/--
theorem `map_append_stream` / 定理 `map_append_stream`

English:
theorem map_append_stream
  given: (f : α -> β)

中文:
定理 map_append_stream
  条件: (f : α -> β)
-/
theorem map_append_stream (f : α -> β) :
    forall (l : List α) (s : Stream' α), map f (l ++ₛ s) = List.map f l ++ₛ map f s
  | [], _ => rfl
  | List.cons a l, s => by
    rw [cons_append_stream]; rw [List.map_cons]; rw [map_cons]; rw [cons_append_stream]; rw [map_append_stream f l]

/--
theorem `drop_append_stream` / 定理 `drop_append_stream`

English:
theorem drop_append_stream
  statement: forall (l : List α) (s : Stream' α), drop l.length (l ++ₛ s) = s

中文:
定理 drop_append_stream
  结论: 对任意 (l : 列表 α) (s : Stream' α), drop l.length (l ++ₛ s) = s
-/
theorem drop_append_stream : forall (l : List α) (s : Stream' α), drop l.length (l ++ₛ s) = s
  | [], s => rfl
  | List.cons a l, s => by
    rw [List.length_cons]; rw [drop_succ]; rw [cons_append_stream]; rw [tail_cons]; rw [drop_append_stream l s]

/--
theorem `append_stream_head_tail` / 定理 `append_stream_head_tail`

English:
theorem append_stream_head_tail
  given: (s : Stream' α)
  statement: [head s] ++ₛ tail s = s
  proof: by
  simp

中文:
定理 append_stream_head_tail
  条件: (s : Stream' α)
  结论: [head s] ++ₛ tail s = s
  证明: by
  simp
-/
theorem append_stream_head_tail (s : Stream' α) : [head s] ++ₛ tail s = s := by
  simp

/--
theorem `mem_append_stream_right` / 定理 `mem_append_stream_right`

English:
theorem mem_append_stream_right
  statement: forall {a : α} (l : List α) {s : Stream' α}, a in s -> a in l ++ₛ s
  proof: mem_append_stream_right l h
    mem_cons_of_mem _ ih

中文:
定理 mem_append_stream_right
  结论: 对任意 {a : α} (l : 列表 α) {s : Stream' α}, a in s -> a in l ++ₛ s
  证明: mem_append_stream_right l h
    mem_cons_of_mem _ ih

Depends on / 依赖: mem_append_stream_right
-/
theorem mem_append_stream_right : forall {a : α} (l : List α) {s : Stream' α}, a in s -> a in l ++ₛ s
  | _, [], _, h => h
  | a, List.cons _ l, s, h =>
    have ih : a in l ++ₛ s := mem_append_stream_right l h
    mem_cons_of_mem _ ih

/--
theorem `mem_append_stream_left` / 定理 `mem_append_stream_left`

English:
theorem mem_append_stream_left
  statement: forall {a : α} {l : List α} (s : Stream' α), a in l -> a in l ++ₛ s

中文:
定理 mem_append_stream_left
  结论: 对任意 {a : α} {l : 列表 α} (s : Stream' α), a in l -> a in l ++ₛ s
-/
theorem mem_append_stream_left : forall {a : α} {l : List α} (s : Stream' α), a in l -> a in l ++ₛ s
  | _, [], _, h => absurd h List.not_mem_nil
  | a, List.cons b l, s, h =>
    Or.elim (List.eq_or_mem_of_mem_cons h) (fun aeqb : a = b => Exists.intro 0 aeqb)
      fun ainl : a in l => mem_cons_of_mem b (mem_append_stream_left s ainl)

@[simp]
/--
theorem `take_zero` / 定理 `take_zero`

English:
theorem take_zero
  given: (s : Stream' α)
  statement: take 0 s = []
  proof: rfl

中文:
定理 take_zero
  条件: (s : Stream' α)
  结论: take 0 s = []
  证明: rfl
-/
theorem take_zero (s : Stream' α) : take 0 s = [] :=
  rfl

-- This lemma used to be simp, but we removed it from the simp set because:
-- 1) It duplicates the (often large) `s` term, resulting in large tactic states.
-- 2) It conflicts with the very useful `dropLast_take` lemma below (causing nonconfluence).
/--
theorem `take_succ` / 定理 `take_succ`

English:
theorem take_succ
  given: (n : Nat) (s : Stream' α)
  statement: take (succ n) s = head s::take n (tail s)
  proof: rfl

中文:
定理 take_succ
  条件: (n : 自然数) (s : Stream' α)
  结论: take (succ n) s = head s::take n (tail s)
  证明: rfl
-/
theorem take_succ (n : Nat) (s : Stream' α) : take (succ n) s = head s::take n (tail s) :=
  rfl

/--
theorem `take_succ_cons` / 定理 `take_succ_cons`

English:
theorem take_succ_cons
  given: {a : α} (n : Nat) (s : Stream' α)
  proof: rfl

中文:
定理 take_succ_cons
  条件: {a : α} (n : 自然数) (s : Stream' α)
  证明: rfl
-/
@[simp] theorem take_succ_cons {a : α} (n : Nat) (s : Stream' α) :
    take (n + 1) (a::s) = a :: take n s := rfl

/--
theorem `take_succ'` / 定理 `take_succ'`

English:
theorem take_succ'
  given: {s : Stream' α}
  statement: forall n, s.take (n + 1) = s.take n ++ [s.get n]

中文:
定理 take_succ'
  条件: {s : Stream' α}
  结论: 对任意 n, s.take (n + 1) = s.take n ++ [s.get n]
-/
theorem take_succ' {s : Stream' α} : forall n, s.take (n + 1) = s.take n ++ [s.get n]
  | 0 => rfl
  | n + 1 => by rw [take_succ, take_succ' n, ← List.cons_append, ← take_succ, get_tail]

@[simp]
/--
theorem `length_take` / 定理 `length_take`

English:
theorem length_take
  given: (n : Nat) (s : Stream' α)
  statement: (take n s).length = n
  proof: by
  induction n generalizing s <;> simp [*, take_succ]

@[simp]

中文:
定理 length_take
  条件: (n : 自然数) (s : Stream' α)
  结论: (take n s).length = n
  证明: by
  induction n generalizing s <;> simp [*, take_succ]

@[simp]

Depends on / 依赖: generalizing, take_succ
-/
theorem length_take (n : Nat) (s : Stream' α) : (take n s).length = n := by
  induction n generalizing s <;> simp [*, take_succ]

@[simp]
/--
theorem `take_take` / 定理 `take_take`

English:
theorem take_take
  given: {s : Stream' α}
  statement: forall {m n}, (s.take n).take m = s.take (min n m)

中文:
定理 take_take
  条件: {s : Stream' α}
  结论: 对任意 {m n}, (s.take n).take m = s.take (最小值 n m)
-/
theorem take_take {s : Stream' α} : forall {m n}, (s.take n).take m = s.take (min n m)
  | 0, n => by rw [Nat.min_zero, List.take_zero, take_zero]
  | m, 0 => by rw [Nat.zero_min, take_zero, List.take_nil]
  | m + 1, n + 1 => by rw [take_succ, List.take_succ_cons, Nat.succ_min_succ, take_succ, take_take]

/--
theorem `concat_take_get` / 定理 `concat_take_get`

English:
theorem concat_take_get
  given: {n : Nat} {s : Stream' α}
  statement: s.take n ++ [s.get n] = s.take (n + 1)
  proof: (take_succ' n).symm

中文:
定理 concat_take_get
  条件: {n : 自然数} {s : Stream' α}
  结论: s.take n ++ [s.get n] = s.take (n + 1)
  证明: (take_succ' n).symm
-/
@[simp] theorem concat_take_get {n : Nat} {s : Stream' α} : s.take n ++ [s.get n] = s.take (n + 1) :=
  (take_succ' n).symm

/--
theorem `getElem?_take` / 定理 `getElem?_take`

English:
theorem getElem?_take
  given: {s : Stream' α}
  statement: forall {k n}, k < n -> (s.take n)[k]? = s.get k

中文:
定理 getElem?_take
  条件: {s : Stream' α}
  结论: 对任意 {k n}, k < n -> (s.take n)[k]? = s.get k
-/
theorem getElem?_take {s : Stream' α} : forall {k n}, k < n -> (s.take n)[k]? = s.get k
  | 0, _ + 1, _ => by simp only [length_take, zero_lt_succ, List.getElem?_eq_getElem]; rfl
  | k + 1, n + 1, h => by
    rw [take_succ]; rw [List.getElem?_cons_succ]; rw [getElem?_take (Nat.lt_of_succ_lt_succ h)]; rw [get_succ]

/--
theorem `getElem?_take_succ` / 定理 `getElem?_take_succ`

English:
theorem getElem?_take_succ
  given: (n : Nat) (s : Stream' α)
  proof: getElem?_take (Nat.lt_succ_self n)

中文:
定理 getElem?_take_succ
  条件: (n : 自然数) (s : Stream' α)
  证明: getElem?_take (Nat.lt_succ_self n)

Depends on / 依赖: Nat.lt_succ_self, _take, getElem, lt_succ_self
-/
theorem getElem?_take_succ (n : Nat) (s : Stream' α) :
    (take (succ n) s)[n]? = some (get s n) :=
  getElem?_take (Nat.lt_succ_self n)

/--
theorem `dropLast_take` / 定理 `dropLast_take`

English:
theorem dropLast_take
  given: {n : Nat} {xs : Stream' α}
  proof: by
  cases n with
  | zero => simp
  | succ n => rw [take_succ', List.dropLast_concat, Nat.add_one_sub_one]

@[simp]

中文:
定理 dropLast_take
  条件: {n : 自然数} {xs : Stream' α}
  证明: by
  cases n with
  | zero => simp
  | succ n => rw [take_succ', List.dropLast_concat, Nat.add_one_sub_one]

@[simp]
-/
@[simp] theorem dropLast_take {n : Nat} {xs : Stream' α} :
    (Stream'.take n xs).dropLast = Stream'.take (n - 1) xs := by
  cases n with
  | zero => simp
  | succ n => rw [take_succ', List.dropLast_concat, Nat.add_one_sub_one]

@[simp]
/--
theorem `append_take_drop` / 定理 `append_take_drop`

English:
theorem append_take_drop
  given: (n : Nat) (s : Stream' α)
  statement: appendStream' (take n s) (drop n s) = s
  proof: by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [take_succ, drop_succ, cons_append_stream, ih (tail s), Stream'.eta]

中文:
定理 append_take_drop
  条件: (n : 自然数) (s : Stream' α)
  结论: appendStream' (take n s) (drop n s) = s
  证明: by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [take_succ, drop_succ, cons_append_stream, ih (tail s), Stream'.eta]

Depends on / 依赖: Stream, cons_append_stream, drop_succ, generalizing, take_succ
-/
theorem append_take_drop (n : Nat) (s : Stream' α) : appendStream' (take n s) (drop n s) = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [take_succ, drop_succ, cons_append_stream, ih (tail s), Stream'.eta]

/--
lemma `append_take` / 引理 `append_take`

English:
lemma append_take
  statement: x ++ (a.take n) = (x ++ₛ a).take (x.length + n)
  proof: by
  induction x <;> simp [take, Nat.add_comm, cons_append_stream, *]

中文:
引理 append_take
  结论: x ++ (a.take n) = (x ++ₛ a).take (x.length + n)
  证明: by
  induction x <;> simp [take, Nat.add_comm, cons_append_stream, *]

Depends on / 依赖: Nat.add_comm, add_comm, cons_append_stream
-/
lemma append_take : x ++ (a.take n) = (x ++ₛ a).take (x.length + n) := by
  induction x <;> simp [take, Nat.add_comm, cons_append_stream, *]

/--
lemma `take_get` / 引理 `take_get`

English:
lemma take_get
  given: (h : m < (a.take n).length)
  statement: (a.take n)[m] = a.get m
  proof: by
  nth_rw 2 [← append_take_drop n a]; rw [get_append_left]

中文:
引理 take_get
  条件: (h : m < (a.take n).length)
  结论: (a.take n)[m] = a.get m
  证明: by
  nth_rw 2 [← append_take_drop n a]; rw [get_append_left]
-/
@[simp] lemma take_get (h : m < (a.take n).length) : (a.take n)[m] = a.get m := by
  nth_rw 2 [← append_take_drop n a]; rw [get_append_left]

/--
theorem `take_append_of_le_length` / 定理 `take_append_of_le_length`

English:
theorem take_append_of_le_length
  given: (h : n <= x.length)
  proof: by
  apply List.ext_getElem (by simp [h])
  intro _ _ _; rw [List.getElem_take, take_get, get_append_left]

中文:
定理 take_append_of_le_length
  条件: (h : n <= x.length)
  证明: by
  apply List.ext_getElem (by simp [h])
  intro _ _ _; rw [List.getElem_take, take_get, get_append_left]

Depends on / 依赖: List.ext_getElem, List.getElem_take, ext_getElem, getElem_take, get_append_left, take_get
-/
theorem take_append_of_le_length (h : n <= x.length) :
    (x ++ₛ a).take n = x.take n := by
  apply List.ext_getElem (by simp [h])
  intro _ _ _; rw [List.getElem_take, take_get, get_append_left]

/--
lemma `take_add` / 引理 `take_add`

English:
lemma take_add
  statement: a.take (m + n) = a.take m ++ (a.drop m).take n
  proof: by
  apply append_left_injective _ _ (a.drop (m + n)) ((a.drop m).drop n) <;>
    simp [-drop_drop]

中文:
引理 take_add
  结论: a.take (m + n) = a.take m ++ (a.drop m).take n
  证明: by
  apply append_left_injective _ _ (a.drop (m + n)) ((a.drop m).drop n) <;>
    simp [-drop_drop]

Depends on / 依赖: a.drop, append_left_injective, drop_drop
-/
lemma take_add : a.take (m + n) = a.take m ++ (a.drop m).take n := by
  apply append_left_injective _ _ (a.drop (m + n)) ((a.drop m).drop n) <;>
    simp [-drop_drop]

/--
lemma `take_prefix_take_left` / 引理 `take_prefix_take_left`

English:
lemma take_prefix_take_left
  given: (h : m <= n)
  statement: a.take m <+: a.take n
  proof: by
  rw [(by simp [h] : a.take m = (a.take n).take m)]
  apply List.take_prefix

中文:
引理 take_prefix_take_left
  条件: (h : m <= n)
  结论: a.take m <+: a.take n
  证明: by
  rw [(by simp [h] : a.take m = (a.take n).take m)]
  apply List.take_prefix
-/
@[gcongr] lemma take_prefix_take_left (h : m <= n) : a.take m <+: a.take n := by
  rw [(by simp [h] : a.take m = (a.take n).take m)]
  apply List.take_prefix

/--
lemma `take_prefix` / 引理 `take_prefix`

English:
lemma take_prefix
  statement: a.take m <+: a.take n ↔ m <= n
  proof: ⟨fun h => by simpa using h.length_le, take_prefix_take_left m n a⟩

中文:
引理 take_prefix
  结论: a.take m <+: a.take n ↔ m <= n
  证明: ⟨fun h => by simpa using h.length_le, take_prefix_take_left m n a⟩
-/
@[simp] lemma take_prefix : a.take m <+: a.take n ↔ m <= n :=
  ⟨fun h => by simpa using h.length_le, take_prefix_take_left m n a⟩

/--
lemma `map_take` / 引理 `map_take`

English:
lemma map_take
  given: (f : α -> β)
  statement: (a.take n).map f = (a.map f).take n
  proof: by
  apply List.ext_getElem <;> simp

中文:
引理 map_take
  条件: (f : α -> β)
  结论: (a.take n).map f = (a.map f).take n
  证明: by
  apply List.ext_getElem <;> simp

Depends on / 依赖: List.ext_getElem, ext_getElem
-/
lemma map_take (f : α -> β) : (a.take n).map f = (a.map f).take n := by
  apply List.ext_getElem <;> simp

/--
lemma `take_drop` / 引理 `take_drop`

English:
lemma take_drop
  statement: (a.drop m).take n = (a.take (m + n)).drop m
  proof: by
  apply List.ext_getElem <;> simp

中文:
引理 take_drop
  结论: (a.drop m).take n = (a.take (m + n)).drop m
  证明: by
  apply List.ext_getElem <;> simp

Depends on / 依赖: List.ext_getElem, ext_getElem
-/
lemma take_drop : (a.drop m).take n = (a.take (m + n)).drop m := by
  apply List.ext_getElem <;> simp

/--
lemma `drop_append_of_le_length` / 引理 `drop_append_of_le_length`

English:
lemma drop_append_of_le_length
  given: (h : n <= x.length)
  proof: by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
  ext k; rcases lt_or_ge k m with _ | hk
  · rw [get_drop, get_append_left, get_append_left, List.getElem_drop]; simpa [hm]
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hm' : m = (x.drop n).length := by simp [hm]
    simp_rw [get_drop, ←

中文:
引理 drop_append_of_le_length
  条件: (h : n <= x.length)
  证明: by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
  ext k; rcases lt_or_ge k m with _ | hk
  · rw [get_drop, get_append_left, get_append_left, List.getElem_drop]; simpa [hm]
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hm' : m = (x.drop n).length := by simp [hm]
    simp_rw [get_drop, ←

Depends on / 依赖: List.getElem_drop, Nat.add_assoc, Nat.exists_eq_add_of_le, add_assoc, exists_eq_add_of_le, getElem_drop, get_append_left, get_append_right, get_drop, length, lt_or_ge, simp_rw, x.drop
-/
lemma drop_append_of_le_length (h : n <= x.length) :
    (x ++ₛ a).drop n = x.drop n ++ₛ a := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
  ext k; rcases lt_or_ge k m with _ | hk
  · rw [get_drop, get_append_left, get_append_left, List.getElem_drop]; simpa [hm]
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hm' : m = (x.drop n).length := by simp [hm]
    simp_rw [get_drop, ← Nat.add_assoc, ← hm, get_append_right, hm', get_append_right]

-- Take theorem reduces a proof of equality of infinite streams to an
-- induction over all their finite approximations.
/--
theorem `take_theorem` / 定理 `take_theorem`

English:
theorem take_theorem
  given: (s₁ s₂ : Stream' α) (h : forall n : Nat, take n s₁ = take n s₂)
  statement: s₁ = s₂
  proof: by
  ext n
  induction n with
  | zero => simpa [take] using h 1
  | succ n =>
    have h₁ : some (get s₁ (succ n)) = some (get s₂ (succ n)) := by
      rw [← getElem?_take_succ]; rw [← getElem?_take_succ]; rw [h (succ (succ n))]
    injection h₁

中文:
定理 take_theorem
  条件: (s₁ s₂ : Stream' α) (h : 对任意 n : 自然数, take n s₁ = take n s₂)
  结论: s₁ = s₂
  证明: by
  ext n
  induction n with
  | zero => simpa [take] using h 1
  | succ n =>
    have h₁ : some (get s₁ (succ n)) = some (get s₂ (succ n)) := by
      rw [← getElem?_take_succ]; rw [← getElem?_take_succ]; rw [h (succ (succ n))]
    injection h₁

Depends on / 依赖: _take_succ, getElem, injection
-/
theorem take_theorem (s₁ s₂ : Stream' α) (h : forall n : Nat, take n s₁ = take n s₂) : s₁ = s₂ := by
  ext n
  induction n with
  | zero => simpa [take] using h 1
  | succ n =>
    have h₁ : some (get s₁ (succ n)) = some (get s₂ (succ n)) := by
      rw [← getElem?_take_succ]; rw [← getElem?_take_succ]; rw [h (succ (succ n))]
    injection h₁

/--
theorem `cycle_g_cons` / 定理 `cycle_g_cons`

English:
theorem cycle_g_cons
  given: (a : α) (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α)
  proof: rfl

中文:
定理 cycle_g_cons
  条件: (a : α) (a₁ : α) (l₁ : 列表 α) (a₀ : α) (l₀ : 列表 α)
  证明: rfl
-/
protected theorem cycle_g_cons (a : α) (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
    Stream'.cycleG (a, a₁::l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) :=
  rfl

/--
theorem `cycle_eq` / 定理 `cycle_eq`

English:
theorem cycle_eq
  statement: forall (l : List α) (h : l != []), cycle l h = l ++ₛ cycle l h
  proof: by
      induction l' generalizing a' with
      | nil => rw [corec_eq]; rfl
      | cons a₁ l₁ ih => rw [corec_eq, Stream'.cycle_g_cons, ih a₁]; rfl
    gen l a

中文:
定理 cycle_eq
  结论: 对任意 (l : 列表 α) (h : l != []), cycle l h = l ++ₛ cycle l h
  证明: by
      induction l' generalizing a' with
      | nil => rw [corec_eq]; rfl
      | cons a₁ l₁ ih => rw [corec_eq, Stream'.cycle_g_cons, ih a₁]; rfl
    gen l a

Depends on / 依赖: Stream, corec_eq, cycle_g_cons, generalizing
-/
theorem cycle_eq : forall (l : List α) (h : l != []), cycle l h = l ++ₛ cycle l h
  | [], h => absurd rfl h
  | List.cons a l, _ =>
    have gen (l' a') : corec Stream'.cycleF Stream'.cycleG (a', l', a, l) =
        (a'::l') ++ₛ corec Stream'.cycleF Stream'.cycleG (a, l, a, l) := by
      induction l' generalizing a' with
      | nil => rw [corec_eq]; rfl
      | cons a₁ l₁ ih => rw [corec_eq, Stream'.cycle_g_cons, ih a₁]; rfl
    gen l a

/--
theorem `mem_cycle` / 定理 `mem_cycle`

English:
theorem mem_cycle
  given: {a : α} {l : List α}
  statement: forall h : l != [], a in l -> a in cycle l h
  proof: fun h ainl => by
  rw [cycle_eq]; exact mem_append_stream_left _ ainl

@[simp]

中文:
定理 mem_cycle
  条件: {a : α} {l : 列表 α}
  结论: 对任意 h : l != [], a in l -> a in cycle l h
  证明: fun h ainl => by
  rw [cycle_eq]; exact mem_append_stream_left _ ainl

@[simp]

Depends on / 依赖: cycle_eq, mem_append_stream_left
-/
theorem mem_cycle {a : α} {l : List α} : forall h : l != [], a in l -> a in cycle l h := fun h ainl => by
  rw [cycle_eq]; exact mem_append_stream_left _ ainl

@[simp]
/--
theorem `cycle_singleton` / 定理 `cycle_singleton`

English:
theorem cycle_singleton
  given: (a : α)
  statement: cycle [a] (by simp) = const a
  proof: coinduction rfl fun β fr ch => by rwa [cycle_eq, const_eq]

中文:
定理 cycle_singleton
  条件: (a : α)
  结论: cycle [a] (by simp) = const a
  证明: coinduction rfl fun β fr ch => by rwa [cycle_eq, const_eq]

Depends on / 依赖: coinduction, const_eq, cycle_eq
-/
theorem cycle_singleton (a : α) : cycle [a] (by simp) = const a :=
  coinduction rfl fun β fr ch => by rwa [cycle_eq, const_eq]

/--
theorem `tails_eq` / 定理 `tails_eq`

English:
theorem tails_eq
  given: (s : Stream' α)
  statement: tails s = tail s::tails (tail s)
  proof: by
  unfold tails; rw [corec_eq]; rfl

@[simp]

中文:
定理 tails_eq
  条件: (s : Stream' α)
  结论: tails s = tail s::tails (tail s)
  证明: by
  unfold tails; rw [corec_eq]; rfl

@[simp]

Depends on / 依赖: corec_eq
-/
theorem tails_eq (s : Stream' α) : tails s = tail s::tails (tail s) := by
  unfold tails; rw [corec_eq]; rfl

@[simp]
/--
theorem `get_tails` / 定理 `get_tails`

English:
theorem get_tails
  given: (n : Nat) (s : Stream' α)
  statement: get (tails s) n = drop n (tail s)
  proof: by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, drop_succ, tails_eq, tail_cons, ih]

中文:
定理 get_tails
  条件: (n : 自然数) (s : Stream' α)
  结论: get (tails s) n = drop n (tail s)
  证明: by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, drop_succ, tails_eq, tail_cons, ih]

Depends on / 依赖: drop_succ, generalizing, get_succ, tail_cons, tails_eq
-/
theorem get_tails (n : Nat) (s : Stream' α) : get (tails s) n = drop n (tail s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, drop_succ, tails_eq, tail_cons, ih]

/--
theorem `tails_eq_iterate` / 定理 `tails_eq_iterate`

English:
theorem tails_eq_iterate
  given: (s : Stream' α)
  statement: tails s = iterate tail (tail s)
  proof: rfl

中文:
定理 tails_eq_iterate
  条件: (s : Stream' α)
  结论: tails s = iterate tail (tail s)
  证明: rfl
-/
theorem tails_eq_iterate (s : Stream' α) : tails s = iterate tail (tail s) :=
  rfl

/--
theorem `inits_core_eq` / 定理 `inits_core_eq`

English:
theorem inits_core_eq
  given: (l : List α) (s : Stream' α)
  proof: by
    unfold initsCore corecOn
    rw [corec_eq]

中文:
定理 inits_core_eq
  条件: (l : 列表 α) (s : Stream' α)
  证明: by
    unfold initsCore corecOn
    rw [corec_eq]

Depends on / 依赖: corecOn, corec_eq, initsCore
-/
theorem inits_core_eq (l : List α) (s : Stream' α) :
    initsCore l s = l::initsCore (l ++ [head s]) (tail s) := by
    unfold initsCore corecOn
    rw [corec_eq]

/--
theorem `tail_inits` / 定理 `tail_inits`

English:
theorem tail_inits
  given: (s : Stream' α)
  proof: by
    unfold inits
    rw [inits_core_eq]; rfl

中文:
定理 tail_inits
  条件: (s : Stream' α)
  证明: by
    unfold inits
    rw [inits_core_eq]; rfl

Depends on / 依赖: inits_core_eq
-/
theorem tail_inits (s : Stream' α) :
    tail (inits s) = initsCore [head s, head (tail s)] (tail (tail s)) := by
    unfold inits
    rw [inits_core_eq]; rfl

/--
theorem `inits_tail` / 定理 `inits_tail`

English:
theorem inits_tail
  given: (s : Stream' α)
  statement: inits (tail s) = initsCore [head (tail s)] (tail (tail s))
  proof: rfl

中文:
定理 inits_tail
  条件: (s : Stream' α)
  结论: inits (tail s) = initsCore [head (tail s)] (tail (tail s))
  证明: rfl
-/
theorem inits_tail (s : Stream' α) : inits (tail s) = initsCore [head (tail s)] (tail (tail s)) :=
  rfl

/--
theorem `cons_get_inits_core` / 定理 `cons_get_inits_core`

English:
theorem cons_get_inits_core
  given: (a : α) (n : Nat) (l : List α) (s : Stream' α)
  proof: by
  induction n generalizing l s with
  | zero => rfl
  | succ n ih =>
    rw [get_succ]; rw [inits_core_eq]; rw [tail_cons]; rw [ih]; rw [inits_core_eq (a :: l) s]
    rfl

@[simp]

中文:
定理 cons_get_inits_core
  条件: (a : α) (n : 自然数) (l : 列表 α) (s : Stream' α)
  证明: by
  induction n generalizing l s with
  | zero => rfl
  | succ n ih =>
    rw [get_succ]; rw [inits_core_eq]; rw [tail_cons]; rw [ih]; rw [inits_core_eq (a :: l) s]
    rfl

@[simp]

Depends on / 依赖: generalizing, get_succ, inits_core_eq, tail_cons
-/
theorem cons_get_inits_core (a : α) (n : Nat) (l : List α) (s : Stream' α) :
    (a :: get (initsCore l s) n) = get (initsCore (a :: l) s) n := by
  induction n generalizing l s with
  | zero => rfl
  | succ n ih =>
    rw [get_succ]; rw [inits_core_eq]; rw [tail_cons]; rw [ih]; rw [inits_core_eq (a :: l) s]
    rfl

@[simp]
/--
theorem `get_inits` / 定理 `get_inits`

English:
theorem get_inits
  given: (n : Nat) (s : Stream' α)
  statement: get (inits s) n = take (succ n) s
  proof: by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, take_succ, ← ih, tail_inits, inits_tail, cons_get_inits_core]

中文:
定理 get_inits
  条件: (n : 自然数) (s : Stream' α)
  结论: get (inits s) n = take (succ n) s
  证明: by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, take_succ, ← ih, tail_inits, inits_tail, cons_get_inits_core]

Depends on / 依赖: IsOfFinOrder, Nat.card_congr, Nat.card_eq_zero_of_infinite, card_congr, card_eq_zero_of_infinite, cons_get_inits_core, finEquivPowers, generalizing, get_succ, infinite_powers, inits_tail, orderOf_eq_zero, tail_inits, take_succ, to_subtype
-/
theorem get_inits (n : Nat) (s : Stream' α) : get (inits s) n = take (succ n) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, take_succ, ← ih, tail_inits, inits_tail, cons_get_inits_core]

/--
theorem `inits_eq` / 定理 `inits_eq`

English:
theorem inits_eq
  given: (s : Stream' α)
  proof: by
  apply Stream'.ext; intro n
  cases n
  · rfl
  · rw [get_inits, get_succ, tail_cons, get_map, get_inits]
    rfl

中文:
定理 inits_eq
  条件: (s : Stream' α)
  证明: by
  apply Stream'.ext; intro n
  cases n
  · rfl
  · rw [get_inits, get_succ, tail_cons, get_map, get_inits]
    rfl

Depends on / 依赖: Stream, get_inits, get_map, get_succ, tail_cons
-/
theorem inits_eq (s : Stream' α) :
    inits s = [head s]::map (List.cons (head s)) (inits (tail s)) := by
  apply Stream'.ext; intro n
  cases n
  · rfl
  · rw [get_inits, get_succ, tail_cons, get_map, get_inits]
    rfl

/--
theorem `zip_inits_tails` / 定理 `zip_inits_tails`

English:
theorem zip_inits_tails
  given: (s : Stream' α)
  statement: zip appendStream' (inits s) (tails s) = const s
  proof: by
  ext
  simp

中文:
定理 zip_inits_tails
  条件: (s : Stream' α)
  结论: zip appendStream' (inits s) (tails s) = const s
  证明: by
  ext
  simp
-/
theorem zip_inits_tails (s : Stream' α) : zip appendStream' (inits s) (tails s) = const s := by
  ext
  simp

/--
theorem `identity` / 定理 `identity`

English:
theorem identity
  given: (s : Stream' α)
  statement: pure id ⊛ s = s
  proof: rfl

中文:
定理 identity
  条件: (s : Stream' α)
  结论: pure id ⊛ s = s
  证明: rfl
-/
theorem identity (s : Stream' α) : pure id ⊛ s = s :=
  rfl

/--
theorem `composition` / 定理 `composition`

English:
theorem composition
  given: (g : Stream' (β -> δ)) (f : Stream' (α -> β)) (s : Stream' α)
  proof: rfl

中文:
定理 composition
  条件: (g : Stream' (β -> δ)) (f : Stream' (α -> β)) (s : Stream' α)
  证明: rfl
-/
theorem composition (g : Stream' (β -> δ)) (f : Stream' (α -> β)) (s : Stream' α) :
    pure comp ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s) :=
  rfl

/--
theorem `homomorphism` / 定理 `homomorphism`

English:
theorem homomorphism
  given: (f : α -> β) (a : α)
  statement: pure f ⊛ pure a = pure (f a)
  proof: rfl

中文:
定理 homomorphism
  条件: (f : α -> β) (a : α)
  结论: pure f ⊛ pure a = pure (f a)
  证明: rfl
-/
theorem homomorphism (f : α -> β) (a : α) : pure f ⊛ pure a = pure (f a) :=
  rfl

/--
theorem `interchange` / 定理 `interchange`

English:
theorem interchange
  given: (fs : Stream' (α -> β)) (a : α)
  proof: rfl

中文:
定理 interchange
  条件: (fs : Stream' (α -> β)) (a : α)
  证明: rfl
-/
theorem interchange (fs : Stream' (α -> β)) (a : α) :
    fs ⊛ pure a = (pure fun f : α -> β => f a) ⊛ fs :=
  rfl

/--
theorem `map_eq_apply` / 定理 `map_eq_apply`

English:
theorem map_eq_apply
  given: (f : α -> β) (s : Stream' α)
  statement: map f s = pure f ⊛ s
  proof: rfl

中文:
定理 map_eq_apply
  条件: (f : α -> β) (s : Stream' α)
  结论: map f s = pure f ⊛ s
  证明: rfl
-/
theorem map_eq_apply (f : α -> β) (s : Stream' α) : map f s = pure f ⊛ s :=
  rfl

/--
theorem `get_nats` / 定理 `get_nats`

English:
theorem get_nats
  given: (n : Nat)
  statement: get nats n = n
  proof: rfl

中文:
定理 get_nats
  条件: (n : 自然数)
  结论: get nats n = n
  证明: rfl
-/
theorem get_nats (n : Nat) : get nats n = n :=
  rfl

/--
theorem `nats_eq` / 定理 `nats_eq`

English:
theorem nats_eq
  statement: nats = cons 0 (map succ nats)
  proof: by
  apply Stream'.ext; intro n
  cases n
  · rfl
  rw [get_succ]; rfl

中文:
定理 nats_eq
  结论: nats = cons 0 (map succ nats)
  证明: by
  apply Stream'.ext; intro n
  cases n
  · rfl
  rw [get_succ]; rfl

Depends on / 依赖: Stream, get_succ
-/
theorem nats_eq : nats = cons 0 (map succ nats) := by
  apply Stream'.ext; intro n
  cases n
  · rfl
  rw [get_succ]; rfl

end Stream'
