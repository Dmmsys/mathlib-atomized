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
variable (m n : ℕ) (x y : List α) (a b : Stream' α)

/-
**Stream.** 是 Mathlib 中的一个实例，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Stream' α) :=
  ⟨Stream'.const default⟩
/-
**Stream.eta** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem eta (s : Stream' α) : head s :: tail s = s :=
  funext fun i => by cases i <;> rfl

/-- Alias for `Stream'.eta` to match `List` API. -/
alias cons_head_tail := Stream'.eta

@[ext]
/-
**Stream.ext** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem ext {s₁ s₂ : Stream' α} : (∀ n, get s₁ n = get s₂ n) → s₁ = s₂ :=
  fun h => funext h

@[simp]
/-
**Stream.get_zero_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_zero_cons (a : α) (s : Stream' α) : get (a::s) 0 = a :=
  rfl

@[simp]
/-
**Stream.head_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_cons (a : α) (s : Stream' α) : head (a::s) = a :=
  rfl

@[simp]
/-
**Stream.tail_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_cons (a : α) (s : Stream' α) : tail (a::s) = s :=
  rfl

@[simp]
/-
**Stream.get_drop** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_drop (n m : ℕ) (s : Stream' α) : get (drop m s) n = get s (m + n) := by
  rw [Nat.add_comm]
  rfl
/-
**Stream.tail_eq_drop** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_eq_drop (s : Stream' α) : tail s = drop 1 s :=
  rfl

@[simp]
/-
**Stream.drop_drop** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem drop_drop (n m : ℕ) (s : Stream' α) : drop n (drop m s) = drop (m + n) s := by
  ext; simp [Nat.add_assoc]
/-
**Stream.get_tail** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem get_tail {n : ℕ} {s : Stream' α} : s.tail.get n = s.get (n + 1) := rfl
/-
**Stream.tail_drop'** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem tail_drop' {i : ℕ} {s : Stream' α} : tail (drop i s) = s.drop (i + 1) := by
  ext; simp [Nat.add_comm, Nat.add_left_comm]
/-
**Stream.drop_tail'** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem drop_tail' {i : ℕ} {s : Stream' α} : drop i (tail s) = s.drop (i + 1) := rfl
/-
**Stream.tail_drop** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_drop (n : ℕ) (s : Stream' α) : tail (drop n s) = drop n (tail s) := by simp
/-
**Stream.get_succ** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_succ (n : ℕ) (s : Stream' α) : get s (succ n) = get (tail s) n :=
  rfl

@[simp]
/-
**Stream.get_succ_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_succ_cons (n : ℕ) (s : Stream' α) (x : α) : get (x :: s) n.succ = get s n :=
  rfl
/-
**Stream.get_cons_append_zero** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma get_cons_append_zero {a : α} {x : List α} {s : Stream' α} :
    (a :: x ++ₛ s).get 0 = a := rfl
/-
**Stream.append_eq_cons** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma append_eq_cons {a : α} {as : Stream' α} : [a] ++ₛ as = a :: as := rfl
/-
**Stream.drop_zero** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem drop_zero {s : Stream' α} : s.drop 0 = s := rfl
/-
**Stream.drop_succ** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem drop_succ (n : ℕ) (s : Stream' α) : drop (succ n) s = drop n (tail s) :=
  rfl
/-
**Stream.head_drop** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_drop (a : Stream' α) (n : ℕ) : (a.drop n).head = a.get n := by simp
/-
**Stream.cons_injective2** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_injective2 : Function.Injective2 (cons : α → Stream' α → Stream' α) := fun x y s t h =>
  ⟨by rw [← get_zero_cons x s, h, get_zero_cons],
    Stream'.ext fun n => by rw [← get_succ_cons n _ x, h, get_succ_cons]⟩
/-
**Stream.cons_injective_left** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_injective_left (s : Stream' α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _
/-
**Stream.cons_injective_right** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_injective_right (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _
/-
**Stream.all_def** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem all_def (p : α → Prop) (s : Stream' α) : All p s = ∀ n, p (get s n) :=
  rfl
/-
**Stream.any_def** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem any_def (p : α → Prop) (s : Stream' α) : Any p s = ∃ n, p (get s n) :=
  rfl

@[simp]
/-
**Stream.mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_cons (a : α) (s : Stream' α) : a ∈ a::s :=
  Exists.intro 0 rfl
/-
**Stream.mem_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_cons_of_mem {a : α} {s : Stream' α} (b : α) : a ∈ s → a ∈ b::s := fun ⟨n, h⟩ =>
  Exists.intro (succ n) (by rw [get_succ, tail_cons, h])
/-
**Stream.eq_or_mem_of_mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_or_mem_of_mem_cons {a b : α} {s : Stream' α} : (a ∈ b::s) → a = b ∨ a ∈ s :=
    fun ⟨n, h⟩ => by
  rcases n with - | n'
  · left
    exact h
  · right
    rw [get_succ, tail_cons] at h
    exact ⟨n', h⟩
/-
**Stream.mem_of_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_of_get_eq {n : ℕ} {s : Stream' α} {a : α} : a = get s n → a ∈ s := fun h =>
  Exists.intro n h
/-
**Stream.mem_iff_exists_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_iff_exists_get_eq {s : Stream' α} {a : α} : a ∈ s ↔ ∃ n, a = s.get n where
  mp := by simp [Membership.mem, any_def]
  mpr h := mem_of_get_eq h.choose_spec

section Map

variable (f : α → β)

/-
**Stream.drop_map** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem drop_map (n : ℕ) (s : Stream' α) : drop n (map f s) = map f (drop n s) :=
  Stream'.ext fun _ => rfl

@[simp]
/-
**Stream.get_map** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_map (n : ℕ) (s : Stream' α) : get (map f s) n = f (get s n) :=
  rfl
/-
**Stream.tail_map** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_map (s : Stream' α) : tail (map f s) = map f (tail s) := rfl

@[simp]
/-
**Stream.head_map** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_map (s : Stream' α) : head (map f s) = f (head s) :=
  rfl
/-
**Stream.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_eq (s : Stream' α) : map f s = f (head s)::map f (tail s) := by
  rw [← Stream'.eta (map f s), tail_map, head_map]
/-
**Stream.map_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_cons (a : α) (s : Stream' α) : map f (a::s) = f a::map f s := by
  rw [← Stream'.eta (map f (a::s)), map_eq]; rfl

@[simp]
/-
**Stream.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id (s : Stream' α) : map id s = s :=
  rfl

@[simp]
/-
**Stream.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_map (g : β → δ) (f : α → β) (s : Stream' α) : map g (map f s) = map (g ∘ f) s :=
  rfl

@[simp]
/-
**Stream.map_tail** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_tail (s : Stream' α) : map f (tail s) = tail (map f s) :=
  rfl
/-
**Stream.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_map {a : α} {s : Stream' α} : a ∈ s → f a ∈ map f s := fun ⟨n, h⟩ =>
  Exists.intro n (by rw [get_map, h])
/-
**Stream.exists_of_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_of_mem_map {f} {b : β} {s : Stream' α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun ⟨n, h⟩ => ⟨get s n, ⟨n, rfl⟩, h.symm⟩

end Map

section Zip

variable (f : α → β → δ)

/-
**Stream.drop_zip** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem drop_zip (n : ℕ) (s₁ : Stream' α) (s₂ : Stream' β) :
    drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
  Stream'.ext fun _ => rfl

@[simp]
/-
**Stream.get_zip** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_zip (n : ℕ) (s₁ : Stream' α) (s₂ : Stream' β) :
    get (zip f s₁ s₂) n = f (get s₁ n) (get s₂ n) :=
  rfl
/-
**Stream.head_zip** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_zip (s₁ : Stream' α) (s₂ : Stream' β) : head (zip f s₁ s₂) = f (head s₁) (head s₂) :=
  rfl
/-
**Stream.tail_zip** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_zip (s₁ : Stream' α) (s₂ : Stream' β) :
    tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) :=
  rfl
/-
**Stream.zip_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zip_eq (s₁ : Stream' α) (s₂ : Stream' β) :
    zip f s₁ s₂ = f (head s₁) (head s₂)::zip f (tail s₁) (tail s₂) := by
  rw [← Stream'.eta (zip f s₁ s₂)]; rfl

@[simp]
/-
**Stream.get_enum** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_enum (s : Stream' α) (n : ℕ) : get (enum s) n = (n, s.get n) :=
  rfl
/-
**Stream.enum_eq_zip** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem enum_eq_zip (s : Stream' α) : enum s = zip Prod.mk nats s :=
  rfl

end Zip

@[simp]
/-
**Stream.mem_const** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_const (a : α) : a ∈ const a :=
  Exists.intro 0 rfl
/-
**Stream.const_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_eq (a : α) : const a = a::const a := by
  apply Stream'.ext; intro n
  cases n <;> rfl

@[simp]
/-
**Stream.tail_const** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_const (a : α) : tail (const a) = const a :=
  suffices tail (a::const a) = const a by rwa [← const_eq] at this
  rfl

@[simp]
/-
**Stream.map_const** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) :=
  rfl

@[simp]
/-
**Stream.get_const** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_const (n : ℕ) (a : α) : get (const a) n = a :=
  rfl

@[simp]
/-
**Stream.drop_const** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem drop_const (n : ℕ) (a : α) : drop n (const a) = const a :=
  Stream'.ext fun _ => rfl

@[simp]
/-
**Stream.head_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a :=
  rfl
/-
**Stream.get_succ_iterate'** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_succ_iterate' (n : ℕ) (f : α → α) (a : α) :
    get (iterate f a) (succ n) = f (get (iterate f a) n) := rfl
/-
**Stream.tail_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) := by
  ext n
  rw [get_tail]
  induction n with
  | zero => rfl
  | succ n ih => rw [get_succ_iterate', ih, get_succ_iterate']
/-
**Stream.iterate_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_eq (f : α → α) (a : α) : iterate f a = a::iterate f (f a) := by
  rw [← Stream'.eta (iterate f a)]
  rw [tail_iterate]; rfl

@[simp]
/-
**Stream.get_zero_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_zero_iterate (f : α → α) (a : α) : get (iterate f a) 0 = a :=
  rfl
/-
**Stream.get_succ_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_succ_iterate (n : ℕ) (f : α → α) (a : α) :
    get (iterate f a) (succ n) = get (iterate f (f a)) n := by rw [get_succ, tail_iterate]

section Bisim

variable (R : Stream' α → Stream' α → Prop)

/-- equivalence relation -/
local infixl:50 " ~ " => R

/-- Streams `s₁` and `s₂` are defined to be bisimulations if
their heads are equal and tails are bisimulations. -/
/-
**Stream.IsBisimulation** 是 Mathlib 中的一个定义，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Streams `s₁` and `s₂` are defined to be bisimulations if
their heads are equal and tails are bisimulations.
-/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ →
      head s₁ = head s₂ ∧ tail s₁ ~ tail s₂
/-
**Stream.get_of_bisim** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_of_bisim (bisim : IsBisimulation R) {s₁ s₂} :
    ∀ n, s₁ ~ s₂ → get s₁ n = get s₂ n ∧ drop (n + 1) s₁ ~ drop (n + 1) s₂
  | 0, h => bisim h
  | n + 1, h =>
    match bisim h with
    | ⟨_, trel⟩ => get_of_bisim bisim n trel

-- If two streams are bisimilar, then they are equal
/-
**Stream.eq_of_bisim** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} : s₁ ~ s₂ → s₁ = s₂ := fun r =>
  Stream'.ext fun n => And.left (get_of_bisim R bisim n r)

end Bisim

/-
**Stream.bisim_simple** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bisim_simple (s₁ s₂ : Stream' α) :
    head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ := fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by grind)
    (And.intro hh (And.intro ht₁ ht₂))
/-
**Stream.coinduction** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coinduction {s₁ s₂ : Stream' α} :
    head s₁ = head s₂ →
      (∀ (β : Type u) (fr : Stream' α → β),
      fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂ :=
  fun hh ht =>
  eq_of_bisim
    (fun s₁ s₂ =>
      head s₁ = head s₂ ∧
        ∀ (β : Type u) (fr : Stream' α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂))
    (fun s₁ s₂ h =>
      have h₁ : head s₁ = head s₂ := And.left h
      have h₂ : head (tail s₁) = head (tail s₂) := And.right h α (@head α) h₁
      have h₃ :
        ∀ (β : Type u) (fr : Stream' α → β),
          fr (tail s₁) = fr (tail s₂) → fr (tail (tail s₁)) = fr (tail (tail s₂)) :=
        fun β fr => And.right h β fun s => fr (tail s)
      And.intro h₁ (And.intro h₂ h₃))
    (And.intro hh ht)

@[simp]
/-
**Stream.iterate_id** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_id (a : α) : iterate id a = const a :=
  coinduction rfl fun β fr ch => by rw [tail_iterate, tail_const]; exact ch
/-
**Stream.map_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold map iterate get
    rw [map, get] at ih
    rw [iterate]
    exact congrArg f ih

section Corec

/-
**Stream.corec_def** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
  rfl
/-
**Stream.corec_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a :: corec f g (g a) := by
  rw [corec_def, map_eq, head_iterate, tail_iterate]; rfl
/-
**Stream.corec_id_id_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem corec_id_id_eq_const (a : α) : corec id id a = const a := by
  rw [corec_def, map_id, iterate_id]
/-
**Stream.corec_id_f_eq_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem corec_id_f_eq_iterate (f : α → α) (a : α) : corec id f a = iterate f a :=
  rfl

end Corec

section Corec'

/-
**Stream.corec'_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem corec'_eq (f : α → β × α) (a : α) : corec' f a = (f a).1 :: corec' f (f a).2 :=
  corec_eq _ _ _

end Corec'

/-
**Stream.unfolds_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unfolds_eq (g : α → β) (f : α → α) (a : α) : unfolds g f a = g a :: unfolds g f (f a) := by
  unfold unfolds; rw [corec_eq]
/-
**Stream.get_unfolds_head_tail** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_unfolds_head_tail (n : ℕ) (s : Stream' α) : get (unfolds head tail s) n = get s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, get_succ, unfolds_eq, tail_cons, ih]
/-
**Stream.unfolds_head_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unfolds_head_eq : ∀ s : Stream' α, unfolds head tail s = s := fun s =>
  Stream'.ext fun n => get_unfolds_head_tail n s
/-
**Stream.interleave_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem interleave_eq (s₁ s₂ : Stream' α) : s₁ ⋈ s₂ = head s₁::head s₂::(tail s₁ ⋈ tail s₂) := by
  let t := tail s₁ ⋈ tail s₂
  change s₁ ⋈ s₂ = head s₁::head s₂::t
  unfold interleave; unfold corecOn; rw [corec_eq]; dsimp; rw [corec_eq]; rfl
/-
**Stream.tail_interleave** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_interleave (s₁ s₂ : Stream' α) : tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁ := by
  unfold interleave corecOn; rw [corec_eq]; rfl
/-
**Stream.interleave_tail_tail** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem interleave_tail_tail (s₁ s₂ : Stream' α) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) := by
  rw [interleave_eq s₁ s₂]; rfl
/-
**Stream.get_interleave_left** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_interleave_left : ∀ (n : ℕ) (s₁ s₂ : Stream' α),
    get (s₁ ⋈ s₂) (2 * n) = get s₁ n
  | 0, _, _ => rfl
  | n + 1, s₁, s₂ => by
    change get (s₁ ⋈ s₂) (succ (succ (2 * n))) = get s₁ (succ n)
    rw [get_succ, get_succ, interleave_eq, tail_cons, tail_cons]
    rw [get_interleave_left n (tail s₁) (tail s₂)]
    rfl
/-
**Stream.get_interleave_right** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_interleave_right : ∀ (n : ℕ) (s₁ s₂ : Stream' α),
    get (s₁ ⋈ s₂) (2 * n + 1) = get s₂ n
  | 0, _, _ => rfl
  | n + 1, s₁, s₂ => by
    change get (s₁ ⋈ s₂) (succ (succ (2 * n + 1))) = get s₂ (succ n)
    rw [get_succ, get_succ, interleave_eq, tail_cons, tail_cons,
      get_interleave_right n (tail s₁) (tail s₂)]
    rfl
/-
**Stream.mem_interleave_left** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_interleave_left {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a ∈ s₁ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n) (by rw [h, get_interleave_left])
/-
**Stream.mem_interleave_right** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_interleave_right {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a ∈ s₂ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n + 1) (by rw [h, get_interleave_right])
/-
**Stream.odd_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem odd_eq (s : Stream' α) : odd s = even (tail s) :=
  rfl

@[simp]
/-
**Stream.head_even** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_even (s : Stream' α) : head (even s) = head s :=
  rfl
/-
**Stream.tail_even** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_even (s : Stream' α) : tail (even s) = even (tail (tail s)) := by
  unfold even
  rw [corec_eq]
  rfl
/-
**Stream.even_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem even_cons_cons (a₁ a₂ : α) (s : Stream' α) : even (a₁::a₂::s) = a₁::even s := by
  unfold even
  rw [corec_eq]; rfl
/-
**Stream.even_tail** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem even_tail (s : Stream' α) : even (tail s) = odd s :=
  rfl
/-
**Stream.even_interleave** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem even_interleave (s₁ s₂ : Stream' α) : even (s₁ ⋈ s₂) = s₁ :=
  eq_of_bisim (fun s₁' s₁ => ∃ s₂, s₁' = even (s₁ ⋈ s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ => by
      rw [h₁]
      constructor
      · rfl
      · exact ⟨tail s₂, by rw [interleave_eq, even_cons_cons, tail_cons]⟩)
    (Exists.intro s₂ rfl)
/-
**Stream.interleave_even_odd** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem interleave_even_odd (s₁ : Stream' α) : even s₁ ⋈ odd s₁ = s₁ :=
  eq_of_bisim (fun s' s => s' = even s ⋈ odd s)
    (fun s' s (h : s' = even s ⋈ odd s) => by
      rw [h]; constructor
      · rfl
      · simp [odd_eq, odd_eq, tail_interleave, tail_even])
    rfl
/-
**Stream.get_even** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_even : ∀ (n : ℕ) (s : Stream' α), get (even s) n = get s (2 * n)
  | 0, _ => rfl
  | succ n, s => by
    change get (even s) (succ n) = get s (succ (succ (2 * n)))
    rw [get_succ, get_succ, tail_even, get_even n]; rfl
/-
**Stream.get_odd** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_odd : ∀ (n : ℕ) (s : Stream' α), get (odd s) n = get s (2 * n + 1) := fun n s => by
  rw [odd_eq, get_even]; rfl
/-
**Stream.mem_of_mem_even** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_of_mem_even (a : α) (s : Stream' α) : a ∈ even s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n) (by rw [h, get_even])
/-
**Stream.mem_of_mem_odd** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_of_mem_odd (a : α) (s : Stream' α) : a ∈ odd s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n + 1) (by rw [h, get_odd])
/-
**Stream.nil_append_stream** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem nil_append_stream (s : Stream' α) : appendStream' [] s = s :=
  rfl
/-
**Stream.cons_append_stream** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_append_stream (a : α) (l : List α) (s : Stream' α) :
    appendStream' (a::l) s = a::appendStream' l s :=
  rfl
/-
**Stream.append_append_stream** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem append_append_stream : ∀ (l₁ l₂ : List α) (s : Stream' α),
    l₁ ++ l₂ ++ₛ s = l₁ ++ₛ (l₂ ++ₛ s)
  | [], _, _ => rfl
  | List.cons a l₁, l₂, s => by
    rw [List.cons_append, cons_append_stream, cons_append_stream, append_append_stream l₁]
/-
**Stream.get_append_left** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma get_append_left (h : n < x.length) : (x ++ₛ a).get n = x[n] := by
  induction x generalizing n with
  | nil => simp at h
  | cons b x ih =>
    rcases n with (_ | n)
    · simp
    · simp [ih n (by simpa using h), cons_append_stream]
/-
**Stream.get_append_right** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma get_append_right : (x ++ₛ a).get (x.length + n) = a.get n := by
  induction x <;> simp [Nat.succ_add, *, cons_append_stream]
/-
**Stream.get_append_length** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma get_append_length : (x ++ₛ a).get x.length = a.get 0 := get_append_right 0 x a
/-
**Stream.append_right_injective** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma append_right_injective (h : x ++ₛ a = x ++ₛ b) : a = b := by
  ext n; replace h := congr_arg (fun a ↦ a.get (x.length + n)) h; simpa using h
/-
**Stream.append_right_inj** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma append_right_inj : x ++ₛ a = x ++ₛ b ↔ a = b :=
  ⟨append_right_injective x a b, by simp +contextual⟩
/-
**Stream.append_left_injective** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma append_left_injective (h : x ++ₛ a = y ++ₛ b) (hl : x.length = y.length) : x = y := by
  apply List.ext_getElem hl
  intros
  rw [← get_append_left, ← get_append_left, h]
/-
**Stream.map_append_stream** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_append_stream (f : α → β) :
    ∀ (l : List α) (s : Stream' α), map f (l ++ₛ s) = List.map f l ++ₛ map f s
  | [], _ => rfl
  | List.cons a l, s => by
    rw [cons_append_stream, List.map_cons, map_cons, cons_append_stream, map_append_stream f l]
/-
**Stream.drop_append_stream** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem drop_append_stream : ∀ (l : List α) (s : Stream' α), drop l.length (l ++ₛ s) = s
  | [], s => rfl
  | List.cons a l, s => by
    rw [List.length_cons, drop_succ, cons_append_stream, tail_cons, drop_append_stream l s]
/-
**Stream.append_stream_head_tail** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_stream_head_tail (s : Stream' α) : [head s] ++ₛ tail s = s := by
  simp
/-
**Stream.mem_append_stream_right** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_append_stream_right : ∀ {a : α} (l : List α) {s : Stream' α}, a ∈ s → a ∈ l ++ₛ s
  | _, [], _, h => h
  | a, List.cons _ l, s, h =>
    have ih : a ∈ l ++ₛ s := mem_append_stream_right l h
    mem_cons_of_mem _ ih
/-
**Stream.mem_append_stream_left** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_append_stream_left : ∀ {a : α} {l : List α} (s : Stream' α), a ∈ l → a ∈ l ++ₛ s
  | _, [], _, h => absurd h List.not_mem_nil
  | a, List.cons b l, s, h =>
    Or.elim (List.eq_or_mem_of_mem_cons h) (fun aeqb : a = b => Exists.intro 0 aeqb)
      fun ainl : a ∈ l => mem_cons_of_mem b (mem_append_stream_left s ainl)

@[simp]
/-
**Stream.take_zero** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem take_zero (s : Stream' α) : take 0 s = [] :=
  rfl

-- This lemma used to be simp, but we removed it from the simp set because:
-- 1) It duplicates the (often large) `s` term, resulting in large tactic states.
-- 2) It conflicts with the very useful `dropLast_take` lemma below (causing nonconfluence).
/-
**Stream.take_succ** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem take_succ (n : ℕ) (s : Stream' α) : take (succ n) s = head s::take n (tail s) :=
  rfl
/-
**Stream.take_succ_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem take_succ_cons {a : α} (n : ℕ) (s : Stream' α) :
    take (n + 1) (a::s) = a :: take n s := rfl
/-
**Stream.take_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem take_succ' {s : Stream' α} : ∀ n, s.take (n + 1) = s.take n ++ [s.get n]
  | 0 => rfl
  | n + 1 => by rw [take_succ, take_succ' n, ← List.cons_append, ← take_succ, get_tail]

@[simp]
/-
**Stream.length_take** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_take (n : ℕ) (s : Stream' α) : (take n s).length = n := by
  induction n generalizing s <;> simp [*, take_succ]

@[simp]
/-
**Stream.take_take** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem take_take {s : Stream' α} : ∀ {m n}, (s.take n).take m = s.take (min n m)
  | 0, n => by rw [Nat.min_zero, List.take_zero, take_zero]
  | m, 0 => by rw [Nat.zero_min, take_zero, List.take_nil]
  | m + 1, n + 1 => by rw [take_succ, List.take_succ_cons, Nat.succ_min_succ, take_succ, take_take]
/-
**Stream.concat_take_get** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem concat_take_get {n : ℕ} {s : Stream' α} : s.take n ++ [s.get n] = s.take (n + 1) :=
  (take_succ' n).symm
/-
**Stream.getElem** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem?_take {s : Stream' α} : ∀ {k n}, k < n → (s.take n)[k]? = s.get k
  | 0, _ + 1, _ => by simp only [length_take, zero_lt_succ, List.getElem?_eq_getElem]; rfl
  | k + 1, n + 1, h => by
    rw [take_succ, List.getElem?_cons_succ, getElem?_take (Nat.lt_of_succ_lt_succ h), get_succ]
/-
**Stream.getElem** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem?_take_succ (n : ℕ) (s : Stream' α) :
    (take (succ n) s)[n]? = some (get s n) :=
  getElem?_take (Nat.lt_succ_self n)
/-
**Stream.dropLast_take** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem dropLast_take {n : ℕ} {xs : Stream' α} :
    (Stream'.take n xs).dropLast = Stream'.take (n - 1) xs := by
  cases n with
  | zero => simp
  | succ n => rw [take_succ', List.dropLast_concat, Nat.add_one_sub_one]

@[simp]
/-
**Stream.append_take_drop** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_take_drop (n : ℕ) (s : Stream' α) : appendStream' (take n s) (drop n s) = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [take_succ, drop_succ, cons_append_stream, ih (tail s), Stream'.eta]
/-
**Stream.append_take** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma append_take : x ++ (a.take n) = (x ++ₛ a).take (x.length + n) := by
  induction x <;> simp [take, Nat.add_comm, cons_append_stream, *]
/-
**Stream.take_get** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma take_get (h : m < (a.take n).length) : (a.take n)[m] = a.get m := by
  nth_rw 2 [← append_take_drop n a]; rw [get_append_left]
/-
**Stream.take_append_of_le_length** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem take_append_of_le_length (h : n ≤ x.length) :
    (x ++ₛ a).take n = x.take n := by
  apply List.ext_getElem (by simp [h])
  intro _ _ _; rw [List.getElem_take, take_get, get_append_left]
/-
**Stream.take_add** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma take_add : a.take (m + n) = a.take m ++ (a.drop m).take n := by
  apply append_left_injective _ _ (a.drop (m + n)) ((a.drop m).drop n) <;>
    simp [-drop_drop]
/-
**Stream.take_prefix_take_left** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] lemma take_prefix_take_left (h : m ≤ n) : a.take m <+: a.take n := by
  rw [(by simp [h] : a.take m = (a.take n).take m)]
  apply List.take_prefix
/-
**Stream.take_prefix** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma take_prefix : a.take m <+: a.take n ↔ m ≤ n :=
  ⟨fun h ↦ by simpa using h.length_le, take_prefix_take_left m n a⟩
/-
**Stream.map_take** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_take (f : α → β) : (a.take n).map f = (a.map f).take n := by
  apply List.ext_getElem <;> simp
/-
**Stream.take_drop** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma take_drop : (a.drop m).take n = (a.take (m + n)).drop m := by
  apply List.ext_getElem <;> simp
/-
**Stream.drop_append_of_le_length** 是 Mathlib 中的一个引理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma drop_append_of_le_length (h : n ≤ x.length) :
    (x ++ₛ a).drop n = x.drop n ++ₛ a := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
  ext k; rcases lt_or_ge k m with _ | hk
  · rw [get_drop, get_append_left, get_append_left, List.getElem_drop]; simpa [hm]
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hm' : m = (x.drop n).length := by simp [hm]
    simp_rw [get_drop, ← Nat.add_assoc, ← hm, get_append_right, hm', get_append_right]

-- Take theorem reduces a proof of equality of infinite streams to an
-- induction over all their finite approximations.
/-
**Stream.take_theorem** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem take_theorem (s₁ s₂ : Stream' α) (h : ∀ n : ℕ, take n s₁ = take n s₂) : s₁ = s₂ := by
  ext n
  induction n with
  | zero => simpa [take] using h 1
  | succ n =>
    have h₁ : some (get s₁ (succ n)) = some (get s₂ (succ n)) := by
      rw [← getElem?_take_succ, ← getElem?_take_succ, h (succ (succ n))]
    injection h₁
/-
**Stream.cycle_g_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem cycle_g_cons (a : α) (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
    Stream'.cycleG (a, a₁::l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) :=
  rfl
/-
**Stream.cycle_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cycle_eq : ∀ (l : List α) (h : l ≠ []), cycle l h = l ++ₛ cycle l h
  | [], h => absurd rfl h
  | List.cons a l, _ =>
    have gen (l' a') : corec Stream'.cycleF Stream'.cycleG (a', l', a, l) =
        (a'::l') ++ₛ corec Stream'.cycleF Stream'.cycleG (a, l, a, l) := by
      induction l' generalizing a' with
      | nil => rw [corec_eq]; rfl
      | cons a₁ l₁ ih => rw [corec_eq, Stream'.cycle_g_cons, ih a₁]; rfl
    gen l a
/-
**Stream.mem_cycle** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_cycle {a : α} {l : List α} : ∀ h : l ≠ [], a ∈ l → a ∈ cycle l h := fun h ainl => by
  rw [cycle_eq]; exact mem_append_stream_left _ ainl

@[simp]
/-
**Stream.cycle_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cycle_singleton (a : α) : cycle [a] (by simp) = const a :=
  coinduction rfl fun β fr ch => by rwa [cycle_eq, const_eq]
/-
**Stream.tails_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tails_eq (s : Stream' α) : tails s = tail s::tails (tail s) := by
  unfold tails; rw [corec_eq]; rfl

@[simp]
/-
**Stream.get_tails** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_tails (n : ℕ) (s : Stream' α) : get (tails s) n = drop n (tail s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, drop_succ, tails_eq, tail_cons, ih]
/-
**Stream.tails_eq_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tails_eq_iterate (s : Stream' α) : tails s = iterate tail (tail s) :=
  rfl
/-
**Stream.inits_core_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inits_core_eq (l : List α) (s : Stream' α) :
    initsCore l s = l::initsCore (l ++ [head s]) (tail s) := by
    unfold initsCore corecOn
    rw [corec_eq]
/-
**Stream.tail_inits** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_inits (s : Stream' α) :
    tail (inits s) = initsCore [head s, head (tail s)] (tail (tail s)) := by
    unfold inits
    rw [inits_core_eq]; rfl
/-
**Stream.inits_tail** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inits_tail (s : Stream' α) : inits (tail s) = initsCore [head (tail s)] (tail (tail s)) :=
  rfl
/-
**Stream.cons_get_inits_core** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_get_inits_core (a : α) (n : ℕ) (l : List α) (s : Stream' α) :
    (a :: get (initsCore l s) n) = get (initsCore (a :: l) s) n := by
  induction n generalizing l s with
  | zero => rfl
  | succ n ih =>
    rw [get_succ, inits_core_eq, tail_cons, ih, inits_core_eq (a :: l) s]
    rfl

@[simp]
/-
**Stream.get_inits** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_inits (n : ℕ) (s : Stream' α) : get (inits s) n = take (succ n) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, take_succ, ← ih, tail_inits, inits_tail, cons_get_inits_core]
/-
**Stream.inits_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inits_eq (s : Stream' α) :
    inits s = [head s]::map (List.cons (head s)) (inits (tail s)) := by
  apply Stream'.ext; intro n
  cases n
  · rfl
  · rw [get_inits, get_succ, tail_cons, get_map, get_inits]
    rfl
/-
**Stream.zip_inits_tails** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zip_inits_tails (s : Stream' α) : zip appendStream' (inits s) (tails s) = const s := by
  ext
  simp
/-
**Stream.identity** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem identity (s : Stream' α) : pure id ⊛ s = s :=
  rfl
/-
**Stream.composition** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem composition (g : Stream' (β → δ)) (f : Stream' (α → β)) (s : Stream' α) :
    pure comp ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s) :=
  rfl
/-
**Stream.homomorphism** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homomorphism (f : α → β) (a : α) : pure f ⊛ pure a = pure (f a) :=
  rfl
/-
**Stream.interchange** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem interchange (fs : Stream' (α → β)) (a : α) :
    fs ⊛ pure a = (pure fun f : α → β => f a) ⊛ fs :=
  rfl
/-
**Stream.map_eq_apply** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_eq_apply (f : α → β) (s : Stream' α) : map f s = pure f ⊛ s :=
  rfl
/-
**Stream.get_nats** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_nats (n : ℕ) : get nats n = n :=
  rfl
/-
**Stream.nats_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nats_eq : nats = cons 0 (map succ nats) := by
  apply Stream'.ext; intro n
  cases n
  · rfl
  rw [get_succ]; rfl

end Stream'

