/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Relator

/-!
# Double universal quantification on a list

This file provides an API for `List.Forall₂` (definition in `Data.List.Defs`).
`Forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length, and whenever `a` is the nth element
of `l₁`, and `b` is the nth element of `l₂`, then `R a b` is satisfied.
-/

public section


open Nat Function

namespace List

variable {α β γ δ : Type*} {R S : α → β → Prop} {P : γ → δ → Prop} {Rₐ : α → α → Prop}

open Relator

mk_iff_of_inductive_prop List.Forall₂ List.forall₂_iff

/-
**List.Forall** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (α → Prop) → List α → Prop
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Forall₂.imp (H : ∀ a b, R a b → S a b) {l₁ l₂} (h : Forall₂ R l₁ l₂) : Forall₂ S l₁ l₂ := by
  induction h <;> constructor <;> solve_by_elim
/-
**List.Forall** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (α → Prop) → List α → Prop
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Forall₂.mp {Q : α → β → Prop} (h : ∀ a b, Q a b → R a b → S a b) :
    ∀ {l₁ l₂}, Forall₂ Q l₁ l₂ → Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂
  | [], [], Forall₂.nil, Forall₂.nil => Forall₂.nil
  | a :: _, b :: _, Forall₂.cons hr hrs, Forall₂.cons hq hqs =>
    Forall₂.cons (h a b hr hq) (Forall₂.mp h hrs hqs)
/-
**List.Forall** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (α → Prop) → List α → Prop
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Forall₂.flip : ∀ {a b}, Forall₂ (flip R) b a → Forall₂ R a b
  | _, _, Forall₂.nil => Forall₂.nil
  | _ :: _, _ :: _, Forall₂.cons h₁ h₂ => Forall₂.cons h₁ h₂.flip

@[simp]
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_same : ∀ {l : List α}, Forall₂ Rₐ l l ↔ ∀ x ∈ l, Rₐ x x
  | [] => by simp
  | a :: l => by simp [@forall₂_same l]
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_refl [Std.Refl Rₐ] (l : List α) : Forall₂ Rₐ l l :=
  forall₂_same.2 fun _ _ => refl _

@[simp]
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_eq_eq_eq : Forall₂ ((· = ·) : α → α → Prop) = Eq := by
  funext a b; apply propext
  constructor
  · intro h
    induction h
    · rfl
    simp only [*]
  · rintro rfl
    exact forall₂_refl _

@[simp]
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_nil_left_iff {l} : Forall₂ R nil l ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

@[simp]
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_nil_right_iff {l} : Forall₂ R l nil ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_cons_left_iff {a l u} :
    Forall₂ R (a :: l) u ↔ ∃ b u', R a b ∧ Forall₂ R l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_cons_right_iff {b l u} :
    Forall₂ R u (b :: l) ↔ ∃ a u', R a b ∧ Forall₂ R u' l ∧ u = a :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_and_left {p : α → Prop} :
    ∀ l u, Forall₂ (fun a b => p a ∧ R a b) l u ↔ (∀ a ∈ l, p a) ∧ Forall₂ R l u
  | [], u => by
    simp only [forall₂_nil_left_iff, forall_prop_of_false not_mem_nil, imp_true_iff, true_and]
  | a :: l, u => by
    simp only [forall₂_and_left l, forall₂_cons_left_iff, forall_mem_cons, and_assoc,
      exists_and_left]
    simp only [and_comm, and_assoc, ← exists_and_right]

@[simp]
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_map_left_iff {f : γ → α} :
    ∀ {l u}, Forall₂ R (map f l) u ↔ Forall₂ (fun c b => R (f c) b) l u
  | [], _ => by simp only [map, forall₂_nil_left_iff]
  | a :: l, _ => by simp only [map, forall₂_cons_left_iff, forall₂_map_left_iff]

@[simp]
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_map_right_iff {f : γ → β} :
    ∀ {l u}, Forall₂ R l (map f u) ↔ Forall₂ (fun a c => R a (f c)) l u
  | _, [] => by simp only [map, forall₂_nil_right_iff]
  | _, b :: u => by simp only [map, forall₂_cons_right_iff, forall₂_map_right_iff]
/-
**List.left_unique_forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_unique_forall₂' (hr : LeftUnique R) : ∀ {a b c}, Forall₂ R a c → Forall₂ R b c → a = b
  | _, _, _, Forall₂.nil, Forall₂.nil => rfl
  | _, _, _, Forall₂.cons ha₀ h₀, Forall₂.cons ha₁ h₁ =>
    hr ha₀ ha₁ ▸ left_unique_forall₂' hr h₀ h₁ ▸ rfl
/-
**List._root_.Relator.LeftUnique.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Relator.LeftUnique.forall₂ (hr : LeftUnique R) : LeftUnique (Forall₂ R) :=
  @left_unique_forall₂' _ _ _ hr
/-
**List.right_unique_forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_unique_forall₂' (hr : RightUnique R) :
    ∀ {a b c}, Forall₂ R a b → Forall₂ R a c → b = c
  | _, _, _, Forall₂.nil, Forall₂.nil => rfl
  | _, _, _, Forall₂.cons ha₀ h₀, Forall₂.cons ha₁ h₁ =>
    hr ha₀ ha₁ ▸ right_unique_forall₂' hr h₀ h₁ ▸ rfl
/-
**List._root_.Relator.RightUnique.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Relator.RightUnique.forall₂ (hr : RightUnique R) : RightUnique (Forall₂ R) :=
  @right_unique_forall₂' _ _ _ hr
/-
**List._root_.Relator.BiUnique.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Relator.BiUnique.forall₂ (hr : BiUnique R) : BiUnique (Forall₂ R) :=
  ⟨hr.left.forall₂, hr.right.forall₂⟩
/-
**List.Forall** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (α → Prop) → List α → Prop
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Forall₂.length_eq : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → length l₁ = length l₂
  | _, _, Forall₂.nil => rfl
  | _, _, Forall₂.cons _ h₂ => congr_arg succ (Forall₂.length_eq h₂)
/-
**List.Forall** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (α → Prop) → List α → Prop
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Forall₂.get :
    ∀ {x : List α} {y : List β}, Forall₂ R x y →
      ∀ ⦃i : ℕ⦄ (hx : i < x.length) (hy : i < y.length), R (x.get ⟨i, hx⟩) (y.get ⟨i, hy⟩)
  | _, _, Forall₂.cons ha _, 0, _, _ => ha
  | _, _, Forall₂.cons _ hl, succ _, _, _ => hl.get _ _
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_of_length_eq_of_get :
    ∀ {x : List α} {y : List β},
      x.length = y.length → (∀ i h₁ h₂, R (x.get ⟨i, h₁⟩) (y.get ⟨i, h₂⟩)) → Forall₂ R x y
  | [], [], _, _ => Forall₂.nil
  | _ :: _, _ :: _, hl, h =>
    Forall₂.cons (h 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))
      (forall₂_of_length_eq_of_get (succ.inj hl) fun i h₁ h₂ =>
        h i.succ (succ_lt_succ h₁) (succ_lt_succ h₂))
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_iff_get {l₁ : List α} {l₂ : List β} :
    Forall₂ R l₁ l₂ ↔ l₁.length = l₂.length ∧ ∀ i h₁ h₂, R (l₁.get ⟨i, h₁⟩) (l₂.get ⟨i, h₂⟩) :=
  ⟨fun h => ⟨h.length_eq, h.get⟩, fun h => forall₂_of_length_eq_of_get h.1 h.2⟩
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_zip : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b
  | _, _, Forall₂.cons h₁ h₂, x, y, hx => by
    rw [zip, zipWith, mem_cons] at hx
    match hx with
    | Or.inl rfl => exact h₁
    | Or.inr h₃ => exact forall₂_zip h₂ h₃
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_iff_zip {l₁ l₂} :
    Forall₂ R l₁ l₂ ↔ length l₁ = length l₂ ∧ ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b :=
  ⟨fun h => ⟨Forall₂.length_eq h, @forall₂_zip _ _ _ _ _ h⟩, fun h => by
    obtain ⟨h₁, h₂⟩ := h
    induction l₁ generalizing l₂ with
    | nil =>
      cases length_eq_zero_iff.1 h₁.symm
      constructor
    | cons a l₁ IH =>
      rcases l₂ with - | ⟨b, l₂⟩
      · simp at h₁
      · simp only [length_cons, succ.injEq] at h₁
        exact Forall₂.cons (h₂ <| by simp [zip])
          (IH h₁ fun h => h₂ <| by
            simp only [zip, zipWith, mem_cons, Prod.mk.injEq]; right
            simpa [zip] using h)⟩
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_take : ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (take n l₁) (take n l₂)
  | 0, _, _, _ => by simp only [Forall₂.nil, take]
  | _ + 1, _, _, Forall₂.nil => by simp only [Forall₂.nil, take]
  | n + 1, _, _, Forall₂.cons h₁ h₂ => by simp [And.intro h₁ h₂, forall₂_take n]
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_drop : ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (drop n l₁) (drop n l₂)
  | 0, _, _, h => by simp only [drop, h]
  | _ + 1, _, _, Forall₂.nil => by simp only [Forall₂.nil, drop]
  | n + 1, _, _, Forall₂.cons h₁ h₂ => by simp [And.intro h₁ h₂, forall₂_drop n]
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_take_append (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.take (length l₁) l) l₁ := by
  have h' : Forall₂ R (take (length l₁) l) (take (length l₁) (l₁ ++ l₂)) :=
    forall₂_take (length l₁) h
  rwa [take_left] at h'
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_drop_append (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.drop (length l₁) l) l₂ := by
  have h' : Forall₂ R (drop (length l₁) l) (drop (length l₁) (l₁ ++ l₂)) :=
    forall₂_drop (length l₁) h
  rwa [drop_left] at h'
/-
**List.rel_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop},   Relator.BiUnique R →
     Relator.LiftFun R (Relator.LiftFun (List.Forall₂ R) Iff) (fun x1 x2 => x1 ∈
 x2) fun x1 x2 => x1 ∈ x2
参数：Relator.LiftFun (List.Forall₂ R) Iff；fun x1 x2 => x1 ∈ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Relator.rel_or`：rel_or : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∨ ·) (· ∨ ·)
· 使用引理 `Relator.rel_eq`：rel_eq {r : α -> β -> Prop} (hr : BiUnique r) : (r ⇒ r ⇒
 (· ↔ ·)) (· = ·) (· = ·)
-/
theorem rel_mem (hr : BiUnique R) : (R ⇒ Forall₂ R ⇒ Iff) (· ∈ ·) (· ∈ ·)
  | a, b, _, [], [], Forall₂.nil => by simp only [not_mem_nil]
  | a, b, h, a' :: as, b' :: bs, Forall₂.cons h₁ h₂ => by
    simp only [mem_cons]
    exact rel_or (rel_eq hr h h₁) (rel_mem hr h h₂)
/-
**List.rel_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {R : α → β →
 Prop} {P : γ → δ → Prop},   Relator.LiftFun (Relator.LiftFun R P) (Relator.Lift
Fun (List.Forall₂ R) (List.Forall₂ P)) List.map List.map
参数：Relator.LiftFun R P；Relator.LiftFun (List.Forall₂ R) (List.Forall₂ P)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
-/
theorem rel_map : ((R ⇒ P) ⇒ Forall₂ R ⇒ Forall₂ P) map map
  | _, _, _, [], [], Forall₂.nil => Forall₂.nil
  | _, _, h, _ :: _, _ :: _, Forall₂.cons h₁ h₂ => Forall₂.cons (h h₁) (rel_map (@h) h₂)
/-
**List.rel_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop},   Relator.LiftFun (Lis
t.Forall₂ R) (Relator.LiftFun (List.Forall₂ R) (List.Forall₂ R)) (fun x1 x2 => x
1 ++ x2)     fun x1 x2 => x1 ++ x2
参数：List.Forall₂ R；Relator.LiftFun (List.Forall₂ R) (List.Forall₂ R)；fun x1 x2 =>
 x1 ++ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
-/
theorem rel_append : (Forall₂ R ⇒ Forall₂ R ⇒ Forall₂ R) (· ++ ·) (· ++ ·)
  | [], [], _, _, _, hl => hl
  | _, _, Forall₂.cons h₁ h₂, _, _, hl => Forall₂.cons h₁ (rel_append h₂ hl)
/-
**List.rel_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop},   Relator.LiftFun (Lis
t.Forall₂ R) (List.Forall₂ R) List.reverse List.reverse
参数：List.Forall₂ R；List.Forall₂ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.rel_append`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop},   R
elator.LiftFun (List.Forall₂ R) (Relator.LiftFun (List.Forall₂ R) (List.Forall₂ 
R)) (…
-/
theorem rel_reverse : (Forall₂ R ⇒ Forall₂ R) reverse reverse
  | [], [], Forall₂.nil => Forall₂.nil
  | _, _, Forall₂.cons h₁ h₂ => by
    simp only [reverse_cons]
    exact rel_append (rel_reverse h₂) (Forall₂.cons h₁ Forall₂.nil)

@[simp]
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_reverse_iff {l₁ l₂} : Forall₂ R (reverse l₁) (reverse l₂) ↔ Forall₂ R l₁ l₂ :=
  Iff.intro
    (fun h => by
      rw [← reverse_reverse l₁, ← reverse_reverse l₂]
      exact rel_reverse h)
    fun h => rel_reverse h
/-
**List.rel_flatten** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop},   Relator.LiftFun (Lis
t.Forall₂ (List.Forall₂ R)) (List.Forall₂ R) List.flatten List.flatten
参数：List.Forall₂ (List.Forall₂ R)；List.Forall₂ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
· 使用定理 `List.rel_append`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop},   R
elator.LiftFun (List.Forall₂ R) (Relator.LiftFun (List.Forall₂ R) (List.Forall₂ 
R)) (…
-/
theorem rel_flatten : (Forall₂ (Forall₂ R) ⇒ Forall₂ R) flatten flatten
  | [], [], Forall₂.nil => Forall₂.nil
  | _, _, Forall₂.cons h₁ h₂ => rel_append h₁ (rel_flatten h₂)
/-
**List.rel_flatMap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rel_flatMap : (Forall₂ R ⇒ (R ⇒ Forall₂ P) ⇒ Forall₂ P) (Function.swap Lis
t.flatMap) (Function.swap List.flatMap)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rel_flatten`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop},   
Relator.LiftFun (List.Forall₂ (List.Forall₂ R)) (List.Forall₂ R) List.flatten Li
st.fla…
· 使用定理 `List.rel_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u
_4} {R : α → β → Prop} {P : γ → δ → Prop},   Relator.LiftFun (Relator.LiftFun R 
P)…
-/
theorem rel_flatMap : (Forall₂ R ⇒ (R ⇒ Forall₂ P) ⇒ Forall₂ P)
    (Function.swap List.flatMap) (Function.swap List.flatMap) :=
  fun _ _ h₁ _ _ h₂ => rel_flatten (rel_map (@h₂) h₁)
/-
**List.rel_foldl** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {R : α → β →
 Prop} {P : γ → δ → Prop},   Relator.LiftFun (Relator.LiftFun P (Relator.LiftFun
 R P)) (Relator.LiftFun P (Relator.LiftFun (List.Forall₂ R) P))     List.foldl L
ist.foldl
参数：Relator.LiftFun P (Relator.LiftFun R P)；Relator.LiftFun P (Relator.LiftFun (L
ist.Forall₂ R) P)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
-/
theorem rel_foldl : ((P ⇒ R ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldl foldl
  | _, _, _, _, _, h, _, _, Forall₂.nil => h
  | _, _, hfg, _, _, hxy, _, _, Forall₂.cons hab hs => rel_foldl (@hfg) (hfg hxy hab) hs
/-
**List.rel_foldr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {R : α → β →
 Prop} {P : γ → δ → Prop},   Relator.LiftFun (Relator.LiftFun R (Relator.LiftFun
 P P)) (Relator.LiftFun P (Relator.LiftFun (List.Forall₂ R) P))     List.foldr L
ist.foldr
参数：Relator.LiftFun R (Relator.LiftFun P P)；Relator.LiftFun P (Relator.LiftFun (L
ist.Forall₂ R) P)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
-/
theorem rel_foldr : ((R ⇒ P ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldr foldr
  | _, _, _, _, _, h, _, _, Forall₂.nil => h
  | _, _, hfg, _, _, hxy, _, _, Forall₂.cons hab hs => hfg hab (rel_foldr (@hfg) hxy hs)
/-
**List.rel_filter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rel_filter {p : α -> Bool} {q : β -> Bool} (hpq : (R ⇒ (· ↔ ·)) (fun x => 
p x) (fun x => q x)) : (Forall₂ R ⇒ Forall₂ R) (filter p) (filter q) | _, _, For
all₂.nil => Forall₂.nil | a :: as, b :: bs, Forall₂.cons h₁ h₂ => by dsimp [Lift
Fun] at hpq by_cases h : p a · have : q b
参数：hpq : (R ⇒ (· ↔ ·)) (fun x => p x) (fun x => q x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.filter_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, p a = true → List.filter p (a :: l) = a :: List.filter p l
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `List.filter_cons_of_neg`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, ¬p a = true → List.filter p (a :: l) = List.filter p l
-/
theorem rel_filter {p : α → Bool} {q : β → Bool}
    (hpq : (R ⇒ (· ↔ ·)) (fun x => p x) (fun x => q x)) :
    (Forall₂ R ⇒ Forall₂ R) (filter p) (filter q)
  | _, _, Forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, Forall₂.cons h₁ h₂ => by
    dsimp [LiftFun] at hpq
    by_cases h : p a
    · have : q b := by rwa [← hpq h₁]
      simp only [filter_cons_of_pos h, filter_cons_of_pos this, forall₂_cons, h₁, true_and,
        rel_filter hpq h₂]
    · have : ¬q b := by rwa [← hpq h₁]
      simp only [filter_cons_of_neg h, filter_cons_of_neg this, rel_filter hpq h₂]
/-
**List.rel_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {R : α → β →
 Prop} {P : γ → δ → Prop},   Relator.LiftFun (Relator.LiftFun R (Option.Rel P)) 
(Relator.LiftFun (List.Forall₂ R) (List.Forall₂ P)) List.filterMap     List.filt
erMap
参数：Relator.LiftFun R (Option.Rel P)；Relator.LiftFun (List.Forall₂ R) (List.Foral
l₂ P)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filterMap_cons`：∀ {α : Type u} {β : Type v} {f : α → Option β} {a :
 α} {l : List α},   List.filterMap f (a :: l) =     match f a with     | none =>
 List.fil…
-/
theorem rel_filterMap : ((R ⇒ Option.Rel P) ⇒ Forall₂ R ⇒ Forall₂ P) filterMap filterMap
  | _, _, _, _, _, Forall₂.nil => Forall₂.nil
  | f, g, hfg, a :: as, b :: bs, Forall₂.cons h₁ h₂ => by
    rw [filterMap_cons, filterMap_cons]
    exact
      match f a, g b, hfg h₁ with
      | _, _, Option.Rel.none => rel_filterMap (@hfg) h₂
      | _, _, Option.Rel.some h => Forall₂.cons h (rel_filterMap (@hfg) h₂)

/-- Given a relation `R`, `sublist_forall₂ r l₁ l₂` indicates that there is a sublist of `l₂` such
  that `forall₂ r l₁ l₂`. -/
/-
**List.SublistForall** 是 Mathlib 中的一个归纳类型，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a relation `R`, `sublist_forall₂ r l₁ l₂` indicates that there is a sublis
t of `l₂` such
  that `forall₂ r l₁ l₂`.
-/
inductive SublistForall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil {l} : SublistForall₂ R [] l
  | cons {a₁ a₂ l₁ l₂} : R a₁ a₂ → SublistForall₂ R l₁ l₂ → SublistForall₂ R (a₁ :: l₁) (a₂ :: l₂)
  | cons_right {a l₁ l₂} : SublistForall₂ R l₁ l₂ → SublistForall₂ R l₁ (a :: l₂)
/-
**List.sublistForall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublistForall₂_iff {l₁ : List α} {l₂ : List β} :
    SublistForall₂ R l₁ l₂ ↔ ∃ l, Forall₂ R l₁ l ∧ l <+ l₂ := by
  constructor <;> intro h
  · induction h with
    | nil => exact ⟨nil, Forall₂.nil, nil_sublist _⟩
    | @cons a b l1 l2 rab _ ih =>
      obtain ⟨l, hl1, hl2⟩ := ih
      exact ⟨b :: l, Forall₂.cons rab hl1, hl2.cons_cons b⟩
    | cons_right _ ih =>
      obtain ⟨l, hl1, hl2⟩ := ih
      exact ⟨l, hl1, hl2.trans (Sublist.cons _ (Sublist.refl _))⟩
  · obtain ⟨l, hl1, hl2⟩ := h
    revert l₁
    induction hl2 with
    | slnil =>
      intro l₁ hl1
      rw [forall₂_nil_right_iff.1 hl1]
      exact SublistForall₂.nil
    | cons _ _ ih => intro l₁ hl1; exact SublistForall₂.cons_right (ih hl1)
    | cons_cons _ _ ih =>
      intro l₁ hl1
      obtain - | ⟨hr, hl⟩ := hl1
      exact SublistForall₂.cons hr (ih hl)
/-
**List.SublistForall** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SublistForall₂.is_refl [Std.Refl Rₐ] : Std.Refl (SublistForall₂ Rₐ) :=
  ⟨fun l => sublistForall₂_iff.2 ⟨l, forall₂_refl l, Sublist.refl l⟩⟩
/-
**List.SublistForall** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SublistForall₂.is_trans [IsTrans α Rₐ] : IsTrans (List α) (SublistForall₂ Rₐ) :=
  ⟨fun a b c => by
    revert a b
    induction c with
    | nil =>
      rintro _ _ h1 h2
      cases h2
      exact h1
    | cons _ _ ih =>
      rintro a b h1 h2
      obtain - | ⟨hbc, tbc⟩ | btc := h2
      · cases h1
        exact SublistForall₂.nil
      · obtain - | ⟨hab, tab⟩ | atb := h1
        · exact SublistForall₂.nil
        · exact SublistForall₂.cons (_root_.trans hab hbc) (ih _ _ tab tbc)
        · exact SublistForall₂.cons_right (ih _ _ atb tbc)
      · exact SublistForall₂.cons_right (ih _ _ h1 btc)⟩
/-
**List.Sublist.sublistForall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sublist.sublistForall₂ {l₁ l₂ : List α} (h : l₁ <+ l₂) [Std.Refl Rₐ] :
    SublistForall₂ Rₐ l₁ l₂ :=
  sublistForall₂_iff.2 ⟨l₁, forall₂_refl l₁, h⟩
/-
**List.tail_sublistForall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_sublistForall₂_self [Std.Refl Rₐ] (l : List α) : SublistForall₂ Rₐ l.tail l :=
  l.tail_sublist.sublistForall₂

@[simp]
/-
**List.sublistForall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublistForall₂_map_left_iff {f : γ → α} {l₁ : List γ} {l₂ : List β} :
    SublistForall₂ R (map f l₁) l₂ ↔ SublistForall₂ (fun c b => R (f c) b) l₁ l₂ := by
  simp [sublistForall₂_iff]

@[simp]
/-
**List.sublistForall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublistForall₂_map_right_iff {f : γ → β} {l₁ : List α} {l₂ : List γ} :
    SublistForall₂ R l₁ (map f l₂) ↔ SublistForall₂ (fun a c => R a (f c)) l₁ l₂ := by
  simp only [sublistForall₂_iff]
  constructor
  · rintro ⟨l1, h1, h2⟩
    obtain ⟨l', hl1, rfl⟩ := sublist_map_iff.mp h2
    use l'
    simpa [hl1] using h1
  · rintro ⟨l1, h1, h2⟩
    use l1.map f
    simp [h1, h2.map]

end List

