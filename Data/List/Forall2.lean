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

variable {α β γ δ : Type*} {R S : α -> β -> Prop} {P : γ -> δ -> Prop} {Rₐ : α -> α -> Prop}

open Relator

mk_iff_of_inductive_prop List.Forall₂ List.forall₂_iff

/--
theorem `Forall₂.imp` / 定理 `Forall₂.imp`

English:
theorem Forall₂.imp
  given: (H : forall a b, R a b -> S a b) {l₁ l₂} (h : Forall₂ R l₁ l₂)
  statement: Forall₂ S l₁ l₂
  proof: by
  induction h <;> constructor <;> solve_by_elim

中文:
定理 Forall₂.imp
  条件: (H : 对任意 a b, R a b -> S a b) {l₁ l₂} (h : Forall₂ R l₁ l₂)
  结论: Forall₂ S l₁ l₂
  证明: by
  induction h <;> constructor <;> solve_by_elim

Depends on / 依赖: solve_by_elim
-/
theorem Forall₂.imp (H : forall a b, R a b -> S a b) {l₁ l₂} (h : Forall₂ R l₁ l₂) : Forall₂ S l₁ l₂ := by
  induction h <;> constructor <;> solve_by_elim

/--
theorem `Forall₂.mp` / 定理 `Forall₂.mp`

English:
theorem Forall₂.mp
  given: {Q : α -> β -> Prop} (h : forall a b, Q a b -> R a b -> S a b)

中文:
定理 Forall₂.mp
  条件: {Q : α -> β -> 命题} (h : 对任意 a b, Q a b -> R a b -> S a b)
-/
theorem Forall₂.mp {Q : α -> β -> Prop} (h : forall a b, Q a b -> R a b -> S a b) :
    forall {l₁ l₂}, Forall₂ Q l₁ l₂ -> Forall₂ R l₁ l₂ -> Forall₂ S l₁ l₂
  | [], [], Forall₂.nil, Forall₂.nil => Forall₂.nil
  | a :: _, b :: _, Forall₂.cons hr hrs, Forall₂.cons hq hqs =>
    Forall₂.cons (h a b hr hq) (Forall₂.mp h hrs hqs)

/--
theorem `Forall₂.flip` / 定理 `Forall₂.flip`

English:
theorem Forall₂.flip
  statement: forall {a b}, Forall₂ (flip R) b a -> Forall₂ R a b

中文:
定理 Forall₂.flip
  结论: 对任意 {a b}, Forall₂ (flip R) b a -> Forall₂ R a b
-/
theorem Forall₂.flip : forall {a b}, Forall₂ (flip R) b a -> Forall₂ R a b
  | _, _, Forall₂.nil => Forall₂.nil
  | _ :: _, _ :: _, Forall₂.cons h₁ h₂ => Forall₂.cons h₁ h₂.flip

@[simp]
/--
theorem `forall₂_same` / 定理 `forall₂_same`

English:
theorem forall₂_same
  statement: forall {l : List α}, Forall₂ Rₐ l l ↔ forall x in l, Rₐ x x

中文:
定理 对任意₂_same
  结论: 对任意 {l : 列表 α}, Forall₂ Rₐ l l ↔ 对任意 x in l, Rₐ x x
-/
theorem forall₂_same : forall {l : List α}, Forall₂ Rₐ l l ↔ forall x in l, Rₐ x x
  | [] => by simp
  | a :: l => by simp [@forall₂_same l]

/--
theorem `forall₂_refl` / 定理 `forall₂_refl`

English:
theorem forall₂_refl
  given: [Std.Refl Rₐ] (l : List α)
  statement: Forall₂ Rₐ l l
  proof: forall₂_same.2 fun _ _ => refl _

@[simp]

中文:
定理 对任意₂_refl
  条件: [Std.Refl Rₐ] (l : 列表 α)
  结论: Forall₂ Rₐ l l
  证明: forall₂_same.2 fun _ _ => refl _

@[simp]
-/
theorem forall₂_refl [Std.Refl Rₐ] (l : List α) : Forall₂ Rₐ l l :=
  forall₂_same.2 fun _ _ => refl _

@[simp]
/--
theorem `forall₂_eq_eq_eq` / 定理 `forall₂_eq_eq_eq`

English:
theorem forall₂_eq_eq_eq
  statement: Forall₂ ((· = ·) : α -> α -> Prop) = Eq
  proof: by
  funext a b; apply propext
  constructor
  · intro h
    induction h
    · rfl
    simp only [*]
  · rintro rfl
    exact forall₂_refl _

@[simp]

中文:
定理 对任意₂_eq_eq_eq
  结论: Forall₂ ((· = ·) : α -> α -> 命题) = 相等
  证明: by
  funext a b; apply propext
  constructor
  · intro h
    induction h
    · rfl
    simp only [*]
  · rintro rfl
    exact forall₂_refl _

@[simp]

Depends on / 依赖: propext
-/
theorem forall₂_eq_eq_eq : Forall₂ ((· = ·) : α -> α -> Prop) = Eq := by
  funext a b; apply propext
  constructor
  · intro h
    induction h
    · rfl
    simp only [*]
  · rintro rfl
    exact forall₂_refl _

@[simp]
/--
theorem `forall₂_nil_left_iff` / 定理 `forall₂_nil_left_iff`

English:
theorem forall₂_nil_left_iff
  given: {l}
  statement: Forall₂ R nil l ↔ l = nil
  proof: ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

@[simp]

中文:
定理 对任意₂_nil_left_iff
  条件: {l}
  结论: Forall₂ R nil l ↔ l = nil
  证明: ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

@[simp]
-/
theorem forall₂_nil_left_iff {l} : Forall₂ R nil l ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

@[simp]
/--
theorem `forall₂_nil_right_iff` / 定理 `forall₂_nil_right_iff`

English:
theorem forall₂_nil_right_iff
  given: {l}
  statement: Forall₂ R l nil ↔ l = nil
  proof: ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

中文:
定理 对任意₂_nil_right_iff
  条件: {l}
  结论: Forall₂ R l nil ↔ l = nil
  证明: ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩
-/
theorem forall₂_nil_right_iff {l} : Forall₂ R l nil ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

/--
theorem `forall₂_cons_left_iff` / 定理 `forall₂_cons_left_iff`

English:
theorem forall₂_cons_left_iff
  given: {a l u}
  proof: Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

中文:
定理 对任意₂_cons_left_iff
  条件: {a l u}
  证明: Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

Depends on / 依赖: Iff.intro
-/
theorem forall₂_cons_left_iff {a l u} :
    Forall₂ R (a :: l) u ↔ exists b u', R a b ∧ Forall₂ R l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

/--
theorem `forall₂_cons_right_iff` / 定理 `forall₂_cons_right_iff`

English:
theorem forall₂_cons_right_iff
  given: {b l u}
  proof: Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

中文:
定理 对任意₂_cons_right_iff
  条件: {b l u}
  证明: Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

Depends on / 依赖: Iff.intro
-/
theorem forall₂_cons_right_iff {b l u} :
    Forall₂ R u (b :: l) ↔ exists a u', R a b ∧ Forall₂ R u' l ∧ u = a :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

/--
theorem `forall₂_and_left` / 定理 `forall₂_and_left`

English:
theorem forall₂_and_left
  given: {p : α -> Prop}

中文:
定理 对任意₂_and_left
  条件: {p : α -> 命题}
-/
theorem forall₂_and_left {p : α -> Prop} :
    forall l u, Forall₂ (fun a b => p a ∧ R a b) l u ↔ (forall a in l, p a) ∧ Forall₂ R l u
  | [], u => by
    simp only [forall₂_nil_left_iff, forall_prop_of_false not_mem_nil, imp_true_iff, true_and]
  | a :: l, u => by
    simp only [forall₂_and_left l, forall₂_cons_left_iff, forall_mem_cons, and_assoc,
      exists_and_left]
    simp only [and_comm, and_assoc, ← exists_and_right]

@[simp]
/--
theorem `forall₂_map_left_iff` / 定理 `forall₂_map_left_iff`

English:
theorem forall₂_map_left_iff
  given: {f : γ -> α}

中文:
定理 对任意₂_map_left_iff
  条件: {f : γ -> α}
-/
theorem forall₂_map_left_iff {f : γ -> α} :
    forall {l u}, Forall₂ R (map f l) u ↔ Forall₂ (fun c b => R (f c) b) l u
  | [], _ => by simp only [map, forall₂_nil_left_iff]
  | a :: l, _ => by simp only [map, forall₂_cons_left_iff, forall₂_map_left_iff]

@[simp]
/--
theorem `forall₂_map_right_iff` / 定理 `forall₂_map_right_iff`

English:
theorem forall₂_map_right_iff
  given: {f : γ -> β}

中文:
定理 对任意₂_map_right_iff
  条件: {f : γ -> β}
-/
theorem forall₂_map_right_iff {f : γ -> β} :
    forall {l u}, Forall₂ R l (map f u) ↔ Forall₂ (fun a c => R a (f c)) l u
  | _, [] => by simp only [map, forall₂_nil_right_iff]
  | _, b :: u => by simp only [map, forall₂_cons_right_iff, forall₂_map_right_iff]

/--
theorem `left_unique_forall₂'` / 定理 `left_unique_forall₂'`

English:
theorem left_unique_forall₂'
  given: (hr : LeftUnique R)
  statement: forall {a b c}, Forall₂ R a c -> Forall₂ R b c -> a = b

中文:
定理 left_unique_对任意₂'
  条件: (hr : LeftUnique R)
  结论: 对任意 {a b c}, Forall₂ R a c -> Forall₂ R b c -> a = b
-/
theorem left_unique_forall₂' (hr : LeftUnique R) : forall {a b c}, Forall₂ R a c -> Forall₂ R b c -> a = b
  | _, _, _, Forall₂.nil, Forall₂.nil => rfl
  | _, _, _, Forall₂.cons ha₀ h₀, Forall₂.cons ha₁ h₁ =>
    hr ha₀ ha₁ ▸ left_unique_forall₂' hr h₀ h₁ ▸ rfl

/--
theorem `_root_.Relator.LeftUnique.forall₂` / 定理 `_root_.Relator.LeftUnique.forall₂`

English:
theorem _root_.Relator.LeftUnique.forall₂
  given: (hr : LeftUnique R)
  statement: LeftUnique (Forall₂ R)
  proof: @left_unique_forall₂' _ _ _ hr

中文:
定理 _root_.Relator.LeftUnique.对任意₂
  条件: (hr : LeftUnique R)
  结论: LeftUnique (Forall₂ R)
  证明: @left_unique_forall₂' _ _ _ hr
-/
theorem _root_.Relator.LeftUnique.forall₂ (hr : LeftUnique R) : LeftUnique (Forall₂ R) :=
  @left_unique_forall₂' _ _ _ hr

/--
theorem `right_unique_forall₂'` / 定理 `right_unique_forall₂'`

English:
theorem right_unique_forall₂'
  given: (hr : RightUnique R)

中文:
定理 right_unique_对任意₂'
  条件: (hr : RightUnique R)
-/
theorem right_unique_forall₂' (hr : RightUnique R) :
    forall {a b c}, Forall₂ R a b -> Forall₂ R a c -> b = c
  | _, _, _, Forall₂.nil, Forall₂.nil => rfl
  | _, _, _, Forall₂.cons ha₀ h₀, Forall₂.cons ha₁ h₁ =>
    hr ha₀ ha₁ ▸ right_unique_forall₂' hr h₀ h₁ ▸ rfl

/--
theorem `_root_.Relator.RightUnique.forall₂` / 定理 `_root_.Relator.RightUnique.forall₂`

English:
theorem _root_.Relator.RightUnique.forall₂
  given: (hr : RightUnique R)
  statement: RightUnique (Forall₂ R)
  proof: @right_unique_forall₂' _ _ _ hr

中文:
定理 _root_.Relator.RightUnique.对任意₂
  条件: (hr : RightUnique R)
  结论: RightUnique (Forall₂ R)
  证明: @right_unique_forall₂' _ _ _ hr
-/
theorem _root_.Relator.RightUnique.forall₂ (hr : RightUnique R) : RightUnique (Forall₂ R) :=
  @right_unique_forall₂' _ _ _ hr

/--
theorem `_root_.Relator.BiUnique.forall₂` / 定理 `_root_.Relator.BiUnique.forall₂`

English:
theorem _root_.Relator.BiUnique.forall₂
  given: (hr : BiUnique R)
  statement: BiUnique (Forall₂ R)
  proof: ⟨hr.left.forall₂, hr.right.forall₂⟩

中文:
定理 _root_.Relator.BiUnique.对任意₂
  条件: (hr : BiUnique R)
  结论: BiUnique (Forall₂ R)
  证明: ⟨hr.left.forall₂, hr.right.forall₂⟩

Depends on / 依赖: hr.left.forall, hr.right.forall
-/
theorem _root_.Relator.BiUnique.forall₂ (hr : BiUnique R) : BiUnique (Forall₂ R) :=
  ⟨hr.left.forall₂, hr.right.forall₂⟩

/--
theorem `Forall₂.length_eq` / 定理 `Forall₂.length_eq`

English:
theorem Forall₂.length_eq
  statement: forall {l₁ l₂}, Forall₂ R l₁ l₂ -> length l₁ = length l₂

中文:
定理 Forall₂.length_eq
  结论: 对任意 {l₁ l₂}, Forall₂ R l₁ l₂ -> length l₁ = length l₂
-/
theorem Forall₂.length_eq : forall {l₁ l₂}, Forall₂ R l₁ l₂ -> length l₁ = length l₂
  | _, _, Forall₂.nil => rfl
  | _, _, Forall₂.cons _ h₂ => congr_arg succ (Forall₂.length_eq h₂)

/--
theorem `Forall₂.get` / 定理 `Forall₂.get`

English:
theorem Forall₂.get

中文:
定理 Forall₂.get
-/
theorem Forall₂.get :
    forall {x : List α} {y : List β}, Forall₂ R x y ->
      forall ⦃i : Nat⦄ (hx : i < x.length) (hy : i < y.length), R (x.get ⟨i, hx⟩) (y.get ⟨i, hy⟩)
  | _, _, Forall₂.cons ha _, 0, _, _ => ha
  | _, _, Forall₂.cons _ hl, succ _, _, _ => hl.get _ _

/--
theorem `forall₂_of_length_eq_of_get` / 定理 `forall₂_of_length_eq_of_get`

English:
theorem forall₂_of_length_eq_of_get

中文:
定理 对任意₂_of_length_eq_of_get
-/
theorem forall₂_of_length_eq_of_get :
    forall {x : List α} {y : List β},
      x.length = y.length -> (forall i h₁ h₂, R (x.get ⟨i, h₁⟩) (y.get ⟨i, h₂⟩)) -> Forall₂ R x y
  | [], [], _, _ => Forall₂.nil
  | _ :: _, _ :: _, hl, h =>
    Forall₂.cons (h 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))
      (forall₂_of_length_eq_of_get (succ.inj hl) fun i h₁ h₂ =>
        h i.succ (succ_lt_succ h₁) (succ_lt_succ h₂))

/--
theorem `forall₂_iff_get` / 定理 `forall₂_iff_get`

English:
theorem forall₂_iff_get
  given: {l₁ : List α} {l₂ : List β}
  proof: ⟨fun h => ⟨h.length_eq, h.get⟩, fun h => forall₂_of_length_eq_of_get h.1 h.2⟩

中文:
定理 对任意₂_iff_get
  条件: {l₁ : 列表 α} {l₂ : 列表 β}
  证明: ⟨fun h => ⟨h.length_eq, h.get⟩, fun h => forall₂_of_length_eq_of_get h.1 h.2⟩

Depends on / 依赖: h.get, h.length_eq, length_eq
-/
theorem forall₂_iff_get {l₁ : List α} {l₂ : List β} :
    Forall₂ R l₁ l₂ ↔ l₁.length = l₂.length ∧ forall i h₁ h₂, R (l₁.get ⟨i, h₁⟩) (l₂.get ⟨i, h₂⟩) :=
  ⟨fun h => ⟨h.length_eq, h.get⟩, fun h => forall₂_of_length_eq_of_get h.1 h.2⟩

/--
theorem `forall₂_zip` / 定理 `forall₂_zip`

English:
theorem forall₂_zip
  statement: forall {l₁ l₂}, Forall₂ R l₁ l₂ -> forall {a b}, (a, b) in zip l₁ l₂ -> R a b

中文:
定理 对任意₂_zip
  结论: 对任意 {l₁ l₂}, Forall₂ R l₁ l₂ -> 对任意 {a b}, (a, b) in zip l₁ l₂ -> R a b
-/
theorem forall₂_zip : forall {l₁ l₂}, Forall₂ R l₁ l₂ -> forall {a b}, (a, b) in zip l₁ l₂ -> R a b
  | _, _, Forall₂.cons h₁ h₂, x, y, hx => by
    rw [zip]; rw [zipWith]; rw [mem_cons] at hx
    match hx with
    | Or.inl rfl => exact h₁
    | Or.inr h₃ => exact forall₂_zip h₂ h₃

/--
theorem `forall₂_iff_zip` / 定理 `forall₂_iff_zip`

English:
theorem forall₂_iff_zip
  given: {l₁ l₂}
  proof: ⟨fun h => ⟨Forall₂.length_eq h, @forall₂_zip _ _ _ _ _ h⟩, fun h => by
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

中文:
定理 对任意₂_iff_zip
  条件: {l₁ l₂}
  证明: ⟨fun h => ⟨Forall₂.length_eq h, @forall₂_zip _ _ _ _ _ h⟩, fun h => by
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

Depends on / 依赖: Prod.mk.injEq, generalizing, length_cons, length_eq, length_eq_zero_iff, mem_cons, succ.injEq, zipWith
-/
theorem forall₂_iff_zip {l₁ l₂} :
    Forall₂ R l₁ l₂ ↔ length l₁ = length l₂ ∧ forall {a b}, (a, b) in zip l₁ l₂ -> R a b :=
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

/--
theorem `forall₂_take` / 定理 `forall₂_take`

English:
theorem forall₂_take
  statement: forall (n) {l₁ l₂}, Forall₂ R l₁ l₂ -> Forall₂ R (take n l₁) (take n l₂)

中文:
定理 对任意₂_take
  结论: 对任意 (n) {l₁ l₂}, Forall₂ R l₁ l₂ -> Forall₂ R (take n l₁) (take n l₂)
-/
theorem forall₂_take : forall (n) {l₁ l₂}, Forall₂ R l₁ l₂ -> Forall₂ R (take n l₁) (take n l₂)
  | 0, _, _, _ => by simp only [Forall₂.nil, take]
  | _ + 1, _, _, Forall₂.nil => by simp only [Forall₂.nil, take]
  | n + 1, _, _, Forall₂.cons h₁ h₂ => by simp [And.intro h₁ h₂, forall₂_take n]

/--
theorem `forall₂_drop` / 定理 `forall₂_drop`

English:
theorem forall₂_drop
  statement: forall (n) {l₁ l₂}, Forall₂ R l₁ l₂ -> Forall₂ R (drop n l₁) (drop n l₂)

中文:
定理 对任意₂_drop
  结论: 对任意 (n) {l₁ l₂}, Forall₂ R l₁ l₂ -> Forall₂ R (drop n l₁) (drop n l₂)
-/
theorem forall₂_drop : forall (n) {l₁ l₂}, Forall₂ R l₁ l₂ -> Forall₂ R (drop n l₁) (drop n l₂)
  | 0, _, _, h => by simp only [drop, h]
  | _ + 1, _, _, Forall₂.nil => by simp only [Forall₂.nil, drop]
  | n + 1, _, _, Forall₂.cons h₁ h₂ => by simp [And.intro h₁ h₂, forall₂_drop n]

/--
theorem `forall₂_take_append` / 定理 `forall₂_take_append`

English:
theorem forall₂_take_append
  given: (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂))
  proof: by
  have h' : Forall₂ R (take (length l₁) l) (take (length l₁) (l₁ ++ l₂)) :=
    forall₂_take (length l₁) h
  rwa [take_left] at h'

中文:
定理 对任意₂_take_append
  条件: (l : 列表 α) (l₁ : 列表 β) (l₂ : 列表 β) (h : Forall₂ R l (l₁ ++ l₂))
  证明: by
  have h' : Forall₂ R (take (length l₁) l) (take (length l₁) (l₁ ++ l₂)) :=
    forall₂_take (length l₁) h
  rwa [take_left] at h'

Depends on / 依赖: length, take_left
-/
theorem forall₂_take_append (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.take (length l₁) l) l₁ := by
  have h' : Forall₂ R (take (length l₁) l) (take (length l₁) (l₁ ++ l₂)) :=
    forall₂_take (length l₁) h
  rwa [take_left] at h'

/--
theorem `forall₂_drop_append` / 定理 `forall₂_drop_append`

English:
theorem forall₂_drop_append
  given: (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂))
  proof: by
  have h' : Forall₂ R (drop (length l₁) l) (drop (length l₁) (l₁ ++ l₂)) :=
    forall₂_drop (length l₁) h
  rwa [drop_left] at h'

中文:
定理 对任意₂_drop_append
  条件: (l : 列表 α) (l₁ : 列表 β) (l₂ : 列表 β) (h : Forall₂ R l (l₁ ++ l₂))
  证明: by
  have h' : Forall₂ R (drop (length l₁) l) (drop (length l₁) (l₁ ++ l₂)) :=
    forall₂_drop (length l₁) h
  rwa [drop_left] at h'

Depends on / 依赖: drop_left, length
-/
theorem forall₂_drop_append (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.drop (length l₁) l) l₂ := by
  have h' : Forall₂ R (drop (length l₁) l) (drop (length l₁) (l₁ ++ l₂)) :=
    forall₂_drop (length l₁) h
  rwa [drop_left] at h'

/--
theorem `rel_mem` / 定理 `rel_mem`

English:
theorem rel_mem
  given: (hr : BiUnique R)
  statement: (R ⇒ Forall₂ R ⇒ Iff) (· in ·) (· in ·)

中文:
定理 rel_mem
  条件: (hr : BiUnique R)
  结论: (R ⇒ Forall₂ R ⇒ 当且仅当) (· in ·) (· in ·)
-/
theorem rel_mem (hr : BiUnique R) : (R ⇒ Forall₂ R ⇒ Iff) (· in ·) (· in ·)
  | a, b, _, [], [], Forall₂.nil => by simp only [not_mem_nil]
  | a, b, h, a' :: as, b' :: bs, Forall₂.cons h₁ h₂ => by
    simp only [mem_cons]
    exact rel_or (rel_eq hr h h₁) (rel_mem hr h h₂)

/--
theorem `rel_map` / 定理 `rel_map`

English:
theorem rel_map
  statement: ((R ⇒ P) ⇒ Forall₂ R ⇒ Forall₂ P) map map

中文:
定理 rel_map
  结论: ((R ⇒ P) ⇒ Forall₂ R ⇒ Forall₂ P) map map
-/
theorem rel_map : ((R ⇒ P) ⇒ Forall₂ R ⇒ Forall₂ P) map map
  | _, _, _, [], [], Forall₂.nil => Forall₂.nil
  | _, _, h, _ :: _, _ :: _, Forall₂.cons h₁ h₂ => Forall₂.cons (h h₁) (rel_map (@h) h₂)

/--
theorem `rel_append` / 定理 `rel_append`

English:
theorem rel_append
  statement: (Forall₂ R ⇒ Forall₂ R ⇒ Forall₂ R) (· ++ ·) (· ++ ·)

中文:
定理 rel_append
  结论: (Forall₂ R ⇒ Forall₂ R ⇒ Forall₂ R) (· ++ ·) (· ++ ·)
-/
theorem rel_append : (Forall₂ R ⇒ Forall₂ R ⇒ Forall₂ R) (· ++ ·) (· ++ ·)
  | [], [], _, _, _, hl => hl
  | _, _, Forall₂.cons h₁ h₂, _, _, hl => Forall₂.cons h₁ (rel_append h₂ hl)

/--
theorem `rel_reverse` / 定理 `rel_reverse`

English:
theorem rel_reverse
  statement: (Forall₂ R ⇒ Forall₂ R) reverse reverse

中文:
定理 rel_reverse
  结论: (Forall₂ R ⇒ Forall₂ R) reverse reverse
-/
theorem rel_reverse : (Forall₂ R ⇒ Forall₂ R) reverse reverse
  | [], [], Forall₂.nil => Forall₂.nil
  | _, _, Forall₂.cons h₁ h₂ => by
    simp only [reverse_cons]
    exact rel_append (rel_reverse h₂) (Forall₂.cons h₁ Forall₂.nil)

@[simp]
/--
theorem `forall₂_reverse_iff` / 定理 `forall₂_reverse_iff`

English:
theorem forall₂_reverse_iff
  given: {l₁ l₂}
  statement: Forall₂ R (reverse l₁) (reverse l₂) ↔ Forall₂ R l₁ l₂
  proof: Iff.intro
    (fun h => by
      rw [← reverse_reverse l₁]; rw [← reverse_reverse l₂]
      exact rel_reverse h)
    fun h => rel_reverse h

中文:
定理 对任意₂_reverse_iff
  条件: {l₁ l₂}
  结论: Forall₂ R (reverse l₁) (reverse l₂) ↔ Forall₂ R l₁ l₂
  证明: Iff.intro
    (fun h => by
      rw [← reverse_reverse l₁]; rw [← reverse_reverse l₂]
      exact rel_reverse h)
    fun h => rel_reverse h

Depends on / 依赖: Iff.intro, rel_reverse, reverse_reverse
-/
theorem forall₂_reverse_iff {l₁ l₂} : Forall₂ R (reverse l₁) (reverse l₂) ↔ Forall₂ R l₁ l₂ :=
  Iff.intro
    (fun h => by
      rw [← reverse_reverse l₁]; rw [← reverse_reverse l₂]
      exact rel_reverse h)
    fun h => rel_reverse h

/--
theorem `rel_flatten` / 定理 `rel_flatten`

English:
theorem rel_flatten
  statement: (Forall₂ (Forall₂ R) ⇒ Forall₂ R) flatten flatten

中文:
定理 rel_flatten
  结论: (Forall₂ (Forall₂ R) ⇒ Forall₂ R) flatten flatten
-/
theorem rel_flatten : (Forall₂ (Forall₂ R) ⇒ Forall₂ R) flatten flatten
  | [], [], Forall₂.nil => Forall₂.nil
  | _, _, Forall₂.cons h₁ h₂ => rel_append h₁ (rel_flatten h₂)

/--
theorem `rel_flatMap` / 定理 `rel_flatMap`

English:
theorem rel_flatMap
  statement: (Forall₂ R ⇒ (R ⇒ Forall₂ P) ⇒ Forall₂ P)
  proof: fun _ _ h₁ _ _ h₂ => rel_flatten (rel_map (@h₂) h₁)

中文:
定理 rel_flatMap
  结论: (Forall₂ R ⇒ (R ⇒ Forall₂ P) ⇒ Forall₂ P)
  证明: fun _ _ h₁ _ _ h₂ => rel_flatten (rel_map (@h₂) h₁)

Depends on / 依赖: rel_flatten, rel_map
-/
theorem rel_flatMap : (Forall₂ R ⇒ (R ⇒ Forall₂ P) ⇒ Forall₂ P)
    (Function.swap List.flatMap) (Function.swap List.flatMap) :=
  fun _ _ h₁ _ _ h₂ => rel_flatten (rel_map (@h₂) h₁)

/--
theorem `rel_foldl` / 定理 `rel_foldl`

English:
theorem rel_foldl
  statement: ((P ⇒ R ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldl foldl

中文:
定理 rel_foldl
  结论: ((P ⇒ R ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldl foldl
-/
theorem rel_foldl : ((P ⇒ R ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldl foldl
  | _, _, _, _, _, h, _, _, Forall₂.nil => h
  | _, _, hfg, _, _, hxy, _, _, Forall₂.cons hab hs => rel_foldl (@hfg) (hfg hxy hab) hs

/--
theorem `rel_foldr` / 定理 `rel_foldr`

English:
theorem rel_foldr
  statement: ((R ⇒ P ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldr foldr

中文:
定理 rel_foldr
  结论: ((R ⇒ P ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldr foldr
-/
theorem rel_foldr : ((R ⇒ P ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldr foldr
  | _, _, _, _, _, h, _, _, Forall₂.nil => h
  | _, _, hfg, _, _, hxy, _, _, Forall₂.cons hab hs => hfg hab (rel_foldr (@hfg) hxy hs)

/--
theorem `rel_filter` / 定理 `rel_filter`

English:
theorem rel_filter
  statement: {p : α -> Bool} {q : β -> Bool}
  proof: by rwa [← hpq h₁]
      simp only [filter_cons_of_pos h, filter_cons_of_pos this, forall₂_cons, h₁, true_and,
        rel_filter hpq h₂]
    · have : ¬q b := by rwa [← hpq h₁]
      simp only [filter_cons_of_neg h, filter_cons_of_neg this, rel_filter hpq h₂]

中文:
定理 rel_filter
  结论: {p : α -> 布尔值} {q : β -> 布尔值}
  证明: by rwa [← hpq h₁]
      simp only [filter_cons_of_pos h, filter_cons_of_pos this, forall₂_cons, h₁, true_and,
        rel_filter hpq h₂]
    · have : ¬q b := by rwa [← hpq h₁]
      simp only [filter_cons_of_neg h, filter_cons_of_neg this, rel_filter hpq h₂]

Depends on / 依赖: filter_cons_of_neg, filter_cons_of_pos, rel_filter, true_and
-/
theorem rel_filter {p : α -> Bool} {q : β -> Bool}
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

/--
theorem `rel_filterMap` / 定理 `rel_filterMap`

English:
theorem rel_filterMap
  statement: ((R ⇒ Option.Rel P) ⇒ Forall₂ R ⇒ Forall₂ P) filterMap filterMap

中文:
定理 rel_filterMap
  结论: ((R ⇒ 选项类型.关系 P) ⇒ Forall₂ R ⇒ Forall₂ P) filterMap filterMap
-/
theorem rel_filterMap : ((R ⇒ Option.Rel P) ⇒ Forall₂ R ⇒ Forall₂ P) filterMap filterMap
  | _, _, _, _, _, Forall₂.nil => Forall₂.nil
  | f, g, hfg, a :: as, b :: bs, Forall₂.cons h₁ h₂ => by
    rw [filterMap_cons]; rw [filterMap_cons]
    exact
      match f a, g b, hfg h₁ with
      | _, _, Option.Rel.none => rel_filterMap (@hfg) h₂
      | _, _, Option.Rel.some h => Forall₂.cons h (rel_filterMap (@hfg) h₂)

/--
Inductive type `SublistForall₂` / 归纳类型 `SublistForall₂`

English:
inductive SublistForall₂
  parameters: (R : α -> β -> Prop)
  constructors (3):
    - nil: {l} : SublistForall₂ R [] l
    - cons: {a₁ a₂ l₁ l₂} : R a₁ a₂ -> SublistForall₂ R l₁ l₂ -> SublistForall₂ R (a₁ :: l₁) (a₂ :: l₂)
    - cons_right: {a l₁ l₂} : SublistForall₂ R l₁ l₂ -> SublistForall₂ R l₁ (a :: l₂)

中文:
归纳类型 SublistForall₂
  参数: (R : α -> β -> 命题)
  构造子 (3 个):
    - nil: {l} : SublistForall₂ R [] l
    - cons: {a₁ a₂ l₁ l₂} : R a₁ a₂ -> SublistForall₂ R l₁ l₂ -> SublistForall₂ R (a₁ :: l₁) (a₂ :: l₂)
    - cons_right: {a l₁ l₂} : SublistForall₂ R l₁ l₂ -> SublistForall₂ R l₁ (a :: l₂)
-/
inductive SublistForall₂ (R : α -> β -> Prop) : List α -> List β -> Prop
  | nil {l} : SublistForall₂ R [] l
  | cons {a₁ a₂ l₁ l₂} : R a₁ a₂ -> SublistForall₂ R l₁ l₂ -> SublistForall₂ R (a₁ :: l₁) (a₂ :: l₂)
  | cons_right {a l₁ l₂} : SublistForall₂ R l₁ l₂ -> SublistForall₂ R l₁ (a :: l₂)

/--
theorem `sublistForall₂_iff` / 定理 `sublistForall₂_iff`

English:
theorem sublistForall₂_iff
  given: {l₁ : List α} {l₂ : List β}
  proof: by
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

中文:
定理 sublistForall₂_iff
  条件: {l₁ : 列表 α} {l₂ : 列表 β}
  证明: by
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

Depends on / 依赖: Sublist, Sublist.cons, Sublist.refl, SublistFor, cons_cons, cons_right, hl2.cons_cons, hl2.trans, nil_sublist, revert
-/
theorem sublistForall₂_iff {l₁ : List α} {l₂ : List β} :
    SublistForall₂ R l₁ l₂ ↔ exists l, Forall₂ R l₁ l ∧ l <+ l₂ := by
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

/--
Instance `SublistForall₂.is_refl` / 实例 `SublistForall₂.is_refl`

English:
instance SublistForall₂.is_refl
  signature: [Std.Refl Rₐ]
  body: ⟨fun l => sublistForall₂_iff.2 ⟨l, forall₂_refl l, Sublist.refl l⟩⟩

中文:
实例 SublistForall₂.is_refl
  签名: [Std.Refl Rₐ]
  定义体: ⟨fun l => sublistForall₂_iff.2 ⟨l, forall₂_refl l, Sublist.refl l⟩⟩

Depends on / 依赖: Sublist, Sublist.refl
-/
instance SublistForall₂.is_refl [Std.Refl Rₐ] : Std.Refl (SublistForall₂ Rₐ) :=
  ⟨fun l => sublistForall₂_iff.2 ⟨l, forall₂_refl l, Sublist.refl l⟩⟩

/--
Instance `SublistForall₂.is_trans` / 实例 `SublistForall₂.is_trans`

English:
instance SublistForall₂.is_trans
  signature: [IsTrans α Rₐ]
  body: ⟨fun a b c => by
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

中文:
实例 SublistForall₂.is_trans
  签名: [是Trans α Rₐ]
  定义体: ⟨fun a b c => by
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

Depends on / 依赖: _root_, _root_.trans, cons_right, revert
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

/--
theorem `Sublist.sublistForall₂` / 定理 `Sublist.sublistForall₂`

English:
theorem Sublist.sublistForall₂
  given: {l₁ l₂ : List α} (h : l₁ <+ l₂) [Std.Refl Rₐ]
  proof: sublistForall₂_iff.2 ⟨l₁, forall₂_refl l₁, h⟩

中文:
定理 子表.sublistForall₂
  条件: {l₁ l₂ : 列表 α} (h : l₁ <+ l₂) [Std.Refl Rₐ]
  证明: sublistForall₂_iff.2 ⟨l₁, forall₂_refl l₁, h⟩
-/
theorem Sublist.sublistForall₂ {l₁ l₂ : List α} (h : l₁ <+ l₂) [Std.Refl Rₐ] :
    SublistForall₂ Rₐ l₁ l₂ :=
  sublistForall₂_iff.2 ⟨l₁, forall₂_refl l₁, h⟩

/--
theorem `tail_sublistForall₂_self` / 定理 `tail_sublistForall₂_self`

English:
theorem tail_sublistForall₂_self
  given: [Std.Refl Rₐ] (l : List α)
  statement: SublistForall₂ Rₐ l.tail l
  proof: l.tail_sublist.sublistForall₂

@[simp]

中文:
定理 tail_sublistForall₂_self
  条件: [Std.Refl Rₐ] (l : 列表 α)
  结论: SublistForall₂ Rₐ l.tail l
  证明: l.tail_sublist.sublistForall₂

@[simp]

Depends on / 依赖: l.tail_sublist.sublistForall, tail_sublist
-/
theorem tail_sublistForall₂_self [Std.Refl Rₐ] (l : List α) : SublistForall₂ Rₐ l.tail l :=
  l.tail_sublist.sublistForall₂

@[simp]
/--
theorem `sublistForall₂_map_left_iff` / 定理 `sublistForall₂_map_left_iff`

English:
theorem sublistForall₂_map_left_iff
  given: {f : γ -> α} {l₁ : List γ} {l₂ : List β}
  proof: by
  simp [sublistForall₂_iff]

@[simp]

中文:
定理 sublistForall₂_map_left_iff
  条件: {f : γ -> α} {l₁ : 列表 γ} {l₂ : 列表 β}
  证明: by
  simp [sublistForall₂_iff]

@[simp]
-/
theorem sublistForall₂_map_left_iff {f : γ -> α} {l₁ : List γ} {l₂ : List β} :
    SublistForall₂ R (map f l₁) l₂ ↔ SublistForall₂ (fun c b => R (f c) b) l₁ l₂ := by
  simp [sublistForall₂_iff]

@[simp]
/--
theorem `sublistForall₂_map_right_iff` / 定理 `sublistForall₂_map_right_iff`

English:
theorem sublistForall₂_map_right_iff
  given: {f : γ -> β} {l₁ : List α} {l₂ : List γ}
  proof: by
  simp only [sublistForall₂_iff]
  constructor
  · rintro ⟨l1, h1, h2⟩
    obtain ⟨l', hl1, rfl⟩ := sublist_map_iff.mp h2
    use l'
    simpa [hl1] using h1
  · rintro ⟨l1, h1, h2⟩
    use l1.map f
    simp [h1, h2.map]

中文:
定理 sublistForall₂_map_right_iff
  条件: {f : γ -> β} {l₁ : 列表 α} {l₂ : 列表 γ}
  证明: by
  simp only [sublistForall₂_iff]
  constructor
  · rintro ⟨l1, h1, h2⟩
    obtain ⟨l', hl1, rfl⟩ := sublist_map_iff.mp h2
    use l'
    simpa [hl1] using h1
  · rintro ⟨l1, h1, h2⟩
    use l1.map f
    simp [h1, h2.map]

Depends on / 依赖: h2.map, l1.map, sublist_map_iff, sublist_map_iff.mp
-/
theorem sublistForall₂_map_right_iff {f : γ -> β} {l₁ : List α} {l₂ : List γ} :
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
