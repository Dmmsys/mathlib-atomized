/-
Copyright (c) 2021 David Wärn,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Kim Morrison, Matteo Cipollina, Runtian Zhou
-/
module

public import Mathlib.Combinatorics.Quiver.Prefunctor
public import Mathlib.Logic.Lemmas
public import Batteries.Data.List.Basic

/-!
# Paths in quivers

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.

We also define `Quiver.Reachable a b`, the existence of a directed path from `a` to `b`.
-/

@[expose] public section

open Function

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace Quiver

/--
Inductive type `Path` / 归纳类型 `Path`

English:
inductive Path
  parameters: {V : Type u} [Quiver.{v} V] (a : V)
  constructors (2):
    - nil: Path a a
    - cons: forall {b c : V}, Path a b -> (b ⟶ c) -> Path a c

中文:
归纳类型 道路
  参数: {V : 类型u} [箭图.{v} V] (a : V)
  构造子 (2 个):
    - nil: 道路 a a
    - cons: 对任意 {b c : V}, 道路 a b -> (b ⟶ c) -> 道路 a c
-/
inductive Path {V : Type u} [Quiver.{v} V] (a : V) : V -> Type max u v
  | nil : Path a a
  | cons : forall {b c : V}, Path a b -> (b ⟶ c) -> Path a c

-- See issue https://github.com/leanprover/lean4/issues/2049
compile_inductive% Path

/--
Definition of `Hom.toPath` / `Hom.toPath` 的定义

English:
definition Hom.toPath
  signature: {V} [Quiver V] {a b : V} (e : a ⟶ b)
  body: Path.nil.cons e

中文:
定义 态射.toPath
  签名: {V} [箭图 V] {a b : V} (e : a ⟶ b)
  定义体: Path.nil.cons e

Depends on / 依赖: Path.nil.cons
-/
def Hom.toPath {V} [Quiver V] {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e

namespace Path

variable {V : Type u} [Quiver V] {a b c d : V}

/--
lemma `nil_ne_cons` / 引理 `nil_ne_cons`

English:
lemma nil_ne_cons
  given: (p : Path a b) (e : b ⟶ a)
  statement: Path.nil != p.cons e
  proof: fun h => by injection h

中文:
引理 nil_ne_cons
  条件: (p : 道路 a b) (e : b ⟶ a)
  结论: 道路.nil != p.cons e
  证明: fun h => by injection h

Depends on / 依赖: injection
-/
lemma nil_ne_cons (p : Path a b) (e : b ⟶ a) : Path.nil != p.cons e :=
  fun h => by injection h

/--
lemma `cons_ne_nil` / 引理 `cons_ne_nil`

English:
lemma cons_ne_nil
  given: (p : Path a b) (e : b ⟶ a)
  statement: p.cons e != Path.nil
  proof: fun h => by injection h

中文:
引理 cons_ne_nil
  条件: (p : 道路 a b) (e : b ⟶ a)
  结论: p.cons e != 道路.nil
  证明: fun h => by injection h

Depends on / 依赖: injection
-/
lemma cons_ne_nil (p : Path a b) (e : b ⟶ a) : p.cons e != Path.nil :=
  fun h => by injection h

/--
lemma `obj_eq_of_cons_eq_cons` / 引理 `obj_eq_of_cons_eq_cons`

English:
lemma obj_eq_of_cons_eq_cons
  statement: {p : Path a b} {p' : Path a c}
  proof: by injection h

中文:
引理 obj_eq_of_cons_eq_cons
  结论: {p : 道路 a b} {p' : 道路 a c}
  证明: by injection h

Depends on / 依赖: injection
-/
lemma obj_eq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : b = c := by injection h

/--
lemma `heq_of_cons_eq_cons` / 引理 `heq_of_cons_eq_cons`

English:
lemma heq_of_cons_eq_cons
  statement: {p : Path a b} {p' : Path a c}
  proof: by injection h

中文:
引理 heq_of_cons_eq_cons
  结论: {p : 道路 a b} {p' : 道路 a c}
  证明: by injection h

Depends on / 依赖: injection
-/
lemma heq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : p ≍ p' := by injection h

/--
lemma `hom_heq_of_cons_eq_cons` / 引理 `hom_heq_of_cons_eq_cons`

English:
lemma hom_heq_of_cons_eq_cons
  statement: {p : Path a b} {p' : Path a c}
  proof: by injection h

中文:
引理 hom_heq_of_cons_eq_cons
  结论: {p : 道路 a b} {p' : 道路 a c}
  证明: by injection h

Depends on / 依赖: injection
-/
lemma hom_heq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : e ≍ e' := by injection h

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: {a : V}

中文:
定义 length
  签名: {a : V}
-/
def length {a : V} : forall {b : V}, Path a b -> Nat
  | _, nil => 0
  | _, cons p _ => p.length + 1

instance {a : V} : Inhabited (Path a a) :=
  ⟨nil⟩

@[simp]
/--
theorem `length_nil` / 定理 `length_nil`

English:
theorem length_nil
  given: {a : V}
  statement: (nil : Path a a).length = 0
  proof: rfl

@[simp]

中文:
定理 length_nil
  条件: {a : V}
  结论: (nil : 道路 a a).length = 0
  证明: rfl

@[simp]
-/
theorem length_nil {a : V} : (nil : Path a a).length = 0 :=
  rfl

@[simp]
/--
theorem `length_cons` / 定理 `length_cons`

English:
theorem length_cons
  given: (a b c : V) (p : Path a b) (e : b ⟶ c)
  statement: (p.cons e).length = p.length + 1
  proof: rfl

中文:
定理 length_cons
  条件: (a b c : V) (p : 道路 a b) (e : b ⟶ c)
  结论: (p.cons e).length = p.length + 1
  证明: rfl
-/
theorem length_cons (a b c : V) (p : Path a b) (e : b ⟶ c) : (p.cons e).length = p.length + 1 :=
  rfl

/--
theorem `eq_of_length_zero` / 定理 `eq_of_length_zero`

English:
theorem eq_of_length_zero
  given: (p : Path a b) (hzero : p.length = 0)
  statement: a = b
  proof: by
  cases p
  · rfl
  · cases Nat.succ_ne_zero _ hzero

中文:
定理 eq_of_length_zero
  条件: (p : 道路 a b) (hzero : p.length = 0)
  结论: a = b
  证明: by
  cases p
  · rfl
  · cases Nat.succ_ne_zero _ hzero

Depends on / 依赖: Nat.succ_ne_zero, succ_ne_zero
-/
theorem eq_of_length_zero (p : Path a b) (hzero : p.length = 0) : a = b := by
  cases p
  · rfl
  · cases Nat.succ_ne_zero _ hzero

/--
theorem `eq_nil_of_length_zero` / 定理 `eq_nil_of_length_zero`

English:
theorem eq_nil_of_length_zero
  given: (p : Path a a) (hzero : p.length = 0)
  statement: p = nil
  proof: by
  cases p
  · rfl
  · simp at hzero

@[simp]

中文:
定理 eq_nil_of_length_zero
  条件: (p : 道路 a a) (hzero : p.length = 0)
  结论: p = nil
  证明: by
  cases p
  · rfl
  · simp at hzero

@[simp]
-/
theorem eq_nil_of_length_zero (p : Path a a) (hzero : p.length = 0) : p = nil := by
  cases p
  · rfl
  · simp at hzero

@[simp]
/--
lemma `length_toPath` / 引理 `length_toPath`

English:
lemma length_toPath
  given: {a b : V} (e : a ⟶ b)
  statement: e.toPath.length = 1
  proof: rfl

中文:
引理 length_toPath
  条件: {a b : V} (e : a ⟶ b)
  结论: e.toPath.length = 1
  证明: rfl
-/
lemma length_toPath {a b : V} (e : a ⟶ b) : e.toPath.length = 1 := rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {a b : V}

中文:
定义 comp
  签名: {a b : V}
-/
def comp {a b : V} : forall {c}, Path a b -> Path b c -> Path a c
  | _, p, nil => p
  | _, p, cons q e => (p.comp q).cons e

@[simp]
/--
theorem `comp_cons` / 定理 `comp_cons`

English:
theorem comp_cons
  given: {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d)
  proof: rfl

@[simp]

中文:
定理 comp_cons
  条件: {a b c d : V} (p : 道路 a b) (q : 道路 b c) (e : c ⟶ d)
  证明: rfl

@[simp]
-/
theorem comp_cons {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d) :
    p.comp (q.cons e) = (p.comp q).cons e :=
  rfl

@[simp]
/--
theorem `comp_nil` / 定理 `comp_nil`

English:
theorem comp_nil
  given: {a b : V} (p : Path a b)
  statement: p.comp Path.nil = p
  proof: rfl

@[simp]

中文:
定理 comp_nil
  条件: {a b : V} (p : 道路 a b)
  结论: p.comp 道路.nil = p
  证明: rfl

@[simp]
-/
theorem comp_nil {a b : V} (p : Path a b) : p.comp Path.nil = p :=
  rfl

@[simp]
/--
theorem `nil_comp` / 定理 `nil_comp`

English:
theorem nil_comp
  given: {a : V}
  statement: forall {b} (p : Path a b), Path.nil.comp p = p

中文:
定理 nil_comp
  条件: {a : V}
  结论: 对任意 {b} (p : 道路 a b), 道路.nil.comp p = p
-/
theorem nil_comp {a : V} : forall {b} (p : Path a b), Path.nil.comp p = p
  | _, nil => rfl
  | _, cons p _ => by rw [comp_cons, nil_comp p]

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: {a b c : V}

中文:
定理 comp_assoc
  条件: {a b c : V}
-/
theorem comp_assoc {a b c : V} :
    forall {d} (p : Path a b) (q : Path b c) (r : Path c d), (p.comp q).comp r = p.comp (q.comp r)
  | _, _, _, nil => rfl
  | _, p, q, cons r _ => by rw [comp_cons, comp_cons, comp_cons, comp_assoc p q r]

@[simp]
/--
theorem `length_comp` / 定理 `length_comp`

English:
theorem length_comp
  given: (p : Path a b)
  statement: forall {c} (q : Path b c), (p.comp q).length = p.length + q.length

中文:
定理 length_comp
  条件: (p : 道路 a b)
  结论: 对任意 {c} (q : 道路 b c), (p.comp q).length = p.length + q.length
-/
theorem length_comp (p : Path a b) : forall {c} (q : Path b c), (p.comp q).length = p.length + q.length
  | _, nil => rfl
  | _, cons _ _ => congr_arg Nat.succ (length_comp _ _)

/--
theorem `comp_inj` / 定理 `comp_inj`

English:
theorem comp_inj
  given: {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq : q₁.length = q₂.length)
  proof: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  induction q₁ with
  | nil =>
    rcases q₂ with _ | ⟨q₂, f₂⟩
    · exact ⟨h, rfl⟩
    · cases hq
  | cons q₁ f₁ ih =>
    rcases q₂ with _ | ⟨q₂, f₂⟩
    · cases hq
    · simp only [comp_cons, cons.injEq] at h
      obtain rfl := h.1
      obtain ⟨rfl, rfl⟩ := ih (Nat.succ.inj hq) h.2.1.eq
      rw [h.2.2.eq]
      exact ⟨rfl, rfl⟩

中文:
定理 comp_inj
  条件: {p₁ p₂ : 道路 a b} {q₁ q₂ : 道路 b c} (hq : q₁.length = q₂.length)
  证明: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  induction q₁ with
  | nil =>
    rcases q₂ with _ | ⟨q₂, f₂⟩
    · exact ⟨h, rfl⟩
    · cases hq
  | cons q₁ f₁ ih =>
    rcases q₂ with _ | ⟨q₂, f₂⟩
    · cases hq
    · simp only [comp_cons, cons.injEq] at h
      obtain rfl := h.1
      obtain ⟨rfl, rfl⟩ := ih (Nat.succ.inj hq) h.2.1.eq
      rw [h.2.2.eq]
      exact ⟨rfl, rfl⟩

Depends on / 依赖: Nat.succ.inj, comp_cons, cons.injEq
-/
theorem comp_inj {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq : q₁.length = q₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  induction q₁ with
  | nil =>
    rcases q₂ with _ | ⟨q₂, f₂⟩
    · exact ⟨h, rfl⟩
    · cases hq
  | cons q₁ f₁ ih =>
    rcases q₂ with _ | ⟨q₂, f₂⟩
    · cases hq
    · simp only [comp_cons, cons.injEq] at h
      obtain rfl := h.1
      obtain ⟨rfl, rfl⟩ := ih (Nat.succ.inj hq) h.2.1.eq
      rw [h.2.2.eq]
      exact ⟨rfl, rfl⟩

/--
theorem `comp_inj'` / 定理 `comp_inj'`

English:
theorem comp_inj'
  given: {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (h : p₁.length = p₂.length)
  proof: ⟨fun h_eq => (comp_inj <| Nat.add_left_cancel (n := p₂.length) <|
    by simpa [h] using congr_arg length h_eq).1 h_eq,
   by rintro ⟨rfl, rfl⟩; rfl⟩

中文:
定理 comp_inj'
  条件: {p₁ p₂ : 道路 a b} {q₁ q₂ : 道路 b c} (h : p₁.length = p₂.length)
  证明: ⟨fun h_eq => (comp_inj <| Nat.add_left_cancel (n := p₂.length) <|
    by simpa [h] using congr_arg length h_eq).1 h_eq,
   by rintro ⟨rfl, rfl⟩; rfl⟩

Depends on / 依赖: Nat.add_left_cancel, add_left_cancel, comp_inj, congr_arg, h_eq, length
-/
theorem comp_inj' {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (h : p₁.length = p₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
  ⟨fun h_eq => (comp_inj <| Nat.add_left_cancel (n := p₂.length) <|
    by simpa [h] using congr_arg length h_eq).1 h_eq,
   by rintro ⟨rfl, rfl⟩; rfl⟩

/--
theorem `comp_injective_left` / 定理 `comp_injective_left`

English:
theorem comp_injective_left
  given: (q : Path b c)
  statement: Injective fun p : Path a b => p.comp q
  proof: fun _ _ h => ((comp_inj rfl).1 h).1

中文:
定理 comp_injective_left
  条件: (q : 道路 b c)
  结论: 单射 fun p : 道路 a b => p.comp q
  证明: fun _ _ h => ((comp_inj rfl).1 h).1

Depends on / 依赖: comp_inj
-/
theorem comp_injective_left (q : Path b c) : Injective fun p : Path a b => p.comp q :=
  fun _ _ h => ((comp_inj rfl).1 h).1

/--
theorem `comp_injective_right` / 定理 `comp_injective_right`

English:
theorem comp_injective_right
  given: (p : Path a b)
  statement: Injective (p.comp : Path b c -> Path a c)
  proof: fun _ _ h => ((comp_inj' rfl).1 h).2

@[simp]

中文:
定理 comp_injective_right
  条件: (p : 道路 a b)
  结论: 单射 (p.comp : 道路 b c -> 道路 a c)
  证明: fun _ _ h => ((comp_inj' rfl).1 h).2

@[simp]

Depends on / 依赖: comp_inj
-/
theorem comp_injective_right (p : Path a b) : Injective (p.comp : Path b c -> Path a c) :=
  fun _ _ h => ((comp_inj' rfl).1 h).2

@[simp]
/--
theorem `comp_inj_left` / 定理 `comp_inj_left`

English:
theorem comp_inj_left
  given: {p₁ p₂ : Path a b} {q : Path b c}
  statement: p₁.comp q = p₂.comp q ↔ p₁ = p₂
  proof: q.comp_injective_left.eq_iff

@[simp]

中文:
定理 comp_inj_left
  条件: {p₁ p₂ : 道路 a b} {q : 道路 b c}
  结论: p₁.comp q = p₂.comp q ↔ p₁ = p₂
  证明: q.comp_injective_left.eq_iff

@[simp]

Depends on / 依赖: comp_injective_left, eq_iff, q.comp_injective_left.eq_iff
-/
theorem comp_inj_left {p₁ p₂ : Path a b} {q : Path b c} : p₁.comp q = p₂.comp q ↔ p₁ = p₂ :=
  q.comp_injective_left.eq_iff

@[simp]
/--
theorem `comp_inj_right` / 定理 `comp_inj_right`

English:
theorem comp_inj_right
  given: {p : Path a b} {q₁ q₂ : Path b c}
  statement: p.comp q₁ = p.comp q₂ ↔ q₁ = q₂
  proof: p.comp_injective_right.eq_iff

中文:
定理 comp_inj_right
  条件: {p : 道路 a b} {q₁ q₂ : 道路 b c}
  结论: p.comp q₁ = p.comp q₂ ↔ q₁ = q₂
  证明: p.comp_injective_right.eq_iff

Depends on / 依赖: comp_injective_right, eq_iff, p.comp_injective_right.eq_iff
-/
theorem comp_inj_right {p : Path a b} {q₁ q₂ : Path b c} : p.comp q₁ = p.comp q₂ ↔ q₁ = q₂ :=
  p.comp_injective_right.eq_iff

/--
lemma `eq_toPath_comp_of_length_eq_succ` / 引理 `eq_toPath_comp_of_length_eq_succ`

English:
lemma eq_toPath_comp_of_length_eq_succ
  statement: (p : Path a b) {n : Nat}
  proof: by
  induction p generalizing n with
  | nil => simp at hp
  | @cons c d p q h =>
    cases n
    · rw [length_cons, Nat.zero_add, Nat.add_eq_right] at hp
      obtain rfl := eq_of_length_zero p hp
      obtain rfl := eq_nil_of_length_zero p hp
      exact ⟨d, q, nil, rfl, rfl⟩
    · rw [length_cons, Nat.add_right_cancel_iff] at hp
      obtain ⟨x, q'', p'', hl, rfl⟩ := h hp
      exact ⟨x, q'', p''.cons q, by simpa, rfl⟩

中文:
引理 eq_toPath_comp_of_length_eq_succ
  结论: (p : 道路 a b) {n : 自然数}
  证明: by
  induction p generalizing n with
  | nil => simp at hp
  | @cons c d p q h =>
    cases n
    · rw [length_cons, Nat.zero_add, Nat.add_eq_right] at hp
      obtain rfl := eq_of_length_zero p hp
      obtain rfl := eq_nil_of_length_zero p hp
      exact ⟨d, q, nil, rfl, rfl⟩
    · rw [length_cons, Nat.add_right_cancel_iff] at hp
      obtain ⟨x, q'', p'', hl, rfl⟩ := h hp
      exact ⟨x, q'', p''.cons q, by simpa, rfl⟩

Depends on / 依赖: Nat.add_eq_right, Nat.add_right_cancel_iff, Nat.zero_add, add_eq_right, add_right_cancel_iff, eq_nil_of_length_zero, eq_of_length_zero, generalizing, length_cons, zero_add
-/
lemma eq_toPath_comp_of_length_eq_succ (p : Path a b) {n : Nat}
    (hp : p.length = n + 1) :
    exists (c : V) (f : a ⟶ c) (q : Quiver.Path c b) (_ : q.length = n),
      p = f.toPath.comp q := by
  induction p generalizing n with
  | nil => simp at hp
  | @cons c d p q h =>
    cases n
    · rw [length_cons, Nat.zero_add, Nat.add_eq_right] at hp
      obtain rfl := eq_of_length_zero p hp
      obtain rfl := eq_nil_of_length_zero p hp
      exact ⟨d, q, nil, rfl, rfl⟩
    · rw [length_cons, Nat.add_right_cancel_iff] at hp
      obtain ⟨x, q'', p'', hl, rfl⟩ := h hp
      exact ⟨x, q'', p''.cons q, by simpa, rfl⟩

section Decomposition

variable {V R : Type*} [Quiver V] {a b : V} (p : Path a b)

/--
lemma `length_ne_zero_iff_eq_comp` / 引理 `length_ne_zero_iff_eq_comp`

English:
lemma length_ne_zero_iff_eq_comp
  given: (p : Path a b)
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · have h_len : p.length = (p.length - 1) + 1 := by lia
    obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
    exact ⟨c, e, p', rfl, by lia⟩
  · rintro ⟨c, p', e, rfl, h⟩
    simp [h]

中文:
引理 length_ne_zero_iff_eq_comp
  条件: (p : 道路 a b)
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · have h_len : p.length = (p.length - 1) + 1 := by lia
    obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
    exact ⟨c, e, p', rfl, by lia⟩
  · rintro ⟨c, p', e, rfl, h⟩
    simp [h]

Depends on / 依赖: Path.eq_toPath_comp_of_length_eq_succ, eq_toPath_comp_of_length_eq_succ, h_len, length, p.length
-/
lemma length_ne_zero_iff_eq_comp (p : Path a b) :
    p.length != 0 ↔ exists (c : V) (e : a ⟶ c) (p' : Path c b),
      p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · have h_len : p.length = (p.length - 1) + 1 := by lia
    obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
    exact ⟨c, e, p', rfl, by lia⟩
  · rintro ⟨c, p', e, rfl, h⟩
    simp [h]

/--
lemma `length_ne_zero_iff_eq_cons` / 引理 `length_ne_zero_iff_eq_cons`

English:
lemma length_ne_zero_iff_eq_cons
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · cases p with
    | nil => simp at h
    | cons p' e => exact ⟨_, p', e, rfl⟩
  · rintro ⟨c, p', e, rfl⟩
    simp

中文:
引理 length_ne_zero_iff_eq_cons
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · cases p with
    | nil => simp at h
    | cons p' e => exact ⟨_, p', e, rfl⟩
  · rintro ⟨c, p', e, rfl⟩
    simp
-/
lemma length_ne_zero_iff_eq_cons :
    p.length != 0 ↔ exists (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  refine ⟨fun h => ?_, ?_⟩
  · cases p with
    | nil => simp at h
    | cons p' e => exact ⟨_, p', e, rfl⟩
  · rintro ⟨c, p', e, rfl⟩
    simp

/--
lemma `comp_toPath_eq_cons` / 引理 `comp_toPath_eq_cons`

English:
lemma comp_toPath_eq_cons
  given: {a b c : V} (p : Path a b) (e : b ⟶ c)
  proof: rfl

中文:
引理 comp_toPath_eq_cons
  条件: {a b c : V} (p : 道路 a b) (e : b ⟶ c)
  证明: rfl
-/
@[simp] lemma comp_toPath_eq_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    p.comp e.toPath = p.cons e :=
  rfl

end Decomposition

/-- Turn a path into a list. The list contains `a` at its head, but not `b` a priori. -/
@[simp]
/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: : forall {b : V}, Path a b -> List V

中文:
定义 toList
  签名: : 对任意 {b : V}, 道路 a b -> 列表 V
-/
def toList : forall {b : V}, Path a b -> List V
  | _, nil => []
  | _, @cons _ _ _ c _ p _ => c :: p.toList

/-- `Quiver.Path.toList` is a contravariant functor. The inversion comes from `Quiver.Path` and
`List` having different preferred directions for adding elements. -/
@[simp]
/--
theorem `toList_comp` / 定理 `toList_comp`

English:
theorem toList_comp
  given: (p : Path a b)
  statement: forall {c} (q : Path b c), (p.comp q).toList = q.toList ++ p.toList

中文:
定理 toList_comp
  条件: (p : 道路 a b)
  结论: 对任意 {c} (q : 道路 b c), (p.comp q).toList = q.toList ++ p.toList
-/
theorem toList_comp (p : Path a b) : forall {c} (q : Path b c), (p.comp q).toList = q.toList ++ p.toList
  | _, nil => by simp
  | _, @cons _ _ _ d _ q _ => by simp [toList_comp]

/--
theorem `isChain_toList_nonempty` / 定理 `isChain_toList_nonempty`

English:
theorem isChain_toList_nonempty

中文:
定理 isChain_toList_nonempty
-/
theorem isChain_toList_nonempty :
    forall {b} (p : Path a b), (p.toList).IsChain (fun x y => Nonempty (y ⟶ x))
  | _, nil => .nil
  | _, cons nil _ => .singleton _
  | _, cons (cons p g) _ => List.IsChain.cons_cons ⟨g⟩ (isChain_toList_nonempty (cons p g))

/--
theorem `isChain_cons_toList_nonempty` / 定理 `isChain_cons_toList_nonempty`

English:
theorem isChain_cons_toList_nonempty

中文:
定理 isChain_cons_toList_nonempty
-/
theorem isChain_cons_toList_nonempty :
    forall {b} (p : Path a b), (b :: p.toList).IsChain (fun x y => Nonempty (y ⟶ x))
  | _, nil => .singleton _
  | _, cons p f => p.isChain_cons_toList_nonempty.cons_cons ⟨f⟩

variable [forall a b : V, Subsingleton (a ⟶ b)]

/--
theorem `toList_injective` / 定理 `toList_injective`

English:
theorem toList_injective
  given: (a : V)
  statement: forall b, Injective (toList : Path a b -> List V)
  proof: h
    simp [toList_injective _ _ hAC, eq_iff_true_of_subsingleton]

@[simp]

中文:
定理 toList_injective
  条件: (a : V)
  结论: 对任意 b, 单射 (toList : 道路 a b -> 列表 V)
  证明: h
    simp [toList_injective _ _ hAC, eq_iff_true_of_subsingleton]

@[simp]
-/
theorem toList_injective (a : V) : forall b, Injective (toList : Path a b -> List V)
  | _, nil, nil, _ => rfl
  | _, nil, @cons _ _ _ c _ p f, h => by cases h
  | _, @cons _ _ _ c _ p f, nil, h => by cases h
  | _, @cons _ _ _ c _ p f, @cons _ _ _ t _ C D, h => by
    simp only [toList, List.cons.injEq] at h
    obtain ⟨rfl, hAC⟩ := h
    simp [toList_injective _ _ hAC, eq_iff_true_of_subsingleton]

@[simp]
/--
theorem `toList_inj` / 定理 `toList_inj`

English:
theorem toList_inj
  given: {p q : Path a b}
  statement: p.toList = q.toList ↔ p = q
  proof: (toList_injective _ _).eq_iff

中文:
定理 toList_inj
  条件: {p q : 道路 a b}
  结论: p.toList = q.toList ↔ p = q
  证明: (toList_injective _ _).eq_iff

Depends on / 依赖: eq_iff, toList_injective
-/
theorem toList_inj {p q : Path a b} : p.toList = q.toList ↔ p = q :=
  (toList_injective _ _).eq_iff


section BoundedPath

variable {V : Type*} [Quiver V]

/--
Definition of `BoundedPaths` / `BoundedPaths` 的定义

English:
definition BoundedPaths
  signature: (v w : V) (n : Nat)
  body: { p : Path v w // p.length <= n }

中文:
定义 BoundedPaths
  签名: (v w : V) (n : 自然数)
  定义体: { p : Path v w // p.length <= n }

Depends on / 依赖: length, p.length
-/
def BoundedPaths (v w : V) (n : Nat) : Sort _ :=
  { p : Path v w // p.length <= n }

/--
Instance `instSubsingletonBddPaths` / 实例 `instSubsingletonBddPaths`

English:
instance instSubsingletonBddPaths
  signature: (v w : V)
  body: fun ⟨p, hp⟩ ⟨q, hq⟩ =>
    match v, w, p, q with
    | _, _, .nil, .nil => rfl
    | _, _, .cons _ _, _ => by simp [Quiver.Path.length] at hp
    | _, _, _, .cons _ _ => by simp [Quiver.Path.length] at hq

中文:
实例 instSubsingletonBddPaths
  签名: (v w : V)
  定义体: fun ⟨p, hp⟩ ⟨q, hq⟩ =>
    match v, w, p, q with
    | _, _, .nil, .nil => rfl
    | _, _, .cons _ _, _ => by simp [Quiver.Path.length] at hp
    | _, _, _, .cons _ _ => by simp [Quiver.Path.length] at hq
-/
instance instSubsingletonBddPaths (v w : V) : Subsingleton (BoundedPaths v w 0) where
  allEq := fun ⟨p, hp⟩ ⟨q, hq⟩ =>
    match v, w, p, q with
    | _, _, .nil, .nil => rfl
    | _, _, .cons _ _, _ => by simp [Quiver.Path.length] at hp
    | _, _, _, .cons _ _ => by simp [Quiver.Path.length] at hq

/--
Definition of `decidableEqBddPathsZero` / `decidableEqBddPathsZero` 的定义

English:
definition decidableEqBddPathsZero
  signature: (v w : V)
  body: fun _ _ => isTrue Subsingleton.elim _ _

中文:
定义 decidableEqBddPathsZero
  签名: (v w : V)
  定义体: fun _ _ => isTrue Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, isTrue
-/
def decidableEqBddPathsZero (v w : V) : DecidableEq (BoundedPaths v w 0) :=
fun _ _ => isTrue Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `decidableEqBddPathsOfDecidableEq` / `decidableEqBddPathsOfDecidableEq` 的定义

English:
definition decidableEqBddPathsOfDecidableEq
  signature: (n : Nat) (h₁ : DecidableEq V)
  body: fun ⟨p, hp⟩ ⟨q, hq⟩ =>
    match v, w, p, q with
    | _, _, .nil, .nil => isTrue rfl
    | _, _, .nil, .cons _ _
    | _, _, .cons _ _, .nil =>
      isFalse fun h => Quiver.Path.noConfusion rfl .rfl .rfl .rfl (heq_of_eq (Subtype.mk.inj h))
    | _, _, .cons (b := v') p' α, .cons (b := v'') q' β =>
      match v', v'', h₁ v' v'' with
      | _, _, isTrue (Eq.refl _) =>
        if h : α = β then
          have hp' : p'.length <= n := by simp [Quiver.Path.length] at hp; lia
          have hq' : q'.length <= n := by simp [Quiver.Path.length] at hq; lia
          if h'' : (⟨p', hp'⟩ : BoundedPaths _ _ n) = ⟨q', hq'⟩ then
isTrue by
              apply Subtype.ext
              dsimp
              rw [h]; rw [show p' = q' from Subtype.mk.inj h'']
          else
            isFalse fun h =>
h'' Subtype.ext eq_of_heq (Quiver.Path.cons.inj <| Subtype.mk.inj h).2.1
        else
          isFalse fun h' =>
h eq_of_heq (Quiver.Path.cons.inj <| Subtype.mk.inj h').2.2
      | _, _, isFalse h => isFalse fun h' =>
        h (Quiver.Path.cons.inj <| Subtype.mk.inj h').1

中文:
定义 decidableEqBddPathsOfDecidableEq
  签名: (n : 自然数) (h₁ : DecidableEq V)
  定义体: fun ⟨p, hp⟩ ⟨q, hq⟩ =>
    match v, w, p, q with
    | _, _, .nil, .nil => isTrue rfl
    | _, _, .nil, .cons _ _
    | _, _, .cons _ _, .nil =>
      isFalse fun h => Quiver.Path.noConfusion rfl .rfl .rfl .rfl (heq_of_eq (Subtype.mk.inj h))
    | _, _, .cons (b := v') p' α, .cons (b := v'') q' β =>
      match v', v'', h₁ v' v'' with
      | _, _, isTrue (Eq.refl _) =>
        if h : α = β then
          have hp' : p'.length <= n := by simp [Quiver.Path.length] at hp; lia
          have hq' : q'.length <= n := by simp [Quiver.Path.length] at hq; lia
          if h'' : (⟨p', hp'⟩ : BoundedPaths _ _ n) = ⟨q', hq'⟩ then
isTrue by
              apply Subtype.ext
              dsimp
              rw [h]; rw [show p' = q' from Subtype.mk.inj h'']
          else
            isFalse fun h =>
h'' Subtype.ext eq_of_heq (Quiver.Path.cons.inj <| Subtype.mk.inj h).2.1
        else
          isFalse fun h' =>
h eq_of_heq (Quiver.Path.cons.inj <| Subtype.mk.inj h').2.2
      | _, _, isFalse h => isFalse fun h' =>
        h (Quiver.Path.cons.inj <| Subtype.mk.inj h').1

Depends on / 依赖: Eq.refl, Quiver, Quiver.Path.length, Quiver.Path.noConfusion, Subtype, Subtype.mk.inj, heq_of_eq, isFalse, isTrue, length, noConfusion
-/
def decidableEqBddPathsOfDecidableEq (n : Nat) (h₁ : DecidableEq V)
    (h₂ : forall (v w : V), DecidableEq (v ⟶ w)) (h₃ : forall (v w : V), DecidableEq (BoundedPaths v w n))
    (v w : V) : DecidableEq (BoundedPaths v w (n + 1)) :=
  fun ⟨p, hp⟩ ⟨q, hq⟩ =>
    match v, w, p, q with
    | _, _, .nil, .nil => isTrue rfl
    | _, _, .nil, .cons _ _
    | _, _, .cons _ _, .nil =>
      isFalse fun h => Quiver.Path.noConfusion rfl .rfl .rfl .rfl (heq_of_eq (Subtype.mk.inj h))
    | _, _, .cons (b := v') p' α, .cons (b := v'') q' β =>
      match v', v'', h₁ v' v'' with
      | _, _, isTrue (Eq.refl _) =>
        if h : α = β then
          have hp' : p'.length <= n := by simp [Quiver.Path.length] at hp; lia
          have hq' : q'.length <= n := by simp [Quiver.Path.length] at hq; lia
          if h'' : (⟨p', hp'⟩ : BoundedPaths _ _ n) = ⟨q', hq'⟩ then
isTrue by
              apply Subtype.ext
              dsimp
              rw [h]; rw [show p' = q' from Subtype.mk.inj h'']
          else
            isFalse fun h =>
h'' Subtype.ext eq_of_heq (Quiver.Path.cons.inj <| Subtype.mk.inj h).2.1
        else
          isFalse fun h' =>
h eq_of_heq (Quiver.Path.cons.inj <| Subtype.mk.inj h').2.2
      | _, _, isFalse h => isFalse fun h' =>
        h (Quiver.Path.cons.inj <| Subtype.mk.inj h').1

/--
Instance `decidableEqBoundedPaths` / 实例 `decidableEqBoundedPaths`

English:
instance decidableEqBoundedPaths
  signature: [DecidableEq V] [forall (v w : V), DecidableEq (v ⟶ w)]
  body: n.rec decidableEqBddPathsZero
    fun n decEq => decidableEqBddPathsOfDecidableEq n inferInstance inferInstance decEq

中文:
实例 decidableEqBoundedPaths
  签名: [DecidableEq V] [对任意 (v w : V), DecidableEq (v ⟶ w)]
  定义体: n.rec decidableEqBddPathsZero
    fun n decEq => decidableEqBddPathsOfDecidableEq n inferInstance inferInstance decEq

Depends on / 依赖: decidableEqBddPathsOfDecidableEq, decidableEqBddPathsZero, n.rec
-/
instance decidableEqBoundedPaths [DecidableEq V] [forall (v w : V), DecidableEq (v ⟶ w)]
    (n : Nat) : (v w : V) -> DecidableEq (BoundedPaths v w n) :=
  n.rec decidableEqBddPathsZero
    fun n decEq => decidableEqBddPathsOfDecidableEq n inferInstance inferInstance decEq

/--
Instance `instDecidableEq` / 实例 `instDecidableEq`

English:
instance instDecidableEq
  signature: [DecidableEq V] [forall (v w : V), DecidableEq (v ⟶ w)]
  body: fun v w p q =>
  let m := max p.length q.length
  let p' : BoundedPaths v w m := ⟨p, Nat.le_max_left ..⟩
  let q' : BoundedPaths v w m := ⟨q, Nat.le_max_right ..⟩
  decidable_of_iff (p' = q') Subtype.ext_iff

中文:
实例 instDecidableEq
  签名: [DecidableEq V] [对任意 (v w : V), DecidableEq (v ⟶ w)]
  定义体: fun v w p q =>
  let m := max p.length q.length
  let p' : BoundedPaths v w m := ⟨p, Nat.le_max_left ..⟩
  let q' : BoundedPaths v w m := ⟨q, Nat.le_max_right ..⟩
  decidable_of_iff (p' = q') Subtype.ext_iff

Depends on / 依赖: _apply, comapDomain, zero_apply
-/
instance instDecidableEq [DecidableEq V] [forall (v w : V), DecidableEq (v ⟶ w)] :
    (v w : V) -> DecidableEq (Path v w) := fun v w p q =>
  let m := max p.length q.length
  let p' : BoundedPaths v w m := ⟨p, Nat.le_max_left ..⟩
  let q' : BoundedPaths v w m := ⟨q, Nat.le_max_right ..⟩
  decidable_of_iff (p' = q') Subtype.ext_iff

end BoundedPath

end Path

section Reachable

variable {V : Type u} [Quiver V]

/--
Definition of `Reachable` / `Reachable` 的定义

English:
definition Reachable
  signature: (a b : V)
  body: Nonempty (Path a b)

中文:
定义 Reachable
  签名: (a b : V)
  定义体: Nonempty (Path a b)

Depends on / 依赖: Nonempty, _apply, add_apply, comapDomain
-/
def Reachable (a b : V) : Prop := Nonempty (Path a b)

variable {a b c : V}

/--
theorem `Reachable.elim` / 定理 `Reachable.elim`

English:
theorem Reachable.elim
  given: {p : Prop} (h : Reachable a b) (hp : Path a b -> p)
  statement: p
  proof: Nonempty.elim h hp

@[refl]

中文:
定理 Reachable.elim
  条件: {p : 命题} (h : Reachable a b) (hp : 道路 a b -> p)
  结论: p
  证明: Nonempty.elim h hp

@[refl]
-/
protected theorem Reachable.elim {p : Prop} (h : Reachable a b) (hp : Path a b -> p) : p :=
  Nonempty.elim h hp

@[refl]
/--
theorem `Reachable.refl` / 定理 `Reachable.refl`

English:
theorem Reachable.refl
  given: (a : V)
  statement: Reachable a a
  proof: ⟨.nil⟩

@[simp]

中文:
定理 Reachable.refl
  条件: (a : V)
  结论: Reachable a a
  证明: ⟨.nil⟩

@[simp]
-/
protected theorem Reachable.refl (a : V) : Reachable a a := ⟨.nil⟩

@[simp]
/--
theorem `Reachable.rfl` / 定理 `Reachable.rfl`

English:
theorem Reachable.rfl
  statement: Reachable a a
  proof: .refl _

@[trans]

中文:
定理 Reachable.rfl
  结论: Reachable a a
  证明: .refl _

@[trans]
-/
protected theorem Reachable.rfl : Reachable a a := .refl _

@[trans]
/--
theorem `Reachable.trans` / 定理 `Reachable.trans`

English:
theorem Reachable.trans
  given: (hab : Reachable a b) (hbc : Reachable b c)
  statement: Reachable a c
  proof: hab.elim fun p => hbc.elim fun q => ⟨p.comp q⟩

中文:
定理 Reachable.trans
  条件: (hab : Reachable a b) (hbc : Reachable b c)
  结论: Reachable a c
  证明: hab.elim fun p => hbc.elim fun q => ⟨p.comp q⟩
-/
protected theorem Reachable.trans (hab : Reachable a b) (hbc : Reachable b c) : Reachable a c :=
  hab.elim fun p => hbc.elim fun q => ⟨p.comp q⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreorder V Reachable
  body: .refl
  trans _ _ _ := .trans

中文:
实例 :
  签名: 是预序 V Reachable
  定义体: .refl
  trans _ _ _ := .trans
-/
instance : IsPreorder V Reachable where
  refl := .refl
  trans _ _ _ := .trans

/--
theorem `Path.reachable` / 定理 `Path.reachable`

English:
theorem Path.reachable
  given: (p : Path a b)
  statement: Reachable a b
  proof: ⟨p⟩

中文:
定理 道路.reachable
  条件: (p : 道路 a b)
  结论: Reachable a b
  证明: ⟨p⟩
-/
protected theorem Path.reachable (p : Path a b) : Reachable a b := ⟨p⟩

/--
theorem `Hom.reachable` / 定理 `Hom.reachable`

English:
theorem Hom.reachable
  given: (e : a ⟶ b)
  statement: Reachable a b
  proof: ⟨e.toPath⟩

中文:
定理 态射.reachable
  条件: (e : a ⟶ b)
  结论: Reachable a b
  证明: ⟨e.toPath⟩
-/
protected theorem Hom.reachable (e : a ⟶ b) : Reachable a b := ⟨e.toPath⟩

end Reachable

end Quiver

namespace Prefunctor

open Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] (F : V ⥤q W)

/--
Definition of `mapPath` / `mapPath` 的定义

English:
definition mapPath
  signature: {a : V}

中文:
定义 mapPath
  签名: {a : V}
-/
def mapPath {a : V} : forall {b : V}, Path a b -> Path (F.obj a) (F.obj b)
  | _, Path.nil => Path.nil
  | _, Path.cons p e => Path.cons (mapPath p) (F.map e)

@[simp]
/--
theorem `mapPath_nil` / 定理 `mapPath_nil`

English:
theorem mapPath_nil
  given: (a : V)
  statement: F.mapPath (Path.nil : Path a a) = Path.nil
  proof: rfl

@[simp]

中文:
定理 mapPath_nil
  条件: (a : V)
  结论: F.mapPath (道路.nil : 道路 a a) = 道路.nil
  证明: rfl

@[simp]
-/
theorem mapPath_nil (a : V) : F.mapPath (Path.nil : Path a a) = Path.nil :=
  rfl

@[simp]
/--
theorem `mapPath_cons` / 定理 `mapPath_cons`

English:
theorem mapPath_cons
  given: {a b c : V} (p : Path a b) (e : b ⟶ c)
  proof: rfl

@[simp]

中文:
定理 mapPath_cons
  条件: {a b c : V} (p : 道路 a b) (e : b ⟶ c)
  证明: rfl

@[simp]
-/
theorem mapPath_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    F.mapPath (Path.cons p e) = Path.cons (F.mapPath p) (F.map e) :=
  rfl

@[simp]
/--
theorem `mapPath_comp` / 定理 `mapPath_comp`

English:
theorem mapPath_comp
  given: {a b : V} (p : Path a b)

中文:
定理 mapPath_comp
  条件: {a b : V} (p : 道路 a b)

Depends on / 依赖: mapRange, map_zero
-/
theorem mapPath_comp {a b : V} (p : Path a b) :
    forall {c : V} (q : Path b c), F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q)
  | _, Path.nil => rfl
  | c, Path.cons q e => by dsimp; rw [mapPath_comp p q]

@[simp]
/--
theorem `mapPath_toPath` / 定理 `mapPath_toPath`

English:
theorem mapPath_toPath
  given: {a b : V} (f : a ⟶ b)
  statement: F.mapPath f.toPath = (F.map f).toPath
  proof: rfl

中文:
定理 mapPath_toPath
  条件: {a b : V} (f : a ⟶ b)
  结论: F.mapPath f.toPath = (F.map f).toPath
  证明: rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, mapRange_id
-/
theorem mapPath_toPath {a b : V} (f : a ⟶ b) : F.mapPath f.toPath = (F.map f).toPath :=
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `mapPath_id` / 定理 `mapPath_id`

English:
theorem mapPath_id
  given: {a b : V}
  statement: (p : Path a b) -> (𝟭q V).mapPath p = p

中文:
定理 mapPath_id
  条件: {a b : V}
  结论: (p : 道路 a b) -> (𝟭q V).mapPath p = p
-/
theorem mapPath_id {a b : V} : (p : Path a b) -> (𝟭q V).mapPath p = p
  | Path.nil => rfl
  | Path.cons q e => by dsimp; rw [mapPath_id q]

variable {U : Type u₃} [Quiver.{v₃} U] (G : W ⥤q U)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `mapPath_comp_apply` / 定理 `mapPath_comp_apply`

English:
theorem mapPath_comp_apply
  given: {a b : V} (p : Path a b)
  proof: by
  induction p with
  | nil => rfl
  | cons x y h => simp [h]

中文:
定理 mapPath_comp_apply
  条件: {a b : V} (p : 道路 a b)
  证明: by
  induction p with
  | nil => rfl
  | cons x y h => simp [h]

Depends on / 依赖: AddEquiv, AddEquiv.self_comp_symm, AddEquiv.symm_comp_self, addMonoidHom, invFun, left_inv, mapRange, mapRange.addMonoidHom, mapRange_comp, map_zero, right_inv, self_comp_symm, simp_rw, symm.map_zero, symm_comp_self, toAddMonoidHom
-/
theorem mapPath_comp_apply {a b : V} (p : Path a b) :
    (F ⋙q G).mapPath p = G.mapPath (F.mapPath p) := by
  induction p with
  | nil => rfl
  | cons x y h => simp [h]

end Prefunctor
