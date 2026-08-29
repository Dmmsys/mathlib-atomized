/-
Copyright (c) 2025 Joseph Myers, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yaël Dillies
-/
module

public import Mathlib.Tactic.MkIffOfInductiveProp
public import Batteries.Data.List.Lemmas

/-!
# Triplewise predicates on list.

## Main definitions

* `List.Triplewise` says that a predicate applies to all ordered triples of elements of a list.

-/

public section


namespace List

variable {α β : Type*}

/-- Whether a predicate holds for all ordered triples of elements of a list. -/
@[mk_iff]
/--
Inductive type `Triplewise` / 归纳类型 `Triplewise`

English:
inductive Triplewise
  parameters: (p : α -> α -> α -> Prop)
  constructors (2):
    - nil: [].Triplewise p
    - cons: {a : α} {l : List α} : l.Pairwise (p a) -> l.Triplewise p -> (a :: l).Triplewise p

中文:
归纳类型 Triplewise
  参数: (p : α -> α -> α -> 命题)
  构造子 (2 个):
    - nil: [].Triplewise p
    - cons: {a : α} {l : 列表 α} : l.两两 (p a) -> l.Triplewise p -> (a :: l).Triplewise p
-/
inductive Triplewise (p : α -> α -> α -> Prop) : List α -> Prop
  | nil : [].Triplewise p
  | cons {a : α} {l : List α} : l.Pairwise (p a) -> l.Triplewise p -> (a :: l).Triplewise p

attribute [simp, grind ←] Triplewise.nil

variable {a b c : α} {l l₁ l₂ : List α} {p q : α -> α -> α -> Prop} {f : α -> β} {p' : β -> β -> β -> Prop}

@[grind =]
/--
lemma `triplewise_cons` / 引理 `triplewise_cons`

English:
lemma triplewise_cons
  statement: (a :: l).Triplewise p ↔ l.Pairwise (p a) ∧ l.Triplewise p
  proof: by
  grind [triplewise_iff]

中文:
引理 triplewise_cons
  结论: (a :: l).Triplewise p ↔ l.两两 (p a) ∧ l.Triplewise p
  证明: by
  grind [triplewise_iff]

Depends on / 依赖: triplewise_iff
-/
lemma triplewise_cons : (a :: l).Triplewise p ↔ l.Pairwise (p a) ∧ l.Triplewise p := by
  grind [triplewise_iff]

variable (a b p)

/--
lemma `triplewise_singleton` / 引理 `triplewise_singleton`

English:
lemma triplewise_singleton
  statement: [a].Triplewise p
  proof: by
  simp [triplewise_cons]

中文:
引理 triplewise_singleton
  结论: [a].Triplewise p
  证明: by
  simp [triplewise_cons]
-/
@[simp] lemma triplewise_singleton : [a].Triplewise p := by
  simp [triplewise_cons]

/--
lemma `triplewise_pair` / 引理 `triplewise_pair`

English:
lemma triplewise_pair
  statement: [a, b].Triplewise p
  proof: by
  simp [triplewise_cons]

中文:
引理 triplewise_pair
  结论: [a, b].Triplewise p
  证明: by
  simp [triplewise_cons]
-/
@[simp] lemma triplewise_pair : [a, b].Triplewise p := by
  simp [triplewise_cons]

variable {a b p}

/--
lemma `triplewise_triple` / 引理 `triplewise_triple`

English:
lemma triplewise_triple
  statement: [a, b, c].Triplewise p ↔ p a b c
  proof: by
  simp [triplewise_cons]

中文:
引理 triplewise_triple
  结论: [a, b, c].Triplewise p ↔ p a b c
  证明: by
  simp [triplewise_cons]
-/
@[simp] lemma triplewise_triple : [a, b, c].Triplewise p ↔ p a b c := by
  simp [triplewise_cons]

/--
lemma `Triplewise.imp` / 引理 `Triplewise.imp`

English:
lemma Triplewise.imp
  given: (h : forall {a b c}, p a b c -> q a b c) (hl : l.Triplewise p)
  proof: by
  induction hl with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.imp h) ih

中文:
引理 Triplewise.imp
  条件: (h : 对任意 {a b c}, p a b c -> q a b c) (hl : l.Triplewise p)
  证明: by
  induction hl with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.imp h) ih

Depends on / 依赖: head.imp
-/
lemma Triplewise.imp (h : forall {a b c}, p a b c -> q a b c) (hl : l.Triplewise p) :
    l.Triplewise q := by
  induction hl with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.imp h) ih

/--
lemma `triplewise_map` / 引理 `triplewise_map`

English:
lemma triplewise_map
  proof: by
  induction l with
  | nil => simp
  | cons h t ih => simp [map, triplewise_cons, ih, pairwise_map]

中文:
引理 triplewise_map
  证明: by
  induction l with
  | nil => simp
  | cons h t ih => simp [map, triplewise_cons, ih, pairwise_map]

Depends on / 依赖: pairwise_map, triplewise_cons
-/
lemma triplewise_map :
    (l.map f).Triplewise p' ↔ l.Triplewise (fun a b c => p' (f a) (f b) (f c)) := by
  induction l with
  | nil => simp
  | cons h t ih => simp [map, triplewise_cons, ih, pairwise_map]

/--
lemma `Triplewise.of_map` / 引理 `Triplewise.of_map`

English:
lemma Triplewise.of_map
  proof: by
  rw [triplewise_map] at hl
  exact hl.imp h

中文:
引理 Triplewise.of_map
  证明: by
  rw [triplewise_map] at hl
  exact hl.imp h

Depends on / 依赖: hl.imp, triplewise_map
-/
lemma Triplewise.of_map
    (h : forall {a b c}, p' (f a) (f b) (f c) -> p a b c) (hl : (l.map f).Triplewise p') :
    l.Triplewise p := by
  rw [triplewise_map] at hl
  exact hl.imp h

/--
lemma `Triplewise.map` / 引理 `Triplewise.map`

English:
lemma Triplewise.map
  given: (h : forall {a b c}, p a b c -> p' (f a) (f b) (f c)) (hl : l.Triplewise p)
  proof: triplewise_map.2 (hl.imp h)

中文:
引理 Triplewise.map
  条件: (h : 对任意 {a b c}, p a b c -> p' (f a) (f b) (f c)) (hl : l.Triplewise p)
  证明: triplewise_map.2 (hl.imp h)

Depends on / 依赖: hl.imp, triplewise_map
-/
lemma Triplewise.map (h : forall {a b c}, p a b c -> p' (f a) (f b) (f c)) (hl : l.Triplewise p) :
    (l.map f).Triplewise p' :=
  triplewise_map.2 (hl.imp h)

/--
lemma `triplewise_iff_getElem` / 引理 `triplewise_iff_getElem`

English:
lemma triplewise_iff_getElem
  statement: l.Triplewise p ↔ forall i j k (hij : i < j) (hjk : j < k)
  proof: by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [triplewise_cons, length_cons, pairwise_iff_getElem, ih]
    refine ⟨fun ⟨hh, ht⟩ i j k hij hjk hk => ?_,
            fun h => ⟨fun i j hi hj hij => ?_, fun i j k hij hjk hk => ?_⟩⟩
    · grind
    · simpa using! h 0 (i + 1

中文:
引理 triplewise_iff_getElem
  结论: l.Triplewise p ↔ 对任意 i j k (hij : i < j) (hjk : j < k)
  证明: by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [triplewise_cons, length_cons, pairwise_iff_getElem, ih]
    refine ⟨fun ⟨hh, ht⟩ i j k hij hjk hk => ?_,
            fun h => ⟨fun i j hi hj hij => ?_, fun i j k hij hjk hk => ?_⟩⟩
    · grind
    · simpa using! h 0 (i + 1

Depends on / 依赖: length_cons, pairwise_iff_getElem, triplewise_cons
-/
lemma triplewise_iff_getElem : l.Triplewise p ↔ forall i j k (hij : i < j) (hjk : j < k)
    (hk : k < l.length), p l[i] l[j] l[k] := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [triplewise_cons, length_cons, pairwise_iff_getElem, ih]
    refine ⟨fun ⟨hh, ht⟩ i j k hij hjk hk => ?_,
            fun h => ⟨fun i j hi hj hij => ?_, fun i j k hij hjk hk => ?_⟩⟩
    · grind
    · simpa using! h 0 (i + 1) (j + 1) (by lia) (by lia) (by lia)
    · simpa using! h (i + 1) (j + 1) (k + 1) (by lia) (by lia) (by lia)

/--
lemma `triplewise_append` / 引理 `triplewise_append`

English:
lemma triplewise_append
  statement: (l₁ ++ l₂).Triplewise p ↔ l₁.Triplewise p ∧ l₂.Triplewise p ∧
  proof: by
  induction l₁ with grind [pairwise_cons]

中文:
引理 triplewise_append
  结论: (l₁ ++ l₂).Triplewise p ↔ l₁.Triplewise p ∧ l₂.Triplewise p ∧
  证明: by
  induction l₁ with grind [pairwise_cons]

Depends on / 依赖: pairwise_cons
-/
lemma triplewise_append : (l₁ ++ l₂).Triplewise p ↔ l₁.Triplewise p ∧ l₂.Triplewise p ∧
    (forall a in l₁, l₂.Pairwise (p a)) ∧ forall a in l₂, l₁.Pairwise fun x y => p x y a := by
  induction l₁ with grind [pairwise_cons]

/--
lemma `triplewise_reverse` / 引理 `triplewise_reverse`

English:
lemma triplewise_reverse
  statement: l.reverse.Triplewise p ↔ l.Triplewise fun a b c => p c b a
  proof: by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [triplewise_append, pairwise_reverse, triplewise_cons, ih, and_comm]

中文:
引理 triplewise_reverse
  结论: l.reverse.Triplewise p ↔ l.Triplewise fun a b c => p c b a
  证明: by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [triplewise_append, pairwise_reverse, triplewise_cons, ih, and_comm]

Depends on / 依赖: and_comm, pairwise_reverse, triplewise_append, triplewise_cons
-/
lemma triplewise_reverse : l.reverse.Triplewise p ↔ l.Triplewise fun a b c => p c b a := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [triplewise_append, pairwise_reverse, triplewise_cons, ih, and_comm]

end List
