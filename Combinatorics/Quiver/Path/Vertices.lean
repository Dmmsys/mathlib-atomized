/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.List.Basic

/-!
# Path Vertices

This file provides lemmas for reasoning about the vertices of a path.
-/

@[expose] public section

namespace Quiver.Path

open List

variable {V : Type*} [Quiver V]

/--
Definition of `«end»` / `«end»` 的定义

English:
definition «end»
  signature: {a : V}

中文:
定义 «end»
  签名: {a : V}
-/
def «end» {a : V} : forall {b : V}, Path a b -> V
  | b, _ => b

@[simp]
/--
lemma `end_cons` / 引理 `end_cons`

English:
lemma end_cons
  given: {a b c : V} (p : Path a b) (e : b ⟶ c)
  statement: (p.cons e).end = c
  proof: rfl

中文:
引理 end_cons
  条件: {a b c : V} (p : Path a b) (e : b ⟶ c)
  结论: (p.cons e).end = c
  证明: rfl
-/
lemma end_cons {a b c : V} (p : Path a b) (e : b ⟶ c) : (p.cons e).end = c := rfl

/--
Definition of `vertices` / `vertices` 的定义

English:
definition vertices
  signature: {a : V}

中文:
定义 vertices
  签名: {a : V}
-/
def vertices {a : V} : forall {b : V}, Path a b -> List V
  | _, nil => [a]
  | _, cons p e => (p.vertices).concat (p.cons e).end

@[simp]
/--
lemma `vertices_nil` / 引理 `vertices_nil`

English:
lemma vertices_nil
  given: (a : V)
  statement: (nil : Path a a).vertices = [a]
  proof: rfl

@[simp]

中文:
引理 vertices_nil
  条件: (a : V)
  结论: (nil : Path a a).vertices = [a]
  证明: rfl

@[simp]
-/
lemma vertices_nil (a : V) : (nil : Path a a).vertices = [a] := rfl

@[simp]
/--
lemma `vertices_cons` / 引理 `vertices_cons`

English:
lemma vertices_cons
  given: {a b c : V} (p : Path a b) (e : b ⟶ c)
  proof: rfl

中文:
引理 vertices_cons
  条件: {a b c : V} (p : Path a b) (e : b ⟶ c)
  证明: rfl
-/
lemma vertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  (p.cons e).vertices = p.vertices.concat c := rfl

/--
lemma `mem_vertices_cons` / 引理 `mem_vertices_cons`

English:
lemma mem_vertices_cons
  statement: {a b c : V} (p : Path a b)
  proof: by
  simp only [vertices_cons]
  simp_all only [concat_eq_append, mem_append, mem_cons, not_mem_nil, or_false]

中文:
引理 mem_vertices_cons
  结论: {a b c : V} (p : Path a b)
  证明: by
  simp only [vertices_cons]
  simp_all only [concat_eq_append, mem_append, mem_cons, not_mem_nil, or_false]

Depends on / 依赖: concat_eq_append, mem_append, mem_cons, not_mem_nil, or_false, vertices_cons
-/
lemma mem_vertices_cons {a b c : V} (p : Path a b)
    (e : b ⟶ c) {x : V} :
    x in (p.cons e).vertices ↔ x in p.vertices ∨ x = c := by
  simp only [vertices_cons]
  simp_all only [concat_eq_append, mem_append, mem_cons, not_mem_nil, or_false]

/--
lemma `verticesSet_nil` / 引理 `verticesSet_nil`

English:
lemma verticesSet_nil
  given: {a : V}
  statement: {v | v in (nil : Path a a).vertices} = {a}
  proof: by
  simp only [vertices_nil, mem_singleton, Set.ext_iff, Set.mem_singleton_iff]
  exact fun x => Set.mem_ofPred

中文:
引理 verticesSet_nil
  条件: {a : V}
  结论: {v | v in (nil : Path a a).vertices} = {a}
  证明: by
  simp only [vertices_nil, mem_singleton, Set.ext_iff, Set.mem_singleton_iff]
  exact fun x => Set.mem_ofPred

Depends on / 依赖: Set.ext_iff, Set.mem_ofPred, Set.mem_singleton_iff, ext_iff, mem_ofPred, mem_singleton, mem_singleton_iff, vertices_nil
-/
lemma verticesSet_nil {a : V} : {v | v in (nil : Path a a).vertices} = {a} := by
  simp only [vertices_nil, mem_singleton, Set.ext_iff, Set.mem_singleton_iff]
  exact fun x => Set.mem_ofPred

/-- The length of vertices list equals path length plus one -/
@[simp]
/--
lemma `vertices_length` / 引理 `vertices_length`

English:
lemma vertices_length
  given: {V : Type*} [Quiver V] {a b : V} (p : Path a b)
  proof: by
  induction p with
  | nil => simp
  | cons p' e ih =>
    simp [vertices_cons, length_cons, ih]

中文:
引理 vertices_length
  条件: {V : 类型} [Quiver V] {a b : V} (p : Path a b)
  证明: by
  induction p with
  | nil => simp
  | cons p' e ih =>
    simp [vertices_cons, length_cons, ih]

Depends on / 依赖: length_cons, vertices_cons
-/
lemma vertices_length {V : Type*} [Quiver V] {a b : V} (p : Path a b) :
    p.vertices.length = p.length + 1 := by
  induction p with
  | nil => simp
  | cons p' e ih =>
    simp [vertices_cons, length_cons, ih]

/--
lemma `length_vertices_pos` / 引理 `length_vertices_pos`

English:
lemma length_vertices_pos
  given: {a b : V} (p : Path a b)
  proof: by simp

中文:
引理 length_vertices_pos
  条件: {a b : V} (p : Path a b)
  证明: by simp
-/
lemma length_vertices_pos {a b : V} (p : Path a b) :
    0 < p.vertices.length := by simp

/--
lemma `vertices_ne_nil` / 引理 `vertices_ne_nil`

English:
lemma vertices_ne_nil
  given: {a : V} {b : V} (p : Path a b)
  statement: p.vertices != []
  proof: by
  simp [← length_pos_iff_ne_nil]

中文:
引理 vertices_ne_nil
  条件: {a : V} {b : V} (p : Path a b)
  结论: p.vertices != []
  证明: by
  simp [← length_pos_iff_ne_nil]

Depends on / 依赖: length_pos_iff_ne_nil
-/
lemma vertices_ne_nil {a : V} {b : V} (p : Path a b) : p.vertices != [] := by
  simp [← length_pos_iff_ne_nil]

/--
lemma `start_mem_vertices` / 引理 `start_mem_vertices`

English:
lemma start_mem_vertices
  given: {a b : V} (p : Path a b)
  statement: a in p.vertices
  proof: by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]

中文:
引理 start_mem_vertices
  条件: {a b : V} (p : Path a b)
  结论: a in p.vertices
  证明: by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]
-/
lemma start_mem_vertices {a b : V} (p : Path a b) : a in p.vertices := by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]

/-- The head of the vertices list is the start vertex -/
@[simp]
/--
lemma `vertices_head?` / 引理 `vertices_head?`

English:
lemma vertices_head?
  given: {a b : V} (p : Path a b)
  statement: p.vertices.head? = some a
  proof: by
  induction p with
  | nil => simp only [vertices_nil, head?_cons]
  | cons p' e ih => simp [ih]

中文:
引理 vertices_head?
  条件: {a b : V} (p : Path a b)
  结论: p.vertices.head? = some a
  证明: by
  induction p with
  | nil => simp only [vertices_nil, head?_cons]
  | cons p' e ih => simp [ih]

Depends on / 依赖: _cons, vertices_nil
-/
lemma vertices_head? {a b : V} (p : Path a b) : p.vertices.head? = some a := by
  induction p with
  | nil => simp only [vertices_nil, head?_cons]
  | cons p' e ih => simp [ih]

/-- The head of the vertices list is the start vertex. -/
@[simp]
/--
lemma `vertices_head_eq` / 引理 `vertices_head_eq`

English:
lemma vertices_head_eq
  given: {a b : V} (p : Path a b) (h : p.vertices != [] := p.vertices_ne_nil)
  proof: by
  induction p with
  | nil => simp only [vertices_nil, head_cons]
  | cons p' _ ih => simp [head_append_of_ne_nil (vertices_ne_nil p'), ih]

@[simp]

中文:
引理 vertices_head_eq
  条件: {a b : V} (p : Path a b) (h : p.vertices != [] := p.vertices_ne_nil)
  证明: by
  induction p with
  | nil => simp only [vertices_nil, head_cons]
  | cons p' _ ih => simp [head_append_of_ne_nil (vertices_ne_nil p'), ih]

@[simp]

Depends on / 依赖: p.vertices_ne_nil, vertices_ne_nil
-/
lemma vertices_head_eq {a b : V} (p : Path a b) (h : p.vertices != [] := p.vertices_ne_nil) :
    p.vertices.head h = a := by
  induction p with
  | nil => simp only [vertices_nil, head_cons]
  | cons p' _ ih => simp [head_append_of_ne_nil (vertices_ne_nil p'), ih]

@[simp]
/--
lemma `getElem_vertices_zero` / 引理 `getElem_vertices_zero`

English:
lemma getElem_vertices_zero
  given: {a b : V} (p : Path a b)
  statement: p.vertices[0] = a
  proof: by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]

@[simp]

中文:
引理 getElem_vertices_zero
  条件: {a b : V} (p : Path a b)
  结论: p.vertices[0] = a
  证明: by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]

@[simp]
-/
lemma getElem_vertices_zero {a b : V} (p : Path a b) : p.vertices[0] = a := by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]

@[simp]
/--
lemma `vertices_getLast` / 引理 `vertices_getLast`

English:
lemma vertices_getLast
  given: {a b : V} (p : Path a b) (h : p.vertices != [] := p.vertices_ne_nil)
  proof: by
  induction p with
  | nil => simp only [vertices_nil, getLast_singleton]
  | cons p' e ih => simp

@[simp]

中文:
引理 vertices_getLast
  条件: {a b : V} (p : Path a b) (h : p.vertices != [] := p.vertices_ne_nil)
  证明: by
  induction p with
  | nil => simp only [vertices_nil, getLast_singleton]
  | cons p' e ih => simp

@[simp]

Depends on / 依赖: p.vertices_ne_nil, vertices_ne_nil
-/
lemma vertices_getLast {a b : V} (p : Path a b) (h : p.vertices != [] := p.vertices_ne_nil) :
    p.vertices.getLast h = b := by
  induction p with
  | nil => simp only [vertices_nil, getLast_singleton]
  | cons p' e ih => simp

@[simp]
/--
lemma `dropLast_append_end_eq` / 引理 `dropLast_append_end_eq`

English:
lemma dropLast_append_end_eq
  given: {a b : V} (p : Path a b)
  proof: by
  simp_rw [← p.vertices_getLast p.vertices_ne_nil, dropLast_concat_getLast]

@[simp]

中文:
引理 dropLast_append_end_eq
  条件: {a b : V} (p : Path a b)
  证明: by
  simp_rw [← p.vertices_getLast p.vertices_ne_nil, dropLast_concat_getLast]

@[simp]

Depends on / 依赖: dropLast_concat_getLast, p.vertices_getLast, p.vertices_ne_nil, simp_rw, vertices_getLast, vertices_ne_nil
-/
lemma dropLast_append_end_eq {a b : V} (p : Path a b) :
    p.vertices.dropLast ++ [b] = p.vertices := by
  simp_rw [← p.vertices_getLast p.vertices_ne_nil, dropLast_concat_getLast]

@[simp]
/--
lemma `vertices_comp` / 引理 `vertices_comp`

English:
lemma vertices_comp
  given: {a b c : V} (p : Path a b) (q : Path b c)
  proof: by
  induction q with
  | nil => simp
  | cons q' e ih => simp [ih]

中文:
引理 vertices_comp
  条件: {a b c : V} (p : Path a b) (q : Path b c)
  证明: by
  induction q with
  | nil => simp
  | cons q' e ih => simp [ih]
-/
lemma vertices_comp {a b c : V} (p : Path a b) (q : Path b c) :
  (p.comp q).vertices = p.vertices.dropLast ++ q.vertices := by
  induction q with
  | nil => simp
  | cons q' e ih => simp [ih]

/--
lemma `length_eq_zero_iff` / 引理 `length_eq_zero_iff`

English:
lemma length_eq_zero_iff
  given: {a : V} (p : Path a a)
  proof: by
  cases p <;> tauto

中文:
引理 length_eq_zero_iff
  条件: {a : V} (p : Path a a)
  证明: by
  cases p <;> tauto
-/
@[simp] lemma length_eq_zero_iff {a : V} (p : Path a a) :
    p.length = 0 ↔ p = Path.nil := by
  cases p <;> tauto

/--
lemma `vertices_comp_get_length_eq` / 引理 `vertices_comp_get_length_eq`

English:
lemma vertices_comp_get_length_eq
  statement: {a b c : V} (p₁ : Path a c) (p₂ : Path c b)
  proof: by
  simp

@[simp]

中文:
引理 vertices_comp_get_length_eq
  结论: {a b c : V} (p₁ : Path a c) (p₂ : Path c b)
  证明: by
  simp

@[simp]

Depends on / 依赖: length, vertices, vertices.get
-/
lemma vertices_comp_get_length_eq {a b c : V} (p₁ : Path a c) (p₂ : Path c b)
    (h : p₁.length < (p₁.comp p₂).vertices.length := by simp) :
    (p₁.comp p₂).vertices.get ⟨p₁.length, h⟩ = c := by
  simp

@[simp]
/--
lemma `vertices_toPath` / 引理 `vertices_toPath`

English:
lemma vertices_toPath
  given: {i j : V} (e : i ⟶ j)
  proof: by
  change (Path.nil.cons e).vertices = [i, j]
  simp

中文:
引理 vertices_toPath
  条件: {i j : V} (e : i ⟶ j)
  证明: by
  change (Path.nil.cons e).vertices = [i, j]
  simp

Depends on / 依赖: Path.nil.cons, vertices
-/
lemma vertices_toPath {i j : V} (e : i ⟶ j) :
    e.toPath.vertices = [i, j] := by
  change (Path.nil.cons e).vertices = [i, j]
  simp

/--
lemma `vertices_toPath_tail` / 引理 `vertices_toPath_tail`

English:
lemma vertices_toPath_tail
  given: {i j : V} (e : i ⟶ j)
  proof: by
  simp

中文:
引理 vertices_toPath_tail
  条件: {i j : V} (e : i ⟶ j)
  证明: by
  simp
-/
lemma vertices_toPath_tail {i j : V} (e : i ⟶ j) :
    e.toPath.vertices.tail = [j] := by
  simp

/--
lemma `nil_of_comp_eq_nil_left` / 引理 `nil_of_comp_eq_nil_left`

English:
lemma nil_of_comp_eq_nil_left
  statement: {a b : V} {p : Path a b} {q : Path b a}
  proof: by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_right this

中文:
引理 nil_of_comp_eq_nil_left
  结论: {a b : V} {p : Path a b} {q : Path b a}
  证明: by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_right this

Depends on / 依赖: Nat.eq_zero_of_add_eq_zero_right, Path.length, eq_zero_of_add_eq_zero_right, length, length_comp, p.comp, p.length, q.length
-/
lemma nil_of_comp_eq_nil_left {a b : V} {p : Path a b} {q : Path b a}
    (h : p.comp q = Path.nil) : p.length = 0 := by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_right this

/--
lemma `nil_of_comp_eq_nil_right` / 引理 `nil_of_comp_eq_nil_right`

English:
lemma nil_of_comp_eq_nil_right
  statement: {a b : V} {p : Path a b} {q : Path b a}
  proof: by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_left this

中文:
引理 nil_of_comp_eq_nil_right
  结论: {a b : V} {p : Path a b} {q : Path b a}
  证明: by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_left this

Depends on / 依赖: Nat.eq_zero_of_add_eq_zero_left, Path.length, eq_zero_of_add_eq_zero_left, length, length_comp, p.comp, p.length, q.length
-/
lemma nil_of_comp_eq_nil_right {a b : V} {p : Path a b} {q : Path b a}
    (h : p.comp q = Path.nil) : q.length = 0 := by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_left this

/--
lemma `comp_eq_nil_iff` / 引理 `comp_eq_nil_iff`

English:
lemma comp_eq_nil_iff
  given: {a b : V} {p : Path a b} {q : Path b a}
  proof: by
  refine ⟨fun h => ⟨nil_of_comp_eq_nil_left h, nil_of_comp_eq_nil_right h⟩, fun ⟨hp, hq⟩ => ?_⟩
  induction p with
  | nil => simpa using (length_eq_zero_iff q).mp hq
  | cons p' _ ihp => simp at hp

@[simp]

中文:
引理 comp_eq_nil_iff
  条件: {a b : V} {p : Path a b} {q : Path b a}
  证明: by
  refine ⟨fun h => ⟨nil_of_comp_eq_nil_left h, nil_of_comp_eq_nil_right h⟩, fun ⟨hp, hq⟩ => ?_⟩
  induction p with
  | nil => simpa using (length_eq_zero_iff q).mp hq
  | cons p' _ ihp => simp at hp

@[simp]

Depends on / 依赖: length_eq_zero_iff, nil_of_comp_eq_nil_left, nil_of_comp_eq_nil_right
-/
lemma comp_eq_nil_iff {a b : V} {p : Path a b} {q : Path b a} :
    p.comp q = Path.nil ↔ p.length = 0 ∧ q.length = 0 := by
  refine ⟨fun h => ⟨nil_of_comp_eq_nil_left h, nil_of_comp_eq_nil_right h⟩, fun ⟨hp, hq⟩ => ?_⟩
  induction p with
  | nil => simpa using (length_eq_zero_iff q).mp hq
  | cons p' _ ihp => simp at hp

@[simp]
/--
lemma `end_mem_vertices` / 引理 `end_mem_vertices`

English:
lemma end_mem_vertices
  given: {a b : V} (p : Path a b)
  statement: b in p.vertices
  proof: by
  have h₁ : p.vertices.getLast (vertices_ne_nil p) = b :=
    vertices_getLast p (vertices_ne_nil p)
  have h₂ := getLast_mem (l := p.vertices) (vertices_ne_nil p)
  simpa [h₁] using h₂

中文:
引理 end_mem_vertices
  条件: {a b : V} (p : Path a b)
  结论: b in p.vertices
  证明: by
  have h₁ : p.vertices.getLast (vertices_ne_nil p) = b :=
    vertices_getLast p (vertices_ne_nil p)
  have h₂ := getLast_mem (l := p.vertices) (vertices_ne_nil p)
  simpa [h₁] using h₂

Depends on / 依赖: getLast, getLast_mem, p.vertices, p.vertices.getLast, vertices, vertices_getLast, vertices_ne_nil
-/
lemma end_mem_vertices {a b : V} (p : Path a b) : b in p.vertices := by
  have h₁ : p.vertices.getLast (vertices_ne_nil p) = b :=
    vertices_getLast p (vertices_ne_nil p)
  have h₂ := getLast_mem (l := p.vertices) (vertices_ne_nil p)
  simpa [h₁] using h₂

/-! ### Path vertices decomposition -/
section

variable {a b : V} (p : Path a b)

open List

/--
theorem `exists_eq_comp_of_le_length` / 定理 `exists_eq_comp_of_le_length`

English:
theorem exists_eq_comp_of_le_length
  given: {n : Nat} (hn : n <= p.length)
  proof: by
  induction p generalizing n with
  | nil =>
    obtain ⟨rfl⟩ : n = 0 := by simpa using hn
    exact ⟨a, Path.nil, Path.nil, by simp, rfl⟩
  | @cons _ c p' e ih =>
    rw [length_cons] at hn
    rcases (Nat.le_succ_iff).1 hn with h | rfl
    · obtain ⟨d, p₁, p₂, hp, hl⟩ := ih h
      exact ⟨d, p₁

中文:
定理 exists_eq_comp_of_le_length
  条件: {n : 自然数} (hn : n <= p.length)
  证明: by
  induction p generalizing n with
  | nil =>
    obtain ⟨rfl⟩ : n = 0 := by simpa using hn
    exact ⟨a, Path.nil, Path.nil, by simp, rfl⟩
  | @cons _ c p' e ih =>
    rw [length_cons] at hn
    rcases (Nat.le_succ_iff).1 hn with h | rfl
    · obtain ⟨d, p₁, p₂, hp, hl⟩ := ih h
      exact ⟨d, p₁

Depends on / 依赖: Nat.le_succ_iff, Path.nil, generalizing, le_succ_iff, length_cons
-/
theorem exists_eq_comp_of_le_length {n : Nat} (hn : n <= p.length) :
    exists (v : V) (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧ p₁.length = n := by
  induction p generalizing n with
  | nil =>
    obtain ⟨rfl⟩ : n = 0 := by simpa using hn
    exact ⟨a, Path.nil, Path.nil, by simp, rfl⟩
  | @cons _ c p' e ih =>
    rw [length_cons] at hn
    rcases (Nat.le_succ_iff).1 hn with h | rfl
    · obtain ⟨d, p₁, p₂, hp, hl⟩ := ih h
      exact ⟨d, p₁, p₂.cons e, by simp [hp], hl⟩
    · exact ⟨c, p'.cons e, Path.nil, by simp, by simp⟩

/--
theorem `exists_eq_comp_and_length_eq_of_lt_length` / 定理 `exists_eq_comp_and_length_eq_of_lt_length`

English:
theorem exists_eq_comp_and_length_eq_of_lt_length
  given: (n : Nat) (hn : n < p.vertices.length)
  proof: by
  have hn_le_len : n <= p.length := by
    rw [vertices_length] at hn
    exact Nat.le_of_lt_succ hn
  obtain ⟨v, p₁, p₂, rfl, rfl⟩ := p.exists_eq_comp_of_le_length hn_le_len
  exact ⟨v, p₁, p₂, rfl, rfl, by simp⟩

中文:
定理 exists_eq_comp_and_length_eq_of_lt_length
  条件: (n : 自然数) (hn : n < p.vertices.length)
  证明: by
  have hn_le_len : n <= p.length := by
    rw [vertices_length] at hn
    exact Nat.le_of_lt_succ hn
  obtain ⟨v, p₁, p₂, rfl, rfl⟩ := p.exists_eq_comp_of_le_length hn_le_len
  exact ⟨v, p₁, p₂, rfl, rfl, by simp⟩

Depends on / 依赖: Nat.le_of_lt_succ, exists_eq_comp_of_le_length, hn_le_len, le_of_lt_succ, length, p.exists_eq_comp_of_le_length, p.length, vertices_length
-/
theorem exists_eq_comp_and_length_eq_of_lt_length (n : Nat) (hn : n < p.vertices.length) :
    exists (v : V) (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧ p₁.length = n ∧ v = p.vertices[n] := by
  have hn_le_len : n <= p.length := by
    rw [vertices_length] at hn
    exact Nat.le_of_lt_succ hn
  obtain ⟨v, p₁, p₂, rfl, rfl⟩ := p.exists_eq_comp_of_le_length hn_le_len
  exact ⟨v, p₁, p₂, rfl, rfl, by simp⟩

/--
theorem `exists_eq_comp_of_mem_vertices` / 定理 `exists_eq_comp_of_mem_vertices`

English:
theorem exists_eq_comp_of_mem_vertices
  given: {v : V} (hv : v in p.vertices)
  proof: by
  obtain ⟨n, hn, rfl⟩ : exists n, exists hn : n < p.vertices.length, v = p.vertices[n] :=
    exists_mem_iff_getElem.mp ⟨v, hv, rfl⟩
  obtain ⟨v, p₁, p₂, hp, hv, rfl⟩ := p.exists_eq_comp_and_length_eq_of_lt_length n hn
  exact ⟨p₁, p₂, hp⟩

中文:
定理 exists_eq_comp_of_mem_vertices
  条件: {v : V} (hv : v in p.vertices)
  证明: by
  obtain ⟨n, hn, rfl⟩ : exists n, exists hn : n < p.vertices.length, v = p.vertices[n] :=
    exists_mem_iff_getElem.mp ⟨v, hv, rfl⟩
  obtain ⟨v, p₁, p₂, hp, hv, rfl⟩ := p.exists_eq_comp_and_length_eq_of_lt_length n hn
  exact ⟨p₁, p₂, hp⟩

Depends on / 依赖: exists_eq_comp_and_length_eq_of_lt_length, exists_mem_iff_getElem, exists_mem_iff_getElem.mp, length, p.exists_eq_comp_and_length_eq_of_lt_length, p.vertices, p.vertices.length, vertices
-/
theorem exists_eq_comp_of_mem_vertices {v : V} (hv : v in p.vertices) :
    exists (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ := by
  obtain ⟨n, hn, rfl⟩ : exists n, exists hn : n < p.vertices.length, v = p.vertices[n] :=
    exists_mem_iff_getElem.mp ⟨v, hv, rfl⟩
  obtain ⟨v, p₁, p₂, hp, hv, rfl⟩ := p.exists_eq_comp_and_length_eq_of_lt_length n hn
  exact ⟨p₁, p₂, hp⟩

/--
theorem `exists_eq_comp_and_notMem_tail_of_mem_vertices` / 定理 `exists_eq_comp_and_notMem_tail_of_mem_vertices`

English:
theorem exists_eq_comp_and_notMem_tail_of_mem_vertices
  given: {v : V} (hv : v in p.vertices)
  proof: by
  induction p with
  | nil =>
    have hxa : v = a := by
      simpa [vertices_nil, List.mem_singleton] using hv
    subst hxa
    exact ⟨Path.nil, Path.nil, by simp only [comp_nil],
      by simp only [vertices_nil, tail_cons, not_mem_nil, not_false_eq_true]⟩
  | cons pPrev e ih =>
    have hv' 

中文:
定理 exists_eq_comp_and_notMem_tail_of_mem_vertices
  条件: {v : V} (hv : v in p.vertices)
  证明: by
  induction p with
  | nil =>
    have hxa : v = a := by
      simpa [vertices_nil, List.mem_singleton] using hv
    subst hxa
    exact ⟨Path.nil, Path.nil, by simp only [comp_nil],
      by simp only [vertices_nil, tail_cons, not_mem_nil, not_false_eq_true]⟩
  | cons pPrev e ih =>
    have hv' 

Depends on / 依赖: List.mem_singleton, Path.nil, comp_nil, mem_singleton, mem_vertices_cons, not_false_eq_true, not_mem_nil, pPrev.cons, pPrev.vertices, tail_cons, vertices, vertices_nil
-/
theorem exists_eq_comp_and_notMem_tail_of_mem_vertices {v : V} (hv : v in p.vertices) :
    exists (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
  induction p with
  | nil =>
    have hxa : v = a := by
      simpa [vertices_nil, List.mem_singleton] using hv
    subst hxa
    exact ⟨Path.nil, Path.nil, by simp only [comp_nil],
      by simp only [vertices_nil, tail_cons, not_mem_nil, not_false_eq_true]⟩
  | cons pPrev e ih =>
    have hv' : v in pPrev.vertices ∨ v = (pPrev.cons e).end := by
      simpa using (mem_vertices_cons pPrev e).1 hv
    have h_case₁ : v = (pPrev.cons e).end -> exists (p₁ : Path a v) (p₂ : Path v (pPrev.cons e).end),
        pPrev.cons e = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
      rintro rfl
      exact ⟨pPrev.cons e, Path.nil, by simp [comp_nil], by simp [vertices_nil]⟩
    have h_case₂ : v in pPrev.vertices -> v != (pPrev.cons e).end ->
        exists (p₁ : Path a v) (p₂ : Path v (pPrev.cons e).end),
          pPrev.cons e = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
      intro hxPrev hxe_ne
      obtain ⟨q₁, q₂, h_prev, h_not_tail⟩ := ih hxPrev
      let q₂' : Path v (pPrev.cons e).end := q₂.cons e
      have h_no_tail : v ∉ q₂'.vertices.tail := by grind [vertices_cons, end_cons]
      exact ⟨q₁, q₂', by simp [q₂', h_prev], h_no_tail⟩
    cases hv' with
    | inl h_in_prefix =>
      by_cases h_eq_end : v = (pPrev.cons e).end
      · exact h_case₁ h_eq_end
      · exact h_case₂ h_in_prefix h_eq_end
    | inr h_eq_end => exact h_case₁ h_eq_end

end

end Quiver.Path
