/-
Copyright (c) 2025 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Subwalks

We define a relation on walks stating that one walk is the subwalk of another.

## Main definitions

* `SimpleGraph.Walk.IsSubwalk`: A relation on walks stating that the first walk is a contiguous
  subwalk of the second walk.

## Tags
walks, subwalks
-/

@[expose] public section

namespace SimpleGraph

namespace Walk

variable {V : Type*} {G G' : SimpleGraph V} {u v u' v' : V}

/--
Definition of `IsSubwalk` / `IsSubwalk` 的定义

English:
definition IsSubwalk
  signature: {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂)
  body: exists (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv

@[refl, simp]

中文:
定义 IsSubwalk
  签名: {u₁ v₁ u₂ v₂} (p : G.途径 u₁ v₁) (q : G.途径 u₂ v₂)
  定义体: exists (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv

@[refl, simp]

Depends on / 依赖: G.Walk, append, ru.append
-/
def IsSubwalk {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop :=
  exists (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv

@[refl, simp]
/--
lemma `isSubwalk_rfl` / 引理 `isSubwalk_rfl`

English:
lemma isSubwalk_rfl
  given: {u v} (p : G.Walk u v)
  statement: p.IsSubwalk p
  proof: ⟨nil, nil, by simp⟩

@[simp]

中文:
引理 isSubwalk_rfl
  条件: {u v} (p : G.途径 u v)
  结论: p.IsSubwalk p
  证明: ⟨nil, nil, by simp⟩

@[simp]
-/
lemma isSubwalk_rfl {u v} (p : G.Walk u v) : p.IsSubwalk p :=
  ⟨nil, nil, by simp⟩

@[simp]
/--
lemma `isSubwalk_nil_start` / 引理 `isSubwalk_nil_start`

English:
lemma isSubwalk_nil_start
  given: {u v} (q : G.Walk u v)
  statement: (Walk.nil : G.Walk u u).IsSubwalk q
  proof: ⟨nil, q, by simp⟩

@[deprecated (since := "2026-07-11")] alias nil_isSubwalk := isSubwalk_nil_start

@[simp]

中文:
引理 isSubwalk_nil_start
  条件: {u v} (q : G.途径 u v)
  结论: (途径.nil : G.途径 u u).IsSubwalk q
  证明: ⟨nil, q, by simp⟩

@[deprecated (since := "2026-07-11")] alias nil_isSubwalk := isSubwalk_nil_start

@[simp]
-/
lemma isSubwalk_nil_start {u v} (q : G.Walk u v) : (Walk.nil : G.Walk u u).IsSubwalk q :=
  ⟨nil, q, by simp⟩

@[deprecated (since := "2026-07-11")] alias nil_isSubwalk := isSubwalk_nil_start

@[simp]
/--
theorem `isSubwalk_nil_end` / 定理 `isSubwalk_nil_end`

English:
theorem isSubwalk_nil_end
  given: {u v} (q : G.Walk u v)
  statement: (nil : G.Walk v v).IsSubwalk q
  proof: ⟨q, nil, by simp⟩

中文:
定理 isSubwalk_nil_end
  条件: {u v} (q : G.途径 u v)
  结论: (nil : G.途径 v v).IsSubwalk q
  证明: ⟨q, nil, by simp⟩
-/
theorem isSubwalk_nil_end {u v} (q : G.Walk u v) : (nil : G.Walk v v).IsSubwalk q :=
  ⟨q, nil, by simp⟩

/--
lemma `IsSubwalk.cons` / 引理 `IsSubwalk.cons`

English:
lemma IsSubwalk.cons
  statement: {u v u' v' w} {p : G.Walk u v} {q : G.Walk u' v'}
  proof: by
  obtain ⟨r1, r2, rfl⟩ := hpq
  use r1.cons h, r2
  simp

@[simp]

中文:
引理 IsSubwalk.cons
  结论: {u v u' v' w} {p : G.途径 u v} {q : G.途径 u' v'}
  证明: by
  obtain ⟨r1, r2, rfl⟩ := hpq
  use r1.cons h, r2
  simp

@[simp]
-/
protected lemma IsSubwalk.cons {u v u' v' w} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) (h : G.Adj w u') : p.IsSubwalk (q.cons h) := by
  obtain ⟨r1, r2, rfl⟩ := hpq
  use r1.cons h, r2
  simp

@[simp]
/--
lemma `isSubwalk_cons` / 引理 `isSubwalk_cons`

English:
lemma isSubwalk_cons
  given: {u v w} (p : G.Walk u v) (h : G.Adj w u)
  statement: p.IsSubwalk (p.cons h)
  proof: (isSubwalk_rfl p).cons h

中文:
引理 isSubwalk_cons
  条件: {u v w} (p : G.途径 u v) (h : G.伴随 w u)
  结论: p.IsSubwalk (p.cons h)
  证明: (isSubwalk_rfl p).cons h

Depends on / 依赖: isSubwalk_rfl
-/
lemma isSubwalk_cons {u v w} (p : G.Walk u v) (h : G.Adj w u) : p.IsSubwalk (p.cons h) :=
  (isSubwalk_rfl p).cons h

/--
lemma `IsSubwalk.concat` / 引理 `IsSubwalk.concat`

English:
lemma IsSubwalk.concat
  statement: {u v u' v' w} {p : G.Walk u v} {q : G.Walk u' v'}
  proof: by
  obtain ⟨r₁, r₂, rfl⟩ := hpq
  exact ⟨r₁, r₂.concat h, by rw [append_concat]⟩

@[simp]

中文:
引理 IsSubwalk.concat
  结论: {u v u' v' w} {p : G.途径 u v} {q : G.途径 u' v'}
  证明: by
  obtain ⟨r₁, r₂, rfl⟩ := hpq
  exact ⟨r₁, r₂.concat h, by rw [append_concat]⟩

@[simp]
-/
protected lemma IsSubwalk.concat {u v u' v' w} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) (h : G.Adj v' w) : p.IsSubwalk (q.concat h) := by
  obtain ⟨r₁, r₂, rfl⟩ := hpq
  exact ⟨r₁, r₂.concat h, by rw [append_concat]⟩

@[simp]
/--
lemma `isSubwalk_concat` / 引理 `isSubwalk_concat`

English:
lemma isSubwalk_concat
  given: {u v w} (p : G.Walk u v) (h : G.Adj v w)
  statement: p.IsSubwalk (p.concat h)
  proof: (isSubwalk_rfl p).concat h

中文:
引理 isSubwalk_concat
  条件: {u v w} (p : G.途径 u v) (h : G.伴随 v w)
  结论: p.IsSubwalk (p.concat h)
  证明: (isSubwalk_rfl p).concat h

Depends on / 依赖: concat, isSubwalk_rfl
-/
lemma isSubwalk_concat {u v w} (p : G.Walk u v) (h : G.Adj v w) : p.IsSubwalk (p.concat h) :=
  (isSubwalk_rfl p).concat h

/--
lemma `IsSubwalk.trans` / 引理 `IsSubwalk.trans`

English:
lemma IsSubwalk.trans
  statement: {u₁ v₁ u₂ v₂ u₃ v₃} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}
  proof: by
  obtain ⟨q₁, r₁, rfl⟩ := h₁
  obtain ⟨q₂, r₂, rfl⟩ := h₂
  use q₂.append q₁, r₁.append r₂
  simp [append_assoc]

中文:
引理 IsSubwalk.trans
  结论: {u₁ v₁ u₂ v₂ u₃ v₃} {p₁ : G.途径 u₁ v₁} {p₂ : G.途径 u₂ v₂}
  证明: by
  obtain ⟨q₁, r₁, rfl⟩ := h₁
  obtain ⟨q₂, r₂, rfl⟩ := h₂
  use q₂.append q₁, r₁.append r₂
  simp [append_assoc]

Depends on / 依赖: append, append_assoc
-/
lemma IsSubwalk.trans {u₁ v₁ u₂ v₂ u₃ v₃} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}
    {p₃ : G.Walk u₃ v₃} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₃) :
    p₁.IsSubwalk p₃ := by
  obtain ⟨q₁, r₁, rfl⟩ := h₁
  obtain ⟨q₂, r₂, rfl⟩ := h₂
  use q₂.append q₁, r₁.append r₂
  simp [append_assoc]

/--
lemma `isSubwalk_nil_iff` / 引理 `isSubwalk_nil_iff`

English:
lemma isSubwalk_nil_iff
  given: {u v u'} (p : G.Walk u v)
  proof: by
  cases p with
  | nil =>
    constructor
    · rintro ⟨_ | _, _, ⟨⟩⟩
      simp
    · rintro ⟨rfl, _, _⟩
      simp
  | cons h p =>
    constructor
    · rintro ⟨_ | _, _, h⟩ <;> simp at h
    · rintro ⟨rfl, rfl, ⟨⟩⟩

中文:
引理 isSubwalk_nil_iff
  条件: {u v u'} (p : G.途径 u v)
  证明: by
  cases p with
  | nil =>
    constructor
    · rintro ⟨_ | _, _, ⟨⟩⟩
      simp
    · rintro ⟨rfl, _, _⟩
      simp
  | cons h p =>
    constructor
    · rintro ⟨_ | _, _, h⟩ <;> simp at h
    · rintro ⟨rfl, rfl, ⟨⟩⟩
-/
lemma isSubwalk_nil_iff {u v u'} (p : G.Walk u v) :
    p.IsSubwalk (nil : G.Walk u' u') ↔ exists (hu : u' = u) (hv : u' = v), p = nil.copy hu hv := by
  cases p with
  | nil =>
    constructor
    · rintro ⟨_ | _, _, ⟨⟩⟩
      simp
    · rintro ⟨rfl, _, _⟩
      simp
  | cons h p =>
    constructor
    · rintro ⟨_ | _, _, h⟩ <;> simp at h
    · rintro ⟨rfl, rfl, ⟨⟩⟩

/--
lemma `nil_isSubwalk_iff_exists` / 引理 `nil_isSubwalk_iff_exists`

English:
lemma nil_isSubwalk_iff_exists
  given: {u' u v} (q : G.Walk u v)
  proof: by
  simp [IsSubwalk]

中文:
引理 nil_isSubwalk_iff_存在
  条件: {u' u v} (q : G.途径 u v)
  证明: by
  simp [IsSubwalk]

Depends on / 依赖: IsSubwalk
-/
lemma nil_isSubwalk_iff_exists {u' u v} (q : G.Walk u v) :
    (Walk.nil : G.Walk u' u').IsSubwalk q ↔
      exists (ru : G.Walk u u') (rv : G.Walk u' v), q = ru.append rv := by
  simp [IsSubwalk]

/--
lemma `length_le_of_isSubwalk` / 引理 `length_le_of_isSubwalk`

English:
lemma length_le_of_isSubwalk
  statement: {u₁ v₁ u₂ v₂} {q : G.Walk u₁ v₁} {p : G.Walk u₂ v₂}
  proof: by
  grind [IsSubwalk, length_append]

中文:
引理 length_le_of_isSubwalk
  结论: {u₁ v₁ u₂ v₂} {q : G.途径 u₁ v₁} {p : G.途径 u₂ v₂}
  证明: by
  grind [IsSubwalk, length_append]

Depends on / 依赖: IsSubwalk, length_append
-/
lemma length_le_of_isSubwalk {u₁ v₁ u₂ v₂} {q : G.Walk u₁ v₁} {p : G.Walk u₂ v₂}
    (h : p.IsSubwalk q) : p.length <= q.length := by
  grind [IsSubwalk, length_append]

/--
lemma `isSubwalk_of_append_left` / 引理 `isSubwalk_of_append_left`

English:
lemma isSubwalk_of_append_left
  statement: {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u}
  proof: ⟨nil, p₂, h⟩

中文:
引理 isSubwalk_of_append_left
  结论: {v w u : V} {p₁ : G.途径 v w} {p₂ : G.途径 w u} {p₃ : G.途径 v u}
  证明: ⟨nil, p₂, h⟩
-/
lemma isSubwalk_of_append_left {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u}
    (h : p₃ = p₁.append p₂) : p₁.IsSubwalk p₃ :=
  ⟨nil, p₂, h⟩

/--
lemma `isSubwalk_of_append_right` / 引理 `isSubwalk_of_append_right`

English:
lemma isSubwalk_of_append_right
  statement: {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u}
  proof: ⟨p₁, nil, append_nil _ ▸ h⟩

中文:
引理 isSubwalk_of_append_right
  结论: {v w u : V} {p₁ : G.途径 v w} {p₂ : G.途径 w u} {p₃ : G.途径 v u}
  证明: ⟨p₁, nil, append_nil _ ▸ h⟩

Depends on / 依赖: append_nil
-/
lemma isSubwalk_of_append_right {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u}
    (h : p₃ = p₁.append p₂) : p₂.IsSubwalk p₃ :=
  ⟨p₁, nil, append_nil _ ▸ h⟩

/--
theorem `isSubwalk_take` / 定理 `isSubwalk_take`

English:
theorem isSubwalk_take
  given: {u v : V} (p : G.Walk u v) (n : Nat)
  statement: (p.take n).IsSubwalk p
  proof: ⟨nil, p.drop n, by simp⟩

中文:
定理 isSubwalk_take
  条件: {u v : V} (p : G.途径 u v) (n : 自然数)
  结论: (p.take n).IsSubwalk p
  证明: ⟨nil, p.drop n, by simp⟩

Depends on / 依赖: p.drop
-/
theorem isSubwalk_take {u v : V} (p : G.Walk u v) (n : Nat) : (p.take n).IsSubwalk p :=
  ⟨nil, p.drop n, by simp⟩

/--
theorem `isSubwalk_drop` / 定理 `isSubwalk_drop`

English:
theorem isSubwalk_drop
  given: {u v : V} (p : G.Walk u v) (n : Nat)
  statement: (p.drop n).IsSubwalk p
  proof: ⟨p.take n, nil, by simp⟩

中文:
定理 isSubwalk_drop
  条件: {u v : V} (p : G.途径 u v) (n : 自然数)
  结论: (p.drop n).IsSubwalk p
  证明: ⟨p.take n, nil, by simp⟩

Depends on / 依赖: p.take
-/
theorem isSubwalk_drop {u v : V} (p : G.Walk u v) (n : Nat) : (p.drop n).IsSubwalk p :=
  ⟨p.take n, nil, by simp⟩

/--
theorem `isSubwalk_iff_support_isInfix` / 定理 `isSubwalk_iff_support_isInfix`

English:
theorem isSubwalk_iff_support_isInfix
  given: {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'}
  proof: by
  refine ⟨fun ⟨ru, rv, h⟩ => ?_, fun ⟨s, t, h⟩ => ?_⟩
  · grind [support_append, support_append_eq_support_dropLast_append]
  · have : (s.length + p₁.length) <= p₂.length := by grind [_=_ length_support]
.copy ?_ rfl, ?_⟩ .copy rfl ?_, p₂.drop (s.length + p₁.length) refine ⟨p₂.take s.length
    · simp [p₂.getVert_eq_support_getElem (by lia : s.length <= p₂.length), ← h,
        List.getElem_zero]
    · simp [p₂.getVert_eq_support_getElem this, ← h, ← p₁.getVert_eq_support_getElem le_rfl]
    apply ext_support
    simp only [← h, support_append, support_copy, support_take,
      List.take_append, drop_support_eq_support_drop_min, List.tail_drop]
    rw [Nat.min_eq_left (by grind)]; rw [List.drop_append]; rw [List.drop_append]; rw [List.drop_eq_nil_of_le (by lia)]; rw [List.drop_eq_nil_of_le (by grind)]; rw [← p₁.cons_tail_support]
    simp +arith [-cons_tail_support]

中文:
定理 isSubwalk_iff_support_isInfix
  条件: {v w v' w' : V} {p₁ : G.途径 v w} {p₂ : G.途径 v' w'}
  证明: by
  refine ⟨fun ⟨ru, rv, h⟩ => ?_, fun ⟨s, t, h⟩ => ?_⟩
  · grind [support_append, support_append_eq_support_dropLast_append]
  · have : (s.length + p₁.length) <= p₂.length := by grind [_=_ length_support]
.copy ?_ rfl, ?_⟩ .copy rfl ?_, p₂.drop (s.length + p₁.length) refine ⟨p₂.take s.length
    · simp [p₂.getVert_eq_support_getElem (by lia : s.length <= p₂.length), ← h,
        List.getElem_zero]
    · simp [p₂.getVert_eq_support_getElem this, ← h, ← p₁.getVert_eq_support_getElem le_rfl]
    apply ext_support
    simp only [← h, support_append, support_copy, support_take,
      List.take_append, drop_support_eq_support_drop_min, List.tail_drop]
    rw [Nat.min_eq_left (by grind)]; rw [List.drop_append]; rw [List.drop_append]; rw [List.drop_eq_nil_of_le (by lia)]; rw [List.drop_eq_nil_of_le (by grind)]; rw [← p₁.cons_tail_support]
    simp +arith [-cons_tail_support]

Depends on / 依赖: List.getElem_zero, ext_support, getElem_zero, getVert_eq_support_getElem, le_rfl, length, length_support, s.length, support_append, support_append_eq_support_dropLast_append
-/
theorem isSubwalk_iff_support_isInfix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} :
    p₁.IsSubwalk p₂ ↔ p₁.support <:+: p₂.support := by
  refine ⟨fun ⟨ru, rv, h⟩ => ?_, fun ⟨s, t, h⟩ => ?_⟩
  · grind [support_append, support_append_eq_support_dropLast_append]
  · have : (s.length + p₁.length) <= p₂.length := by grind [_=_ length_support]
.copy ?_ rfl, ?_⟩ .copy rfl ?_, p₂.drop (s.length + p₁.length) refine ⟨p₂.take s.length
    · simp [p₂.getVert_eq_support_getElem (by lia : s.length <= p₂.length), ← h,
        List.getElem_zero]
    · simp [p₂.getVert_eq_support_getElem this, ← h, ← p₁.getVert_eq_support_getElem le_rfl]
    apply ext_support
    simp only [← h, support_append, support_copy, support_take,
      List.take_append, drop_support_eq_support_drop_min, List.tail_drop]
    rw [Nat.min_eq_left (by grind)]; rw [List.drop_append]; rw [List.drop_append]; rw [List.drop_eq_nil_of_le (by lia)]; rw [List.drop_eq_nil_of_le (by grind)]; rw [← p₁.cons_tail_support]
    simp +arith [-cons_tail_support]

/--
theorem `isSubwalk_iff_darts_isInfix` / 定理 `isSubwalk_iff_darts_isInfix`

English:
theorem isSubwalk_iff_darts_isInfix
  given: {p₁ : G.Walk u v} {p₂ : G.Walk u' v'} (hnil : ¬p₁.Nil)
  proof: by
  rw [isSubwalk_iff_support_isInfix]; rw [List.infix_iff_getElem?]; rw [List.infix_iff_getElem?]
  refine ⟨fun ⟨k, hk, h⟩ => ⟨k, by grind, fun i hi => ?_⟩,
    fun ⟨k, hk, h⟩ => ⟨k, by grind, fun i hi => ?_⟩⟩
  · rw [getElem?_pos _ _ <| by grind, Option.some_inj]
    ext <;> grind [fst_darts_getElem, snd_darts_getElem]
  · rw [getElem?_pos _ _ <| by grind, Option.some_inj]
    by_cases hi' : i = p₁.length
· have := h i - 1
      grind [not_nil_iff_lt_length, snd_darts_getElem]
    have := h i
    grind [fst_darts_getElem]

@[simp]

中文:
定理 isSubwalk_iff_darts_isInfix
  条件: {p₁ : G.途径 u v} {p₂ : G.途径 u' v'} (hnil : ¬p₁.Nil)
  证明: by
  rw [isSubwalk_iff_support_isInfix]; rw [List.infix_iff_getElem?]; rw [List.infix_iff_getElem?]
  refine ⟨fun ⟨k, hk, h⟩ => ⟨k, by grind, fun i hi => ?_⟩,
    fun ⟨k, hk, h⟩ => ⟨k, by grind, fun i hi => ?_⟩⟩
  · rw [getElem?_pos _ _ <| by grind, Option.some_inj]
    ext <;> grind [fst_darts_getElem, snd_darts_getElem]
  · rw [getElem?_pos _ _ <| by grind, Option.some_inj]
    by_cases hi' : i = p₁.length
· have := h i - 1
      grind [not_nil_iff_lt_length, snd_darts_getElem]
    have := h i
    grind [fst_darts_getElem]

@[simp]

Depends on / 依赖: List.infix_iff_getElem, Option.some_inj, _pos, fst_darts_getElem, getElem, infix_iff_getElem, isSubwalk_iff_support_isInfix, length, not_nil_iff_lt_length, snd_darts_getElem, some_inj
-/
theorem isSubwalk_iff_darts_isInfix {p₁ : G.Walk u v} {p₂ : G.Walk u' v'} (hnil : ¬p₁.Nil) :
    p₁.IsSubwalk p₂ ↔ p₁.darts <:+: p₂.darts := by
  rw [isSubwalk_iff_support_isInfix]; rw [List.infix_iff_getElem?]; rw [List.infix_iff_getElem?]
  refine ⟨fun ⟨k, hk, h⟩ => ⟨k, by grind, fun i hi => ?_⟩,
    fun ⟨k, hk, h⟩ => ⟨k, by grind, fun i hi => ?_⟩⟩
  · rw [getElem?_pos _ _ <| by grind, Option.some_inj]
    ext <;> grind [fst_darts_getElem, snd_darts_getElem]
  · rw [getElem?_pos _ _ <| by grind, Option.some_inj]
    by_cases hi' : i = p₁.length
· have := h i - 1
      grind [not_nil_iff_lt_length, snd_darts_getElem]
    have := h i
    grind [fst_darts_getElem]

@[simp]
/--
theorem `isSubwalk_nil_iff_mem_support` / 定理 `isSubwalk_nil_iff_mem_support`

English:
theorem isSubwalk_nil_iff_mem_support
  given: (p : G.Walk u v)
  proof: isSubwalk_iff_support_isInfix.trans p.support.singleton_infix_iff _

中文:
定理 isSubwalk_nil_iff_mem_support
  条件: (p : G.途径 u v)
  证明: isSubwalk_iff_support_isInfix.trans p.support.singleton_infix_iff _

Depends on / 依赖: isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.trans, p.support.singleton_infix_iff, singleton_infix_iff, support
-/
theorem isSubwalk_nil_iff_mem_support (p : G.Walk u v) :
    (nil : G.Walk v' v').IsSubwalk p ↔ v' in p.support :=
isSubwalk_iff_support_isInfix.trans p.support.singleton_infix_iff _

/--
theorem `isSubwalk_toWalk_iff_mem_darts` / 定理 `isSubwalk_toWalk_iff_mem_darts`

English:
theorem isSubwalk_toWalk_iff_mem_darts
  given: (p : G.Walk u v) (h : G.Adj u' v')
  proof: by
  simp [isSubwalk_iff_darts_isInfix, List.singleton_infix_iff]

中文:
定理 isSubwalk_toWalk_iff_mem_darts
  条件: (p : G.途径 u v) (h : G.伴随 u' v')
  证明: by
  simp [isSubwalk_iff_darts_isInfix, List.singleton_infix_iff]

Depends on / 依赖: List.singleton_infix_iff, isSubwalk_iff_darts_isInfix, singleton_infix_iff
-/
theorem isSubwalk_toWalk_iff_mem_darts (p : G.Walk u v) (h : G.Adj u' v') :
    h.toWalk.IsSubwalk p ↔ ⟨⟨u', v'⟩, h⟩ in p.darts := by
  simp [isSubwalk_iff_darts_isInfix, List.singleton_infix_iff]

/--
theorem `isSubwalk_toWalk_adj_iff_mem_darts` / 定理 `isSubwalk_toWalk_adj_iff_mem_darts`

English:
theorem isSubwalk_toWalk_adj_iff_mem_darts
  given: {d : G.Dart} (p : G.Walk u v)
  proof: isSubwalk_toWalk_iff_mem_darts ..

中文:
定理 isSubwalk_toWalk_adj_iff_mem_darts
  条件: {d : G.Dart} (p : G.途径 u v)
  证明: isSubwalk_toWalk_iff_mem_darts ..

Depends on / 依赖: isSubwalk_toWalk_iff_mem_darts
-/
theorem isSubwalk_toWalk_adj_iff_mem_darts {d : G.Dart} (p : G.Walk u v) :
    d.adj.toWalk.IsSubwalk p ↔ d in p.darts :=
  isSubwalk_toWalk_iff_mem_darts ..

/--
theorem `isSubwalk_toWalk_iff_mem_edges` / 定理 `isSubwalk_toWalk_iff_mem_edges`

English:
theorem isSubwalk_toWalk_iff_mem_edges
  given: {p : G.Walk u v} (h : G.Adj u' v')
  proof: by
  rw [isSubwalk_toWalk_iff_mem_darts]; rw [isSubwalk_toWalk_iff_mem_darts]; rw [edges]; rw [List.mem_map]
  refine ⟨fun h => by grind [Dart.edge], fun h => ?_⟩
  have ⟨d, hd, h⟩ := h
  rw [Dart.edge]; rw [Sym2.eq]; rw [Sym2.rel_iff'] at h
  refine h.imp (fun h => ?_) (fun h => ?_)
    <;> convert! hd using 2
    <;> exact h.symm

中文:
定理 isSubwalk_toWalk_iff_mem_edges
  条件: {p : G.途径 u v} (h : G.伴随 u' v')
  证明: by
  rw [isSubwalk_toWalk_iff_mem_darts]; rw [isSubwalk_toWalk_iff_mem_darts]; rw [edges]; rw [List.mem_map]
  refine ⟨fun h => by grind [Dart.edge], fun h => ?_⟩
  have ⟨d, hd, h⟩ := h
  rw [Dart.edge]; rw [Sym2.eq]; rw [Sym2.rel_iff'] at h
  refine h.imp (fun h => ?_) (fun h => ?_)
    <;> convert! hd using 2
    <;> exact h.symm

Depends on / 依赖: Dart.edge, List.mem_map, Sym2.eq, Sym2.rel_iff, convert, h.imp, h.symm, isSubwalk_toWalk_iff_mem_darts, mem_map, rel_iff
-/
theorem isSubwalk_toWalk_iff_mem_edges {p : G.Walk u v} (h : G.Adj u' v') :
    h.toWalk.IsSubwalk p ∨ h.symm.toWalk.IsSubwalk p ↔ s(u', v') in p.edges := by
  rw [isSubwalk_toWalk_iff_mem_darts]; rw [isSubwalk_toWalk_iff_mem_darts]; rw [edges]; rw [List.mem_map]
  refine ⟨fun h => by grind [Dart.edge], fun h => ?_⟩
  have ⟨d, hd, h⟩ := h
  rw [Dart.edge]; rw [Sym2.eq]; rw [Sym2.rel_iff'] at h
  refine h.imp (fun h => ?_) (fun h => ?_)
    <;> convert! hd using 2
    <;> exact h.symm

/--
theorem `infix_support_iff_mem_edges` / 定理 `infix_support_iff_mem_edges`

English:
theorem infix_support_iff_mem_edges
  given: {p : G.Walk u v}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.elim adj_of_infix_support (adj_of_infix_support · |>.symm)
    simpa [← isSubwalk_toWalk_iff_mem_edges this, isSubwalk_iff_support_isInfix]
  · have := (isSubwalk_toWalk_iff_mem_edges <| p.adj_of_mem_edges h).mpr h
    simpa [isSubwalk_iff_support_isInfix]

中文:
定理 infix_support_iff_mem_edges
  条件: {p : G.途径 u v}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.elim adj_of_infix_support (adj_of_infix_support · |>.symm)
    simpa [← isSubwalk_toWalk_iff_mem_edges this, isSubwalk_iff_support_isInfix]
  · have := (isSubwalk_toWalk_iff_mem_edges <| p.adj_of_mem_edges h).mpr h
    simpa [isSubwalk_iff_support_isInfix]

Depends on / 依赖: adj_of_infix_support, adj_of_mem_edges, h.elim, isSubwalk_iff_support_isInfix, isSubwalk_toWalk_iff_mem_edges, p.adj_of_mem_edges
-/
theorem infix_support_iff_mem_edges {p : G.Walk u v} :
    [u', v'] <:+: p.support ∨ [v', u'] <:+: p.support ↔ s(u', v') in p.edges := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.elim adj_of_infix_support (adj_of_infix_support · |>.symm)
    simpa [← isSubwalk_toWalk_iff_mem_edges this, isSubwalk_iff_support_isInfix]
  · have := (isSubwalk_toWalk_iff_mem_edges <| p.adj_of_mem_edges h).mpr h
    simpa [isSubwalk_iff_support_isInfix]

/--
lemma `isSubwalk_antisymm` / 引理 `isSubwalk_antisymm`

English:
lemma isSubwalk_antisymm
  given: {u v} {p₁ p₂ : G.Walk u v} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₁)
  proof: by
  rw [isSubwalk_iff_support_isInfix] at h₁ h₂
exact ext_support List.infix_antisymm h₁ h₂

@[simp]

中文:
引理 isSubwalk_antisymm
  条件: {u v} {p₁ p₂ : G.途径 u v} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₁)
  证明: by
  rw [isSubwalk_iff_support_isInfix] at h₁ h₂
exact ext_support List.infix_antisymm h₁ h₂

@[simp]

Depends on / 依赖: List.infix_antisymm, ext_support, infix_antisymm, isSubwalk_iff_support_isInfix
-/
lemma isSubwalk_antisymm {u v} {p₁ p₂ : G.Walk u v} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₁) :
    p₁ = p₂ := by
  rw [isSubwalk_iff_support_isInfix] at h₁ h₂
exact ext_support List.infix_antisymm h₁ h₂

@[simp]
/--
theorem `IsSubwalk.support_subset` / 定理 `IsSubwalk.support_subset`

English:
theorem IsSubwalk.support_subset
  statement: {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
  proof: (isSubwalk_iff_support_isInfix.mp h).subset

中文:
定理 IsSubwalk.support_subset
  结论: {u v u' v' : V} {p₁ : G.途径 u v} {p₂ : G.途径 u' v'}
  证明: (isSubwalk_iff_support_isInfix.mp h).subset

Depends on / 依赖: isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp, subset
-/
theorem IsSubwalk.support_subset {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) : p₂.support subseteq p₁.support :=
  (isSubwalk_iff_support_isInfix.mp h).subset

/--
theorem `IsSubwalk.edges_isInfix` / 定理 `IsSubwalk.edges_isInfix`

English:
theorem IsSubwalk.edges_isInfix
  statement: {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
  proof: by
  grind [edges_append, IsSubwalk]

@[simp]

中文:
定理 IsSubwalk.edges_isInfix
  结论: {u v u' v' : V} {p₁ : G.途径 u v} {p₂ : G.途径 u' v'}
  证明: by
  grind [edges_append, IsSubwalk]

@[simp]

Depends on / 依赖: IsSubwalk, edges_append
-/
theorem IsSubwalk.edges_isInfix {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₁.IsSubwalk p₂) : p₁.edges <:+: p₂.edges := by
  grind [edges_append, IsSubwalk]

@[simp]
/--
theorem `IsSubwalk.edges_subset` / 定理 `IsSubwalk.edges_subset`

English:
theorem IsSubwalk.edges_subset
  statement: {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
  proof: h.edges_isInfix.subset

中文:
定理 IsSubwalk.edges_subset
  结论: {u v u' v' : V} {p₁ : G.途径 u v} {p₂ : G.途径 u' v'}
  证明: h.edges_isInfix.subset

Depends on / 依赖: edges_isInfix, h.edges_isInfix.subset, subset
-/
theorem IsSubwalk.edges_subset {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) : p₂.edges subseteq p₁.edges :=
  h.edges_isInfix.subset

/--
theorem `IsSubwalk.darts_isInfix` / 定理 `IsSubwalk.darts_isInfix`

English:
theorem IsSubwalk.darts_isInfix
  statement: {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
  proof: by
  grind [darts_append, IsSubwalk]

@[simp]

中文:
定理 IsSubwalk.darts_isInfix
  结论: {u v u' v' : V} {p₁ : G.途径 u v} {p₂ : G.途径 u' v'}
  证明: by
  grind [darts_append, IsSubwalk]

@[simp]

Depends on / 依赖: IsSubwalk, darts_append
-/
theorem IsSubwalk.darts_isInfix {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₁.IsSubwalk p₂) : p₁.darts <:+: p₂.darts := by
  grind [darts_append, IsSubwalk]

@[simp]
/--
theorem `IsSubwalk.darts_subset` / 定理 `IsSubwalk.darts_subset`

English:
theorem IsSubwalk.darts_subset
  statement: {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
  proof: h.darts_isInfix.subset

中文:
定理 IsSubwalk.darts_subset
  结论: {u v u' v' : V} {p₁ : G.途径 u v} {p₂ : G.途径 u' v'}
  证明: h.darts_isInfix.subset

Depends on / 依赖: darts_isInfix, h.darts_isInfix.subset, subset
-/
theorem IsSubwalk.darts_subset {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) : p₂.darts subseteq p₁.darts :=
  h.darts_isInfix.subset

/--
lemma `IsSubwalk.map` / 引理 `IsSubwalk.map`

English:
lemma IsSubwalk.map
  statement: {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
  proof: by
  simp [isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp h, List.IsInfix.map]

中文:
引理 IsSubwalk.map
  结论: {u v u' v' : V} {p₁ : G.途径 u v} {p₂ : G.途径 u' v'}
  证明: by
  simp [isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp h, List.IsInfix.map]
-/
protected lemma IsSubwalk.map {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) (f : G ->g G') : (p₂.map f).IsSubwalk (p₁.map f) := by
  simp [isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp h, List.IsInfix.map]

/--
lemma `IsSubwalk.copy` / 引理 `IsSubwalk.copy`

English:
lemma IsSubwalk.copy
  statement: {u v u' v' x y x' y'} {p : G.Walk x y} {q : G.Walk u v}
  proof: by
  simp [isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp h]

中文:
引理 IsSubwalk.copy
  结论: {u v u' v' x y x' y'} {p : G.途径 x y} {q : G.途径 u v}
  证明: by
  simp [isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp h]
-/
protected lemma IsSubwalk.copy {u v u' v' x y x' y'} {p : G.Walk x y} {q : G.Walk u v}
    (h : p.IsSubwalk q) (hx : x = x') (hy : y = y') (hu : u = u') (hv : v = v') :
    (p.copy hx hy).IsSubwalk (q.copy hu hv) := by
  simp [isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp h]

/--
lemma `IsSubwalk.dropLast` / 引理 `IsSubwalk.dropLast`

English:
lemma IsSubwalk.dropLast
  statement: {u v u' v'} {p : G.Walk u v} {q : G.Walk u' v'}
  proof: (isSubwalk_take _ _).trans hpq

中文:
引理 IsSubwalk.dropLast
  结论: {u v u' v'} {p : G.途径 u v} {q : G.途径 u' v'}
  证明: (isSubwalk_take _ _).trans hpq
-/
protected lemma IsSubwalk.dropLast {u v u' v'} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) : p.dropLast.IsSubwalk q :=
  (isSubwalk_take _ _).trans hpq

/--
lemma `IsSubwalk.tail` / 引理 `IsSubwalk.tail`

English:
lemma IsSubwalk.tail
  statement: {u v u' v'} {p : G.Walk u v} {q : G.Walk u' v'}
  proof: (isSubwalk_drop _ _).trans hpq

中文:
引理 IsSubwalk.tail
  结论: {u v u' v'} {p : G.途径 u v} {q : G.途径 u' v'}
  证明: (isSubwalk_drop _ _).trans hpq
-/
protected lemma IsSubwalk.tail {u v u' v'} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) : p.tail.IsSubwalk q :=
  (isSubwalk_drop _ _).trans hpq

set_option backward.isDefEq.respectTransparency false in
/--
theorem `take_isSubwalk_take` / 定理 `take_isSubwalk_take`

English:
theorem take_isSubwalk_take
  given: {u v n k} (p : G.Walk u v) (h : n <= k)
  proof: by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
    apply ih.trans
    cases p
    · exact isSubwalk_take _ _
    · cases k
      · exact isSubwalk_of_append_left rfl
      simp [isSubwalk_iff_support_isInfix, support_take, List.IsPrefix.isInfix]

中文:
定理 take_isSubwalk_take
  条件: {u v n k} (p : G.途径 u v) (h : n <= k)
  证明: by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
    apply ih.trans
    cases p
    · exact isSubwalk_take _ _
    · cases k
      · exact isSubwalk_of_append_left rfl
      simp [isSubwalk_iff_support_isInfix, support_take, List.IsPrefix.isInfix]

Depends on / 依赖: IsPrefix, List.IsPrefix.isInfix, Nat.le_induction, ih.trans, isInfix, isSubwalk_iff_support_isInfix, isSubwalk_of_append_left, isSubwalk_take, le_induction, support_take
-/
theorem take_isSubwalk_take {u v n k} (p : G.Walk u v) (h : n <= k) :
    (p.take n).IsSubwalk (p.take k) := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
    apply ih.trans
    cases p
    · exact isSubwalk_take _ _
    · cases k
      · exact isSubwalk_of_append_left rfl
      simp [isSubwalk_iff_support_isInfix, support_take, List.IsPrefix.isInfix]

/--
theorem `drop_isSubwalk_drop` / 定理 `drop_isSubwalk_drop`

English:
theorem drop_isSubwalk_drop
  given: {u v n k} (p : G.Walk u v) (h : n <= k)
  proof: by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
    apply IsSubwalk.trans ?_ ih
    clear h ih
    induction k generalizing p u with
    | zero => exact p.drop_zero ▸ (p.isSubwalk_rfl.copy rfl rfl p.getVert_zero.symm rfl).tail
    | succ _ ih => cases p <;> simp [drop, ih]

中文:
定理 drop_isSubwalk_drop
  条件: {u v n k} (p : G.途径 u v) (h : n <= k)
  证明: by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
    apply IsSubwalk.trans ?_ ih
    clear h ih
    induction k generalizing p u with
    | zero => exact p.drop_zero ▸ (p.isSubwalk_rfl.copy rfl rfl p.getVert_zero.symm rfl).tail
    | succ _ ih => cases p <;> simp [drop, ih]

Depends on / 依赖: IsSubwalk, IsSubwalk.trans, Nat.le_induction, drop_zero, generalizing, getVert_zero, isSubwalk_rfl, le_induction, p.drop_zero, p.getVert_zero.symm, p.isSubwalk_rfl.copy
-/
theorem drop_isSubwalk_drop {u v n k} (p : G.Walk u v) (h : n <= k) :
    (p.drop k).IsSubwalk (p.drop n) := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
    apply IsSubwalk.trans ?_ ih
    clear h ih
    induction k generalizing p u with
    | zero => exact p.drop_zero ▸ (p.isSubwalk_rfl.copy rfl rfl p.getVert_zero.symm rfl).tail
    | succ _ ih => cases p <;> simp [drop, ih]

end Walk

end SimpleGraph
