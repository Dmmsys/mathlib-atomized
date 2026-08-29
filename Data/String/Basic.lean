/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Data.String.Lemmas
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Char
public import Mathlib.Algebra.Order.Group.Nat
import all Init.Data.String.Iterator -- for unfolding `Iterator.curr`
import all Init.Data.Ord.String -- for unfolding `String.compare`

/-!
# Strings

Supplementary theorems about the `String` type.
-/

@[expose] public section

namespace String

/--
Definition of `ltb` / `ltb` 的定义

English:
definition ltb
  signature: (s₁ s₂ : Legacy.Iterator)
  body: if s₂.hasNext then
    if s₁.hasNext then
      if s₁.curr = s₂.curr then
        ltb s₁.next s₂.next
      else s₁.curr < s₂.curr
    else true
  else false

中文:
定义 ltb
  签名: (s₁ s₂ : Legacy.Iterator)
  定义体: if s₂.hasNext then
    if s₁.hasNext then
      if s₁.curr = s₂.curr then
        ltb s₁.next s₂.next
      else s₁.curr < s₂.curr
    else true
  else false

Depends on / 依赖: hasNext
-/
def ltb (s₁ s₂ : Legacy.Iterator) : Bool :=
  if s₂.hasNext then
    if s₁.hasNext then
      if s₁.curr = s₂.curr then
        ltb s₁.next s₂.next
      else s₁.curr < s₂.curr
    else true
  else false

/--
Definition of `ltb.inductionOn.` / `ltb.inductionOn.` 的定义

English:
definition ltb.inductionOn.{u}
  signature: {motive : Legacy.Iterator -> Legacy.Iterator -> Sort u}
  body: if h₂ : it₂.hasNext then
    if h₁ : it₁.hasNext then
      if heq : it₁.curr = it₂.curr then
        ind it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq (inductionOn it₁.next it₂.next ind eq base₁ base₂)
      else eq it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq
    else base₁ it₁.s it₂.s it₁.i it₂.i h₂ h₁
  else base₂ it₁

中文:
定义 ltb.inductionOn.{u}
  签名: {motive : Legacy.Iterator -> Legacy.Iterator -> 类型层 u}
  定义体: if h₂ : it₂.hasNext then
    if h₁ : it₁.hasNext then
      if heq : it₁.curr = it₂.curr then
        ind it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq (inductionOn it₁.next it₂.next ind eq base₁ base₂)
      else eq it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq
    else base₁ it₁.s it₂.s it₁.i it₂.i h₂ h₁
  else base₂ it₁
-/
@[no_expose] def ltb.inductionOn.{u} {motive : Legacy.Iterator -> Legacy.Iterator -> Sort u}
    (it₁ it₂ : Legacy.Iterator)
    (ind : forall s₁ s₂ i₁ i₂, Legacy.Iterator.hasNext ⟨s₂, i₂⟩ -> Legacy.Iterator.hasNext ⟨s₁, i₁⟩ ->
      i₁.get s₁ = i₂.get s₂ ->
        motive (Legacy.Iterator.next ⟨s₁, i₁⟩) (Legacy.Iterator.next ⟨s₂, i₂⟩) ->
          motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (eq : forall s₁ s₂ i₁ i₂, Legacy.Iterator.hasNext ⟨s₂, i₂⟩ -> Legacy.Iterator.hasNext ⟨s₁, i₁⟩ ->
      ¬ i₁.get s₁ = i₂.get s₂ -> motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (base₁ : forall s₁ s₂ i₁ i₂, Legacy.Iterator.hasNext ⟨s₂, i₂⟩ -> ¬ Legacy.Iterator.hasNext ⟨s₁, i₁⟩ ->
      motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (base₂ : forall s₁ s₂ i₁ i₂, ¬ Legacy.Iterator.hasNext ⟨s₂, i₂⟩ -> motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩) :
    motive it₁ it₂ :=
  if h₂ : it₂.hasNext then
    if h₁ : it₁.hasNext then
      if heq : it₁.curr = it₂.curr then
        ind it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq (inductionOn it₁.next it₂.next ind eq base₁ base₂)
      else eq it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq
    else base₁ it₁.s it₂.s it₁.i it₂.i h₂ h₁
  else base₂ it₁.s it₂.s it₁.i it₂.i h₂

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ltb_cons_addChar'` / 定理 `ltb_cons_addChar'`

English:
theorem ltb_cons_addChar'
  given: (c : Char) (s₁ s₂ : Legacy.Iterator)
  proof: by
  fun_induction ltb s₁ s₂ with
  | case1 s₁ s₂ h₁ h₂ h ih =>
    rw [ltb]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [if_pos (by simpa using h₁)]; rw [if_pos (by simpa using h₂)]; rw [if_pos]; rw [← ih]
    · simp only [Legacy.Iterator.next, Pos.Raw.

中文:
定理 ltb_cons_addChar'
  条件: (c : Char) (s₁ s₂ : Legacy.Iterator)
  证明: by
  fun_induction ltb s₁ s₂ with
  | case1 s₁ s₂ h₁ h₂ h ih =>
    rw [ltb]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [if_pos (by simpa using h₁)]; rw [if_pos (by simpa using h₂)]; rw [if_pos]; rw [← ih]
    · simp only [Legacy.Iterator.next, Pos.Raw.

Depends on / 依赖: Iterator, Legacy, Legacy.Iter, Legacy.Iterator.curr, Legacy.Iterator.hasNext_cons_addChar, Legacy.Iterator.next, Pos.Raw.add_char_right_comm, Pos.Raw.next, add_char_right_comm, fun_induction, get_cons_addChar, hasNext_cons_addChar, if_pos, ofList_toList
-/
theorem ltb_cons_addChar' (c : Char) (s₁ s₂ : Legacy.Iterator) :
    ltb ⟨ofList (c :: s₁.s.toList), s₁.i + c⟩ ⟨ofList (c :: s₂.s.toList), s₂.i + c⟩ =
      ltb s₁ s₂ := by
  fun_induction ltb s₁ s₂ with
  | case1 s₁ s₂ h₁ h₂ h ih =>
    rw [ltb]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [if_pos (by simpa using h₁)]; rw [if_pos (by simpa using h₂)]; rw [if_pos]; rw [← ih]
    · simp only [Legacy.Iterator.next, Pos.Raw.next, get_cons_addChar, ofList_toList]
      congr 2 <;> apply Pos.Raw.add_char_right_comm
    · simpa only [Legacy.Iterator.curr, get_cons_addChar, ofList_toList] using h
  | case2 s₁ s₂ h₁ h₂ h =>
    rw [ltb]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [if_pos (by simpa using h₁)]; rw [if_pos (by simpa using h₂)]; rw [if_neg]
    · simp only [Legacy.Iterator.curr, get_cons_addChar, ofList_toList]
    · simpa only [Legacy.Iterator.curr, get_cons_addChar, ofList_toList] using h
  | case3 s₁ s₂ h₁ h₂ =>
    rw [ltb]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [if_pos (by simpa using h₁)]; rw [if_neg (by simpa using h₂)]
  | case4 s₁ s₂ h₁ =>
    rw [ltb]; rw [Legacy.Iterator.hasNext_cons_addChar]; rw [if_neg (by simpa using h₁)]

/--
theorem `ltb_cons_addChar` / 定理 `ltb_cons_addChar`

English:
theorem ltb_cons_addChar
  given: (c : Char) (cs₁ cs₂ : List Char) (i₁ i₂ : Pos.Raw)
  proof: by
  rw [eq_comm]; rw [← ltb_cons_addChar' c]
  simp

中文:
定理 ltb_cons_addChar
  条件: (c : Char) (cs₁ cs₂ : 列表 Char) (i₁ i₂ : Pos.Raw)
  证明: by
  rw [eq_comm]; rw [← ltb_cons_addChar' c]
  simp

Depends on / 依赖: eq_comm, ltb_cons_addChar
-/
theorem ltb_cons_addChar (c : Char) (cs₁ cs₂ : List Char) (i₁ i₂ : Pos.Raw) :
    ltb ⟨ofList (c :: cs₁), i₁ + c⟩ ⟨ofList (c :: cs₂), i₂ + c⟩ =
      ltb ⟨ofList cs₁, i₁⟩ ⟨ofList cs₂, i₂⟩ := by
  rw [eq_comm]; rw [← ltb_cons_addChar' c]
  simp

/--
theorem `lt_iff_toList_lt` / 定理 `lt_iff_toList_lt`

English:
theorem lt_iff_toList_lt
  given: {s₁ s₂ : String}
  statement: s₁ < s₂ ↔ s₁.toList < s₂.toList
  proof: Iff.rfl

@[simp]

中文:
定理 lt_iff_toList_lt
  条件: {s₁ s₂ : String}
  结论: s₁ < s₂ ↔ s₁.toList < s₂.toList
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem lt_iff_toList_lt {s₁ s₂ : String} : s₁ < s₂ ↔ s₁.toList < s₂.toList :=
  Iff.rfl

@[simp]
/--
theorem `lt_iff_ltb` / 定理 `lt_iff_ltb`

English:
theorem lt_iff_ltb
  given: {s₁ s₂ : String}
  proof: by
  rw [Iff.comm]
  obtain ⟨s₁, rfl⟩ := s₁.exists_eq_ofList
  obtain ⟨s₂, rfl⟩ := s₂.exists_eq_ofList
  simp only [lt_iff_toList_lt, String.Legacy.iter, String.Legacy.mkIterator, String.toList_ofList]
  induction s₁ generalizing s₂ <;> cases s₂
  · unfold ltb; decide
  · rename_i c₂ cs₂; apply iff_

中文:
定理 lt_iff_ltb
  条件: {s₁ s₂ : String}
  证明: by
  rw [Iff.comm]
  obtain ⟨s₁, rfl⟩ := s₁.exists_eq_ofList
  obtain ⟨s₂, rfl⟩ := s₂.exists_eq_ofList
  simp only [lt_iff_toList_lt, String.Legacy.iter, String.Legacy.mkIterator, String.toList_ofList]
  induction s₁ generalizing s₂ <;> cases s₂
  · unfold ltb; decide
  · rename_i c₂ cs₂; apply iff_

Depends on / 依赖: Char.utf8Size_pos, Iff.comm, Iterator, Legacy, Legacy.Iterator.hasNext, List.nil_lt_cons, String.Legacy.iter, String.Legacy.mkIterator, String.toList_ofList, exists_eq_ofList, generalizing, hasNext, iff_of_false, iff_of_true, lt_iff_toList_lt, mkIterator, nil_lt_cons, not_lt_of_gt, rename_i, toList_ofList
-/
theorem lt_iff_ltb {s₁ s₂ : String} :
    s₁ < s₂ ↔ ltb (String.Legacy.iter s₁) (String.Legacy.iter s₂) := by
  rw [Iff.comm]
  obtain ⟨s₁, rfl⟩ := s₁.exists_eq_ofList
  obtain ⟨s₂, rfl⟩ := s₂.exists_eq_ofList
  simp only [lt_iff_toList_lt, String.Legacy.iter, String.Legacy.mkIterator, String.toList_ofList]
  induction s₁ generalizing s₂ <;> cases s₂
  · unfold ltb; decide
  · rename_i c₂ cs₂; apply iff_of_true
    · unfold ltb
      simp [Legacy.Iterator.hasNext, Char.utf8Size_pos]
    · apply List.nil_lt_cons
  · rename_i c₁ cs₁ ih; apply iff_of_false
    · unfold ltb
      simp [Legacy.Iterator.hasNext]
    · apply not_lt_of_gt; apply List.nil_lt_cons
  · rename_i c₁ cs₁ ih c₂ cs₂; unfold ltb
    simp only [Legacy.Iterator.hasNext, Pos.Raw.byteIdx_zero, rawEndPos_ofList, utf8Len_cons,
      add_pos_iff, Char.utf8Size_pos, or_true, decide_true, ↓reduceIte, Legacy.Iterator.curr,
      Pos.Raw.get, String.toList_ofList, Pos.Raw.utf8GetAux, Legacy.Iterator.next, Pos.Raw.next,
      Bool.ite_eq_true_distrib, decide_eq_true_eq]
    split_ifs with h
    · subst c₂
      suffices ltb ⟨ofList (c₁ :: cs₁), (0 : Pos.Raw) + c₁⟩
          ⟨ofList (c₁ :: cs₂), (0 : Pos.Raw) + c₁⟩ =
            ltb ⟨ofList cs₁, 0⟩ ⟨ofList cs₂, 0⟩ by
        rw [this]; exact (ih cs₂).trans List.lex_cons_iff.symm
      apply ltb_cons_addChar
    · refine ⟨List.Lex.rel, fun e => ?_⟩
      cases e <;> rename_i h'
      · assumption
      · contradiction

@[deprecated "Use the new String API" (since := "2026-04-01")]
/--
theorem `toList_nonempty` / 定理 `toList_nonempty`

English:
theorem toList_nonempty
  proof: s.exists_eq_ofList
    match l with
    | [] => simp at h
    | c::cs => simp [Legacy.front, Pos.Raw.get, Pos.Raw.utf8GetAux]

@[simp]

中文:
定理 toList_nonempty
  证明: s.exists_eq_ofList
    match l with
    | [] => simp at h
    | c::cs => simp [Legacy.front, Pos.Raw.get, Pos.Raw.utf8GetAux]

@[simp]

Depends on / 依赖: exists_eq_ofList, s.exists_eq_ofList
-/
theorem toList_nonempty :
    forall {s : String}, s != "" -> s.toList = String.Legacy.front s :: (String.Legacy.drop s 1).toList
  | s, h => by
    obtain ⟨l, rfl⟩ := s.exists_eq_ofList
    match l with
    | [] => simp at h
    | c::cs => simp [Legacy.front, Pos.Raw.get, Pos.Raw.utf8GetAux]

@[simp]
/--
theorem `head_empty` / 定理 `head_empty`

English:
theorem head_empty
  statement: "".toList.head! = default
  proof: rfl

中文:
定理 head_empty
  结论: "".toList.head! = default
  证明: rfl
-/
theorem head_empty : "".toList.head! = default :=
  rfl

/--
theorem `le_iff_not_lt` / 定理 `le_iff_not_lt`

English:
theorem le_iff_not_lt
  given: {s₁ s₂ : String}
  statement: s₁ <= s₂ ↔ ¬ s₂ < s₁
  proof: Iff.rfl

中文:
定理 le_iff_not_lt
  条件: {s₁ s₂ : String}
  结论: s₁ <= s₂ ↔ ¬ s₂ < s₁
  证明: Iff.rfl
-/
private theorem le_iff_not_lt {s₁ s₂ : String} : s₁ <= s₂ ↔ ¬ s₂ < s₁ :=
  Iff.rfl

/--
theorem `le_iff_toList_le` / 定理 `le_iff_toList_le`

English:
theorem le_iff_toList_le
  given: {s₁ s₂ : String}
  statement: s₁ <= s₂ ↔ s₁.toList <= s₂.toList
  proof: by
  rw [String.le_iff_not_lt]; rw [lt_iff_toList_lt]; rw [not_lt]

中文:
定理 le_iff_toList_le
  条件: {s₁ s₂ : String}
  结论: s₁ <= s₂ ↔ s₁.toList <= s₂.toList
  证明: by
  rw [String.le_iff_not_lt]; rw [lt_iff_toList_lt]; rw [not_lt]

Depends on / 依赖: String.le_iff_not_lt, le_iff_not_lt, lt_iff_toList_lt, not_lt
-/
theorem le_iff_toList_le {s₁ s₂ : String} : s₁ <= s₂ ↔ s₁.toList <= s₂.toList := by
  rw [String.le_iff_not_lt]; rw [lt_iff_toList_lt]; rw [not_lt]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder String
  body: le_iff_toList_le.mpr le_rfl
  le_trans a b c := by
    simp only [le_iff_toList_le]
    apply le_trans
  lt_iff_le_not_ge a b := by
    simp only [lt_iff_toList_lt, le_iff_toList_le, lt_iff_le_not_ge]
  le_antisymm a b := by
    simp only [le_iff_toList_le, ← toList_inj]
    apply le_antisymm
  le_t

中文:
实例 :
  签名: 线性序 String
  定义体: le_iff_toList_le.mpr le_rfl
  le_trans a b c := by
    simp only [le_iff_toList_le]
    apply le_trans
  lt_iff_le_not_ge a b := by
    simp only [lt_iff_toList_lt, le_iff_toList_le, lt_iff_le_not_ge]
  le_antisymm a b := by
    simp only [le_iff_toList_le, ← toList_inj]
    apply le_antisymm
  le_t

Depends on / 依赖: le_iff_toList_le, le_iff_toList_le.mpr, le_rfl
-/
instance : LinearOrder String where
  le_refl _ := le_iff_toList_le.mpr le_rfl
  le_trans a b c := by
    simp only [le_iff_toList_le]
    apply le_trans
  lt_iff_le_not_ge a b := by
    simp only [lt_iff_toList_lt, le_iff_toList_le, lt_iff_le_not_ge]
  le_antisymm a b := by
    simp only [le_iff_toList_le, ← toList_inj]
    apply le_antisymm
  le_total a b := by
    simp only [le_iff_toList_le]
    apply le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := String.decidableLT
  compare_eq_compareOfLessAndEq a b := by simp [Ord.compare, String.compare]

/--
theorem `ofList_eq` / 定理 `ofList_eq`

English:
theorem ofList_eq
  given: {l : List Char} {s : String}
  statement: ofList l = s ↔ l = s.toList
  proof: by
  simp [← toList_inj]

中文:
定理 ofList_eq
  条件: {l : 列表 Char} {s : String}
  结论: ofList l = s ↔ l = s.toList
  证明: by
  simp [← toList_inj]

Depends on / 依赖: toList_inj
-/
theorem ofList_eq {l : List Char} {s : String} : ofList l = s ↔ l = s.toList := by
  simp [← toList_inj]

end String
