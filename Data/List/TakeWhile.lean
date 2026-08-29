/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Set

/-! ### List.takeWhile and List.dropWhile -/

public section

namespace List

variable {α : Type*} (p : α -> Bool)

/--
theorem `dropWhile_get_zero_not` / 定理 `dropWhile_get_zero_not`

English:
theorem dropWhile_get_zero_not
  given: (l : List α) (hl : 0 < (l.dropWhile p).length)
  proof: by
  induction l with
  | nil => cases hl
  | cons hd tl IH =>
    simp only [dropWhile]
    by_cases hp : p hd
    · simp_all only [get_eq_getElem]
      apply IH
      simp_all only [dropWhile_cons_of_pos]
    · simp [hp]

中文:
定理 dropWhile_get_zero_not
  条件: (l : 列表 α) (hl : 0 < (l.dropWhile p).length)
  证明: by
  induction l with
  | nil => cases hl
  | cons hd tl IH =>
    simp only [dropWhile]
    by_cases hp : p hd
    · simp_all only [get_eq_getElem]
      apply IH
      simp_all only [dropWhile_cons_of_pos]
    · simp [hp]

Depends on / 依赖: dropWhile, dropWhile_cons_of_pos, get_eq_getElem
-/
theorem dropWhile_get_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) :
    ¬p ((l.dropWhile p).get ⟨0, hl⟩) := by
  induction l with
  | nil => cases hl
  | cons hd tl IH =>
    simp only [dropWhile]
    by_cases hp : p hd
    · simp_all only [get_eq_getElem]
      apply IH
      simp_all only [dropWhile_cons_of_pos]
    · simp [hp]

/--
theorem `length_dropWhile_le` / 定理 `length_dropWhile_le`

English:
theorem length_dropWhile_le
  given: (l : List α)
  statement: (dropWhile p l).length <= l.length
  proof: by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [dropWhile, length_cons]
    split
    · lia
    · simp

中文:
定理 length_dropWhile_le
  条件: (l : 列表 α)
  结论: (dropWhile p l).length <= l.length
  证明: by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [dropWhile, length_cons]
    split
    · lia
    · simp

Depends on / 依赖: dropWhile, length_cons
-/
theorem length_dropWhile_le (l : List α) : (dropWhile p l).length <= l.length := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [dropWhile, length_cons]
    split
    · lia
    · simp

variable {p} {l : List α}

@[simp]
/--
theorem `dropWhile_eq_nil_iff` / 定理 `dropWhile_eq_nil_iff`

English:
theorem dropWhile_eq_nil_iff
  statement: dropWhile p l = [] ↔ forall x in l, p x
  proof: by
  induction l with
  | nil => simp [dropWhile]
  | cons x xs IH => by_cases hp : p x <;> simp [hp, IH]

@[simp]

中文:
定理 dropWhile_eq_nil_iff
  结论: dropWhile p l = [] ↔ 对任意 x in l, p x
  证明: by
  induction l with
  | nil => simp [dropWhile]
  | cons x xs IH => by_cases hp : p x <;> simp [hp, IH]

@[simp]

Depends on / 依赖: dropWhile
-/
theorem dropWhile_eq_nil_iff : dropWhile p l = [] ↔ forall x in l, p x := by
  induction l with
  | nil => simp [dropWhile]
  | cons x xs IH => by_cases hp : p x <;> simp [hp, IH]

@[simp]
/--
theorem `dropWhile_eq_self_iff` / 定理 `dropWhile_eq_self_iff`

English:
theorem dropWhile_eq_self_iff
  statement: dropWhile p l = l ↔ forall hl : 0 < l.length, ¬p (l[0]'hl)
  proof: by
  rcases l with - | ⟨hd, tl⟩
  · simp
  · rw [dropWhile]
    by_cases h_p_hd : p hd
    · simp only [h_p_hd, length_cons, Nat.zero_lt_succ, getElem_cons_zero, not_true_eq_false,
        imp_false, iff_false]
      intro h
      replace h := congrArg length h
      have := length_dropWhile_le p tl

中文:
定理 dropWhile_eq_self_iff
  结论: dropWhile p l = l ↔ 对任意 hl : 0 < l.length, ¬p (l[0]'hl)
  证明: by
  rcases l with - | ⟨hd, tl⟩
  · simp
  · rw [dropWhile]
    by_cases h_p_hd : p hd
    · simp only [h_p_hd, length_cons, Nat.zero_lt_succ, getElem_cons_zero, not_true_eq_false,
        imp_false, iff_false]
      intro h
      replace h := congrArg length h
      have := length_dropWhile_le p tl

Depends on / 依赖: Nat.zero_lt_succ, dropWhile, getElem_cons_zero, h_p_hd, iff_false, imp_false, length, length_cons, length_dropWhile_le, not_true_eq_false, replace, zero_lt_succ
-/
theorem dropWhile_eq_self_iff : dropWhile p l = l ↔ forall hl : 0 < l.length, ¬p (l[0]'hl) := by
  rcases l with - | ⟨hd, tl⟩
  · simp
  · rw [dropWhile]
    by_cases h_p_hd : p hd
    · simp only [h_p_hd, length_cons, Nat.zero_lt_succ, getElem_cons_zero, not_true_eq_false,
        imp_false, iff_false]
      intro h
      replace h := congrArg length h
      have := length_dropWhile_le p tl
      simp at h
      lia
    · simp [h_p_hd]

@[simp]
/--
theorem `takeWhile_eq_self_iff` / 定理 `takeWhile_eq_self_iff`

English:
theorem takeWhile_eq_self_iff
  statement: takeWhile p l = l ↔ forall x in l, p x
  proof: by
  induction l with
  | nil => simp
  | cons x xs IH => by_cases hp : p x <;> simp [hp, IH]

@[simp]

中文:
定理 takeWhile_eq_self_iff
  结论: takeWhile p l = l ↔ 对任意 x in l, p x
  证明: by
  induction l with
  | nil => simp
  | cons x xs IH => by_cases hp : p x <;> simp [hp, IH]

@[simp]
-/
theorem takeWhile_eq_self_iff : takeWhile p l = l ↔ forall x in l, p x := by
  induction l with
  | nil => simp
  | cons x xs IH => by_cases hp : p x <;> simp [hp, IH]

@[simp]
/--
theorem `takeWhile_eq_nil_iff` / 定理 `takeWhile_eq_nil_iff`

English:
theorem takeWhile_eq_nil_iff
  statement: takeWhile p l = [] ↔ forall hl : 0 < l.length, ¬p (l.get ⟨0, hl⟩)
  proof: by
  induction l with
  | nil =>
    simp only [takeWhile_nil, Bool.not_eq_true, true_iff]
    intro h
    simp at h
  | cons x xs IH => by_cases hp : p x <;> simp [hp]

中文:
定理 takeWhile_eq_nil_iff
  结论: takeWhile p l = [] ↔ 对任意 hl : 0 < l.length, ¬p (l.get ⟨0, hl⟩)
  证明: by
  induction l with
  | nil =>
    simp only [takeWhile_nil, Bool.not_eq_true, true_iff]
    intro h
    simp at h
  | cons x xs IH => by_cases hp : p x <;> simp [hp]

Depends on / 依赖: Bool.not_eq_true, not_eq_true, takeWhile_nil, true_iff
-/
theorem takeWhile_eq_nil_iff : takeWhile p l = [] ↔ forall hl : 0 < l.length, ¬p (l.get ⟨0, hl⟩) := by
  induction l with
  | nil =>
    simp only [takeWhile_nil, Bool.not_eq_true, true_iff]
    intro h
    simp at h
  | cons x xs IH => by_cases hp : p x <;> simp [hp]

/--
theorem `mem_takeWhile_imp` / 定理 `mem_takeWhile_imp`

English:
theorem mem_takeWhile_imp
  given: {x : α} (hx : x in takeWhile p l)
  statement: p x
  proof: by
  induction l with simp [takeWhile] at hx
  | cons hd tl IH =>
    cases hp : p hd
    · simp [hp] at hx
    · rw [hp, mem_cons] at hx
      rcases hx with (rfl | hx)
      · exact hp
      · exact IH hx

中文:
定理 mem_takeWhile_imp
  条件: {x : α} (hx : x in takeWhile p l)
  结论: p x
  证明: by
  induction l with simp [takeWhile] at hx
  | cons hd tl IH =>
    cases hp : p hd
    · simp [hp] at hx
    · rw [hp, mem_cons] at hx
      rcases hx with (rfl | hx)
      · exact hp
      · exact IH hx

Depends on / 依赖: mem_cons, takeWhile
-/
theorem mem_takeWhile_imp {x : α} (hx : x in takeWhile p l) : p x := by
  induction l with simp [takeWhile] at hx
  | cons hd tl IH =>
    cases hp : p hd
    · simp [hp] at hx
    · rw [hp, mem_cons] at hx
      rcases hx with (rfl | hx)
      · exact hp
      · exact IH hx

/--
theorem `takeWhile_takeWhile` / 定理 `takeWhile_takeWhile`

English:
theorem takeWhile_takeWhile
  given: (p q : α -> Bool) (l : List α)
  proof: by
  induction l with
  | nil => simp
  | cons hd tl IH => by_cases hp : p hd <;> by_cases hq : q hd <;> simp [takeWhile, hp, hq, IH]

中文:
定理 takeWhile_takeWhile
  条件: (p q : α -> 布尔值) (l : 列表 α)
  证明: by
  induction l with
  | nil => simp
  | cons hd tl IH => by_cases hp : p hd <;> by_cases hq : q hd <;> simp [takeWhile, hp, hq, IH]

Depends on / 依赖: takeWhile
-/
theorem takeWhile_takeWhile (p q : α -> Bool) (l : List α) :
    takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l := by
  induction l with
  | nil => simp
  | cons hd tl IH => by_cases hp : p hd <;> by_cases hq : q hd <;> simp [takeWhile, hp, hq, IH]

/--
theorem `takeWhile_idem` / 定理 `takeWhile_idem`

English:
theorem takeWhile_idem
  statement: takeWhile p (takeWhile p l) = takeWhile p l
  proof: by
  simp_rw [takeWhile_takeWhile, and_self_iff, Bool.decide_coe]

中文:
定理 takeWhile_idem
  结论: takeWhile p (takeWhile p l) = takeWhile p l
  证明: by
  simp_rw [takeWhile_takeWhile, and_self_iff, Bool.decide_coe]

Depends on / 依赖: Bool.decide_coe, and_self_iff, decide_coe, simp_rw, takeWhile_takeWhile
-/
theorem takeWhile_idem : takeWhile p (takeWhile p l) = takeWhile p l := by
  simp_rw [takeWhile_takeWhile, and_self_iff, Bool.decide_coe]

variable (p) (l)

/--
lemma `find?_eq_head?_dropWhile_not` / 引理 `find?_eq_head?_dropWhile_not`

English:
lemma find?_eq_head?_dropWhile_not
  proof: by
  induction l
  case nil => simp
  case cons head tail hi =>
    set ph := p head with phh
    rcases ph with rfl | rfl
    · have phh' : ¬(p head = true) := by simp [phh.symm]
      rw [find?_cons_of_neg phh']; rw [dropWhile_cons_of_pos]
      · exact hi
      · simpa using phh
    · rw [find?_c

中文:
引理 find?_eq_head?_dropWhile_not
  证明: by
  induction l
  case nil => simp
  case cons head tail hi =>
    set ph := p head with phh
    rcases ph with rfl | rfl
    · have phh' : ¬(p head = true) := by simp [phh.symm]
      rw [find?_cons_of_neg phh']; rw [dropWhile_cons_of_pos]
      · exact hi
      · simpa using phh
    · rw [find?_c
-/
lemma find?_eq_head?_dropWhile_not :
    l.find? p = (l.dropWhile (fun x => !(p x))).head? := by
  induction l
  case nil => simp
  case cons head tail hi =>
    set ph := p head with phh
    rcases ph with rfl | rfl
    · have phh' : ¬(p head = true) := by simp [phh.symm]
      rw [find?_cons_of_neg phh']; rw [dropWhile_cons_of_pos]
      · exact hi
      · simpa using phh
    · rw [find?_cons_of_pos phh.symm, dropWhile_cons_of_neg]
      · simp
      · simpa using phh

/--
lemma `find?_not_eq_head?_dropWhile` / 引理 `find?_not_eq_head?_dropWhile`

English:
lemma find?_not_eq_head?_dropWhile
  proof: by
  convert! l.find?_eq_head?_dropWhile_not ?_
  simp

中文:
引理 find?_not_eq_head?_dropWhile
  证明: by
  convert! l.find?_eq_head?_dropWhile_not ?_
  simp
-/
lemma find?_not_eq_head?_dropWhile :
    l.find? (fun x => !(p x)) = (l.dropWhile p).head? := by
  convert! l.find?_eq_head?_dropWhile_not ?_
  simp

variable {p} {l}

/--
lemma `find?_eq_head_dropWhile_not` / 引理 `find?_eq_head_dropWhile_not`

English:
lemma find?_eq_head_dropWhile_not
  given: (h : exists x in l, p x)
  proof: by
  rw [l.find?_eq_head?_dropWhile_not p]; rw [← head_eq_iff_head?_eq_some]

中文:
引理 find?_eq_head_dropWhile_not
  条件: (h : 存在 x in l, p x)
  证明: by
  rw [l.find?_eq_head?_dropWhile_not p]; rw [← head_eq_iff_head?_eq_some]
-/
lemma find?_eq_head_dropWhile_not (h : exists x in l, p x) :
    l.find? p = some ((l.dropWhile (fun x => !(p x))).head (by simpa using h)) := by
  rw [l.find?_eq_head?_dropWhile_not p]; rw [← head_eq_iff_head?_eq_some]

/--
lemma `find?_not_eq_head_dropWhile` / 引理 `find?_not_eq_head_dropWhile`

English:
lemma find?_not_eq_head_dropWhile
  given: (h : exists x in l, ¬p x)
  proof: by
  convert! l.find?_eq_head_dropWhile_not ?_
  · simp
  · simpa using h

中文:
引理 find?_not_eq_head_dropWhile
  条件: (h : 存在 x in l, ¬p x)
  证明: by
  convert! l.find?_eq_head_dropWhile_not ?_
  · simp
  · simpa using h
-/
lemma find?_not_eq_head_dropWhile (h : exists x in l, ¬p x) :
    l.find? (fun x => !(p x)) = some ((l.dropWhile p).head (by simpa using h)) := by
  convert! l.find?_eq_head_dropWhile_not ?_
  · simp
  · simpa using h

end List
