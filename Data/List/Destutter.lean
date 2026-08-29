/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Eric Wieser
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Dedup

/-!
# Destuttering of Lists

This file proves theorems about `List.destutter` (in `Data.List.Defs`), which greedily removes all
non-related items that are adjacent in a list, e.g. `[2, 2, 3, 3, 2].destutter (≠) = [2, 3, 2]`.
Note that we make no guarantees of being the longest sublist with this property; e.g.,
`[123, 1, 2, 5, 543, 1000].destutter (<) = [123, 543, 1000]`, but a longer ascending chain could be
`[1, 2, 5, 543, 1000]`.

## Main statements

* `List.destutter_sublist`: `l.destutter` is a sublist of `l`.
* `List.isChain_destutter'`: `l.destutter` satisfies `IsChain R`.
* Analogies of these theorems for `List.destutter'`, which is the `destutter` equivalent of `Chain`.

## Tags

adjacent, chain, duplicates, remove, list, stutter, destutter
-/

public section

open Function

variable {α β : Type*} (l l₁ l₂ : List α) (R : α -> α -> Prop) [DecidableRel R] {a b : α}

variable {R₂ : β -> β -> Prop} [DecidableRel R₂]

namespace List

@[simp]
/--
theorem `destutter'_nil` / 定理 `destutter'_nil`

English:
theorem destutter'_nil
  statement: destutter' R a [] = [a]
  proof: rfl

中文:
定理 destutter'_nil
  结论: destutter' R a [] = [a]
  证明: rfl
-/
theorem destutter'_nil : destutter' R a [] = [a] :=
  rfl

/--
theorem `destutter'_cons` / 定理 `destutter'_cons`

English:
theorem destutter'_cons
  proof: rfl

中文:
定理 destutter'_cons
  证明: rfl
-/
theorem destutter'_cons :
    (b :: l).destutter' R a = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl

variable {R}

@[simp]
/--
theorem `destutter'_cons_pos` / 定理 `destutter'_cons_pos`

English:
theorem destutter'_cons_pos
  given: (h : R b a)
  statement: (a :: l).destutter' R b = b :: l.destutter' R a
  proof: by
  rw [destutter']; rw [if_pos h]

@[simp]

中文:
定理 destutter'_cons_pos
  条件: (h : R b a)
  结论: (a :: l).destutter' R b = b :: l.destutter' R a
  证明: by
  rw [destutter']; rw [if_pos h]

@[simp]
-/
theorem destutter'_cons_pos (h : R b a) : (a :: l).destutter' R b = b :: l.destutter' R a := by
  rw [destutter']; rw [if_pos h]

@[simp]
/--
theorem `destutter'_cons_neg` / 定理 `destutter'_cons_neg`

English:
theorem destutter'_cons_neg
  given: (h : ¬R b a)
  statement: (a :: l).destutter' R b = l.destutter' R b
  proof: by
  rw [destutter']; rw [if_neg h]

中文:
定理 destutter'_cons_neg
  条件: (h : ¬R b a)
  结论: (a :: l).destutter' R b = l.destutter' R b
  证明: by
  rw [destutter']; rw [if_neg h]
-/
theorem destutter'_cons_neg (h : ¬R b a) : (a :: l).destutter' R b = l.destutter' R b := by
  rw [destutter']; rw [if_neg h]

variable (R)

@[simp]
/--
theorem `destutter'_singleton` / 定理 `destutter'_singleton`

English:
theorem destutter'_singleton
  statement: [b].destutter' R a = if R a b then [a, b] else [a]
  proof: by
  split_ifs with h <;> simp! [h]

中文:
定理 destutter'_singleton
  结论: [b].destutter' R a = if R a b then [a, b] else [a]
  证明: by
  split_ifs with h <;> simp! [h]
-/
theorem destutter'_singleton : [b].destutter' R a = if R a b then [a, b] else [a] := by
  split_ifs with h <;> simp! [h]

/--
theorem `destutter'_sublist` / 定理 `destutter'_sublist`

English:
theorem destutter'_sublist
  given: (a)
  statement: l.destutter' R a <+ a :: l
  proof: by
  induction l generalizing a with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs
    · exact Sublist.cons_cons a (hl b)
    · exact (hl a).trans ((l.sublist_cons_self b).cons_cons a)

中文:
定理 destutter'_sublist
  条件: (a)
  结论: l.destutter' R a <+ a :: l
  证明: by
  induction l generalizing a with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs
    · exact Sublist.cons_cons a (hl b)
    · exact (hl a).trans ((l.sublist_cons_self b).cons_cons a)
-/
theorem destutter'_sublist (a) : l.destutter' R a <+ a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs
    · exact Sublist.cons_cons a (hl b)
    · exact (hl a).trans ((l.sublist_cons_self b).cons_cons a)

/--
theorem `mem_destutter'` / 定理 `mem_destutter'`

English:
theorem mem_destutter'
  given: (a)
  statement: a in l.destutter' R a
  proof: by
  induction l with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs
    · simp
    · assumption

中文:
定理 mem_destutter'
  条件: (a)
  结论: a in l.destutter' R a
  证明: by
  induction l with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs
    · simp
    · assumption

Depends on / 依赖: destutter, split_ifs
-/
theorem mem_destutter' (a) : a in l.destutter' R a := by
  induction l with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs
    · simp
    · assumption

/--
theorem `isChain_destutter'` / 定理 `isChain_destutter'`

English:
theorem isChain_destutter'
  given: (l : List α) (a : α)
  statement: (l.destutter' R a).IsChain R
  proof: by
  induction l using twoStepInduction generalizing a with
  | nil => simp
  | singleton => simp [apply_ite]
  | cons_cons b c l IH IH2 =>
    simp_rw [destutter'_cons, apply_ite (IsChain R ·), IH, if_true_right] at IH2
    simp_rw [destutter'_cons, apply_ite (IsChain R ·),
      apply_ite (IsChain

中文:
定理 isChain_destutter'
  条件: (l : List α) (a : α)
  结论: (l.destutter' R a).IsChain R
  证明: by
  induction l using twoStepInduction generalizing a with
  | nil => simp
  | singleton => simp [apply_ite]
  | cons_cons b c l IH IH2 =>
    simp_rw [destutter'_cons, apply_ite (IsChain R ·), IH, if_true_right] at IH2
    simp_rw [destutter'_cons, apply_ite (IsChain R ·),
      apply_ite (IsChain

Depends on / 依赖: Function, Function.swap, IsChain, _cons, apply_ite, cons_cons, destutter, generalizing, if_true_right, imp_and, isChain_cons_cons, ite_prop_iff_and, simp_rw, singleton, twoStepInduction
-/
theorem isChain_destutter' (l : List α) (a : α) : (l.destutter' R a).IsChain R := by
  induction l using twoStepInduction generalizing a with
  | nil => simp
  | singleton => simp [apply_ite]
  | cons_cons b c l IH IH2 =>
    simp_rw [destutter'_cons, apply_ite (IsChain R ·), IH, if_true_right] at IH2
    simp_rw [destutter'_cons, apply_ite (IsChain R ·),
      apply_ite (IsChain R <| a :: ·), IH, isChain_cons_cons,
      if_true_right, ite_prop_iff_and, imp_and]
exact ⟨⟨⟨Function.swap fun _ => id, fun _ => IH2 c b⟩,
Function.swap fun _ => IH2 b a⟩, fun _ => IH2 c a⟩

/--
theorem `isChain_cons_destutter'_of_rel` / 定理 `isChain_cons_destutter'_of_rel`

English:
theorem isChain_cons_destutter'_of_rel
  given: (l : List α) {a b} (hab : R a b)
  proof: by
  simpa [destutter'_cons, hab] using isChain_destutter' R (b :: l) a

中文:
定理 isChain_cons_destutter'_of_rel
  条件: (l : List α) {a b} (hab : R a b)
  证明: by
  simpa [destutter'_cons, hab] using isChain_destutter' R (b :: l) a

Depends on / 依赖: _cons, destutter, isChain_destutter
-/
theorem isChain_cons_destutter'_of_rel (l : List α) {a b} (hab : R a b) :
    (a :: l.destutter' R b).IsChain R := by
  simpa [destutter'_cons, hab] using isChain_destutter' R (b :: l) a

/--
theorem `destutter'_of_isChain_cons` / 定理 `destutter'_of_isChain_cons`

English:
theorem destutter'_of_isChain_cons
  given: (h : (a :: l).IsChain R)
  statement: l.destutter' R a = a :: l
  proof: by
  induction l generalizing a with
  | nil => simp
  | cons b l hb =>
    obtain ⟨h, hc⟩ := isChain_cons_cons.mp h
    rw [l.destutter'_cons_pos h]; rw [hb hc]

@[simp]

中文:
定理 destutter'_of_isChain_cons
  条件: (h : (a :: l).IsChain R)
  结论: l.destutter' R a = a :: l
  证明: by
  induction l generalizing a with
  | nil => simp
  | cons b l hb =>
    obtain ⟨h, hc⟩ := isChain_cons_cons.mp h
    rw [l.destutter'_cons_pos h]; rw [hb hc]

@[simp]
-/
theorem destutter'_of_isChain_cons (h : (a :: l).IsChain R) : l.destutter' R a = a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l hb =>
    obtain ⟨h, hc⟩ := isChain_cons_cons.mp h
    rw [l.destutter'_cons_pos h]; rw [hb hc]

@[simp]
/--
theorem `destutter'_eq_self_iff` / 定理 `destutter'_eq_self_iff`

English:
theorem destutter'_eq_self_iff
  given: (a)
  statement: l.destutter' R a = a :: l ↔ (a :: l).IsChain R
  proof: ⟨fun h => by
    rw [← h]
    exact l.isChain_destutter' R a, destutter'_of_isChain_cons _ _⟩

中文:
定理 destutter'_eq_self_iff
  条件: (a)
  结论: l.destutter' R a = a :: l ↔ (a :: l).IsChain R
  证明: ⟨fun h => by
    rw [← h]
    exact l.isChain_destutter' R a, destutter'_of_isChain_cons _ _⟩
-/
theorem destutter'_eq_self_iff (a) : l.destutter' R a = a :: l ↔ (a :: l).IsChain R :=
  ⟨fun h => by
    rw [← h]
    exact l.isChain_destutter' R a, destutter'_of_isChain_cons _ _⟩

/--
theorem `destutter'_ne_nil` / 定理 `destutter'_ne_nil`

English:
theorem destutter'_ne_nil
  statement: l.destutter' R a != []
  proof: ne_nil_of_mem l.mem_destutter' R a

@[simp]

中文:
定理 destutter'_ne_nil
  结论: l.destutter' R a != []
  证明: ne_nil_of_mem l.mem_destutter' R a

@[simp]
-/
theorem destutter'_ne_nil : l.destutter' R a != [] :=
ne_nil_of_mem l.mem_destutter' R a

@[simp]
/--
theorem `destutter_nil` / 定理 `destutter_nil`

English:
theorem destutter_nil
  statement: ([] : List α).destutter R = []
  proof: rfl

中文:
定理 destutter_nil
  结论: ([] : List α).destutter R = []
  证明: rfl
-/
theorem destutter_nil : ([] : List α).destutter R = [] :=
  rfl

/--
theorem `destutter_cons'` / 定理 `destutter_cons'`

English:
theorem destutter_cons'
  statement: (a :: l).destutter R = destutter' R a l
  proof: rfl

中文:
定理 destutter_cons'
  结论: (a :: l).destutter R = destutter' R a l
  证明: rfl
-/
theorem destutter_cons' : (a :: l).destutter R = destutter' R a l :=
  rfl

/--
theorem `destutter_cons_cons` / 定理 `destutter_cons_cons`

English:
theorem destutter_cons_cons
  proof: rfl

@[simp]

中文:
定理 destutter_cons_cons
  证明: rfl

@[simp]
-/
theorem destutter_cons_cons :
    (a :: b :: l).destutter R = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl

@[simp]
/--
theorem `destutter_singleton` / 定理 `destutter_singleton`

English:
theorem destutter_singleton
  statement: destutter R [a] = [a]
  proof: rfl

@[simp]

中文:
定理 destutter_singleton
  结论: destutter R [a] = [a]
  证明: rfl

@[simp]
-/
theorem destutter_singleton : destutter R [a] = [a] :=
  rfl

@[simp]
/--
theorem `destutter_pair` / 定理 `destutter_pair`

English:
theorem destutter_pair
  statement: destutter R [a, b] = if R a b then [a, b] else [a]
  proof: destutter_cons_cons _ R

中文:
定理 destutter_pair
  结论: destutter R [a, b] = if R a b then [a, b] else [a]
  证明: destutter_cons_cons _ R

Depends on / 依赖: destutter_cons_cons
-/
theorem destutter_pair : destutter R [a, b] = if R a b then [a, b] else [a] :=
  destutter_cons_cons _ R

/--
theorem `destutter_sublist` / 定理 `destutter_sublist`

English:
theorem destutter_sublist
  statement: forall l : List α, l.destutter R <+ l

中文:
定理 destutter_sublist
  结论: 对任意 l : List α, l.destutter R <+ l
-/
theorem destutter_sublist : forall l : List α, l.destutter R <+ l
  | [] => Sublist.slnil
  | h :: l => l.destutter'_sublist R h

/--
theorem `isChain_destutter` / 定理 `isChain_destutter`

English:
theorem isChain_destutter
  statement: forall l : List α, (l.destutter R).IsChain R

中文:
定理 isChain_destutter
  结论: 对任意 l : List α, (l.destutter R).IsChain R
-/
theorem isChain_destutter : forall l : List α, (l.destutter R).IsChain R
  | [] => .nil
  | h :: l => l.isChain_destutter' R h

/--
theorem `destutter_of_isChain` / 定理 `destutter_of_isChain`

English:
theorem destutter_of_isChain
  statement: forall l : List α, l.IsChain R -> l.destutter R = l

中文:
定理 destutter_of_isChain
  结论: 对任意 l : List α, l.IsChain R -> l.destutter R = l
-/
theorem destutter_of_isChain : forall l : List α, l.IsChain R -> l.destutter R = l
  | [], _ => rfl
  | _ :: l, h => l.destutter'_of_isChain_cons _ h

@[simp]
/--
theorem `destutter_eq_self_iff` / 定理 `destutter_eq_self_iff`

English:
theorem destutter_eq_self_iff
  statement: forall l : List α, l.destutter R = l ↔ l.IsChain R

中文:
定理 destutter_eq_self_iff
  结论: 对任意 l : List α, l.destutter R = l ↔ l.IsChain R
-/
theorem destutter_eq_self_iff : forall l : List α, l.destutter R = l ↔ l.IsChain R
  | [] => by simp
  | a :: l => l.destutter'_eq_self_iff R a

/--
theorem `destutter_idem` / 定理 `destutter_idem`

English:
theorem destutter_idem
  statement: (l.destutter R).destutter R = l.destutter R
  proof: destutter_of_isChain R _ l.isChain_destutter R

@[simp]

中文:
定理 destutter_idem
  结论: (l.destutter R).destutter R = l.destutter R
  证明: destutter_of_isChain R _ l.isChain_destutter R

@[simp]

Depends on / 依赖: destutter_of_isChain, isChain_destutter, l.isChain_destutter
-/
theorem destutter_idem : (l.destutter R).destutter R = l.destutter R :=
destutter_of_isChain R _ l.isChain_destutter R

@[simp]
/--
theorem `destutter_eq_nil` / 定理 `destutter_eq_nil`

English:
theorem destutter_eq_nil
  statement: forall {l : List α}, destutter R l = [] ↔ l = []

中文:
定理 destutter_eq_nil
  结论: 对任意 {l : List α}, destutter R l = [] ↔ l = []
-/
theorem destutter_eq_nil : forall {l : List α}, destutter R l = [] ↔ l = []
  | [] => Iff.rfl
| _ :: l => ⟨fun h => absurd h l.destutter'_ne_nil R, fun h => nomatch h⟩

variable {R}

/--
theorem `map_destutter` / 定理 `map_destutter`

English:
theorem map_destutter
  given: {f : α -> β}
  statement: forall {l : List α}, (forall a in l, forall b in l, R a b ↔ R₂ (f a) (f b)) ->
  proof: hl a (by simp) b (by simp)
    simp_rw [map_cons, destutter_cons_cons, ← this]
    by_cases hr : R a b <;>
      simp [hr, ← destutter_cons', map_destutter fun c hc d hd => hl _ (cons_subset_cons _
        (subset_cons_self _ _) hc) _ (cons_subset_cons _ (subset_cons_self _ _) hd),
        map_destu

中文:
定理 map_destutter
  条件: {f : α -> β}
  结论: 对任意 {l : List α}, (对任意 a in l, 对任意 b in l, R a b ↔ R₂ (f a) (f b)) ->
  证明: hl a (by simp) b (by simp)
    simp_rw [map_cons, destutter_cons_cons, ← this]
    by_cases hr : R a b <;>
      simp [hr, ← destutter_cons', map_destutter fun c hc d hd => hl _ (cons_subset_cons _
        (subset_cons_self _ _) hc) _ (cons_subset_cons _ (subset_cons_self _ _) hd),
        map_destu
-/
theorem map_destutter {f : α -> β} : forall {l : List α}, (forall a in l, forall b in l, R a b ↔ R₂ (f a) (f b)) ->
    (l.destutter R).map f = (l.map f).destutter R₂
  | [], hl => by simp
  | [a], hl => by simp
  | a :: b :: l, hl => by
    have := hl a (by simp) b (by simp)
    simp_rw [map_cons, destutter_cons_cons, ← this]
    by_cases hr : R a b <;>
      simp [hr, ← destutter_cons', map_destutter fun c hc d hd => hl _ (cons_subset_cons _
        (subset_cons_self _ _) hc) _ (cons_subset_cons _ (subset_cons_self _ _) hd),
        map_destutter fun c hc d hd => hl _ (subset_cons_self _ _ hc) _ (subset_cons_self _ _ hd)]

/--
theorem `map_destutter_ne` / 定理 `map_destutter_ne`

English:
theorem map_destutter_ne
  given: {f : α -> β} (h : Injective f) [DecidableEq α] [DecidableEq β]
  proof: map_destutter fun _ _ _ _ => h.ne_iff.symm

中文:
定理 map_destutter_ne
  条件: {f : α -> β} (h : Injective f) [DecidableEq α] [DecidableEq β]
  证明: map_destutter fun _ _ _ _ => h.ne_iff.symm

Depends on / 依赖: h.ne_iff.symm, map_destutter, ne_iff
-/
theorem map_destutter_ne {f : α -> β} (h : Injective f) [DecidableEq α] [DecidableEq β] :
    (l.destutter (· != ·)).map f = (l.map f).destutter (· != ·) :=
  map_destutter fun _ _ _ _ => h.ne_iff.symm

/--
theorem `length_destutter'_cotrans_ge` / 定理 `length_destutter'_cotrans_ge`

English:
theorem length_destutter'_cotrans_ge
  given: [i : IsTrans α Rᶜ]
  proof: (mt (_root_.trans hba)) (not_not.2 hbc)
      simp_rw [destutter', if_pos (not_not.1 hac), if_pos hbc, length_cons, le_refl]
    case neg =>
      simp only [destutter', if_neg hbc]
      by_cases hac : R a c
      case pos =>
        simp only [if_pos hac, length_cons]
        exact Nat.le_succ_of_

中文:
定理 length_destutter'_cotrans_ge
  条件: [i : IsTrans α Rᶜ]
  证明: (mt (_root_.trans hba)) (not_not.2 hbc)
      simp_rw [destutter', if_pos (not_not.1 hac), if_pos hbc, length_cons, le_refl]
    case neg =>
      simp only [destutter', if_neg hbc]
      by_cases hac : R a c
      case pos =>
        simp only [if_pos hac, length_cons]
        exact Nat.le_succ_of_

Depends on / 依赖: _root_, _root_.trans, not_not
-/
theorem length_destutter'_cotrans_ge [i : IsTrans α Rᶜ] :
    forall {a} {l : List α}, ¬R b a -> (l.destutter' R b).length <= (l.destutter' R a).length
  | a, [], hba => by simp
  | a, c :: l, hba => by
    by_cases hbc : R b c
    case pos =>
      have hac : ¬Rᶜ a c := (mt (_root_.trans hba)) (not_not.2 hbc)
      simp_rw [destutter', if_pos (not_not.1 hac), if_pos hbc, length_cons, le_refl]
    case neg =>
      simp only [destutter', if_neg hbc]
      by_cases hac : R a c
      case pos =>
        simp only [if_pos hac, length_cons]
        exact Nat.le_succ_of_le (length_destutter'_cotrans_ge hbc)
      case neg =>
        simp only [if_neg hac]
        exact length_destutter'_cotrans_ge hba

/--
theorem `length_destutter'_congr` / 定理 `length_destutter'_congr`

English:
theorem length_destutter'_congr
  given: [IsEquiv α Rᶜ] (hab : ¬R a b)
  proof: (length_destutter'_cotrans_ge hab).antisymm length_destutter'_cotrans_ge (symm hab : Rᶜ b a)

中文:
定理 length_destutter'_congr
  条件: [IsEquiv α Rᶜ] (hab : ¬R a b)
  证明: (length_destutter'_cotrans_ge hab).antisymm length_destutter'_cotrans_ge (symm hab : Rᶜ b a)
-/
theorem length_destutter'_congr [IsEquiv α Rᶜ] (hab : ¬R a b) :
    (l.destutter' R a).length = (l.destutter' R b).length :=
(length_destutter'_cotrans_ge hab).antisymm length_destutter'_cotrans_ge (symm hab : Rᶜ b a)

/-- `List.destutter'` on a relation like ≠, whose negation is an equivalence, has length
monotonic under List.cons -/
/--
theorem `le_length_destutter'_cons` / 定理 `le_length_destutter'_cons`

English:
theorem le_length_destutter'_cons
  given: [IsEquiv α Rᶜ]
  proof: em _
    · have hbc : ¬Rᶜ b c := mt (_root_.trans hab) (not_not.2 hac)
      simp [destutter', if_pos hac, if_pos (not_not.1 hbc), if_neg hab]
    · have hbc : ¬R b c := trans (symm hab) hac
      simp only [destutter', if_neg hbc, if_neg hac, if_neg hab]
      exact (length_destutter'_congr cs hab)

中文:
定理 le_length_destutter'_cons
  条件: [IsEquiv α Rᶜ]
  证明: em _
    · have hbc : ¬Rᶜ b c := mt (_root_.trans hab) (not_not.2 hac)
      simp [destutter', if_pos hac, if_pos (not_not.1 hbc), if_neg hab]
    · have hbc : ¬R b c := trans (symm hab) hac
      simp only [destutter', if_neg hbc, if_neg hac, if_neg hab]
      exact (length_destutter'_congr cs hab)
-/
theorem le_length_destutter'_cons [IsEquiv α Rᶜ] :
    forall {l : List α}, (l.destutter' R b).length <= ((b :: l).destutter' R a).length
  | [] => by by_cases hab : (R a b) <;> simp_all [Nat.le_succ]
  | c :: cs => by
    by_cases hab : R a b
    case pos => simp [destutter', if_pos hab, Nat.le_succ]
    obtain hac | hac : R a c ∨ Rᶜ a c := em _
    · have hbc : ¬Rᶜ b c := mt (_root_.trans hab) (not_not.2 hac)
      simp [destutter', if_pos hac, if_pos (not_not.1 hbc), if_neg hab]
    · have hbc : ¬R b c := trans (symm hab) hac
      simp only [destutter', if_neg hbc, if_neg hac, if_neg hab]
      exact (length_destutter'_congr cs hab).ge

/--
theorem `length_destutter_le_length_destutter_cons` / 定理 `length_destutter_le_length_destutter_cons`

English:
theorem length_destutter_le_length_destutter_cons
  given: [IsEquiv α Rᶜ]

中文:
定理 length_destutter_le_length_destutter_cons
  条件: [IsEquiv α Rᶜ]
-/
theorem length_destutter_le_length_destutter_cons [IsEquiv α Rᶜ] :
    forall {l : List α}, (l.destutter R).length <= ((a :: l).destutter R).length
  | [] => by simp [destutter]
  | b :: l => le_length_destutter'_cons

variable {l l₁ l₂}

/--
theorem `length_destutter_ne_le_length_destutter_cons` / 定理 `length_destutter_ne_le_length_destutter_cons`

English:
theorem length_destutter_ne_le_length_destutter_cons
  given: [DecidableEq α]
  proof: length_destutter_le_length_destutter_cons

中文:
定理 length_destutter_ne_le_length_destutter_cons
  条件: [DecidableEq α]
  证明: length_destutter_le_length_destutter_cons

Depends on / 依赖: length_destutter_le_length_destutter_cons
-/
theorem length_destutter_ne_le_length_destutter_cons [DecidableEq α] :
    (l.destutter (· != ·)).length <= ((a :: l).destutter (· != ·)).length :=
  length_destutter_le_length_destutter_cons

/--
lemma `IsChain.length_le_length_destutter` / 引理 `IsChain.length_le_length_destutter`

English:
lemma IsChain.length_le_length_destutter
  given: [IsEquiv α Rᶜ]
  proof: []`, `l₂ := []`
  | [], [], _, _ => by simp
  -- `l₁ := l₁`, `l₂ := a :: l₂`
  | l₁, _, .cons (l₂ := l₂) a hl, hl₁ =>
    (hl₁.length_le_length_destutter hl).trans length_destutter_le_length_destutter_cons
  -- `l₁ := [a]`, `l₂ := a :: l₂`
  | _, _, .cons_cons (l₁ := []) (l₂ := l₁) a hl, hl₁ => by s

中文:
引理 IsChain.length_le_length_destutter
  条件: [IsEquiv α Rᶜ]
  证明: []`, `l₂ := []`
  | [], [], _, _ => by simp
  -- `l₁ := l₁`, `l₂ := a :: l₂`
  | l₁, _, .cons (l₂ := l₂) a hl, hl₁ =>
    (hl₁.length_le_length_destutter hl).trans length_destutter_le_length_destutter_cons
  -- `l₁ := [a]`, `l₂ := a :: l₂`
  | _, _, .cons_cons (l₁ := []) (l₂ := l₁) a hl, hl₁ => by s
-/
lemma IsChain.length_le_length_destutter [IsEquiv α Rᶜ] :
    forall {l₁ l₂ : List α}, l₁ <+ l₂ -> l₁.IsChain R -> l₁.length <= (l₂.destutter R).length
  -- `l₁ := []`, `l₂ := []`
  | [], [], _, _ => by simp
  -- `l₁ := l₁`, `l₂ := a :: l₂`
  | l₁, _, .cons (l₂ := l₂) a hl, hl₁ =>
    (hl₁.length_le_length_destutter hl).trans length_destutter_le_length_destutter_cons
  -- `l₁ := [a]`, `l₂ := a :: l₂`
  | _, _, .cons_cons (l₁ := []) (l₂ := l₁) a hl, hl₁ => by simp [Nat.one_le_iff_ne_zero]
  -- `l₁ := a :: l₁`, `l₂ := a :: b :: l₂`
| _, _, .cons_cons a .cons (l₁ := l₁) (l₂ := l₂) b hl, hl₁ => by
    by_cases hab : R a b
    · simpa [destutter_cons_cons, hab] using! hl₁.tail.length_le_length_destutter (hl.cons _)
    · simpa [destutter_cons_cons, hab] using! hl₁.length_le_length_destutter (hl.cons_cons _)
  -- `l₁ := a :: b :: l₁`, `l₂ := a :: b :: l₂`
| _, _, .cons_cons a .cons_cons (l₁ := l₁) (l₂ := l₂) b hl, hl₁ => by
    simpa [destutter_cons_cons, rel_of_isChain_cons_cons hl₁]
      using! hl₁.tail.length_le_length_destutter (hl.cons_cons _)

/--
lemma `IsChain.length_le_length_destutter_ne` / 引理 `IsChain.length_le_length_destutter_ne`

English:
lemma IsChain.length_le_length_destutter_ne
  statement: [DecidableEq α] (hl : l₁ <+ l₂)
  proof: hl₁.length_le_length_destutter hl

中文:
引理 IsChain.length_le_length_destutter_ne
  结论: [DecidableEq α] (hl : l₁ <+ l₂)
  证明: hl₁.length_le_length_destutter hl

Depends on / 依赖: length_le_length_destutter
-/
lemma IsChain.length_le_length_destutter_ne [DecidableEq α] (hl : l₁ <+ l₂)
    (hl₁ : l₁.IsChain (· != ·)) : l₁.length <= (l₂.destutter (· != ·)).length :=
  hl₁.length_le_length_destutter hl

/--
lemma `Pairwise.destutter_eq_dedup` / 引理 `Pairwise.destutter_eq_dedup`

English:
lemma Pairwise.destutter_eq_dedup
  given: [DecidableEq α] {r : α -> α -> Prop} [Std.Antisymm r]
  proof: eq_or_ne x y
    · simpa using h.2.destutter_eq_dedup
    · simp only [mem_cons, forall_eq_or_imp, pairwise_cons] at h
      have : x ∉ xs := fun hx => hxy (antisymm h.1.1 (h.2.1 x hx))
      rw [if_pos hxy]; rw [dedup_cons_of_notMem (a := x) (by simp [*])]

中文:
引理 Pairwise.destutter_eq_dedup
  条件: [DecidableEq α] {r : α -> α -> 命题} [Std.Antisymm r]
  证明: eq_or_ne x y
    · simpa using h.2.destutter_eq_dedup
    · simp only [mem_cons, forall_eq_or_imp, pairwise_cons] at h
      have : x ∉ xs := fun hx => hxy (antisymm h.1.1 (h.2.1 x hx))
      rw [if_pos hxy]; rw [dedup_cons_of_notMem (a := x) (by simp [*])]

Depends on / 依赖: eq_or_ne
-/
lemma Pairwise.destutter_eq_dedup [DecidableEq α] {r : α -> α -> Prop} [Std.Antisymm r] :
    forall {l : List α}, l.Pairwise r -> l.destutter (· != ·) = l.dedup
  | [], h => by simp
  | [x], h => by simp
  | x :: y :: xs, h => by
    rw [pairwise_cons] at h
    rw [destutter_cons_cons]; rw [← destutter_cons']; rw [← destutter_cons']; rw [h.2.destutter_eq_dedup]
    obtain rfl | hxy := eq_or_ne x y
    · simpa using h.2.destutter_eq_dedup
    · simp only [mem_cons, forall_eq_or_imp, pairwise_cons] at h
      have : x ∉ xs := fun hx => hxy (antisymm h.1.1 (h.2.1 x hx))
      rw [if_pos hxy]; rw [dedup_cons_of_notMem (a := x) (by simp [*])]

end List
