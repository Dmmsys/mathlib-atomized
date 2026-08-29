/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Basic

/-!
# Dense orders and finsets

We prove that in a dense order, there's always an element lying in between any two finite sets of
elements.
-/

public section

variable {α : Type*} [LinearOrder α] [DenselyOrdered α]

/--
theorem `Finset.exists_between` / 定理 `Finset.exists_between`

English:
theorem Finset.exists_between
  statement: {s t : Finset α}
  proof: by
  convert! _root_.exists_between (a₁ := s.max' hs) (a₂ := t.min' ht) (by simp_all) <;> simp

中文:
定理 有限集.存在_between
  结论: {s t : 有限集 α}
  证明: by
  convert! _root_.exists_between (a₁ := s.max' hs) (a₂ := t.min' ht) (by simp_all) <;> simp

Depends on / 依赖: _root_, _root_.exists_between, convert, exists_between, s.max, t.min
-/
theorem Finset.exists_between {s t : Finset α}
    (hs : s.Nonempty) (ht : t.Nonempty) (H : forall x in s, forall y in t, x < y) :
    exists b, (forall x in s, x < b) ∧ (forall y in t, b < y) := by
  convert! _root_.exists_between (a₁ := s.max' hs) (a₂ := t.min' ht) (by simp_all) <;> simp

/--
theorem `Finset.exists_between'` / 定理 `Finset.exists_between'`

English:
theorem Finset.exists_between'
  statement: (s t : Finset α) [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
  proof: by
  by_cases hs : s.Nonempty <;> by_cases ht : t.Nonempty
  · exact s.exists_between hs ht H
  · exact let ⟨p, hp⟩ := exists_gt (s.max' hs); ⟨p, by simp_all⟩
  · exact let ⟨p, hp⟩ := exists_lt (t.min' ht); ⟨p, by simp_all⟩
  · exact Nonempty.elim ‹_› fun p => ⟨p, by simp_all⟩

中文:
定理 有限集.存在_between'
  结论: (s t : 有限集 α) [NoMax序 α] [NoMin序 α] [非空 α]
  证明: by
  by_cases hs : s.Nonempty <;> by_cases ht : t.Nonempty
  · exact s.exists_between hs ht H
  · exact let ⟨p, hp⟩ := exists_gt (s.max' hs); ⟨p, by simp_all⟩
  · exact let ⟨p, hp⟩ := exists_lt (t.min' ht); ⟨p, by simp_all⟩
  · exact Nonempty.elim ‹_› fun p => ⟨p, by simp_all⟩

Depends on / 依赖: Nonempty, Nonempty.elim, exists_between, exists_gt, exists_lt, s.Nonempty, s.exists_between, s.max, t.Nonempty, t.min
-/
theorem Finset.exists_between' (s t : Finset α) [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
    (H : forall x in s, forall y in t, x < y) : exists b, (forall x in s, x < b) ∧ (forall y in t, b < y) := by
  by_cases hs : s.Nonempty <;> by_cases ht : t.Nonempty
  · exact s.exists_between hs ht H
  · exact let ⟨p, hp⟩ := exists_gt (s.max' hs); ⟨p, by simp_all⟩
  · exact let ⟨p, hp⟩ := exists_lt (t.min' ht); ⟨p, by simp_all⟩
  · exact Nonempty.elim ‹_› fun p => ⟨p, by simp_all⟩

/--
theorem `Set.Finite.exists_between` / 定理 `Set.Finite.exists_between`

English:
theorem Set.Finite.exists_between
  statement: {s t : Set α}
  proof: by
  convert!
    Finset.exists_between (s := hsf.toFinset) (t := htf.toFinset) (by simpa) (by simpa)
      (by simpa) using
    1; simp

中文:
定理 集合.有限.存在_between
  结论: {s t : 集合 α}
  证明: by
  convert!
    Finset.exists_between (s := hsf.toFinset) (t := htf.toFinset) (by simpa) (by simpa)
      (by simpa) using
    1; simp

Depends on / 依赖: Finset, Finset.exists_between, convert, exists_between, hsf.toFinset, htf.toFinset, toFinset
-/
theorem Set.Finite.exists_between {s t : Set α}
    (hsf : s.Finite) (hs : s.Nonempty) (htf : t.Finite) (ht : t.Nonempty)
    (H : forall x in s, forall y in t, x < y) : exists b, (forall x in s, x < b) ∧ (forall y in t, b < y) := by
  convert!
    Finset.exists_between (s := hsf.toFinset) (t := htf.toFinset) (by simpa) (by simpa)
      (by simpa) using
    1; simp

/--
theorem `Set.Finite.exists_between'` / 定理 `Set.Finite.exists_between'`

English:
theorem Set.Finite.exists_between'
  statement: [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
  proof: by
  convert! hs.toFinset.exists_between' ht.toFinset (by simpa) using 1; simp

中文:
定理 集合.有限.存在_between'
  结论: [NoMax序 α] [NoMin序 α] [非空 α]
  证明: by
  convert! hs.toFinset.exists_between' ht.toFinset (by simpa) using 1; simp

Depends on / 依赖: convert, exists_between, hs.toFinset.exists_between, ht.toFinset, toFinset
-/
theorem Set.Finite.exists_between' [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
    {s t : Set α} (hs : s.Finite) (ht : t.Finite)
    (H : forall x in s, forall y in t, x < y) : exists b, (forall x in s, x < b) ∧ (forall y in t, b < y) := by
  convert! hs.toFinset.exists_between' ht.toFinset (by simpa) using 1; simp
