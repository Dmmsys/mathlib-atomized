/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module
public import Mathlib.Data.List.Find
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Set.Subsingleton

/-!
# Finding subsingleton elements within multisets

This module provides `Multiset.find? s p ⋯`, which lifts `List.find?` to multisets.
-/

public section

namespace Multiset
variable {α : Type*} (p : α -> Prop) [DecidablePred p]

/--
Definition of `find?` / `find?` 的定义

English:
definition find?
  signature: (s : Multiset α)
  body: Quotient.recOn s (fun l _ => l.find? p) fun l₁ l₂ h => by
    unfold Eq.ndrec
    rw [eqRec_eq_cast]; rw [cast_eq_iff_heq]
    refine Function.hfunext ?_ (fun hp₁ hp₂ _ => heq_of_eq ?_)
    · congr!
      exact congrArg _ (Quotient.sound h)
    refine List.find?_eq_find?_of_perm h ?_
    simpa using hp₁

@[simp, grind =]

中文:
定义 find?
  签名: (s : Multiset α)
  定义体: Quotient.recOn s (fun l _ => l.find? p) fun l₁ l₂ h => by
    unfold Eq.ndrec
    rw [eqRec_eq_cast]; rw [cast_eq_iff_heq]
    refine Function.hfunext ?_ (fun hp₁ hp₂ _ => heq_of_eq ?_)
    · congr!
      exact congrArg _ (Quotient.sound h)
    refine List.find?_eq_find?_of_perm h ?_
    simpa using hp₁

@[simp, grind =]
-/
@[expose] def find? (s : Multiset α) : {x in s | p x}.Subsingleton -> Option α :=
  Quotient.recOn s (fun l _ => l.find? p) fun l₁ l₂ h => by
    unfold Eq.ndrec
    rw [eqRec_eq_cast]; rw [cast_eq_iff_heq]
    refine Function.hfunext ?_ (fun hp₁ hp₂ _ => heq_of_eq ?_)
    · congr!
      exact congrArg _ (Quotient.sound h)
    refine List.find?_eq_find?_of_perm h ?_
    simpa using hp₁

@[simp, grind =]
/--
theorem `find?_coe` / 定理 `find?_coe`

English:
theorem find?_coe
  given: (l : List α) (hp)
  proof: rfl

中文:
定理 find?_coe
  条件: (l : 列表 α) (hp)
  证明: rfl
-/
theorem find?_coe (l : List α) (hp) :
    (l : Multiset α).find? p hp = l.find? (fun a => p a) := rfl

/--
theorem `find?_some` / 定理 `find?_some`

English:
theorem find?_some
  given: {a : α} {s : Multiset α} {hp}
  proof: by
  induction s using Quotient.inductionOn with | _ l
  simp only [quot_mk_to_coe, find?_coe _ _ hp]
  simpa using l.find?_some (p := (p ·))

@[simp]

中文:
定理 find?_some
  条件: {a : α} {s : Multiset α} {hp}
  证明: by
  induction s using Quotient.inductionOn with | _ l
  simp only [quot_mk_to_coe, find?_coe _ _ hp]
  simpa using l.find?_some (p := (p ·))

@[simp]
-/
theorem find?_some {a : α} {s : Multiset α} {hp} :
    s.find? p hp = some a -> p a := by
  induction s using Quotient.inductionOn with | _ l
  simp only [quot_mk_to_coe, find?_coe _ _ hp]
  simpa using l.find?_some (p := (p ·))

@[simp]
/--
theorem `find?_zero` / 定理 `find?_zero`

English:
theorem find?_zero
  statement: (0 : Multiset α).find? p (by simp) = none
  proof: rfl

@[simp]

中文:
定理 find?_zero
  结论: (0 : Multiset α).find? p (by simp) = none
  证明: rfl

@[simp]
-/
theorem find?_zero : (0 : Multiset α).find? p (by simp) = none := rfl

@[simp]
/--
theorem `find?_cons` / 定理 `find?_cons`

English:
theorem find?_cons
  given: (a : α) (s : Multiset α) (hp)
  proof: by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, cons_coe]
  grind

@[simp]

中文:
定理 find?_cons
  条件: (a : α) (s : Multiset α) (hp)
  证明: by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, cons_coe]
  grind

@[simp]
-/
theorem find?_cons (a : α) (s : Multiset α) (hp) :
    (cons a s).find? p hp = if h : p a then some a else s.find? p (by grind) := by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, cons_coe]
  grind

@[simp]
/--
theorem `find?_singleton` / 定理 `find?_singleton`

English:
theorem find?_singleton
  given: (a : α) (hp)
  proof: find?_cons _ _ _ _

@[simp]

中文:
定理 find?_singleton
  条件: (a : α) (hp)
  证明: find?_cons _ _ _ _

@[simp]
-/
theorem find?_singleton (a : α) (hp) :
    ({a} : Multiset α).find? p hp = if p a then some a else none :=
  find?_cons _ _ _ _

@[simp]
/--
theorem `find?_add` / 定理 `find?_add`

English:
theorem find?_add
  given: (s t : Multiset α) (hp)
  proof: by
  induction s, t using Quotient.inductionOn₂
  exact List.find?_append

中文:
定理 find?_add
  条件: (s t : Multiset α) (hp)
  证明: by
  induction s, t using Quotient.inductionOn₂
  exact List.find?_append
-/
theorem find?_add (s t : Multiset α) (hp) :
    (s + t).find? p hp =
      (s.find? p (hp.anti <| by grind)).or (t.find? p (hp.anti <| by grind)) := by
  induction s, t using Quotient.inductionOn₂
  exact List.find?_append

variable {p} in
@[simp, grind =]
/--
theorem `find?_eq_some_iff` / 定理 `find?_eq_some_iff`

English:
theorem find?_eq_some_iff
  given: {a : α} {s : Multiset α} (hp)
  proof: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [find?_cons]
    split
    · dsimp [Set.Subsingleton] at hp
      specialize hp ⟨mem_cons_self _ _, ‹p x›⟩
      grind
    · simp_rw [ih]
      grind

中文:
定理 find?_eq_some_iff
  条件: {a : α} {s : Multiset α} (hp)
  证明: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [find?_cons]
    split
    · dsimp [Set.Subsingleton] at hp
      specialize hp ⟨mem_cons_self _ _, ‹p x›⟩
      grind
    · simp_rw [ih]
      grind
-/
theorem find?_eq_some_iff {a : α} {s : Multiset α} (hp) :
    s.find? p hp = some a ↔ a in s ∧ p a := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [find?_cons]
    split
    · dsimp [Set.Subsingleton] at hp
      specialize hp ⟨mem_cons_self _ _, ‹p x›⟩
      grind
    · simp_rw [ih]
      grind

variable {p} in
@[simp, grind =]
/--
theorem `find?_eq_none_iff` / 定理 `find?_eq_none_iff`

English:
theorem find?_eq_none_iff
  given: {s : Multiset α} (hp)
  proof: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [find?_cons]
    dsimp [Set.Subsingleton] at hp
    grind

中文:
定理 find?_eq_none_iff
  条件: {s : Multiset α} (hp)
  证明: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [find?_cons]
    dsimp [Set.Subsingleton] at hp
    grind
-/
theorem find?_eq_none_iff {s : Multiset α} (hp) :
    s.find? p hp = none ↔ forall a in s, ¬ p a := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [find?_cons]
    dsimp [Set.Subsingleton] at hp
    grind

/-- If two predicates agree on all the elements, so does `find?`. -/
@[congr]
/--
theorem `find?_congr` / 定理 `find?_congr`

English:
theorem find?_congr
  statement: {p₁ p₂ : α -> Prop} [DecidablePred p₁] [DecidablePred p₂] {s : Multiset α}
  proof: by
  induction s using Quotient.ind
  exact List.find?_congr fun x hx => by simp [h x (by simpa using hx)]

中文:
定理 find?_congr
  结论: {p₁ p₂ : α -> 命题} [DecidablePred p₁] [DecidablePred p₂] {s : Multiset α}
  证明: by
  induction s using Quotient.ind
  exact List.find?_congr fun x hx => by simp [h x (by simpa using hx)]
-/
theorem find?_congr {p₁ p₂ : α -> Prop} [DecidablePred p₁] [DecidablePred p₂] {s : Multiset α}
    (hp₁ : {x in s | p₁ x}.Subsingleton) (h : forall x in s, p₁ x ↔ p₂ x) :
    s.find? p₁ hp₁ = s.find? p₂
      (by simp_rw +contextual [← exists_prop, ← h, exists_prop, hp₁]) := by
  induction s using Quotient.ind
  exact List.find?_congr fun x hx => by simp [h x (by simpa using hx)]

/--
theorem `find?_eq_choose` / 定理 `find?_eq_choose`

English:
theorem find?_eq_choose
  given: {s : Multiset α} (hp : exists! x, x in s ∧ p x)
  proof: by
  ext a
.trans ?_ refine find?_eq_some_iff _
  simp only [Option.some.injEq, choose_eq_iff]

中文:
定理 find?_eq_choose
  条件: {s : Multiset α} (hp : 存在! x, x in s ∧ p x)
  证明: by
  ext a
.trans ?_ refine find?_eq_some_iff _
  simp only [Option.some.injEq, choose_eq_iff]
-/
theorem find?_eq_choose {s : Multiset α} (hp : exists! x, x in s ∧ p x) :
    s.find? p hp.setSubsingleton = some (s.choose p hp) := by
  ext a
.trans ?_ refine find?_eq_some_iff _
  simp only [Option.some.injEq, choose_eq_iff]

end Multiset
