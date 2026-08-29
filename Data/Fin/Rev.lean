/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Joel Riou, Yury Kudryashov
-/
module

public import Mathlib.Data.Fin.SuccPred
/-!
# Reverse on `Fin n`

This file contains lemmas about `Fin.rev : Fin n → Fin n` which maps `i` to `n - 1 - i`.

## Definitions

* `Fin.revPerm : Equiv.Perm (Fin n)` : `Fin.rev` as an `Equiv.Perm`, the antitone involution given
  by `i ↦ n-(i+1)`
-/

@[expose] public section

assert_not_exists Monoid Fintype

open Fin Nat Function

namespace Fin

variable {n m : Nat}

/--
theorem `rev_involutive` / 定理 `rev_involutive`

English:
theorem rev_involutive
  statement: Involutive (rev : Fin n -> Fin n)
  proof: rev_rev

中文:
定理 rev_involutive
  结论: Involutive (rev : Fin n -> Fin n)
  证明: rev_rev

Depends on / 依赖: rev_rev
-/
theorem rev_involutive : Involutive (rev : Fin n -> Fin n) := rev_rev

/-- `Fin.rev` as an `Equiv.Perm`, the antitone involution `Fin n → Fin n` given by
`i ↦ n-(i+1)`. -/
@[simps! apply]
/--
Definition of `revPerm` / `revPerm` 的定义

English:
definition revPerm
  signature: : Equiv.Perm (Fin n)
  body: Involutive.toPerm rev rev_involutive

中文:
定义 revPerm
  签名: : Equiv.Perm (Fin n)
  定义体: Involutive.toPerm rev rev_involutive

Depends on / 依赖: Involutive, Involutive.toPerm, rev_involutive, toPerm
-/
def revPerm : Equiv.Perm (Fin n) :=
  Involutive.toPerm rev rev_involutive

/--
theorem `rev_injective` / 定理 `rev_injective`

English:
theorem rev_injective
  statement: Injective (@rev n)
  proof: rev_involutive.injective

中文:
定理 rev_injective
  结论: Injective (@rev n)
  证明: rev_involutive.injective

Depends on / 依赖: injective, rev_involutive, rev_involutive.injective
-/
theorem rev_injective : Injective (@rev n) :=
  rev_involutive.injective

/--
theorem `rev_surjective` / 定理 `rev_surjective`

English:
theorem rev_surjective
  statement: Surjective (@rev n)
  proof: rev_involutive.surjective

中文:
定理 rev_surjective
  结论: Surjective (@rev n)
  证明: rev_involutive.surjective

Depends on / 依赖: rev_involutive, rev_involutive.surjective, surjective
-/
theorem rev_surjective : Surjective (@rev n) :=
  rev_involutive.surjective

/--
theorem `rev_bijective` / 定理 `rev_bijective`

English:
theorem rev_bijective
  statement: Bijective (@rev n)
  proof: rev_involutive.bijective

@[simp]

中文:
定理 rev_bijective
  结论: Bijective (@rev n)
  证明: rev_involutive.bijective

@[simp]

Depends on / 依赖: bijective, rev_involutive, rev_involutive.bijective
-/
theorem rev_bijective : Bijective (@rev n) :=
  rev_involutive.bijective

@[simp]
/--
theorem `revPerm_symm` / 定理 `revPerm_symm`

English:
theorem revPerm_symm
  statement: (@revPerm n).symm = revPerm
  proof: rfl

中文:
定理 revPerm_symm
  结论: (@revPerm n).symm = revPerm
  证明: rfl
-/
theorem revPerm_symm : (@revPerm n).symm = revPerm :=
  rfl

/--
theorem `cast_rev` / 定理 `cast_rev`

English:
theorem cast_rev
  given: (i : Fin n) (h : n = m)
  proof: by
  subst h; simp

中文:
定理 cast_rev
  条件: (i : Fin n) (h : n = m)
  证明: by
  subst h; simp
-/
theorem cast_rev (i : Fin n) (h : n = m) :
    i.rev.cast h = (i.cast h).rev := by
  subst h; simp

/--
theorem `rev_eq_iff` / 定理 `rev_eq_iff`

English:
theorem rev_eq_iff
  given: {i j : Fin n}
  statement: rev i = j ↔ i = rev j
  proof: by
  rw [← rev_inj]; rw [rev_rev]

中文:
定理 rev_eq_iff
  条件: {i j : Fin n}
  结论: rev i = j ↔ i = rev j
  证明: by
  rw [← rev_inj]; rw [rev_rev]

Depends on / 依赖: rev_inj, rev_rev
-/
theorem rev_eq_iff {i j : Fin n} : rev i = j ↔ i = rev j := by
  rw [← rev_inj]; rw [rev_rev]

/--
theorem `rev_ne_iff` / 定理 `rev_ne_iff`

English:
theorem rev_ne_iff
  given: {i j : Fin n}
  statement: rev i != j ↔ i != rev j
  proof: rev_eq_iff.not

中文:
定理 rev_ne_iff
  条件: {i j : Fin n}
  结论: rev i != j ↔ i != rev j
  证明: rev_eq_iff.not

Depends on / 依赖: rev_eq_iff, rev_eq_iff.not
-/
theorem rev_ne_iff {i j : Fin n} : rev i != j ↔ i != rev j := rev_eq_iff.not

/--
theorem `rev_lt_iff` / 定理 `rev_lt_iff`

English:
theorem rev_lt_iff
  given: {i j : Fin n}
  statement: rev i < j ↔ rev j < i
  proof: by
  rw [← rev_lt_rev]; rw [rev_rev]

中文:
定理 rev_lt_iff
  条件: {i j : Fin n}
  结论: rev i < j ↔ rev j < i
  证明: by
  rw [← rev_lt_rev]; rw [rev_rev]

Depends on / 依赖: rev_lt_rev, rev_rev
-/
theorem rev_lt_iff {i j : Fin n} : rev i < j ↔ rev j < i := by
  rw [← rev_lt_rev]; rw [rev_rev]

/--
theorem `rev_le_iff` / 定理 `rev_le_iff`

English:
theorem rev_le_iff
  given: {i j : Fin n}
  statement: rev i <= j ↔ rev j <= i
  proof: by
  rw [← rev_le_rev]; rw [rev_rev]

中文:
定理 rev_le_iff
  条件: {i j : Fin n}
  结论: rev i <= j ↔ rev j <= i
  证明: by
  rw [← rev_le_rev]; rw [rev_rev]

Depends on / 依赖: rev_le_rev, rev_rev
-/
theorem rev_le_iff {i j : Fin n} : rev i <= j ↔ rev j <= i := by
  rw [← rev_le_rev]; rw [rev_rev]

/--
theorem `lt_rev_iff` / 定理 `lt_rev_iff`

English:
theorem lt_rev_iff
  given: {i j : Fin n}
  statement: i < rev j ↔ j < rev i
  proof: by
  rw [← rev_lt_rev]; rw [rev_rev]

中文:
定理 lt_rev_iff
  条件: {i j : Fin n}
  结论: i < rev j ↔ j < rev i
  证明: by
  rw [← rev_lt_rev]; rw [rev_rev]

Depends on / 依赖: rev_lt_rev, rev_rev
-/
theorem lt_rev_iff {i j : Fin n} : i < rev j ↔ j < rev i := by
  rw [← rev_lt_rev]; rw [rev_rev]

/--
theorem `le_rev_iff` / 定理 `le_rev_iff`

English:
theorem le_rev_iff
  given: {i j : Fin n}
  statement: i <= rev j ↔ j <= rev i
  proof: by
  rw [← rev_le_rev]; rw [rev_rev]

中文:
定理 le_rev_iff
  条件: {i j : Fin n}
  结论: i <= rev j ↔ j <= rev i
  证明: by
  rw [← rev_le_rev]; rw [rev_rev]

Depends on / 依赖: rev_le_rev, rev_rev
-/
theorem le_rev_iff {i j : Fin n} : i <= rev j ↔ j <= rev i := by
  rw [← rev_le_rev]; rw [rev_rev]

/--
theorem `val_rev_zero` / 定理 `val_rev_zero`

English:
theorem val_rev_zero
  given: [NeZero n]
  statement: ((rev 0 : Fin n) : Nat) = n.pred
  proof: rfl

中文:
定理 val_rev_zero
  条件: [NeZero n]
  结论: ((rev 0 : Fin n) : 自然数) = n.pred
  证明: rfl
-/
theorem val_rev_zero [NeZero n] : ((rev 0 : Fin n) : Nat) = n.pred := rfl

/--
theorem `rev_pred` / 定理 `rev_pred`

English:
theorem rev_pred
  given: {i : Fin (n + 1)} (h : i != 0) (h' := rev_ne_iff.mpr ((rev_last _).symm ▸ h))
  proof: by
  rw [← castSucc_inj]; rw [castSucc_castPred]; rw [← rev_succ]; rw [succ_pred]

中文:
定理 rev_pred
  条件: {i : Fin (n + 1)} (h : i != 0) (h' := rev_ne_iff.mpr ((rev_last _).symm ▸ h))
  证明: by
  rw [← castSucc_inj]; rw [castSucc_castPred]; rw [← rev_succ]; rw [succ_pred]

Depends on / 依赖: rev_last, rev_ne_iff, rev_ne_iff.mpr
-/
theorem rev_pred {i : Fin (n + 1)} (h : i != 0) (h' := rev_ne_iff.mpr ((rev_last _).symm ▸ h)) :
    rev (pred i h) = castPred (rev i) h' := by
  rw [← castSucc_inj]; rw [castSucc_castPred]; rw [← rev_succ]; rw [succ_pred]

/--
theorem `rev_castPred` / 定理 `rev_castPred`

English:
theorem rev_castPred
  statement: {i : Fin (n + 1)}
  proof: by
  rw [← succ_inj]; rw [succ_pred]; rw [← rev_castSucc]; rw [castSucc_castPred]

中文:
定理 rev_castPred
  结论: {i : Fin (n + 1)}
  证明: by
  rw [← succ_inj]; rw [succ_pred]; rw [← rev_castSucc]; rw [castSucc_castPred]

Depends on / 依赖: rev_ne_iff, rev_ne_iff.mpr, rev_zero
-/
theorem rev_castPred {i : Fin (n + 1)}
    (h : i != last n) (h' := rev_ne_iff.mpr ((rev_zero _).symm ▸ h)) :
    rev (castPred i h) = pred (rev i) h' := by
  rw [← succ_inj]; rw [succ_pred]; rw [← rev_castSucc]; rw [castSucc_castPred]

/--
lemma `succAbove_rev_left` / 引理 `succAbove_rev_left`

English:
lemma succAbove_rev_left
  given: (p : Fin (n + 1)) (i : Fin n)
  proof: by
  obtain h | h := (rev p).succ_le_or_le_castSucc i
  · rw [succAbove_of_succ_le _ _ h,
      succAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), rev_succ, rev_rev]
  · rw [succAbove_of_le_castSucc _ _ h,
      succAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev_le_iff.mpr h)), rev_castSuc

中文:
引理 succAbove_rev_left
  条件: (p : Fin (n + 1)) (i : Fin n)
  证明: by
  obtain h | h := (rev p).succ_le_or_le_castSucc i
  · rw [succAbove_of_succ_le _ _ h,
      succAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), rev_succ, rev_rev]
  · rw [succAbove_of_le_castSucc _ _ h,
      succAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev_le_iff.mpr h)), rev_castSuc

Depends on / 依赖: le_rev_iff, le_rev_iff.mpr, rev_castSucc, rev_le_iff, rev_le_iff.mpr, rev_rev, rev_succ, succAbove_of_le_castSucc, succAbove_of_succ_le, succ_le_or_le_castSucc
-/
lemma succAbove_rev_left (p : Fin (n + 1)) (i : Fin n) :
    p.rev.succAbove i = (p.succAbove i.rev).rev := by
  obtain h | h := (rev p).succ_le_or_le_castSucc i
  · rw [succAbove_of_succ_le _ _ h,
      succAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), rev_succ, rev_rev]
  · rw [succAbove_of_le_castSucc _ _ h,
      succAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev_le_iff.mpr h)), rev_castSucc, rev_rev]

/--
lemma `succAbove_rev_right` / 引理 `succAbove_rev_right`

English:
lemma succAbove_rev_right
  given: (p : Fin (n + 1)) (i : Fin n)
  proof: by rw [succAbove_rev_left, rev_rev]

中文:
引理 succAbove_rev_right
  条件: (p : Fin (n + 1)) (i : Fin n)
  证明: by rw [succAbove_rev_left, rev_rev]

Depends on / 依赖: rev_rev, succAbove_rev_left
-/
lemma succAbove_rev_right (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i.rev = (p.rev.succAbove i).rev := by rw [succAbove_rev_left, rev_rev]

/--
lemma `rev_succAbove` / 引理 `rev_succAbove`

English:
lemma rev_succAbove
  given: (p : Fin (n + 1)) (i : Fin n)
  proof: by
  rw [succAbove_rev_left]; rw [rev_rev]

中文:
引理 rev_succAbove
  条件: (p : Fin (n + 1)) (i : Fin n)
  证明: by
  rw [succAbove_rev_left]; rw [rev_rev]

Depends on / 依赖: rev_rev, succAbove_rev_left
-/
lemma rev_succAbove (p : Fin (n + 1)) (i : Fin n) :
    rev (succAbove p i) = succAbove (rev p) (rev i) := by
  rw [succAbove_rev_left]; rw [rev_rev]

/--
lemma `predAbove_rev_left` / 引理 `predAbove_rev_left`

English:
lemma predAbove_rev_left
  given: (p : Fin n) (i : Fin (n + 1))
  proof: by
  obtain h | h := (rev i).succ_le_or_le_castSucc p
  · rw [predAbove_of_succ_le _ _ h, rev_pred,
      predAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), castPred_inj, rev_rev]
  · rw [predAbove_of_le_castSucc _ _ h, rev_castPred,
      predAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev

中文:
引理 predAbove_rev_left
  条件: (p : Fin n) (i : Fin (n + 1))
  证明: by
  obtain h | h := (rev i).succ_le_or_le_castSucc p
  · rw [predAbove_of_succ_le _ _ h, rev_pred,
      predAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), castPred_inj, rev_rev]
  · rw [predAbove_of_le_castSucc _ _ h, rev_castPred,
      predAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev

Depends on / 依赖: castPred_inj, le_rev_iff, le_rev_iff.mpr, predAbove_of_le_castSucc, predAbove_of_succ_le, pred_inj, rev_castPred, rev_castSucc, rev_le_iff, rev_le_iff.mpr, rev_pred, rev_rev, rev_succ, succ_le_or_le_castSucc
-/
lemma predAbove_rev_left (p : Fin n) (i : Fin (n + 1)) :
    p.rev.predAbove i = (p.predAbove i.rev).rev := by
  obtain h | h := (rev i).succ_le_or_le_castSucc p
  · rw [predAbove_of_succ_le _ _ h, rev_pred,
      predAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), castPred_inj, rev_rev]
  · rw [predAbove_of_le_castSucc _ _ h, rev_castPred,
      predAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev_le_iff.mpr h)), pred_inj, rev_rev]

/--
lemma `predAbove_rev_right` / 引理 `predAbove_rev_right`

English:
lemma predAbove_rev_right
  given: (p : Fin n) (i : Fin (n + 1))
  proof: by rw [predAbove_rev_left, rev_rev]

中文:
引理 predAbove_rev_right
  条件: (p : Fin n) (i : Fin (n + 1))
  证明: by rw [predAbove_rev_left, rev_rev]

Depends on / 依赖: predAbove_rev_left, rev_rev
-/
lemma predAbove_rev_right (p : Fin n) (i : Fin (n + 1)) :
    p.predAbove i.rev = (p.rev.predAbove i).rev := by rw [predAbove_rev_left, rev_rev]

/--
lemma `rev_predAbove` / 引理 `rev_predAbove`

English:
lemma rev_predAbove
  given: {n : Nat} (p : Fin n) (i : Fin (n + 1))
  proof: by rw [predAbove_rev_left, rev_rev]

中文:
引理 rev_predAbove
  条件: {n : 自然数} (p : Fin n) (i : Fin (n + 1))
  证明: by rw [predAbove_rev_left, rev_rev]

Depends on / 依赖: predAbove_rev_left, rev_rev
-/
lemma rev_predAbove {n : Nat} (p : Fin n) (i : Fin (n + 1)) :
    (predAbove p i).rev = predAbove p.rev i.rev := by rw [predAbove_rev_left, rev_rev]

/--
lemma `add_rev_cast` / 引理 `add_rev_cast`

English:
lemma add_rev_cast
  given: (j : Fin (n + 1))
  statement: j.1 + j.rev.1 = n
  proof: by
  obtain ⟨j, hj⟩ := j
  simp [Nat.add_sub_cancel' <| le_of_lt_succ hj]

中文:
引理 add_rev_cast
  条件: (j : Fin (n + 1))
  结论: j.1 + j.rev.1 = n
  证明: by
  obtain ⟨j, hj⟩ := j
  simp [Nat.add_sub_cancel' <| le_of_lt_succ hj]

Depends on / 依赖: Nat.add_sub_cancel, add_sub_cancel, le_of_lt_succ
-/
lemma add_rev_cast (j : Fin (n + 1)) : j.1 + j.rev.1 = n := by
  obtain ⟨j, hj⟩ := j
  simp [Nat.add_sub_cancel' <| le_of_lt_succ hj]

/--
lemma `rev_add_cast` / 引理 `rev_add_cast`

English:
lemma rev_add_cast
  given: (j : Fin (n + 1))
  statement: j.rev.1 + j.1 = n
  proof: by
  rw [Nat.add_comm]; rw [j.add_rev_cast]

中文:
引理 rev_add_cast
  条件: (j : Fin (n + 1))
  结论: j.rev.1 + j.1 = n
  证明: by
  rw [Nat.add_comm]; rw [j.add_rev_cast]

Depends on / 依赖: Nat.add_comm, add_comm, add_rev_cast, j.add_rev_cast
-/
lemma rev_add_cast (j : Fin (n + 1)) : j.rev.1 + j.1 = n := by
  rw [Nat.add_comm]; rw [j.add_rev_cast]

end Fin
