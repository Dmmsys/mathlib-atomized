/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.Nat.Basic

/-!
# zip & unzip

This file provides results about `List.zipWith`, `List.zip` and `List.unzip` (definitions are in
core Lean).
`zipWith f l₁ l₂` applies `f : α → β → γ` pointwise to a list `l₁ : List α` and `l₂ : List β`. It
applies, until one of the lists is exhausted. For example,
`zipWith f [0, 1, 2] [6.28, 31] = [f 0 6.28, f 1 31]`.
`zip` is `zipWith` applied to `Prod.mk`. For example,
`zip [a₁, a₂] [b₁, b₂, b₃] = [(a₁, b₁), (a₂, b₂)]`.
`unzip` undoes `zip`. For example, `unzip [(a₁, b₁), (a₂, b₂)] = ([a₁, a₂], [b₁, b₂])`.
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid

universe u

open Nat

namespace List

variable {α : Type u} {β γ δ ε : Type*}

open Function in
/--
theorem `rightInverse_unzip_zip` / 定理 `rightInverse_unzip_zip`

English:
theorem rightInverse_unzip_zip
  proof: by
  grind [zip_unzip]

@[simp]

中文:
定理 rightInverse_unzip_zip
  证明: by
  grind [zip_unzip]

@[simp]

Depends on / 依赖: zip_unzip
-/
theorem rightInverse_unzip_zip :
    RightInverse (unzip : List (α × β) -> List α × List β) (uncurry zip) := by
  grind [zip_unzip]

@[simp]
/--
theorem `zip_swap` / 定理 `zip_swap`

English:
theorem zip_swap
  statement: forall (l₁ : List α) (l₂ : List β), (zip l₁ l₂).map Prod.swap = zip l₂ l₁

中文:
定理 zip_swap
  结论: 对任意 (l₁ : 列表 α) (l₂ : 列表 β), (zip l₁ l₂).map 积类型.swap = zip l₂ l₁
-/
theorem zip_swap : forall (l₁ : List α) (l₂ : List β), (zip l₁ l₂).map Prod.swap = zip l₂ l₁
  | [], _ => zip_nil_right.symm
  | l₁, [] => by rw [zip_nil_right]; rfl
  | a :: l₁, b :: l₂ => by
    simp only [zip_cons_cons, map_cons, zip_swap l₁ l₂, Prod.swap_prod_mk]

/--
theorem `forall_zipWith` / 定理 `forall_zipWith`

English:
theorem forall_zipWith
  given: {f : α -> β -> γ} {p : γ -> Prop}

中文:
定理 对任意_zipWith
  条件: {f : α -> β -> γ} {p : γ -> 命题}
-/
theorem forall_zipWith {f : α -> β -> γ} {p : γ -> Prop} :
    forall {l₁ : List α} {l₂ : List β}, length l₁ = length l₂ ->
      (Forall p (zipWith f l₁ l₂) ↔ Forall₂ (fun x y => p (f x y)) l₁ l₂)
  | [], [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [length_cons, succ_inj] at h
    simp [forall_zipWith h]

/--
theorem `unzip_swap` / 定理 `unzip_swap`

English:
theorem unzip_swap
  given: (l : List (α × β))
  statement: unzip (l.map Prod.swap) = (unzip l).swap
  proof: by
  simp only [unzip_eq_map, map_map]
  rfl

@[congr]

中文:
定理 unzip_swap
  条件: (l : 列表 (α × β))
  结论: unzip (l.map 积类型.swap) = (unzip l).swap
  证明: by
  simp only [unzip_eq_map, map_map]
  rfl

@[congr]

Depends on / 依赖: map_map, unzip_eq_map
-/
theorem unzip_swap (l : List (α × β)) : unzip (l.map Prod.swap) = (unzip l).swap := by
  simp only [unzip_eq_map, map_map]
  rfl

@[congr]
/--
theorem `zipWith_congr` / 定理 `zipWith_congr`

English:
theorem zipWith_congr
  statement: (f g : α -> β -> γ) (la : List α) (lb : List β)
  proof: by
  induction h with
  | nil => rfl
  | cons hfg _ ih => exact congr_arg₂ _ hfg ih

中文:
定理 zipWith_congr
  结论: (f g : α -> β -> γ) (la : 列表 α) (lb : 列表 β)
  证明: by
  induction h with
  | nil => rfl
  | cons hfg _ ih => exact congr_arg₂ _ hfg ih
-/
theorem zipWith_congr (f g : α -> β -> γ) (la : List α) (lb : List β)
    (h : List.Forall₂ (fun a b => f a b = g a b) la lb) : zipWith f la lb = zipWith g la lb := by
  induction h with
  | nil => rfl
  | cons hfg _ ih => exact congr_arg₂ _ hfg ih

/--
theorem `zipWith_zipWith_left` / 定理 `zipWith_zipWith_left`

English:
theorem zipWith_zipWith_left
  given: (f : δ -> γ -> ε) (g : α -> β -> δ)

中文:
定理 zipWith_zipWith_left
  条件: (f : δ -> γ -> ε) (g : α -> β -> δ)
-/
theorem zipWith_zipWith_left (f : δ -> γ -> ε) (g : α -> β -> δ) :
    forall (la : List α) (lb : List β) (lc : List γ),
      zipWith f (zipWith g la lb) lc = zipWith3 (fun a b c => f (g a b) c) la lb lc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
| _ :: as, _ :: bs, _ :: cs => congr_arg (cons _) zipWith_zipWith_left f g as bs cs

/--
theorem `zipWith_zipWith_right` / 定理 `zipWith_zipWith_right`

English:
theorem zipWith_zipWith_right
  given: (f : α -> δ -> ε) (g : β -> γ -> δ)

中文:
定理 zipWith_zipWith_right
  条件: (f : α -> δ -> ε) (g : β -> γ -> δ)
-/
theorem zipWith_zipWith_right (f : α -> δ -> ε) (g : β -> γ -> δ) :
    forall (la : List α) (lb : List β) (lc : List γ),
      zipWith f la (zipWith g lb lc) = zipWith3 (fun a b c => f a (g b c)) la lb lc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
| _ :: as, _ :: bs, _ :: cs => congr_arg (cons _) zipWith_zipWith_right f g as bs cs

@[simp]
/--
theorem `zipWith3_same_left` / 定理 `zipWith3_same_left`

English:
theorem zipWith3_same_left
  given: (f : α -> α -> β -> γ)

中文:
定理 zipWith3_same_left
  条件: (f : α -> α -> β -> γ)
-/
theorem zipWith3_same_left (f : α -> α -> β -> γ) :
    forall (la : List α) (lb : List β), zipWith3 f la la lb = zipWith (fun a b => f a a b) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
| _ :: as, _ :: bs => congr_arg (cons _) zipWith3_same_left f as bs

@[simp]
/--
theorem `zipWith3_same_mid` / 定理 `zipWith3_same_mid`

English:
theorem zipWith3_same_mid
  given: (f : α -> β -> α -> γ)

中文:
定理 zipWith3_same_mid
  条件: (f : α -> β -> α -> γ)
-/
theorem zipWith3_same_mid (f : α -> β -> α -> γ) :
    forall (la : List α) (lb : List β), zipWith3 f la lb la = zipWith (fun a b => f a b a) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
| _ :: as, _ :: bs => congr_arg (cons _) zipWith3_same_mid f as bs

@[simp]
/--
theorem `zipWith3_same_right` / 定理 `zipWith3_same_right`

English:
theorem zipWith3_same_right
  given: (f : α -> β -> β -> γ)

中文:
定理 zipWith3_same_right
  条件: (f : α -> β -> β -> γ)
-/
theorem zipWith3_same_right (f : α -> β -> β -> γ) :
    forall (la : List α) (lb : List β), zipWith3 f la lb lb = zipWith (fun a b => f a b b) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
| _ :: as, _ :: bs => congr_arg (cons _) zipWith3_same_right f as bs

instance (f : α -> α -> β) [IsSymmOp f] : IsSymmOp (zipWith f) :=
  ⟨fun _ _ => zipWith_comm_of_comm IsSymmOp.symm_op⟩

@[simp]
/--
theorem `length_revzip` / 定理 `length_revzip`

English:
theorem length_revzip
  given: (l : List α)
  statement: length (revzip l) = length l
  proof: by
  simp only [revzip, length_zip, length_reverse, min_self]

@[simp]

中文:
定理 length_revzip
  条件: (l : 列表 α)
  结论: length (revzip l) = length l
  证明: by
  simp only [revzip, length_zip, length_reverse, min_self]

@[simp]

Depends on / 依赖: length_reverse, length_zip, min_self, revzip
-/
theorem length_revzip (l : List α) : length (revzip l) = length l := by
  simp only [revzip, length_zip, length_reverse, min_self]

@[simp]
/--
theorem `unzip_revzip` / 定理 `unzip_revzip`

English:
theorem unzip_revzip
  given: (l : List α)
  statement: (revzip l).unzip = (l, l.reverse)
  proof: unzip_zip length_reverse.symm

@[simp]

中文:
定理 unzip_revzip
  条件: (l : 列表 α)
  结论: (revzip l).unzip = (l, l.reverse)
  证明: unzip_zip length_reverse.symm

@[simp]

Depends on / 依赖: length_reverse, length_reverse.symm, unzip_zip
-/
theorem unzip_revzip (l : List α) : (revzip l).unzip = (l, l.reverse) :=
  unzip_zip length_reverse.symm

@[simp]
/--
theorem `revzip_map_fst` / 定理 `revzip_map_fst`

English:
theorem revzip_map_fst
  given: (l : List α)
  statement: (revzip l).map Prod.fst = l
  proof: by
  rw [← unzip_fst]; rw [unzip_revzip]

@[simp]

中文:
定理 revzip_map_fst
  条件: (l : 列表 α)
  结论: (revzip l).map 积类型.fst = l
  证明: by
  rw [← unzip_fst]; rw [unzip_revzip]

@[simp]

Depends on / 依赖: unzip_fst, unzip_revzip
-/
theorem revzip_map_fst (l : List α) : (revzip l).map Prod.fst = l := by
  rw [← unzip_fst]; rw [unzip_revzip]

@[simp]
/--
theorem `revzip_map_snd` / 定理 `revzip_map_snd`

English:
theorem revzip_map_snd
  given: (l : List α)
  statement: (revzip l).map Prod.snd = l.reverse
  proof: by
  rw [← unzip_snd]; rw [unzip_revzip]

中文:
定理 revzip_map_snd
  条件: (l : 列表 α)
  结论: (revzip l).map 积类型.snd = l.reverse
  证明: by
  rw [← unzip_snd]; rw [unzip_revzip]

Depends on / 依赖: unzip_revzip, unzip_snd
-/
theorem revzip_map_snd (l : List α) : (revzip l).map Prod.snd = l.reverse := by
  rw [← unzip_snd]; rw [unzip_revzip]

/--
theorem `reverse_revzip` / 定理 `reverse_revzip`

English:
theorem reverse_revzip
  given: (l : List α)
  statement: reverse l.revzip = revzip l.reverse
  proof: by
  rw [← zip_unzip (revzip l).reverse]
  simp [unzip_eq_map, revzip, map_reverse, map_fst_zip, map_snd_zip]

中文:
定理 reverse_revzip
  条件: (l : 列表 α)
  结论: reverse l.revzip = revzip l.reverse
  证明: by
  rw [← zip_unzip (revzip l).reverse]
  simp [unzip_eq_map, revzip, map_reverse, map_fst_zip, map_snd_zip]

Depends on / 依赖: map_fst_zip, map_reverse, map_snd_zip, reverse, revzip, unzip_eq_map, zip_unzip
-/
theorem reverse_revzip (l : List α) : reverse l.revzip = revzip l.reverse := by
  rw [← zip_unzip (revzip l).reverse]
  simp [unzip_eq_map, revzip, map_reverse, map_fst_zip, map_snd_zip]

/--
theorem `revzip_swap` / 定理 `revzip_swap`

English:
theorem revzip_swap
  given: (l : List α)
  statement: (revzip l).map Prod.swap = revzip l.reverse
  proof: by simp [revzip]

中文:
定理 revzip_swap
  条件: (l : 列表 α)
  结论: (revzip l).map 积类型.swap = revzip l.reverse
  证明: by simp [revzip]

Depends on / 依赖: revzip
-/
theorem revzip_swap (l : List α) : (revzip l).map Prod.swap = revzip l.reverse := by simp [revzip]

/--
theorem `mem_zip_inits_tails` / 定理 `mem_zip_inits_tails`

English:
theorem mem_zip_inits_tails
  given: {l : List α} {init tail : List α}
  proof: by
  induction l generalizing init tail <;> simp_rw [tails, inits, zip_cons_cons]
  case nil => simp
  case cons hd tl ih =>
    constructor <;> rw [mem_cons, zip_map_left, mem_map, Prod.exists]
    · rintro (⟨rfl, rfl⟩ | ⟨_, _, h, rfl, rfl⟩)
      · simp
      · simp [ih.mp h]
    · rcases init wit

中文:
定理 mem_zip_inits_tails
  条件: {l : 列表 α} {init tail : 列表 α}
  证明: by
  induction l generalizing init tail <;> simp_rw [tails, inits, zip_cons_cons]
  case nil => simp
  case cons hd tl ih =>
    constructor <;> rw [mem_cons, zip_map_left, mem_map, Prod.exists]
    · rintro (⟨rfl, rfl⟩ | ⟨_, _, h, rfl, rfl⟩)
      · simp
      · simp [ih.mp h]
    · rcases init wit

Depends on / 依赖: Prod.exists, generalizing, ih.mp, mem_cons, mem_map, simp_rw, zip_cons_cons, zip_map_left
-/
theorem mem_zip_inits_tails {l : List α} {init tail : List α} :
    (init, tail) in zip l.inits l.tails ↔ init ++ tail = l := by
  induction l generalizing init tail <;> simp_rw [tails, inits, zip_cons_cons]
  case nil => simp
  case cons hd tl ih =>
    constructor <;> rw [mem_cons, zip_map_left, mem_map, Prod.exists]
    · rintro (⟨rfl, rfl⟩ | ⟨_, _, h, rfl, rfl⟩)
      · simp
      · simp [ih.mp h]
    · rcases init with - | ⟨hd', tl'⟩
      · simp
      · intro h
        right
        use tl', tail
        simp_all

end List
