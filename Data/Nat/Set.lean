/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image

/-!
### Recursion on the natural numbers and `Set.range`
-/

public section


namespace Nat

section Set

open Set

/--
theorem `zero_union_range_succ` / 定理 `zero_union_range_succ`

English:
theorem zero_union_range_succ
  statement: {0} union range succ = univ
  proof: by
  ext n
  cases n <;> simp

@[simp]

中文:
定理 zero_union_range_succ
  结论: {0} union range succ = univ
  证明: by
  ext n
  cases n <;> simp

@[simp]
-/
theorem zero_union_range_succ : {0} union range succ = univ := by
  ext n
  cases n <;> simp

@[simp]
/--
theorem `range_succ` / 定理 `range_succ`

English:
theorem range_succ
  statement: range succ = { i | 0 < i }
  proof: by
  ext (_ | i) <;> simp

中文:
定理 range_succ
  结论: range succ = { i | 0 < i }
  证明: by
  ext (_ | i) <;> simp
-/
protected theorem range_succ : range succ = { i | 0 < i } := by
  ext (_ | i) <;> simp

variable {α : Type*}

/--
theorem `range_of_succ` / 定理 `range_of_succ`

English:
theorem range_of_succ
  given: (f : Nat -> α)
  statement: {f 0} union range (f ∘ succ) = range f
  proof: by
  rw [← image_singleton]; rw [range_comp]; rw [← image_union]; rw [zero_union_range_succ]; rw [image_univ]

中文:
定理 range_of_succ
  条件: (f : 自然数 -> α)
  结论: {f 0} union range (f ∘ succ) = range f
  证明: by
  rw [← image_singleton]; rw [range_comp]; rw [← image_union]; rw [zero_union_range_succ]; rw [image_univ]

Depends on / 依赖: image_singleton, image_union, image_univ, range_comp, zero_union_range_succ
-/
theorem range_of_succ (f : Nat -> α) : {f 0} union range (f ∘ succ) = range f := by
  rw [← image_singleton]; rw [range_comp]; rw [← image_union]; rw [zero_union_range_succ]; rw [image_univ]

/--
theorem `range_rec` / 定理 `range_rec`

English:
theorem range_rec
  given: {α : Type*} (x : α) (f : Nat -> α -> α)
  proof: by
  convert! (range_of_succ (fun n => Nat.rec x f n : Nat -> α)).symm using 4
  dsimp
  rename_i n
  induction n with
  | zero => rfl
  | succ n ihn => dsimp at ihn ⊢; rw [ihn]

中文:
定理 range_rec
  条件: {α : 类型} (x : α) (f : 自然数 -> α -> α)
  证明: by
  convert! (range_of_succ (fun n => Nat.rec x f n : Nat -> α)).symm using 4
  dsimp
  rename_i n
  induction n with
  | zero => rfl
  | succ n ihn => dsimp at ihn ⊢; rw [ihn]

Depends on / 依赖: Nat.rec, convert, range_of_succ, rename_i
-/
theorem range_rec {α : Type*} (x : α) (f : Nat -> α -> α) :
    (Set.range fun n => Nat.rec x f n : Set α) =
      {x} union Set.range fun n => Nat.rec (f 0 x) (f ∘ succ) n := by
  convert! (range_of_succ (fun n => Nat.rec x f n : Nat -> α)).symm using 4
  dsimp
  rename_i n
  induction n with
  | zero => rfl
  | succ n ihn => dsimp at ihn ⊢; rw [ihn]

/--
theorem `range_casesOn` / 定理 `range_casesOn`

English:
theorem range_casesOn
  given: {α : Type*} (x : α) (f : Nat -> α)
  proof: (range_of_succ _).symm

中文:
定理 range_casesOn
  条件: {α : 类型} (x : α) (f : 自然数 -> α)
  证明: (range_of_succ _).symm

Depends on / 依赖: range_of_succ
-/
theorem range_casesOn {α : Type*} (x : α) (f : Nat -> α) :
    (Set.range fun n => Nat.casesOn n x f : Set α) = {x} union Set.range f :=
  (range_of_succ _).symm

end Set

end Nat
