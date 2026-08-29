/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about pointwise operations in the presence of `Multiplicative` and `Additive`.
-/

public section

open scoped Pointwise

variable {M : Type*}

namespace Multiplicative

variable [AddMonoid M]

@[simp]
/--
lemma `ofAdd_image_setAdd` / 引理 `ofAdd_image_setAdd`

English:
lemma ofAdd_image_setAdd
  given: (s t : Set M)
  proof: by
  rw [← Set.image2_add]; rw [Set.image_image2_distrib ofAdd_add]; rw [Set.image2_mul]

@[simp]

中文:
引理 ofAdd_image_setAdd
  条件: (s t : Set M)
  证明: by
  rw [← Set.image2_add]; rw [Set.image_image2_distrib ofAdd_add]; rw [Set.image2_mul]

@[simp]

Depends on / 依赖: Set.image2_add, Set.image2_mul, Set.image_image2_distrib, image2_add, image2_mul, image_image2_distrib, ofAdd_add
-/
lemma ofAdd_image_setAdd (s t : Set M) :
    ofAdd '' (s + t) = ofAdd '' s * ofAdd '' t := by
  rw [← Set.image2_add]; rw [Set.image_image2_distrib ofAdd_add]; rw [Set.image2_mul]

@[simp]
/--
lemma `ofAdd_image_nsmul` / 引理 `ofAdd_image_nsmul`

English:
lemma ofAdd_image_nsmul
  given: (n : Nat) (s : Set M)
  proof: by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

@[simp]

中文:
引理 ofAdd_image_nsmul
  条件: (n : 自然数) (s : Set M)
  证明: by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

@[simp]

Depends on / 依赖: pow_succ, succ_nsmul
-/
lemma ofAdd_image_nsmul (n : Nat) (s : Set M) :
    ofAdd '' (n • s) = (ofAdd '' s) ^ n := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

@[simp]
/--
lemma `toAdd_image_setMul` / 引理 `toAdd_image_setMul`

English:
lemma toAdd_image_setMul
  given: (s t : Set (Multiplicative M))
  proof: by
  rw [← Set.image2_mul]; rw [Set.image_image2_distrib toAdd_mul]; rw [Set.image2_add]

@[simp]

中文:
引理 toAdd_image_setMul
  条件: (s t : Set (Multiplicative M))
  证明: by
  rw [← Set.image2_mul]; rw [Set.image_image2_distrib toAdd_mul]; rw [Set.image2_add]

@[simp]

Depends on / 依赖: Set.image2_add, Set.image2_mul, Set.image_image2_distrib, image2_add, image2_mul, image_image2_distrib, toAdd_mul
-/
lemma toAdd_image_setMul (s t : Set (Multiplicative M)) :
    toAdd '' (s * t) = (toAdd '' s) + (toAdd '' t) := by
  rw [← Set.image2_mul]; rw [Set.image_image2_distrib toAdd_mul]; rw [Set.image2_add]

@[simp]
/--
lemma `toAdd_image_nsmul` / 引理 `toAdd_image_nsmul`

English:
lemma toAdd_image_nsmul
  given: (n : Nat) (s : Set (Multiplicative M))
  proof: by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

中文:
引理 toAdd_image_nsmul
  条件: (n : 自然数) (s : Set (Multiplicative M))
  证明: by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

Depends on / 依赖: pow_succ, succ_nsmul
-/
lemma toAdd_image_nsmul (n : Nat) (s : Set (Multiplicative M)) :
    toAdd '' (s ^ n) = n • (toAdd '' s) := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

end Multiplicative
