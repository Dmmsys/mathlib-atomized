/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ComplexShape

/-!
# Complex shapes for pages of spectral sequences

In this file, we define complex shapes which correspond
to pages of spectral sequences:
* `ComplexShape.spectralSequenceNat`: for any `u : ℤ × ℤ`, this
is the complex shape on `ℕ × ℕ` corresponding to differentials
of `ComplexShape.up' u : ComplexShape (ℤ × ℤ)` with source
and target in `ℕ × ℕ`. (With `u := (r, 1 - r)`, this will
apply to the `r`th-page of first quadrant `E₂` cohomological
spectral sequence).
* `ComplexShape.spectralSequenceFin`: for any `u : ℤ × ℤ` and `l : ℕ`,
this is a similar definition as `ComplexShape.spectralSequenceNat`
but for `ℤ × Fin l` (identified as a subset of `ℤ × ℤ`). (This could
be used for spectral sequences associated to a *finite* filtration.)

-/

@[expose] public section

namespace ComplexShape

/--
Definition of `spectralSequenceNat` / `spectralSequenceNat` 的定义

English:
definition spectralSequenceNat
  signature: (u : Int × Int)
  body: a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2
  next_eq _ _ := by ext <;> lia
  prev_eq _ _ := by ext <;> lia

@[simp]

中文:
定义 spectralSequence自然数
  签名: (u : 整数 × 整数)
  定义体: a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2
  next_eq _ _ := by ext <;> lia
  prev_eq _ _ := by ext <;> lia

@[simp]
-/
def spectralSequenceNat (u : Int × Int) : ComplexShape (Nat × Nat) where
  Rel a b := a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2
  next_eq _ _ := by ext <;> lia
  prev_eq _ _ := by ext <;> lia

@[simp]
/--
lemma `spectralSequenceNat_rel_iff` / 引理 `spectralSequenceNat_rel_iff`

English:
lemma spectralSequenceNat_rel_iff
  given: (u : Int × Int) (a b : Nat × Nat)
  proof: Iff.rfl

中文:
引理 spectralSequence自然数_rel_iff
  条件: (u : 整数 × 整数) (a b : 自然数 × 自然数)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma spectralSequenceNat_rel_iff (u : Int × Int) (a b : Nat × Nat) :
    (spectralSequenceNat u).Rel a b ↔ a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2 := Iff.rfl

/--
Definition of `spectralSequenceFin` / `spectralSequenceFin` 的定义

English:
definition spectralSequenceFin
  signature: (l : Nat) (u : Int × Int)
  body: a.1 + u.1 = b.1 ∧ a.2.1 + u.2 = b.2.1
  next_eq _ _ := by ext <;> lia
  prev_eq _ _ := by ext <;> lia

@[simp]

中文:
定义 spectralSequenceFin
  签名: (l : 自然数) (u : 整数 × 整数)
  定义体: a.1 + u.1 = b.1 ∧ a.2.1 + u.2 = b.2.1
  next_eq _ _ := by ext <;> lia
  prev_eq _ _ := by ext <;> lia

@[simp]
-/
def spectralSequenceFin (l : Nat) (u : Int × Int) : ComplexShape (Int × Fin l) where
  Rel a b := a.1 + u.1 = b.1 ∧ a.2.1 + u.2 = b.2.1
  next_eq _ _ := by ext <;> lia
  prev_eq _ _ := by ext <;> lia

@[simp]
/--
lemma `spectralSequenceFin_rel_iff` / 引理 `spectralSequenceFin_rel_iff`

English:
lemma spectralSequenceFin_rel_iff
  given: {l : Nat} (u : Int × Int) (a b : Int × Fin l)
  proof: Iff.rfl

中文:
引理 spectralSequenceFin_rel_iff
  条件: {l : 自然数} (u : 整数 × 整数) (a b : 整数 × 有限集 l)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma spectralSequenceFin_rel_iff {l : Nat} (u : Int × Int) (a b : Int × Fin l) :
    (spectralSequenceFin l u).Rel a b ↔ a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2 := Iff.rfl

end ComplexShape
