/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Tactic.Push

/-!
# Results about `IsRegular` and `0`
-/

public section

variable {R}

section MulZeroClass
variable [MulZeroClass R] {a b : R}

/--
theorem `IsLeftRegular.subsingleton` / 定理 `IsLeftRegular.subsingleton`

English:
theorem IsLeftRegular.subsingleton
  given: (h : IsLeftRegular (0 : R))
  statement: Subsingleton R
  proof: ⟨fun a b => h Eq.trans (zero_mul a) (zero_mul b).symm⟩

中文:
定理 IsLeftRegular.subsingleton
  条件: (h : IsLeftRegular (0 : R))
  结论: 子单例 R
  证明: ⟨fun a b => h Eq.trans (zero_mul a) (zero_mul b).symm⟩

Depends on / 依赖: Eq.trans, zero_mul
-/
theorem IsLeftRegular.subsingleton (h : IsLeftRegular (0 : R)) : Subsingleton R :=
⟨fun a b => h Eq.trans (zero_mul a) (zero_mul b).symm⟩

/--
theorem `IsRightRegular.subsingleton` / 定理 `IsRightRegular.subsingleton`

English:
theorem IsRightRegular.subsingleton
  given: (h : IsRightRegular (0 : R))
  statement: Subsingleton R
  proof: ⟨fun a b => h Eq.trans (mul_zero a) (mul_zero b).symm⟩

中文:
定理 IsRightRegular.subsingleton
  条件: (h : IsRightRegular (0 : R))
  结论: 子单例 R
  证明: ⟨fun a b => h Eq.trans (mul_zero a) (mul_zero b).symm⟩

Depends on / 依赖: Eq.trans, mul_zero
-/
theorem IsRightRegular.subsingleton (h : IsRightRegular (0 : R)) : Subsingleton R :=
⟨fun a b => h Eq.trans (mul_zero a) (mul_zero b).symm⟩

/--
theorem `IsRegular.subsingleton` / 定理 `IsRegular.subsingleton`

English:
theorem IsRegular.subsingleton
  given: (h : IsRegular (0 : R))
  statement: Subsingleton R
  proof: h.left.subsingleton

中文:
定理 是正则.subsingleton
  条件: (h : 是正则 (0 : R))
  结论: 子单例 R
  证明: h.left.subsingleton

Depends on / 依赖: h.left.subsingleton, subsingleton
-/
theorem IsRegular.subsingleton (h : IsRegular (0 : R)) : Subsingleton R :=
  h.left.subsingleton

/--
theorem `isLeftRegular_zero_iff_subsingleton` / 定理 `isLeftRegular_zero_iff_subsingleton`

English:
theorem isLeftRegular_zero_iff_subsingleton
  statement: IsLeftRegular (0 : R) ↔ Subsingleton R
  proof: ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

中文:
定理 isLeftRegular_zero_iff_subsingleton
  结论: IsLeftRegular (0 : R) ↔ 子单例 R
  证明: ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, h.subsingleton, subsingleton
-/
theorem isLeftRegular_zero_iff_subsingleton : IsLeftRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/--
theorem `not_isLeftRegular_zero_iff` / 定理 `not_isLeftRegular_zero_iff`

English:
theorem not_isLeftRegular_zero_iff
  statement: ¬IsLeftRegular (0 : R) ↔ Nontrivial R
  proof: by
  rw [nontrivial_iff]; rw [not_iff_comm]; rw [isLeftRegular_zero_iff_subsingleton]; rw [subsingleton_iff]
  push Not
  exact Iff.rfl

中文:
定理 not_isLeftRegular_zero_iff
  结论: ¬IsLeftRegular (0 : R) ↔ 非平凡 R
  证明: by
  rw [nontrivial_iff]; rw [not_iff_comm]; rw [isLeftRegular_zero_iff_subsingleton]; rw [subsingleton_iff]
  push Not
  exact Iff.rfl

Depends on / 依赖: Iff.rfl, isLeftRegular_zero_iff_subsingleton, nontrivial_iff, not_iff_comm, subsingleton_iff
-/
theorem not_isLeftRegular_zero_iff : ¬IsLeftRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff]; rw [not_iff_comm]; rw [isLeftRegular_zero_iff_subsingleton]; rw [subsingleton_iff]
  push Not
  exact Iff.rfl

/--
theorem `isRightRegular_zero_iff_subsingleton` / 定理 `isRightRegular_zero_iff_subsingleton`

English:
theorem isRightRegular_zero_iff_subsingleton
  statement: IsRightRegular (0 : R) ↔ Subsingleton R
  proof: ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

中文:
定理 isRightRegular_zero_iff_subsingleton
  结论: IsRightRegular (0 : R) ↔ 子单例 R
  证明: ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, h.subsingleton, subsingleton
-/
theorem isRightRegular_zero_iff_subsingleton : IsRightRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/--
theorem `not_isRightRegular_zero_iff` / 定理 `not_isRightRegular_zero_iff`

English:
theorem not_isRightRegular_zero_iff
  statement: ¬IsRightRegular (0 : R) ↔ Nontrivial R
  proof: by
  rw [nontrivial_iff]; rw [not_iff_comm]; rw [isRightRegular_zero_iff_subsingleton]; rw [subsingleton_iff]
  push Not
  exact Iff.rfl

中文:
定理 not_isRightRegular_zero_iff
  结论: ¬IsRightRegular (0 : R) ↔ 非平凡 R
  证明: by
  rw [nontrivial_iff]; rw [not_iff_comm]; rw [isRightRegular_zero_iff_subsingleton]; rw [subsingleton_iff]
  push Not
  exact Iff.rfl

Depends on / 依赖: Iff.rfl, isRightRegular_zero_iff_subsingleton, nontrivial_iff, not_iff_comm, subsingleton_iff
-/
theorem not_isRightRegular_zero_iff : ¬IsRightRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff]; rw [not_iff_comm]; rw [isRightRegular_zero_iff_subsingleton]; rw [subsingleton_iff]
  push Not
  exact Iff.rfl

/--
theorem `isRegular_iff_subsingleton` / 定理 `isRegular_iff_subsingleton`

English:
theorem isRegular_iff_subsingleton
  statement: IsRegular (0 : R) ↔ Subsingleton R
  proof: ⟨fun h => h.left.subsingleton, fun h =>
    ⟨isLeftRegular_zero_iff_subsingleton.mpr h, isRightRegular_zero_iff_subsingleton.mpr h⟩⟩

中文:
定理 isRegular_iff_subsingleton
  结论: 是正则 (0 : R) ↔ 子单例 R
  证明: ⟨fun h => h.left.subsingleton, fun h =>
    ⟨isLeftRegular_zero_iff_subsingleton.mpr h, isRightRegular_zero_iff_subsingleton.mpr h⟩⟩

Depends on / 依赖: h.left.subsingleton, isLeftRegular_zero_iff_subsingleton, isLeftRegular_zero_iff_subsingleton.mpr, isRightRegular_zero_iff_subsingleton, isRightRegular_zero_iff_subsingleton.mpr, subsingleton
-/
theorem isRegular_iff_subsingleton : IsRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.left.subsingleton, fun h =>
    ⟨isLeftRegular_zero_iff_subsingleton.mpr h, isRightRegular_zero_iff_subsingleton.mpr h⟩⟩

/--
theorem `IsLeftRegular.ne_zero` / 定理 `IsLeftRegular.ne_zero`

English:
theorem IsLeftRegular.ne_zero
  given: [Nontrivial R] (la : IsLeftRegular a)
  statement: a != 0
  proof: by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (la ?_)
  simp

中文:
定理 IsLeftRegular.ne_zero
  条件: [非平凡 R] (la : IsLeftRegular a)
  结论: a != 0
  证明: by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (la ?_)
  simp

Depends on / 依赖: exists_pair_ne
-/
theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a != 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (la ?_)
  simp

/--
theorem `IsRightRegular.ne_zero` / 定理 `IsRightRegular.ne_zero`

English:
theorem IsRightRegular.ne_zero
  given: [Nontrivial R] (ra : IsRightRegular a)
  statement: a != 0
  proof: by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (ra ?_)
  simp

中文:
定理 IsRightRegular.ne_zero
  条件: [非平凡 R] (ra : IsRightRegular a)
  结论: a != 0
  证明: by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (ra ?_)
  simp

Depends on / 依赖: exists_pair_ne
-/
theorem IsRightRegular.ne_zero [Nontrivial R] (ra : IsRightRegular a) : a != 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (ra ?_)
  simp

/--
theorem `IsRegular.ne_zero` / 定理 `IsRegular.ne_zero`

English:
theorem IsRegular.ne_zero
  given: [Nontrivial R] (la : IsRegular a)
  statement: a != 0
  proof: la.left.ne_zero

中文:
定理 是正则.ne_zero
  条件: [非平凡 R] (la : 是正则 a)
  结论: a != 0
  证明: la.left.ne_zero

Depends on / 依赖: la.left.ne_zero, ne_zero
-/
theorem IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) : a != 0 :=
  la.left.ne_zero

/--
theorem `not_isLeftRegular_zero` / 定理 `not_isLeftRegular_zero`

English:
theorem not_isLeftRegular_zero
  given: [nR : Nontrivial R]
  statement: ¬IsLeftRegular (0 : R)
  proof: not_isLeftRegular_zero_iff.mpr nR

中文:
定理 not_isLeftRegular_zero
  条件: [nR : 非平凡 R]
  结论: ¬IsLeftRegular (0 : R)
  证明: not_isLeftRegular_zero_iff.mpr nR

Depends on / 依赖: not_isLeftRegular_zero_iff, not_isLeftRegular_zero_iff.mpr
-/
theorem not_isLeftRegular_zero [nR : Nontrivial R] : ¬IsLeftRegular (0 : R) :=
  not_isLeftRegular_zero_iff.mpr nR

/--
theorem `not_isRightRegular_zero` / 定理 `not_isRightRegular_zero`

English:
theorem not_isRightRegular_zero
  given: [nR : Nontrivial R]
  statement: ¬IsRightRegular (0 : R)
  proof: not_isRightRegular_zero_iff.mpr nR

中文:
定理 not_isRightRegular_zero
  条件: [nR : 非平凡 R]
  结论: ¬IsRightRegular (0 : R)
  证明: not_isRightRegular_zero_iff.mpr nR

Depends on / 依赖: not_isRightRegular_zero_iff, not_isRightRegular_zero_iff.mpr
-/
theorem not_isRightRegular_zero [nR : Nontrivial R] : ¬IsRightRegular (0 : R) :=
  not_isRightRegular_zero_iff.mpr nR

/--
theorem `not_isRegular_zero` / 定理 `not_isRegular_zero`

English:
theorem not_isRegular_zero
  given: [Nontrivial R]
  statement: ¬IsRegular (0 : R)
  proof: fun h => IsRegular.ne_zero h rfl

中文:
定理 not_isRegular_zero
  条件: [非平凡 R]
  结论: ¬是正则 (0 : R)
  证明: fun h => IsRegular.ne_zero h rfl

Depends on / 依赖: IsRegular, IsRegular.ne_zero, ne_zero
-/
theorem not_isRegular_zero [Nontrivial R] : ¬IsRegular (0 : R) := fun h => IsRegular.ne_zero h rfl

/--
lemma `IsLeftRegular.mul_left_eq_zero_iff` / 引理 `IsLeftRegular.mul_left_eq_zero_iff`

English:
lemma IsLeftRegular.mul_left_eq_zero_iff
  given: (hb : IsLeftRegular b)
  statement: b * a = 0 ↔ a = 0
  proof: by
  conv_lhs => rw [← mul_zero b]
  exact ⟨fun h => hb h, fun ha => by rw [ha]⟩

中文:
引理 IsLeftRegular.mul_left_eq_zero_iff
  条件: (hb : IsLeftRegular b)
  结论: b * a = 0 ↔ a = 0
  证明: by
  conv_lhs => rw [← mul_zero b]
  exact ⟨fun h => hb h, fun ha => by rw [ha]⟩
-/
@[simp] lemma IsLeftRegular.mul_left_eq_zero_iff (hb : IsLeftRegular b) : b * a = 0 ↔ a = 0 := by
  conv_lhs => rw [← mul_zero b]
  exact ⟨fun h => hb h, fun ha => by rw [ha]⟩

/--
lemma `IsRightRegular.mul_right_eq_zero_iff` / 引理 `IsRightRegular.mul_right_eq_zero_iff`

English:
lemma IsRightRegular.mul_right_eq_zero_iff
  given: (hb : IsRightRegular b)
  statement: a * b = 0 ↔ a = 0
  proof: by
  conv_lhs => rw [← zero_mul b]
  exact ⟨fun h => hb h, fun ha => by rw [ha]⟩

中文:
引理 IsRightRegular.mul_right_eq_zero_iff
  条件: (hb : IsRightRegular b)
  结论: a * b = 0 ↔ a = 0
  证明: by
  conv_lhs => rw [← zero_mul b]
  exact ⟨fun h => hb h, fun ha => by rw [ha]⟩
-/
@[simp] lemma IsRightRegular.mul_right_eq_zero_iff (hb : IsRightRegular b) : a * b = 0 ↔ a = 0 := by
  conv_lhs => rw [← zero_mul b]
  exact ⟨fun h => hb h, fun ha => by rw [ha]⟩

end MulZeroClass

section CancelMonoidWithZero
variable [MulZeroClass R] [IsCancelMulZero R] {a : R}

/--
theorem `IsRegular.of_ne_zero` / 定理 `IsRegular.of_ne_zero`

English:
theorem IsRegular.of_ne_zero
  given: (a0 : a != 0)
  statement: IsRegular a
  proof: ⟨fun _ _ => mul_left_cancel₀ a0, fun _ _ => mul_right_cancel₀ a0⟩

@[deprecated (since := "2026-01-21")] alias isRegular_of_ne_zero := IsRegular.of_ne_zero

中文:
定理 是正则.of_ne_zero
  条件: (a0 : a != 0)
  结论: 是正则 a
  证明: ⟨fun _ _ => mul_left_cancel₀ a0, fun _ _ => mul_right_cancel₀ a0⟩

@[deprecated (since := "2026-01-21")] alias isRegular_of_ne_zero := IsRegular.of_ne_zero
-/
theorem IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a :=
  ⟨fun _ _ => mul_left_cancel₀ a0, fun _ _ => mul_right_cancel₀ a0⟩

@[deprecated (since := "2026-01-21")] alias isRegular_of_ne_zero := IsRegular.of_ne_zero

/--
theorem `isRegular_iff_ne_zero` / 定理 `isRegular_iff_ne_zero`

English:
theorem isRegular_iff_ne_zero
  given: [Nontrivial R]
  statement: IsRegular a ↔ a != 0
  proof: ⟨IsRegular.ne_zero, .of_ne_zero⟩

中文:
定理 isRegular_iff_ne_zero
  条件: [非平凡 R]
  结论: 是正则 a ↔ a != 0
  证明: ⟨IsRegular.ne_zero, .of_ne_zero⟩

Depends on / 依赖: IsRegular, IsRegular.ne_zero, ne_zero, of_ne_zero
-/
theorem isRegular_iff_ne_zero [Nontrivial R] : IsRegular a ↔ a != 0 :=
  ⟨IsRegular.ne_zero, .of_ne_zero⟩

end CancelMonoidWithZero
