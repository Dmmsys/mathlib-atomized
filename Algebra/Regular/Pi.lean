/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and pi types
-/

public section

variable {ι α : Type*} {R : ι -> Type*}

namespace Pi

section
variable [forall i, Mul (R i)]

@[to_additive (attr := simp)]
/--
theorem `isLeftRegular_iff` / 定理 `isLeftRegular_iff`

English:
theorem isLeftRegular_iff
  given: {a : forall i, R i}
  statement: IsLeftRegular a ↔ forall i, IsLeftRegular (a i)
  proof: have (i : _) : Nonempty (R i) := ⟨a i⟩; Pi.map_injective

@[to_additive (attr := simp)]

中文:
定理 isLeftRegular_iff
  条件: {a : 对任意 i, R i}
  结论: IsLeftRegular a ↔ 对任意 i, IsLeftRegular (a i)
  证明: have (i : _) : Nonempty (R i) := ⟨a i⟩; Pi.map_injective

@[to_additive (attr := simp)]

Depends on / 依赖: Nonempty, Pi.map_injective, map_injective
-/
theorem isLeftRegular_iff {a : forall i, R i} : IsLeftRegular a ↔ forall i, IsLeftRegular (a i) :=
  have (i : _) : Nonempty (R i) := ⟨a i⟩; Pi.map_injective

@[to_additive (attr := simp)]
/--
theorem `isRightRegular_iff` / 定理 `isRightRegular_iff`

English:
theorem isRightRegular_iff
  given: {a : forall i, R i}
  statement: IsRightRegular a ↔ forall i, IsRightRegular (a i)
  proof: have (i : _) : Nonempty (R i) := ⟨a i⟩; .symm Pi.map_injective.symm

@[to_additive (attr := simp)]

中文:
定理 isRightRegular_iff
  条件: {a : 对任意 i, R i}
  结论: IsRightRegular a ↔ 对任意 i, IsRightRegular (a i)
  证明: have (i : _) : Nonempty (R i) := ⟨a i⟩; .symm Pi.map_injective.symm

@[to_additive (attr := simp)]

Depends on / 依赖: Nonempty, Pi.map_injective.symm, map_injective
-/
theorem isRightRegular_iff {a : forall i, R i} : IsRightRegular a ↔ forall i, IsRightRegular (a i) :=
have (i : _) : Nonempty (R i) := ⟨a i⟩; .symm Pi.map_injective.symm

@[to_additive (attr := simp)]
/--
theorem `isRegular_iff` / 定理 `isRegular_iff`

English:
theorem isRegular_iff
  given: {a : forall i, R i}
  statement: IsRegular a ↔ forall i, IsRegular (a i)
  proof: by
  simp [_root_.isRegular_iff, forall_and]

中文:
定理 isRegular_iff
  条件: {a : 对任意 i, R i}
  结论: 是正则 a ↔ 对任意 i, 是正则 (a i)
  证明: by
  simp [_root_.isRegular_iff, forall_and]

Depends on / 依赖: _root_, _root_.isRegular_iff, forall_and, isRegular_iff
-/
theorem isRegular_iff {a : forall i, R i} : IsRegular a ↔ forall i, IsRegular (a i) := by
  simp [_root_.isRegular_iff, forall_and]

end

@[simp]
/--
theorem `isSMulRegular_iff` / 定理 `isSMulRegular_iff`

English:
theorem isSMulRegular_iff
  given: [forall i, SMul α (R i)] {r : α} [forall i, Nonempty (R i)]
  proof: Pi.map_injective

中文:
定理 isSMulRegular_iff
  条件: [对任意 i, 标量乘法 α (R i)] {r : α} [对任意 i, 非空 (R i)]
  证明: Pi.map_injective

Depends on / 依赖: Pi.map_injective, map_injective
-/
theorem isSMulRegular_iff [forall i, SMul α (R i)] {r : α} [forall i, Nonempty (R i)] :
    IsSMulRegular (forall i, R i) r ↔ forall i, IsSMulRegular (R i) r :=
  Pi.map_injective

end Pi
