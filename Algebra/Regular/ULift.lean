/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and `ULift`
-/

public section

universe u v

variable {α} {R : Type v}

namespace ULift

section
variable [Mul R]

@[to_additive (attr := simp)]
/--
theorem `isLeftRegular_up` / 定理 `isLeftRegular_up`

English:
theorem isLeftRegular_up
  given: {a : R}
  statement: IsLeftRegular (ULift.up.{u} a) ↔ IsLeftRegular a
  proof: .trans .symm Equiv.ulift.symm.injective_comp _ Equiv.ulift.symm.comp_injective _

@[to_additive (attr := simp)]

中文:
定理 isLeftRegular_up
  条件: {a : R}
  结论: IsLeftRegular (类型层提升.up.{u} a) ↔ IsLeftRegular a
  证明: .trans .symm Equiv.ulift.symm.injective_comp _ Equiv.ulift.symm.comp_injective _

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.ulift.symm.comp_injective, Equiv.ulift.symm.injective_comp, comp_injective, injective_comp
-/
theorem isLeftRegular_up {a : R} : IsLeftRegular (ULift.up.{u} a) ↔ IsLeftRegular a :=
.trans .symm Equiv.ulift.symm.injective_comp _ Equiv.ulift.symm.comp_injective _

@[to_additive (attr := simp)]
/--
theorem `isRightRegular_up` / 定理 `isRightRegular_up`

English:
theorem isRightRegular_up
  given: {a : R}
  statement: IsRightRegular (ULift.up.{u} a) ↔ IsRightRegular a
  proof: .trans .symm Equiv.ulift.symm.injective_comp _ Equiv.ulift.symm.comp_injective _

@[to_additive (attr := simp)]

中文:
定理 isRightRegular_up
  条件: {a : R}
  结论: IsRightRegular (类型层提升.up.{u} a) ↔ IsRightRegular a
  证明: .trans .symm Equiv.ulift.symm.injective_comp _ Equiv.ulift.symm.comp_injective _

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.ulift.symm.comp_injective, Equiv.ulift.symm.injective_comp, comp_injective, injective_comp
-/
theorem isRightRegular_up {a : R} : IsRightRegular (ULift.up.{u} a) ↔ IsRightRegular a :=
.trans .symm Equiv.ulift.symm.injective_comp _ Equiv.ulift.symm.comp_injective _

@[to_additive (attr := simp)]
/--
theorem `isRegular_up` / 定理 `isRegular_up`

English:
theorem isRegular_up
  given: {a : R}
  statement: IsRegular (ULift.up.{u} a) ↔ IsRegular a
  proof: by
  simp [isRegular_iff]

@[to_additive (attr := simp)]

中文:
定理 isRegular_up
  条件: {a : R}
  结论: 是正则 (类型层提升.up.{u} a) ↔ 是正则 a
  证明: by
  simp [isRegular_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: isRegular_iff
-/
theorem isRegular_up {a : R} : IsRegular (ULift.up.{u} a) ↔ IsRegular a := by
  simp [isRegular_iff]

@[to_additive (attr := simp)]
/--
theorem `isLeftRegular_down` / 定理 `isLeftRegular_down`

English:
theorem isLeftRegular_down
  given: {a : ULift.{u} R}
  statement: IsLeftRegular a.down ↔ IsLeftRegular a
  proof: isLeftRegular_up.symm

@[to_additive (attr := simp)]

中文:
定理 isLeftRegular_down
  条件: {a : 类型层提升.{u} R}
  结论: IsLeftRegular a.down ↔ IsLeftRegular a
  证明: isLeftRegular_up.symm

@[to_additive (attr := simp)]

Depends on / 依赖: isLeftRegular_up, isLeftRegular_up.symm
-/
theorem isLeftRegular_down {a : ULift.{u} R} : IsLeftRegular a.down ↔ IsLeftRegular a :=
  isLeftRegular_up.symm

@[to_additive (attr := simp)]
/--
theorem `isRightRegular_down` / 定理 `isRightRegular_down`

English:
theorem isRightRegular_down
  given: {a : ULift.{u} R}
  statement: IsRightRegular a.down ↔ IsRightRegular a
  proof: isRightRegular_up.symm

@[to_additive (attr := simp)]

中文:
定理 isRightRegular_down
  条件: {a : 类型层提升.{u} R}
  结论: IsRightRegular a.down ↔ IsRightRegular a
  证明: isRightRegular_up.symm

@[to_additive (attr := simp)]

Depends on / 依赖: isRightRegular_up, isRightRegular_up.symm
-/
theorem isRightRegular_down {a : ULift.{u} R} : IsRightRegular a.down ↔ IsRightRegular a :=
  isRightRegular_up.symm

@[to_additive (attr := simp)]
/--
theorem `isRegular_down` / 定理 `isRegular_down`

English:
theorem isRegular_down
  given: {a : ULift.{u} R}
  statement: IsRegular a.down ↔ IsRegular a
  proof: isRegular_up.symm

中文:
定理 isRegular_down
  条件: {a : 类型层提升.{u} R}
  结论: 是正则 a.down ↔ 是正则 a
  证明: isRegular_up.symm

Depends on / 依赖: isRegular_up, isRegular_up.symm
-/
theorem isRegular_down {a : ULift.{u} R} : IsRegular a.down ↔ IsRegular a :=
  isRegular_up.symm

end

@[simp]
/--
theorem `isSMulRegular_iff` / 定理 `isSMulRegular_iff`

English:
theorem isSMulRegular_iff
  given: [SMul α R] {r : α}
  proof: .trans .symm Equiv.ulift.symm.injective_comp _ Equiv.ulift.symm.comp_injective _

中文:
定理 isSMulRegular_iff
  条件: [标量乘法 α R] {r : α}
  证明: .trans .symm Equiv.ulift.symm.injective_comp _ Equiv.ulift.symm.comp_injective _

Depends on / 依赖: Equiv.ulift.symm.comp_injective, Equiv.ulift.symm.injective_comp, comp_injective, injective_comp
-/
theorem isSMulRegular_iff [SMul α R] {r : α} :
    IsSMulRegular (ULift R) r ↔ IsSMulRegular R r :=
.trans .symm Equiv.ulift.symm.injective_comp _ Equiv.ulift.symm.comp_injective _

end ULift
