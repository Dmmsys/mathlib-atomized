/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Opposites

/-!
# Results about `IsRegular` and `MulOpposite`
-/

public section

variable {R} [Mul R]
open MulOpposite

@[to_additive (attr := simp)]
/--
theorem `isLeftRegular_op` / 定理 `isLeftRegular_op`

English:
theorem isLeftRegular_op
  given: {a : R}
  statement: IsLeftRegular (op a) ↔ IsRightRegular a
  proof: .trans .symm opEquiv.injective_comp _ opEquiv.comp_injective _

@[to_additive (attr := simp)]

中文:
定理 isLeftRegular_op
  条件: {a : R}
  结论: IsLeftRegular (op a) ↔ IsRightRegular a
  证明: .trans .symm opEquiv.injective_comp _ opEquiv.comp_injective _

@[to_additive (attr := simp)]

Depends on / 依赖: comp_injective, injective_comp, opEquiv, opEquiv.comp_injective, opEquiv.injective_comp
-/
theorem isLeftRegular_op {a : R} : IsLeftRegular (op a) ↔ IsRightRegular a :=
.trans .symm opEquiv.injective_comp _ opEquiv.comp_injective _

@[to_additive (attr := simp)]
/--
theorem `isRightRegular_op` / 定理 `isRightRegular_op`

English:
theorem isRightRegular_op
  given: {a : R}
  statement: IsRightRegular (op a) ↔ IsLeftRegular a
  proof: .trans .symm opEquiv.injective_comp _ opEquiv.comp_injective _

@[to_additive (attr := simp)]

中文:
定理 isRightRegular_op
  条件: {a : R}
  结论: IsRightRegular (op a) ↔ IsLeftRegular a
  证明: .trans .symm opEquiv.injective_comp _ opEquiv.comp_injective _

@[to_additive (attr := simp)]

Depends on / 依赖: comp_injective, injective_comp, opEquiv, opEquiv.comp_injective, opEquiv.injective_comp
-/
theorem isRightRegular_op {a : R} : IsRightRegular (op a) ↔ IsLeftRegular a :=
.trans .symm opEquiv.injective_comp _ opEquiv.comp_injective _

@[to_additive (attr := simp)]
/--
theorem `isRegular_op` / 定理 `isRegular_op`

English:
theorem isRegular_op
  given: {a : R}
  statement: IsRegular (op a) ↔ IsRegular a
  proof: by
  simp [isRegular_iff, and_comm]

@[to_additive] protected alias ⟨_, IsLeftRegular.op⟩ := isLeftRegular_op
@[to_additive] protected alias ⟨_, IsRightRegular.op⟩ := isRightRegular_op
@[to_additive] protected alias ⟨_, IsRegular.op⟩ := isRegular_op

@[to_additive (attr := simp)]

中文:
定理 isRegular_op
  条件: {a : R}
  结论: IsRegular (op a) ↔ IsRegular a
  证明: by
  simp [isRegular_iff, and_comm]

@[to_additive] protected alias ⟨_, IsLeftRegular.op⟩ := isLeftRegular_op
@[to_additive] protected alias ⟨_, IsRightRegular.op⟩ := isRightRegular_op
@[to_additive] protected alias ⟨_, IsRegular.op⟩ := isRegular_op

@[to_additive (attr := simp)]

Depends on / 依赖: and_comm, isRegular_iff
-/
theorem isRegular_op {a : R} : IsRegular (op a) ↔ IsRegular a := by
  simp [isRegular_iff, and_comm]

@[to_additive] protected alias ⟨_, IsLeftRegular.op⟩ := isLeftRegular_op
@[to_additive] protected alias ⟨_, IsRightRegular.op⟩ := isRightRegular_op
@[to_additive] protected alias ⟨_, IsRegular.op⟩ := isRegular_op

@[to_additive (attr := simp)]
/--
theorem `isLeftRegular_unop` / 定理 `isLeftRegular_unop`

English:
theorem isLeftRegular_unop
  given: {a : Rᵐᵒᵖ}
  statement: IsLeftRegular a.unop ↔ IsRightRegular a
  proof: isRightRegular_op.symm

@[to_additive (attr := simp)]

中文:
定理 isLeftRegular_unop
  条件: {a : Rᵐᵒᵖ}
  结论: IsLeftRegular a.unop ↔ IsRightRegular a
  证明: isRightRegular_op.symm

@[to_additive (attr := simp)]

Depends on / 依赖: isRightRegular_op, isRightRegular_op.symm
-/
theorem isLeftRegular_unop {a : Rᵐᵒᵖ} : IsLeftRegular a.unop ↔ IsRightRegular a :=
  isRightRegular_op.symm

@[to_additive (attr := simp)]
/--
theorem `isRightRegular_unop` / 定理 `isRightRegular_unop`

English:
theorem isRightRegular_unop
  given: {a : Rᵐᵒᵖ}
  statement: IsRightRegular a.unop ↔ IsLeftRegular a
  proof: isLeftRegular_op.symm

@[to_additive (attr := simp)]

中文:
定理 isRightRegular_unop
  条件: {a : Rᵐᵒᵖ}
  结论: IsRightRegular a.unop ↔ IsLeftRegular a
  证明: isLeftRegular_op.symm

@[to_additive (attr := simp)]

Depends on / 依赖: isLeftRegular_op, isLeftRegular_op.symm
-/
theorem isRightRegular_unop {a : Rᵐᵒᵖ} : IsRightRegular a.unop ↔ IsLeftRegular a :=
  isLeftRegular_op.symm

@[to_additive (attr := simp)]
/--
theorem `isRegular_unop` / 定理 `isRegular_unop`

English:
theorem isRegular_unop
  given: {a : Rᵐᵒᵖ}
  statement: IsRegular a.unop ↔ IsRegular a
  proof: isRegular_op.symm

@[to_additive] protected alias ⟨_, IsLeftRegular.unop⟩ := isLeftRegular_unop
@[to_additive] protected alias ⟨_, IsRightRegular.unop⟩ := isRightRegular_unop
@[to_additive] protected alias ⟨_, IsRegular.unop⟩ := isRegular_unop

中文:
定理 isRegular_unop
  条件: {a : Rᵐᵒᵖ}
  结论: IsRegular a.unop ↔ IsRegular a
  证明: isRegular_op.symm

@[to_additive] protected alias ⟨_, IsLeftRegular.unop⟩ := isLeftRegular_unop
@[to_additive] protected alias ⟨_, IsRightRegular.unop⟩ := isRightRegular_unop
@[to_additive] protected alias ⟨_, IsRegular.unop⟩ := isRegular_unop

Depends on / 依赖: isRegular_op, isRegular_op.symm
-/
theorem isRegular_unop {a : Rᵐᵒᵖ} : IsRegular a.unop ↔ IsRegular a :=
  isRegular_op.symm

@[to_additive] protected alias ⟨_, IsLeftRegular.unop⟩ := isLeftRegular_unop
@[to_additive] protected alias ⟨_, IsRightRegular.unop⟩ := isRightRegular_unop
@[to_additive] protected alias ⟨_, IsRegular.unop⟩ := isRegular_unop
