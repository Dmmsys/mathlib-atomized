/-
Copyright (c) 2025 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.Algebra.Opposites

/-!
# Subsemigroup of opposite semigroups

For every semigroup `M`, we construct an equivalence between subsemigroups of `M` and that of
`Mᵐᵒᵖ`.

-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {ι : Sort*} {M : Type*} [Mul M]

namespace Subsemigroup

/-- Pull a subsemigroup back to an opposite subsemigroup along `MulOpposite.unop` -/
@[to_additive (attr := simps) /-- Pull an additive subsemigroup back to an opposite subsemigroup
  along `AddOpposite.unop` -/]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (x : Subsemigroup M)
  body: MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha

@[to_additive (attr := simp)]

中文:
定义 op
  签名: (x : 子半群 M)
  定义体: MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha

@[to_additive (attr := simp)]
-/
protected def op (x : Subsemigroup M) : Subsemigroup Mᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha

@[to_additive (attr := simp)]
/--
theorem `mem_op` / 定理 `mem_op`

English:
theorem mem_op
  given: {x : Mᵐᵒᵖ} {S : Subsemigroup M}
  statement: x in S.op ↔ x.unop in S
  proof: Iff.rfl

中文:
定理 mem_op
  条件: {x : Mᵐᵒᵖ} {S : 子半群 M}
  结论: x in S.op ↔ x.unop in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_op {x : Mᵐᵒᵖ} {S : Subsemigroup M} : x in S.op ↔ x.unop in S := Iff.rfl

/-- Pull an opposite subsemigroup back to a subsemigroup along `MulOpposite.op` -/
@[to_additive (attr := simps) /-- Pull an opposite additive subsemigroup back to a subsemigroup
  along `AddOpposite.op` -/]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (x : Subsemigroup Mᵐᵒᵖ)
  body: MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha

@[to_additive (attr := simp)]

中文:
定义 unop
  签名: (x : 子半群 Mᵐᵒᵖ)
  定义体: MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha

@[to_additive (attr := simp)]
-/
protected def unop (x : Subsemigroup Mᵐᵒᵖ) : Subsemigroup M where
  carrier := MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha

@[to_additive (attr := simp)]
/--
theorem `mem_unop` / 定理 `mem_unop`

English:
theorem mem_unop
  given: {x : M} {S : Subsemigroup Mᵐᵒᵖ}
  statement: x in S.unop ↔ MulOpposite.op x in S
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mem_unop
  条件: {x : M} {S : 子半群 Mᵐᵒᵖ}
  结论: x in S.unop ↔ MulOpposite.op x in S
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_unop {x : M} {S : Subsemigroup Mᵐᵒᵖ} : x in S.unop ↔ MulOpposite.op x in S := Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `unop_op` / 定理 `unop_op`

English:
theorem unop_op
  given: (S : Subsemigroup M)
  statement: S.op.unop = S
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unop_op
  条件: (S : 子半群 M)
  结论: S.op.unop = S
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unop_op (S : Subsemigroup M) : S.op.unop = S := rfl

@[to_additive (attr := simp)]
/--
theorem `op_unop` / 定理 `op_unop`

English:
theorem op_unop
  given: (S : Subsemigroup Mᵐᵒᵖ)
  statement: S.unop.op = S
  proof: rfl

中文:
定理 op_unop
  条件: (S : 子半群 Mᵐᵒᵖ)
  结论: S.unop.op = S
  证明: rfl
-/
theorem op_unop (S : Subsemigroup Mᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

@[to_additive]
/--
theorem `op_le_iff` / 定理 `op_le_iff`

English:
theorem op_le_iff
  given: {S₁ : Subsemigroup M} {S₂ : Subsemigroup Mᵐᵒᵖ}
  statement: S₁.op <= S₂ ↔ S₁ <= S₂.unop
  proof: MulOpposite.op_surjective.forall

@[to_additive]

中文:
定理 op_le_iff
  条件: {S₁ : 子半群 M} {S₂ : 子半群 Mᵐᵒᵖ}
  结论: S₁.op <= S₂ ↔ S₁ <= S₂.unop
  证明: MulOpposite.op_surjective.forall

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem op_le_iff {S₁ : Subsemigroup M} {S₂ : Subsemigroup Mᵐᵒᵖ} : S₁.op <= S₂ ↔ S₁ <= S₂.unop :=
  MulOpposite.op_surjective.forall

@[to_additive]
/--
theorem `le_op_iff` / 定理 `le_op_iff`

English:
theorem le_op_iff
  given: {S₁ : Subsemigroup Mᵐᵒᵖ} {S₂ : Subsemigroup M}
  statement: S₁ <= S₂.op ↔ S₁.unop <= S₂
  proof: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

中文:
定理 le_op_iff
  条件: {S₁ : 子半群 Mᵐᵒᵖ} {S₂ : 子半群 M}
  结论: S₁ <= S₂.op ↔ S₁.unop <= S₂
  证明: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem le_op_iff {S₁ : Subsemigroup Mᵐᵒᵖ} {S₂ : Subsemigroup M} : S₁ <= S₂.op ↔ S₁.unop <= S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
/--
theorem `op_le_op_iff` / 定理 `op_le_op_iff`

English:
theorem op_le_op_iff
  given: {S₁ S₂ : Subsemigroup M}
  statement: S₁.op <= S₂.op ↔ S₁ <= S₂
  proof: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

中文:
定理 op_le_op_iff
  条件: {S₁ S₂ : 子半群 M}
  结论: S₁.op <= S₂.op ↔ S₁ <= S₂
  证明: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem op_le_op_iff {S₁ S₂ : Subsemigroup M} : S₁.op <= S₂.op ↔ S₁ <= S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
/--
theorem `unop_le_unop_iff` / 定理 `unop_le_unop_iff`

English:
theorem unop_le_unop_iff
  given: {S₁ S₂ : Subsemigroup Mᵐᵒᵖ}
  statement: S₁.unop <= S₂.unop ↔ S₁ <= S₂
  proof: MulOpposite.unop_surjective.forall

中文:
定理 unop_le_unop_iff
  条件: {S₁ S₂ : 子半群 Mᵐᵒᵖ}
  结论: S₁.unop <= S₂.unop ↔ S₁ <= S₂
  证明: MulOpposite.unop_surjective.forall

Depends on / 依赖: MulOpposite, MulOpposite.unop_surjective.forall, unop_surjective
-/
theorem unop_le_unop_iff {S₁ S₂ : Subsemigroup Mᵐᵒᵖ} : S₁.unop <= S₂.unop ↔ S₁ <= S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subsemigroup `H` of `M` determines a subsemigroup `H.op` of the opposite semigroup `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps) /-- An additive subsemigroup `H` of `M` determines an additive
  subsemigroup `H.op` of the opposite semigroup `Mᵐᵒᵖ`. -/]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : Subsemigroup M ≃o Subsemigroup Mᵐᵒᵖ where
  body: Subsemigroup.op
  invFun := Subsemigroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]

中文:
定义 opEquiv
  签名: : 子半群 M ≃o 子半群 Mᵐᵒᵖ where
  定义体: Subsemigroup.op
  invFun := Subsemigroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]

Depends on / 依赖: Subsemigroup, Subsemigroup.op
-/
def opEquiv : Subsemigroup M ≃o Subsemigroup Mᵐᵒᵖ where
  toFun := Subsemigroup.op
  invFun := Subsemigroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]
/--
theorem `op_injective` / 定理 `op_injective`

English:
theorem op_injective
  statement: (@Subsemigroup.op M _).Injective
  proof: opEquiv.injective

@[to_additive]

中文:
定理 op_injective
  结论: (@子半群.op M _).单射
  证明: opEquiv.injective

@[to_additive]

Depends on / 依赖: injective, opEquiv, opEquiv.injective
-/
theorem op_injective : (@Subsemigroup.op M _).Injective := opEquiv.injective

@[to_additive]
/--
theorem `unop_injective` / 定理 `unop_injective`

English:
theorem unop_injective
  statement: (@Subsemigroup.unop M _).Injective
  proof: opEquiv.symm.injective

@[to_additive (attr := simp)]

中文:
定理 unop_injective
  结论: (@子半群.unop M _).单射
  证明: opEquiv.symm.injective

@[to_additive (attr := simp)]

Depends on / 依赖: injective, opEquiv, opEquiv.symm.injective
-/
theorem unop_injective : (@Subsemigroup.unop M _).Injective := opEquiv.symm.injective

@[to_additive (attr := simp)]
/--
theorem `op_inj` / 定理 `op_inj`

English:
theorem op_inj
  given: {S T : Subsemigroup M}
  statement: S.op = T.op ↔ S = T
  proof: opEquiv.eq_iff_eq

@[to_additive (attr := simp)]

中文:
定理 op_inj
  条件: {S T : 子半群 M}
  结论: S.op = T.op ↔ S = T
  证明: opEquiv.eq_iff_eq

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff_eq, opEquiv, opEquiv.eq_iff_eq
-/
theorem op_inj {S T : Subsemigroup M} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq

@[to_additive (attr := simp)]
/--
theorem `unop_inj` / 定理 `unop_inj`

English:
theorem unop_inj
  given: {S T : Subsemigroup Mᵐᵒᵖ}
  statement: S.unop = T.unop ↔ S = T
  proof: opEquiv.symm.eq_iff_eq

@[to_additive (attr := simp)]

中文:
定理 unop_inj
  条件: {S T : 子半群 Mᵐᵒᵖ}
  结论: S.unop = T.unop ↔ S = T
  证明: opEquiv.symm.eq_iff_eq

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff_eq, opEquiv, opEquiv.symm.eq_iff_eq
-/
theorem unop_inj {S T : Subsemigroup Mᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

@[to_additive (attr := simp)]
/--
theorem `op_bot` / 定理 `op_bot`

English:
theorem op_bot
  statement: (⊥ : Subsemigroup M).op = ⊥
  proof: opEquiv.map_bot

@[to_additive (attr := simp)]

中文:
定理 op_bot
  结论: (⊥ : 子半群 M).op = ⊥
  证明: opEquiv.map_bot

@[to_additive (attr := simp)]

Depends on / 依赖: map_bot, opEquiv, opEquiv.map_bot
-/
theorem op_bot : (⊥ : Subsemigroup M).op = ⊥ := opEquiv.map_bot

@[to_additive (attr := simp)]
/--
theorem `op_eq_bot` / 定理 `op_eq_bot`

English:
theorem op_eq_bot
  given: {S : Subsemigroup M}
  statement: S.op = ⊥ ↔ S = ⊥
  proof: op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]

中文:
定理 op_eq_bot
  条件: {S : 子半群 M}
  结论: S.op = ⊥ ↔ S = ⊥
  证明: op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, op_bot, op_injective, op_injective.eq_iff
-/
theorem op_eq_bot {S : Subsemigroup M} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]
/--
theorem `unop_bot` / 定理 `unop_bot`

English:
theorem unop_bot
  statement: (⊥ : Subsemigroup Mᵐᵒᵖ).unop = ⊥
  proof: opEquiv.symm.map_bot

@[to_additive (attr := simp)]

中文:
定理 unop_bot
  结论: (⊥ : 子半群 Mᵐᵒᵖ).unop = ⊥
  证明: opEquiv.symm.map_bot

@[to_additive (attr := simp)]

Depends on / 依赖: map_bot, opEquiv, opEquiv.symm.map_bot
-/
theorem unop_bot : (⊥ : Subsemigroup Mᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[to_additive (attr := simp)]
/--
theorem `unop_eq_bot` / 定理 `unop_eq_bot`

English:
theorem unop_eq_bot
  given: {S : Subsemigroup Mᵐᵒᵖ}
  statement: S.unop = ⊥ ↔ S = ⊥
  proof: unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]

中文:
定理 unop_eq_bot
  条件: {S : 子半群 Mᵐᵒᵖ}
  结论: S.unop = ⊥ ↔ S = ⊥
  证明: unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, unop_bot, unop_injective, unop_injective.eq_iff
-/
theorem unop_eq_bot {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]
/--
theorem `op_top` / 定理 `op_top`

English:
theorem op_top
  statement: (⊤ : Subsemigroup M).op = ⊤
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 op_top
  结论: (⊤ : 子半群 M).op = ⊤
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem op_top : (⊤ : Subsemigroup M).op = ⊤ := rfl

@[to_additive (attr := simp)]
/--
theorem `op_eq_top` / 定理 `op_eq_top`

English:
theorem op_eq_top
  given: {S : Subsemigroup M}
  statement: S.op = ⊤ ↔ S = ⊤
  proof: op_injective.eq_iff' op_top

@[to_additive (attr := simp)]

中文:
定理 op_eq_top
  条件: {S : 子半群 M}
  结论: S.op = ⊤ ↔ S = ⊤
  证明: op_injective.eq_iff' op_top

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, op_injective, op_injective.eq_iff, op_top
-/
theorem op_eq_top {S : Subsemigroup M} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[to_additive (attr := simp)]
/--
theorem `unop_top` / 定理 `unop_top`

English:
theorem unop_top
  statement: (⊤ : Subsemigroup Mᵐᵒᵖ).unop = ⊤
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unop_top
  结论: (⊤ : 子半群 Mᵐᵒᵖ).unop = ⊤
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unop_top : (⊤ : Subsemigroup Mᵐᵒᵖ).unop = ⊤ := rfl

@[to_additive (attr := simp)]
/--
theorem `unop_eq_top` / 定理 `unop_eq_top`

English:
theorem unop_eq_top
  given: {S : Subsemigroup Mᵐᵒᵖ}
  statement: S.unop = ⊤ ↔ S = ⊤
  proof: unop_injective.eq_iff' unop_top

@[to_additive]

中文:
定理 unop_eq_top
  条件: {S : 子半群 Mᵐᵒᵖ}
  结论: S.unop = ⊤ ↔ S = ⊤
  证明: unop_injective.eq_iff' unop_top

@[to_additive]

Depends on / 依赖: eq_iff, unop_injective, unop_injective.eq_iff, unop_top
-/
theorem unop_eq_top {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' unop_top

@[to_additive]
/--
theorem `op_sup` / 定理 `op_sup`

English:
theorem op_sup
  given: (S₁ S₂ : Subsemigroup M)
  statement: (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
  proof: opEquiv.map_sup _ _

@[to_additive]

中文:
定理 op_sup
  条件: (S₁ S₂ : 子半群 M)
  结论: (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
  证明: opEquiv.map_sup _ _

@[to_additive]

Depends on / 依赖: map_sup, opEquiv, opEquiv.map_sup
-/
theorem op_sup (S₁ S₂ : Subsemigroup M) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

@[to_additive]
/--
theorem `unop_sup` / 定理 `unop_sup`

English:
theorem unop_sup
  given: (S₁ S₂ : Subsemigroup Mᵐᵒᵖ)
  statement: (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
  proof: opEquiv.symm.map_sup _ _

@[to_additive]

中文:
定理 unop_sup
  条件: (S₁ S₂ : 子半群 Mᵐᵒᵖ)
  结论: (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
  证明: opEquiv.symm.map_sup _ _

@[to_additive]

Depends on / 依赖: map_sup, opEquiv, opEquiv.symm.map_sup
-/
theorem unop_sup (S₁ S₂ : Subsemigroup Mᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

@[to_additive]
/--
theorem `op_inf` / 定理 `op_inf`

English:
theorem op_inf
  given: (S₁ S₂ : Subsemigroup M)
  statement: (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
  proof: rfl

@[to_additive]

中文:
定理 op_inf
  条件: (S₁ S₂ : 子半群 M)
  结论: (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
  证明: rfl

@[to_additive]
-/
theorem op_inf (S₁ S₂ : Subsemigroup M) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

@[to_additive]
/--
theorem `unop_inf` / 定理 `unop_inf`

English:
theorem unop_inf
  given: (S₁ S₂ : Subsemigroup Mᵐᵒᵖ)
  statement: (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
  proof: rfl

@[to_additive]

中文:
定理 unop_inf
  条件: (S₁ S₂ : 子半群 Mᵐᵒᵖ)
  结论: (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
  证明: rfl

@[to_additive]
-/
theorem unop_inf (S₁ S₂ : Subsemigroup Mᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

@[to_additive]
/--
theorem `op_sSup` / 定理 `op_sSup`

English:
theorem op_sSup
  given: (S : Set (Subsemigroup M))
  statement: (sSup S).op = sSup (.unop ⁻¹' S)
  proof: opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

中文:
定理 op_sSup
  条件: (S : 集合 (子半群 M))
  结论: (sSup S).op = sSup (.unop ⁻¹' S)
  证明: opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

Depends on / 依赖: IsLeftCancelMulZero, IsLeftCancelMulZero.to_noZeroDivisors, map_sSup_eq_sSup_symm_preimage, opEquiv, opEquiv.map_sSup_eq_sSup_symm_preimage, to_noZeroDivisors
-/
theorem op_sSup (S : Set (Subsemigroup M)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
/--
theorem `unop_sSup` / 定理 `unop_sSup`

English:
theorem unop_sSup
  given: (S : Set (Subsemigroup Mᵐᵒᵖ))
  statement: (sSup S).unop = sSup (.op ⁻¹' S)
  proof: opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

中文:
定理 unop_sSup
  条件: (S : 集合 (子半群 Mᵐᵒᵖ))
  结论: (sSup S).unop = sSup (.op ⁻¹' S)
  证明: opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

Depends on / 依赖: IsRightCancelMulZero, IsRightCancelMulZero.to_noZeroDivisors, map_sSup_eq_sSup_symm_preimage, opEquiv, opEquiv.symm.map_sSup_eq_sSup_symm_preimage, to_noZeroDivisors
-/
theorem unop_sSup (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
/--
theorem `op_sInf` / 定理 `op_sInf`

English:
theorem op_sInf
  given: (S : Set (Subsemigroup M))
  statement: (sInf S).op = sInf (.unop ⁻¹' S)
  proof: opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

中文:
定理 op_sInf
  条件: (S : 集合 (子半群 M))
  结论: (sInf S).op = sInf (.unop ⁻¹' S)
  证明: opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

Depends on / 依赖: map_sInf_eq_sInf_symm_preimage, opEquiv, opEquiv.map_sInf_eq_sInf_symm_preimage
-/
theorem op_sInf (S : Set (Subsemigroup M)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
/--
theorem `unop_sInf` / 定理 `unop_sInf`

English:
theorem unop_sInf
  given: (S : Set (Subsemigroup Mᵐᵒᵖ))
  statement: (sInf S).unop = sInf (.op ⁻¹' S)
  proof: opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

中文:
定理 unop_sInf
  条件: (S : 集合 (子半群 Mᵐᵒᵖ))
  结论: (sInf S).unop = sInf (.op ⁻¹' S)
  证明: opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

Depends on / 依赖: map_sInf_eq_sInf_symm_preimage, opEquiv, opEquiv.symm.map_sInf_eq_sInf_symm_preimage
-/
theorem unop_sInf (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
/--
theorem `op_iSup` / 定理 `op_iSup`

English:
theorem op_iSup
  given: (S : ι -> Subsemigroup M)
  statement: (iSup S).op = ⨆ i, (S i).op
  proof: opEquiv.map_iSup _

@[to_additive]

中文:
定理 op_iSup
  条件: (S : ι -> 子半群 M)
  结论: (iSup S).op = ⨆ i, (S i).op
  证明: opEquiv.map_iSup _

@[to_additive]

Depends on / 依赖: map_iSup, opEquiv, opEquiv.map_iSup
-/
theorem op_iSup (S : ι -> Subsemigroup M) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

@[to_additive]
/--
theorem `unop_iSup` / 定理 `unop_iSup`

English:
theorem unop_iSup
  given: (S : ι -> Subsemigroup Mᵐᵒᵖ)
  statement: (iSup S).unop = ⨆ i, (S i).unop
  proof: opEquiv.symm.map_iSup _

@[to_additive]

中文:
定理 unop_iSup
  条件: (S : ι -> 子半群 Mᵐᵒᵖ)
  结论: (iSup S).unop = ⨆ i, (S i).unop
  证明: opEquiv.symm.map_iSup _

@[to_additive]

Depends on / 依赖: map_iSup, opEquiv, opEquiv.symm.map_iSup
-/
theorem unop_iSup (S : ι -> Subsemigroup Mᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

@[to_additive]
/--
theorem `op_iInf` / 定理 `op_iInf`

English:
theorem op_iInf
  given: (S : ι -> Subsemigroup M)
  statement: (iInf S).op = ⨅ i, (S i).op
  proof: opEquiv.map_iInf _

@[to_additive]

中文:
定理 op_iInf
  条件: (S : ι -> 子半群 M)
  结论: (iInf S).op = ⨅ i, (S i).op
  证明: opEquiv.map_iInf _

@[to_additive]

Depends on / 依赖: map_iInf, opEquiv, opEquiv.map_iInf
-/
theorem op_iInf (S : ι -> Subsemigroup M) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

@[to_additive]
/--
theorem `unop_iInf` / 定理 `unop_iInf`

English:
theorem unop_iInf
  given: (S : ι -> Subsemigroup Mᵐᵒᵖ)
  statement: (iInf S).unop = ⨅ i, (S i).unop
  proof: opEquiv.symm.map_iInf _

@[to_additive]

中文:
定理 unop_iInf
  条件: (S : ι -> 子半群 Mᵐᵒᵖ)
  结论: (iInf S).unop = ⨅ i, (S i).unop
  证明: opEquiv.symm.map_iInf _

@[to_additive]

Depends on / 依赖: GroupWithZero, GroupWithZero.toMulDivCancelClass, MulDivCancelClass, map_iInf, opEquiv, opEquiv.symm.map_iInf, toMulDivCancelClass
-/
theorem unop_iInf (S : ι -> Subsemigroup Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

@[to_additive]
/--
theorem `op_closure` / 定理 `op_closure`

English:
theorem op_closure
  given: (s : Set M)
  statement: (closure s).op = closure (MulOpposite.unop ⁻¹' s)
  proof: by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Subsemigroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]

中文:
定理 op_closure
  条件: (s : 集合 M)
  结论: (closure s).op = closure (MulOpposite.unop ⁻¹' s)
  证明: by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Subsemigroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.unop_surjective.forall, Set.preimage_ofPred_eq, Subsemigroup, Subsemigroup.coe_unop, closure, coe_unop, op_sInf, preimage_ofPred_eq, simp_rw, unop_surjective
-/
theorem op_closure (s : Set M) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Subsemigroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]
/--
theorem `unop_closure` / 定理 `unop_closure`

English:
theorem unop_closure
  given: (s : Set Mᵐᵒᵖ)
  statement: (closure s).unop = closure (MulOpposite.op ⁻¹' s)
  proof: by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

中文:
定理 unop_closure
  条件: (s : 集合 Mᵐᵒᵖ)
  结论: (closure s).unop = closure (MulOpposite.op ⁻¹' s)
  证明: by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

Depends on / 依赖: MulOpposite, MulOpposite.op_unop, Set.preimage_id, Set.preimage_preimage, op_closure, op_inj, op_unop, preimage_id, preimage_preimage, simp_rw
-/
theorem unop_closure (s : Set Mᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

/-- Bijection between a subsemigroup `H` and its opposite. -/
@[to_additive (attr := simps!) /-- Bijection between an additive subsemigroup `H` and its opposite.
  -/]
/--
Definition of `equivOp` / `equivOp` 的定义

English:
definition equivOp
  signature: (H : Subsemigroup M)
  body: MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

中文:
定义 equivOp
  签名: (H : 子半群 M)
  定义体: MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

Depends on / 依赖: Iff.rfl, MulOpposite, MulOpposite.opEquiv.subtypeEquiv, opEquiv, subtypeEquiv
-/
def equivOp (H : Subsemigroup M) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

end Subsemigroup
