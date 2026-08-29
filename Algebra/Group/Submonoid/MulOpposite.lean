/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
module

public import Mathlib.Algebra.Group.Subsemigroup.MulOpposite
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Opposite

/-!
# Submonoid of opposite monoids

For every monoid `M`, we construct an equivalence between submonoids of `M` and that of `Mᵐᵒᵖ`.

-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {ι : Sort*} {M : Type*} [MulOneClass M]

namespace Submonoid

/-- Pull a submonoid back to an opposite submonoid along `MulOpposite.unop` -/
@[to_additive (attr := simps) /-- Pull an additive submonoid back to an opposite submonoid along
`AddOpposite.unop` -/]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (x : Submonoid M)
  body: MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[to_additive (attr := simp)]

中文:
定义 op
  签名: (x : Submonoid M)
  定义体: MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[to_additive (attr := simp)]

Depends on / 依赖: TwoUniqueSums, TwoUniqueSums.uniqueAdd_of_one_lt_card, uniqueAdd_of_one_lt_card
-/
protected def op (x : Submonoid M) : Submonoid Mᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[to_additive (attr := simp)]
/--
theorem `mem_op` / 定理 `mem_op`

English:
theorem mem_op
  given: {x : Mᵐᵒᵖ} {S : Submonoid M}
  statement: x in S.op ↔ x.unop in S
  proof: Iff.rfl

中文:
定理 mem_op
  条件: {x : Mᵐᵒᵖ} {S : Submonoid M}
  结论: x in S.op ↔ x.unop in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, UniqueProds, UniqueProds.uniqueMul_of_nonempty, uniqueMul_of_nonempty
-/
theorem mem_op {x : Mᵐᵒᵖ} {S : Submonoid M} : x in S.op ↔ x.unop in S := Iff.rfl

/--
lemma `op_toSubsemigroup` / 引理 `op_toSubsemigroup`

English:
lemma op_toSubsemigroup
  given: (H : Submonoid M)
  proof: rfl

中文:
引理 op_toSubsemigroup
  条件: (H : Submonoid M)
  证明: rfl

Depends on / 依赖: TwoUniqueProds, TwoUniqueProds.uniqueMul_of_one_lt_card, uniqueMul_of_one_lt_card
-/
@[to_additive (attr := simp)] lemma op_toSubsemigroup (H : Submonoid M) :
    H.op.toSubsemigroup = H.toSubsemigroup.op :=
  rfl

/-- Pull an opposite submonoid back to a submonoid along `MulOpposite.op` -/
@[to_additive (attr := simps) /-- Pull an opposite additive submonoid back to a submonoid along
`AddOpposite.op` -/]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (x : Submonoid Mᵐᵒᵖ)
  body: MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[to_additive (attr := simp)]

中文:
定义 unop
  签名: (x : Submonoid Mᵐᵒᵖ)
  定义体: MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[to_additive (attr := simp)]
-/
protected def unop (x : Submonoid Mᵐᵒᵖ) : Submonoid M where
  carrier := MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[to_additive (attr := simp)]
/--
theorem `mem_unop` / 定理 `mem_unop`

English:
theorem mem_unop
  given: {x : M} {S : Submonoid Mᵐᵒᵖ}
  statement: x in S.unop ↔ MulOpposite.op x in S
  proof: Iff.rfl

中文:
定理 mem_unop
  条件: {x : M} {S : Submonoid Mᵐᵒᵖ}
  结论: x in S.unop ↔ MulOpposite.op x in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_unop {x : M} {S : Submonoid Mᵐᵒᵖ} : x in S.unop ↔ MulOpposite.op x in S := Iff.rfl

/--
lemma `unop_toSubsemigroup` / 引理 `unop_toSubsemigroup`

English:
lemma unop_toSubsemigroup
  given: (H : Submonoid Mᵐᵒᵖ)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 unop_toSubsemigroup
  条件: (H : Submonoid Mᵐᵒᵖ)
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma unop_toSubsemigroup (H : Submonoid Mᵐᵒᵖ) :
    H.unop.toSubsemigroup = H.toSubsemigroup.unop :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `unop_op` / 定理 `unop_op`

English:
theorem unop_op
  given: (S : Submonoid M)
  statement: S.op.unop = S
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unop_op
  条件: (S : Submonoid M)
  结论: S.op.unop = S
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: DFinsupp, DFinsupp.coeFnAddMonoidHom.toAddHom, DFunLike, DFunLike.coe_injective, UniqueSums, UniqueSums.of_injective_addHom, coeFnAddMonoidHom, coe_injective, of_injective_addHom, toAddHom
-/
theorem unop_op (S : Submonoid M) : S.op.unop = S := rfl

@[to_additive (attr := simp)]
/--
theorem `op_unop` / 定理 `op_unop`

English:
theorem op_unop
  given: (S : Submonoid Mᵐᵒᵖ)
  statement: S.unop.op = S
  proof: rfl

中文:
定理 op_unop
  条件: (S : Submonoid Mᵐᵒᵖ)
  结论: S.unop.op = S
  证明: rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Finsupp, Finsupp.coeFnAddHom.toAddHom, UniqueSums, UniqueSums.of_injective_addHom, coeFnAddHom, coe_injective, of_injective_addHom, toAddHom
-/
theorem op_unop (S : Submonoid Mᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

@[to_additive]
/--
theorem `op_le_iff` / 定理 `op_le_iff`

English:
theorem op_le_iff
  given: {S₁ : Submonoid M} {S₂ : Submonoid Mᵐᵒᵖ}
  statement: S₁.op <= S₂ ↔ S₁ <= S₂.unop
  proof: MulOpposite.op_surjective.forall

@[to_additive]

中文:
定理 op_le_iff
  条件: {S₁ : Submonoid M} {S₂ : Submonoid Mᵐᵒᵖ}
  结论: S₁.op <= S₂ ↔ S₁ <= S₂.unop
  证明: MulOpposite.op_surjective.forall

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem op_le_iff {S₁ : Submonoid M} {S₂ : Submonoid Mᵐᵒᵖ} : S₁.op <= S₂ ↔ S₁ <= S₂.unop :=
  MulOpposite.op_surjective.forall

@[to_additive]
/--
theorem `le_op_iff` / 定理 `le_op_iff`

English:
theorem le_op_iff
  given: {S₁ : Submonoid Mᵐᵒᵖ} {S₂ : Submonoid M}
  statement: S₁ <= S₂.op ↔ S₁.unop <= S₂
  proof: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

中文:
定理 le_op_iff
  条件: {S₁ : Submonoid Mᵐᵒᵖ} {S₂ : Submonoid M}
  结论: S₁ <= S₂.op ↔ S₁.unop <= S₂
  证明: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem le_op_iff {S₁ : Submonoid Mᵐᵒᵖ} {S₂ : Submonoid M} : S₁ <= S₂.op ↔ S₁.unop <= S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
/--
theorem `op_le_op_iff` / 定理 `op_le_op_iff`

English:
theorem op_le_op_iff
  given: {S₁ S₂ : Submonoid M}
  statement: S₁.op <= S₂.op ↔ S₁ <= S₂
  proof: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

中文:
定理 op_le_op_iff
  条件: {S₁ S₂ : Submonoid M}
  结论: S₁.op <= S₂.op ↔ S₁ <= S₂
  证明: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem op_le_op_iff {S₁ S₂ : Submonoid M} : S₁.op <= S₂.op ↔ S₁ <= S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
/--
theorem `unop_le_unop_iff` / 定理 `unop_le_unop_iff`

English:
theorem unop_le_unop_iff
  given: {S₁ S₂ : Submonoid Mᵐᵒᵖ}
  statement: S₁.unop <= S₂.unop ↔ S₁ <= S₂
  proof: MulOpposite.unop_surjective.forall

中文:
定理 unop_le_unop_iff
  条件: {S₁ S₂ : Submonoid Mᵐᵒᵖ}
  结论: S₁.unop <= S₂.unop ↔ S₁ <= S₂
  证明: MulOpposite.unop_surjective.forall

Depends on / 依赖: MulOpposite, MulOpposite.unop_surjective.forall, unop_surjective
-/
theorem unop_le_unop_iff {S₁ S₂ : Submonoid Mᵐᵒᵖ} : S₁.unop <= S₂.unop ↔ S₁ <= S₂ :=
  MulOpposite.unop_surjective.forall

/-- A submonoid `H` of `M` determines a submonoid `H.op` of the opposite monoid `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps) /-- An additive submonoid `H` of `M` determines an additive submonoid
`H.op` of the opposite monoid `Mᵐᵒᵖ`. -/]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : Submonoid M ≃o Submonoid Mᵐᵒᵖ where
  body: Submonoid.op
  invFun := Submonoid.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]

中文:
定义 opEquiv
  签名: : Submonoid M ≃o Submonoid Mᵐᵒᵖ where
  定义体: Submonoid.op
  invFun := Submonoid.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.op
-/
def opEquiv : Submonoid M ≃o Submonoid Mᵐᵒᵖ where
  toFun := Submonoid.op
  invFun := Submonoid.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]
/--
theorem `op_injective` / 定理 `op_injective`

English:
theorem op_injective
  statement: (@Submonoid.op M _).Injective
  proof: opEquiv.injective

@[to_additive]

中文:
定理 op_injective
  结论: (@Submonoid.op M _).Injective
  证明: opEquiv.injective

@[to_additive]

Depends on / 依赖: IsRightCancelMul, injective, of_covariant_right, opEquiv, opEquiv.injective
-/
theorem op_injective : (@Submonoid.op M _).Injective := opEquiv.injective

@[to_additive]
/--
theorem `unop_injective` / 定理 `unop_injective`

English:
theorem unop_injective
  statement: (@Submonoid.unop M _).Injective
  proof: opEquiv.symm.injective

@[to_additive (attr := simp)]

中文:
定理 unop_injective
  结论: (@Submonoid.unop M _).Injective
  证明: opEquiv.symm.injective

@[to_additive (attr := simp)]

Depends on / 依赖: IsLeftCancelMul, injective, of_covariant_left, opEquiv, opEquiv.symm.injective
-/
theorem unop_injective : (@Submonoid.unop M _).Injective := opEquiv.symm.injective

@[to_additive (attr := simp)]
/--
theorem `op_inj` / 定理 `op_inj`

English:
theorem op_inj
  given: {S T : Submonoid M}
  statement: S.op = T.op ↔ S = T
  proof: opEquiv.eq_iff_eq

@[to_additive (attr := simp)]

中文:
定理 op_inj
  条件: {S T : Submonoid M}
  结论: S.op = T.op ↔ S = T
  证明: opEquiv.eq_iff_eq

@[to_additive (attr := simp)]

Depends on / 依赖: DFinsupp, DFinsupp.coeFnAddMonoidHom.toAddHom, DFunLike, DFunLike.coe_injective, TwoUniqueSums, TwoUniqueSums.of_injective_addHom, coeFnAddMonoidHom, coe_injective, eq_iff_eq, of_injective_addHom, opEquiv, opEquiv.eq_iff_eq, toAddHom
-/
theorem op_inj {S T : Submonoid M} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq

@[to_additive (attr := simp)]
/--
theorem `unop_inj` / 定理 `unop_inj`

English:
theorem unop_inj
  given: {S T : Submonoid Mᵐᵒᵖ}
  statement: S.unop = T.unop ↔ S = T
  proof: opEquiv.symm.eq_iff_eq

@[to_additive (attr := simp)]

中文:
定理 unop_inj
  条件: {S T : Submonoid Mᵐᵒᵖ}
  结论: S.unop = T.unop ↔ S = T
  证明: opEquiv.symm.eq_iff_eq

@[to_additive (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Finsupp, Finsupp.coeFnAddHom.toAddHom, TwoUniqueSums, TwoUniqueSums.of_injective_addHom, coeFnAddHom, coe_injective, eq_iff_eq, of_injective_addHom, opEquiv, opEquiv.symm.eq_iff_eq, toAddHom
-/
theorem unop_inj {S T : Submonoid Mᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

@[to_additive (attr := simp)]
/--
theorem `op_bot` / 定理 `op_bot`

English:
theorem op_bot
  statement: (⊥ : Submonoid M).op = ⊥
  proof: opEquiv.map_bot

@[to_additive (attr := simp)]

中文:
定理 op_bot
  结论: (⊥ : Submonoid M).op = ⊥
  证明: opEquiv.map_bot

@[to_additive (attr := simp)]

Depends on / 依赖: map_bot, opEquiv, opEquiv.map_bot
-/
theorem op_bot : (⊥ : Submonoid M).op = ⊥ := opEquiv.map_bot

@[to_additive (attr := simp)]
/--
theorem `op_eq_bot` / 定理 `op_eq_bot`

English:
theorem op_eq_bot
  given: {S : Submonoid M}
  statement: S.op = ⊥ ↔ S = ⊥
  proof: op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]

中文:
定理 op_eq_bot
  条件: {S : Submonoid M}
  结论: S.op = ⊥ ↔ S = ⊥
  证明: op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, op_bot, op_injective, op_injective.eq_iff
-/
theorem op_eq_bot {S : Submonoid M} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]
/--
theorem `unop_bot` / 定理 `unop_bot`

English:
theorem unop_bot
  statement: (⊥ : Submonoid Mᵐᵒᵖ).unop = ⊥
  proof: opEquiv.symm.map_bot

@[to_additive (attr := simp)]

中文:
定理 unop_bot
  结论: (⊥ : Submonoid Mᵐᵒᵖ).unop = ⊥
  证明: opEquiv.symm.map_bot

@[to_additive (attr := simp)]

Depends on / 依赖: map_bot, opEquiv, opEquiv.symm.map_bot
-/
theorem unop_bot : (⊥ : Submonoid Mᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[to_additive (attr := simp)]
/--
theorem `unop_eq_bot` / 定理 `unop_eq_bot`

English:
theorem unop_eq_bot
  given: {S : Submonoid Mᵐᵒᵖ}
  statement: S.unop = ⊥ ↔ S = ⊥
  proof: unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]

中文:
定理 unop_eq_bot
  条件: {S : Submonoid Mᵐᵒᵖ}
  结论: S.unop = ⊥ ↔ S = ⊥
  证明: unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, unop_bot, unop_injective, unop_injective.eq_iff
-/
theorem unop_eq_bot {S : Submonoid Mᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]
/--
theorem `op_top` / 定理 `op_top`

English:
theorem op_top
  statement: (⊤ : Submonoid M).op = ⊤
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 op_top
  结论: (⊤ : Submonoid M).op = ⊤
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem op_top : (⊤ : Submonoid M).op = ⊤ := rfl

@[to_additive (attr := simp)]
/--
theorem `op_eq_top` / 定理 `op_eq_top`

English:
theorem op_eq_top
  given: {S : Submonoid M}
  statement: S.op = ⊤ ↔ S = ⊤
  proof: op_injective.eq_iff' op_top

@[to_additive (attr := simp)]

中文:
定理 op_eq_top
  条件: {S : Submonoid M}
  结论: S.op = ⊤ ↔ S = ⊤
  证明: op_injective.eq_iff' op_top

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, op_injective, op_injective.eq_iff, op_top
-/
theorem op_eq_top {S : Submonoid M} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[to_additive (attr := simp)]
/--
theorem `unop_top` / 定理 `unop_top`

English:
theorem unop_top
  statement: (⊤ : Submonoid Mᵐᵒᵖ).unop = ⊤
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unop_top
  结论: (⊤ : Submonoid Mᵐᵒᵖ).unop = ⊤
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unop_top : (⊤ : Submonoid Mᵐᵒᵖ).unop = ⊤ := rfl

@[to_additive (attr := simp)]
/--
theorem `unop_eq_top` / 定理 `unop_eq_top`

English:
theorem unop_eq_top
  given: {S : Submonoid Mᵐᵒᵖ}
  statement: S.unop = ⊤ ↔ S = ⊤
  proof: unop_injective.eq_iff' unop_top

@[to_additive]

中文:
定理 unop_eq_top
  条件: {S : Submonoid Mᵐᵒᵖ}
  结论: S.unop = ⊤ ↔ S = ⊤
  证明: unop_injective.eq_iff' unop_top

@[to_additive]

Depends on / 依赖: eq_iff, unop_injective, unop_injective.eq_iff, unop_top
-/
theorem unop_eq_top {S : Submonoid Mᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' unop_top

@[to_additive]
/--
theorem `op_sup` / 定理 `op_sup`

English:
theorem op_sup
  given: (S₁ S₂ : Submonoid M)
  statement: (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
  proof: opEquiv.map_sup _ _

@[to_additive]

中文:
定理 op_sup
  条件: (S₁ S₂ : Submonoid M)
  结论: (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
  证明: opEquiv.map_sup _ _

@[to_additive]

Depends on / 依赖: map_sup, opEquiv, opEquiv.map_sup
-/
theorem op_sup (S₁ S₂ : Submonoid M) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

@[to_additive]
/--
theorem `unop_sup` / 定理 `unop_sup`

English:
theorem unop_sup
  given: (S₁ S₂ : Submonoid Mᵐᵒᵖ)
  statement: (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
  proof: opEquiv.symm.map_sup _ _

@[to_additive]

中文:
定理 unop_sup
  条件: (S₁ S₂ : Submonoid Mᵐᵒᵖ)
  结论: (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
  证明: opEquiv.symm.map_sup _ _

@[to_additive]

Depends on / 依赖: map_sup, opEquiv, opEquiv.symm.map_sup
-/
theorem unop_sup (S₁ S₂ : Submonoid Mᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

@[to_additive]
/--
theorem `op_inf` / 定理 `op_inf`

English:
theorem op_inf
  given: (S₁ S₂ : Submonoid M)
  statement: (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
  proof: rfl

@[to_additive]

中文:
定理 op_inf
  条件: (S₁ S₂ : Submonoid M)
  结论: (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
  证明: rfl

@[to_additive]
-/
theorem op_inf (S₁ S₂ : Submonoid M) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

@[to_additive]
/--
theorem `unop_inf` / 定理 `unop_inf`

English:
theorem unop_inf
  given: (S₁ S₂ : Submonoid Mᵐᵒᵖ)
  statement: (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
  proof: rfl

@[to_additive]

中文:
定理 unop_inf
  条件: (S₁ S₂ : Submonoid Mᵐᵒᵖ)
  结论: (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
  证明: rfl

@[to_additive]
-/
theorem unop_inf (S₁ S₂ : Submonoid Mᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

@[to_additive]
/--
theorem `op_sSup` / 定理 `op_sSup`

English:
theorem op_sSup
  given: (S : Set (Submonoid M))
  statement: (sSup S).op = sSup (.unop ⁻¹' S)
  proof: opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

中文:
定理 op_sSup
  条件: (S : Set (Submonoid M))
  结论: (sSup S).op = sSup (.unop ⁻¹' S)
  证明: opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

Depends on / 依赖: map_sSup_eq_sSup_symm_preimage, opEquiv, opEquiv.map_sSup_eq_sSup_symm_preimage
-/
theorem op_sSup (S : Set (Submonoid M)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
/--
theorem `unop_sSup` / 定理 `unop_sSup`

English:
theorem unop_sSup
  given: (S : Set (Submonoid Mᵐᵒᵖ))
  statement: (sSup S).unop = sSup (.op ⁻¹' S)
  proof: opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

中文:
定理 unop_sSup
  条件: (S : Set (Submonoid Mᵐᵒᵖ))
  结论: (sSup S).unop = sSup (.op ⁻¹' S)
  证明: opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

Depends on / 依赖: map_sSup_eq_sSup_symm_preimage, opEquiv, opEquiv.symm.map_sSup_eq_sSup_symm_preimage
-/
theorem unop_sSup (S : Set (Submonoid Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
/--
theorem `op_sInf` / 定理 `op_sInf`

English:
theorem op_sInf
  given: (S : Set (Submonoid M))
  statement: (sInf S).op = sInf (.unop ⁻¹' S)
  proof: opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

中文:
定理 op_sInf
  条件: (S : Set (Submonoid M))
  结论: (sInf S).op = sInf (.unop ⁻¹' S)
  证明: opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

Depends on / 依赖: map_sInf_eq_sInf_symm_preimage, opEquiv, opEquiv.map_sInf_eq_sInf_symm_preimage
-/
theorem op_sInf (S : Set (Submonoid M)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
/--
theorem `unop_sInf` / 定理 `unop_sInf`

English:
theorem unop_sInf
  given: (S : Set (Submonoid Mᵐᵒᵖ))
  statement: (sInf S).unop = sInf (.op ⁻¹' S)
  proof: opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

中文:
定理 unop_sInf
  条件: (S : Set (Submonoid Mᵐᵒᵖ))
  结论: (sInf S).unop = sInf (.op ⁻¹' S)
  证明: opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

Depends on / 依赖: map_sInf_eq_sInf_symm_preimage, opEquiv, opEquiv.symm.map_sInf_eq_sInf_symm_preimage
-/
theorem unop_sInf (S : Set (Submonoid Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
/--
theorem `op_iSup` / 定理 `op_iSup`

English:
theorem op_iSup
  given: (S : ι -> Submonoid M)
  statement: (iSup S).op = ⨆ i, (S i).op
  proof: opEquiv.map_iSup _

@[to_additive]

中文:
定理 op_iSup
  条件: (S : ι -> Submonoid M)
  结论: (iSup S).op = ⨆ i, (S i).op
  证明: opEquiv.map_iSup _

@[to_additive]

Depends on / 依赖: map_iSup, opEquiv, opEquiv.map_iSup
-/
theorem op_iSup (S : ι -> Submonoid M) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

@[to_additive]
/--
theorem `unop_iSup` / 定理 `unop_iSup`

English:
theorem unop_iSup
  given: (S : ι -> Submonoid Mᵐᵒᵖ)
  statement: (iSup S).unop = ⨆ i, (S i).unop
  proof: opEquiv.symm.map_iSup _

@[to_additive]

中文:
定理 unop_iSup
  条件: (S : ι -> Submonoid Mᵐᵒᵖ)
  结论: (iSup S).unop = ⨆ i, (S i).unop
  证明: opEquiv.symm.map_iSup _

@[to_additive]

Depends on / 依赖: map_iSup, opEquiv, opEquiv.symm.map_iSup
-/
theorem unop_iSup (S : ι -> Submonoid Mᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

@[to_additive]
/--
theorem `op_iInf` / 定理 `op_iInf`

English:
theorem op_iInf
  given: (S : ι -> Submonoid M)
  statement: (iInf S).op = ⨅ i, (S i).op
  proof: opEquiv.map_iInf _

@[to_additive]

中文:
定理 op_iInf
  条件: (S : ι -> Submonoid M)
  结论: (iInf S).op = ⨅ i, (S i).op
  证明: opEquiv.map_iInf _

@[to_additive]

Depends on / 依赖: map_iInf, opEquiv, opEquiv.map_iInf
-/
theorem op_iInf (S : ι -> Submonoid M) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

@[to_additive]
/--
theorem `unop_iInf` / 定理 `unop_iInf`

English:
theorem unop_iInf
  given: (S : ι -> Submonoid Mᵐᵒᵖ)
  statement: (iInf S).unop = ⨅ i, (S i).unop
  proof: opEquiv.symm.map_iInf _

@[to_additive]

中文:
定理 unop_iInf
  条件: (S : ι -> Submonoid Mᵐᵒᵖ)
  结论: (iInf S).unop = ⨅ i, (S i).unop
  证明: opEquiv.symm.map_iInf _

@[to_additive]

Depends on / 依赖: map_iInf, opEquiv, opEquiv.symm.map_iInf
-/
theorem unop_iInf (S : ι -> Submonoid Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

@[to_additive]
/--
theorem `op_closure` / 定理 `op_closure`

English:
theorem op_closure
  given: (s : Set M)
  statement: (closure s).op = closure (MulOpposite.unop ⁻¹' s)
  proof: by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Submonoid.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]

中文:
定理 op_closure
  条件: (s : Set M)
  结论: (closure s).op = closure (MulOpposite.unop ⁻¹' s)
  证明: by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Submonoid.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.unop_surjective.forall, Set.preimage_ofPred_eq, Submonoid, Submonoid.coe_unop, closure, coe_unop, op_sInf, preimage_ofPred_eq, simp_rw, unop_surjective
-/
theorem op_closure (s : Set M) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Submonoid.coe_unop]
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
  条件: (s : Set Mᵐᵒᵖ)
  结论: (closure s).unop = closure (MulOpposite.op ⁻¹' s)
  证明: by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

Depends on / 依赖: MulOpposite, MulOpposite.op_unop, Set.preimage_id, Set.preimage_preimage, op_closure, op_inj, op_unop, preimage_id, preimage_preimage, simp_rw
-/
theorem unop_closure (s : Set Mᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

/-- Bijection between a submonoid `H` and its opposite. -/
@[to_additive (attr := simps!) /-- Bijection between an additive submonoid `H` and its opposite. -/]
/--
Definition of `equivOp` / `equivOp` 的定义

English:
definition equivOp
  signature: (H : Submonoid M)
  body: MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

中文:
定义 equivOp
  签名: (H : Submonoid M)
  定义体: MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

Depends on / 依赖: Iff.rfl, MulOpposite, MulOpposite.opEquiv.subtypeEquiv, opEquiv, subtypeEquiv
-/
def equivOp (H : Submonoid M) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

end Submonoid
