/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.MulOpposite

/-!
# Mul-opposite subgroups

## Tags
subgroup, subgroups

-/

@[expose] public section

variable {ι : Sort*} {G : Type*} [Group G]

namespace Subgroup

/-- Pull a subgroup back to an opposite subgroup along `MulOpposite.unop` -/
@[to_additive (attr := simps)
/-- Pull an additive subgroup back to an opposite additive subgroup along `AddOpposite.unop` -/]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (H : Subgroup G)
  body: MulOpposite.unop ⁻¹' (H : Set G)
  one_mem' := H.one_mem
  mul_mem' ha hb := H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]

中文:
定义 op
  签名: (H : Subgroup G)
  定义体: MulOpposite.unop ⁻¹' (H : Set G)
  one_mem' := H.one_mem
  mul_mem' ha hb := H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]
-/
protected def op (H : Subgroup G) : Subgroup Gᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' (H : Set G)
  one_mem' := H.one_mem
  mul_mem' ha hb := H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]
/--
theorem `mem_op` / 定理 `mem_op`

English:
theorem mem_op
  given: {x : Gᵐᵒᵖ} {S : Subgroup G}
  statement: x in S.op ↔ x.unop in S
  proof: Iff.rfl

中文:
定理 mem_op
  条件: {x : Gᵐᵒᵖ} {S : Subgroup G}
  结论: x in S.op ↔ x.unop in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_op {x : Gᵐᵒᵖ} {S : Subgroup G} : x in S.op ↔ x.unop in S := Iff.rfl

/--
lemma `op_toSubmonoid` / 引理 `op_toSubmonoid`

English:
lemma op_toSubmonoid
  given: (H : Subgroup G)
  proof: rfl

中文:
引理 op_toSubmonoid
  条件: (H : Subgroup G)
  证明: rfl
-/
@[to_additive (attr := simp)] lemma op_toSubmonoid (H : Subgroup G) :
    H.op.toSubmonoid = H.toSubmonoid.op :=
  rfl

/--
lemma `op_toSubsemigroup` / 引理 `op_toSubsemigroup`

English:
lemma op_toSubsemigroup
  given: (H : Subgroup G)
  proof: by
  dsimp

中文:
引理 op_toSubsemigroup
  条件: (H : Subgroup G)
  证明: by
  dsimp
-/
@[to_additive] lemma op_toSubsemigroup (H : Subgroup G) :
    H.op.toSubsemigroup = H.toSubsemigroup.op := by
  dsimp

/-- Pull an opposite subgroup back to a subgroup along `MulOpposite.op` -/
@[to_additive (attr := simps)
/-- Pull an opposite additive subgroup back to an additive subgroup along `AddOpposite.op` -/]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (H : Subgroup Gᵐᵒᵖ)
  body: MulOpposite.op ⁻¹' (H : Set Gᵐᵒᵖ)
  one_mem' := H.one_mem
  mul_mem' := fun ha hb => H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]

中文:
定义 unop
  签名: (H : Subgroup Gᵐᵒᵖ)
  定义体: MulOpposite.op ⁻¹' (H : Set Gᵐᵒᵖ)
  one_mem' := H.one_mem
  mul_mem' := fun ha hb => H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]
-/
protected def unop (H : Subgroup Gᵐᵒᵖ) : Subgroup G where
  carrier := MulOpposite.op ⁻¹' (H : Set Gᵐᵒᵖ)
  one_mem' := H.one_mem
  mul_mem' := fun ha hb => H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]
/--
theorem `mem_unop` / 定理 `mem_unop`

English:
theorem mem_unop
  given: {x : G} {S : Subgroup Gᵐᵒᵖ}
  statement: x in S.unop ↔ MulOpposite.op x in S
  proof: Iff.rfl

中文:
定理 mem_unop
  条件: {x : G} {S : Subgroup Gᵐᵒᵖ}
  结论: x in S.unop ↔ MulOpposite.op x in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_unop {x : G} {S : Subgroup Gᵐᵒᵖ} : x in S.unop ↔ MulOpposite.op x in S := Iff.rfl

/--
lemma `unop_toSubmonoid` / 引理 `unop_toSubmonoid`

English:
lemma unop_toSubmonoid
  given: (H : Subgroup Gᵐᵒᵖ)
  proof: rfl

中文:
引理 unop_toSubmonoid
  条件: (H : Subgroup Gᵐᵒᵖ)
  证明: rfl
-/
@[to_additive (attr := simp)] lemma unop_toSubmonoid (H : Subgroup Gᵐᵒᵖ) :
    H.unop.toSubmonoid = H.toSubmonoid.unop :=
  rfl

/--
lemma `unop_toSubsemigroup` / 引理 `unop_toSubsemigroup`

English:
lemma unop_toSubsemigroup
  given: (H : Subgroup Gᵐᵒᵖ)
  proof: by
  dsimp

@[to_additive (attr := simp)]

中文:
引理 unop_toSubsemigroup
  条件: (H : Subgroup Gᵐᵒᵖ)
  证明: by
  dsimp

@[to_additive (attr := simp)]
-/
@[to_additive] lemma unop_toSubsemigroup (H : Subgroup Gᵐᵒᵖ) :
    H.unop.toSubsemigroup = H.toSubsemigroup.unop := by
  dsimp

@[to_additive (attr := simp)]
/--
theorem `unop_op` / 定理 `unop_op`

English:
theorem unop_op
  given: (S : Subgroup G)
  statement: S.op.unop = S
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unop_op
  条件: (S : Subgroup G)
  结论: S.op.unop = S
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unop_op (S : Subgroup G) : S.op.unop = S := rfl

@[to_additive (attr := simp)]
/--
theorem `op_unop` / 定理 `op_unop`

English:
theorem op_unop
  given: (S : Subgroup Gᵐᵒᵖ)
  statement: S.unop.op = S
  proof: rfl

中文:
定理 op_unop
  条件: (S : Subgroup Gᵐᵒᵖ)
  结论: S.unop.op = S
  证明: rfl
-/
theorem op_unop (S : Subgroup Gᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

@[to_additive]
/--
theorem `op_le_iff` / 定理 `op_le_iff`

English:
theorem op_le_iff
  given: {S₁ : Subgroup G} {S₂ : Subgroup Gᵐᵒᵖ}
  statement: S₁.op <= S₂ ↔ S₁ <= S₂.unop
  proof: MulOpposite.op_surjective.forall

@[to_additive]

中文:
定理 op_le_iff
  条件: {S₁ : Subgroup G} {S₂ : Subgroup Gᵐᵒᵖ}
  结论: S₁.op <= S₂ ↔ S₁ <= S₂.unop
  证明: MulOpposite.op_surjective.forall

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem op_le_iff {S₁ : Subgroup G} {S₂ : Subgroup Gᵐᵒᵖ} : S₁.op <= S₂ ↔ S₁ <= S₂.unop :=
  MulOpposite.op_surjective.forall

@[to_additive]
/--
theorem `le_op_iff` / 定理 `le_op_iff`

English:
theorem le_op_iff
  given: {S₁ : Subgroup Gᵐᵒᵖ} {S₂ : Subgroup G}
  statement: S₁ <= S₂.op ↔ S₁.unop <= S₂
  proof: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

中文:
定理 le_op_iff
  条件: {S₁ : Subgroup Gᵐᵒᵖ} {S₂ : Subgroup G}
  结论: S₁ <= S₂.op ↔ S₁.unop <= S₂
  证明: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem le_op_iff {S₁ : Subgroup Gᵐᵒᵖ} {S₂ : Subgroup G} : S₁ <= S₂.op ↔ S₁.unop <= S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
/--
theorem `op_le_op_iff` / 定理 `op_le_op_iff`

English:
theorem op_le_op_iff
  given: {S₁ S₂ : Subgroup G}
  statement: S₁.op <= S₂.op ↔ S₁ <= S₂
  proof: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

中文:
定理 op_le_op_iff
  条件: {S₁ S₂ : Subgroup G}
  结论: S₁.op <= S₂.op ↔ S₁ <= S₂
  证明: MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem op_le_op_iff {S₁ S₂ : Subgroup G} : S₁.op <= S₂.op ↔ S₁ <= S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
/--
theorem `unop_le_unop_iff` / 定理 `unop_le_unop_iff`

English:
theorem unop_le_unop_iff
  given: {S₁ S₂ : Subgroup Gᵐᵒᵖ}
  statement: S₁.unop <= S₂.unop ↔ S₁ <= S₂
  proof: MulOpposite.unop_surjective.forall

中文:
定理 unop_le_unop_iff
  条件: {S₁ S₂ : Subgroup Gᵐᵒᵖ}
  结论: S₁.unop <= S₂.unop ↔ S₁ <= S₂
  证明: MulOpposite.unop_surjective.forall

Depends on / 依赖: MulOpposite, MulOpposite.unop_surjective.forall, unop_surjective
-/
theorem unop_le_unop_iff {S₁ S₂ : Subgroup Gᵐᵒᵖ} : S₁.unop <= S₂.unop ↔ S₁ <= S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subgroup `H` of `G` determines a subgroup `H.op` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive (attr := simps) /-- An additive subgroup `H` of `G` determines an additive subgroup
`H.op` of the opposite additive group `Gᵃᵒᵖ`. -/]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : Subgroup G ≃o Subgroup Gᵐᵒᵖ where
  body: Subgroup.op
  invFun := Subgroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]

中文:
定义 opEquiv
  签名: : Subgroup G ≃o Subgroup Gᵐᵒᵖ where
  定义体: Subgroup.op
  invFun := Subgroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.op
-/
def opEquiv : Subgroup G ≃o Subgroup Gᵐᵒᵖ where
  toFun := Subgroup.op
  invFun := Subgroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]
/--
theorem `op_injective` / 定理 `op_injective`

English:
theorem op_injective
  statement: (@Subgroup.op G _).Injective
  proof: opEquiv.injective

@[to_additive]

中文:
定理 op_injective
  结论: (@Subgroup.op G _).Injective
  证明: opEquiv.injective

@[to_additive]

Depends on / 依赖: injective, opEquiv, opEquiv.injective
-/
theorem op_injective : (@Subgroup.op G _).Injective := opEquiv.injective

@[to_additive]
/--
theorem `unop_injective` / 定理 `unop_injective`

English:
theorem unop_injective
  statement: (@Subgroup.unop G _).Injective
  proof: opEquiv.symm.injective

@[to_additive (attr := simp)]

中文:
定理 unop_injective
  结论: (@Subgroup.unop G _).Injective
  证明: opEquiv.symm.injective

@[to_additive (attr := simp)]

Depends on / 依赖: injective, opEquiv, opEquiv.symm.injective
-/
theorem unop_injective : (@Subgroup.unop G _).Injective := opEquiv.symm.injective

@[to_additive (attr := simp)]
/--
theorem `op_inj` / 定理 `op_inj`

English:
theorem op_inj
  given: {S T : Subgroup G}
  statement: S.op = T.op ↔ S = T
  proof: opEquiv.eq_iff_eq

@[to_additive (attr := simp)]

中文:
定理 op_inj
  条件: {S T : Subgroup G}
  结论: S.op = T.op ↔ S = T
  证明: opEquiv.eq_iff_eq

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff_eq, opEquiv, opEquiv.eq_iff_eq
-/
theorem op_inj {S T : Subgroup G} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq

@[to_additive (attr := simp)]
/--
theorem `unop_inj` / 定理 `unop_inj`

English:
theorem unop_inj
  given: {S T : Subgroup Gᵐᵒᵖ}
  statement: S.unop = T.unop ↔ S = T
  proof: opEquiv.symm.eq_iff_eq

中文:
定理 unop_inj
  条件: {S T : Subgroup Gᵐᵒᵖ}
  结论: S.unop = T.unop ↔ S = T
  证明: opEquiv.symm.eq_iff_eq

Depends on / 依赖: eq_iff_eq, opEquiv, opEquiv.symm.eq_iff_eq
-/
theorem unop_inj {S T : Subgroup Gᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

/-- Bijection between a subgroup `H` and its opposite. -/
@[to_additive (attr := simps!) /-- Bijection between an additive subgroup `H` and its opposite. -/]
/--
Definition of `equivOp` / `equivOp` 的定义

English:
definition equivOp
  signature: (H : Subgroup G)
  body: MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

@[to_additive]

中文:
定义 equivOp
  签名: (H : Subgroup G)
  定义体: MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl, MulOpposite, MulOpposite.opEquiv.subtypeEquiv, opEquiv, subtypeEquiv
-/
def equivOp (H : Subgroup G) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

@[to_additive]
/--
theorem `op_normalizer` / 定理 `op_normalizer`

English:
theorem op_normalizer
  given: (H : Subgroup G)
  statement: (normalizer H : Subgroup G).op = normalizer H.op
  proof: by
  ext x
  rw [mem_op]; rw [mem_normalizer_iff']; rw [mem_normalizer_iff']
  simp [iff_comm]

@[to_additive]

中文:
定理 op_normalizer
  条件: (H : Subgroup G)
  结论: (normalizer H : Subgroup G).op = normalizer H.op
  证明: by
  ext x
  rw [mem_op]; rw [mem_normalizer_iff']; rw [mem_normalizer_iff']
  simp [iff_comm]

@[to_additive]

Depends on / 依赖: iff_comm, mem_normalizer_iff, mem_op
-/
theorem op_normalizer (H : Subgroup G) : (normalizer H : Subgroup G).op = normalizer H.op := by
  ext x
  rw [mem_op]; rw [mem_normalizer_iff']; rw [mem_normalizer_iff']
  simp [iff_comm]

@[to_additive]
/--
theorem `unop_normalizer` / 定理 `unop_normalizer`

English:
theorem unop_normalizer
  given: (H : Subgroup Gᵐᵒᵖ)
  proof: by
  rw [← op_inj]; rw [op_unop]; rw [op_normalizer]; rw [op_unop]

中文:
定理 unop_normalizer
  条件: (H : Subgroup Gᵐᵒᵖ)
  证明: by
  rw [← op_inj]; rw [op_unop]; rw [op_normalizer]; rw [op_unop]

Depends on / 依赖: op_inj, op_normalizer, op_unop
-/
theorem unop_normalizer (H : Subgroup Gᵐᵒᵖ) :
    (normalizer H).unop = normalizer (H.unop : Set G) := by
  rw [← op_inj]; rw [op_unop]; rw [op_normalizer]; rw [op_unop]

end Subgroup
