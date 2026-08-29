/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.MulOpposite
public import Mathlib.Algebra.Ring.Subring.Basic

/-!

# Subring of opposite rings

For every ring `R`, we construct an equivalence between subrings of `R` and that of `Rᵐᵒᵖ`.

-/

@[expose] public section

namespace Subring

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

/-- Pull a subring back to an opposite subring along `MulOpposite.unop` -/
@[simps! coe toSubsemiring]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (S : Subring R)
  body: S.toSubsemiring.op
  neg_mem' := by simp

中文:
定义 op
  签名: (S : 子环 R)
  定义体: S.toSubsemiring.op
  neg_mem' := by simp

Depends on / 依赖: IsAffineOpen, IsAffineOpen.fromSpecStalk_isPreimmersion, fromSpecStalk_isPreimmersion
-/
protected def op (S : Subring R) : Subring Rᵐᵒᵖ where
  toSubsemiring := S.toSubsemiring.op
  neg_mem' := by simp

attribute [norm_cast] coe_op

@[simp]
/--
theorem `mem_op` / 定理 `mem_op`

English:
theorem mem_op
  given: {x : Rᵐᵒᵖ} {S : Subring R}
  statement: x in S.op ↔ x.unop in S
  proof: Iff.rfl

中文:
定理 mem_op
  条件: {x : Rᵐᵒᵖ} {S : 子环 R}
  结论: x in S.op ↔ x.unop in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_op {x : Rᵐᵒᵖ} {S : Subring R} : x in S.op ↔ x.unop in S := Iff.rfl

/-- Pull an opposite subring back to a subring along `MulOpposite.op` -/
@[simps! coe toSubsemiring]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (S : Subring Rᵐᵒᵖ)
  body: S.toSubsemiring.unop
  neg_mem' := by simp

中文:
定义 unop
  签名: (S : 子环 Rᵐᵒᵖ)
  定义体: S.toSubsemiring.unop
  neg_mem' := by simp
-/
protected def unop (S : Subring Rᵐᵒᵖ) : Subring R where
  toSubsemiring := S.toSubsemiring.unop
  neg_mem' := by simp

attribute [norm_cast] coe_unop

@[simp]
/--
theorem `mem_unop` / 定理 `mem_unop`

English:
theorem mem_unop
  given: {x : R} {S : Subring Rᵐᵒᵖ}
  statement: x in S.unop ↔ MulOpposite.op x in S
  proof: Iff.rfl

@[simp]

中文:
定理 mem_unop
  条件: {x : R} {S : 子环 Rᵐᵒᵖ}
  结论: x in S.unop ↔ MulOpposite.op x in S
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_unop {x : R} {S : Subring Rᵐᵒᵖ} : x in S.unop ↔ MulOpposite.op x in S := Iff.rfl

@[simp]
/--
theorem `unop_op` / 定理 `unop_op`

English:
theorem unop_op
  given: (S : Subring R)
  statement: S.op.unop = S
  proof: rfl

@[simp]

中文:
定理 unop_op
  条件: (S : 子环 R)
  结论: S.op.unop = S
  证明: rfl

@[simp]
-/
theorem unop_op (S : Subring R) : S.op.unop = S := rfl

@[simp]
/--
theorem `op_unop` / 定理 `op_unop`

English:
theorem op_unop
  given: (S : Subring Rᵐᵒᵖ)
  statement: S.unop.op = S
  proof: rfl

中文:
定理 op_unop
  条件: (S : 子环 Rᵐᵒᵖ)
  结论: S.unop.op = S
  证明: rfl
-/
theorem op_unop (S : Subring Rᵐᵒᵖ) : S.unop.op = S := rfl


/--
theorem `op_le_iff` / 定理 `op_le_iff`

English:
theorem op_le_iff
  given: {S₁ : Subring R} {S₂ : Subring Rᵐᵒᵖ}
  statement: S₁.op <= S₂ ↔ S₁ <= S₂.unop
  proof: MulOpposite.op_surjective.forall

中文:
定理 op_le_iff
  条件: {S₁ : 子环 R} {S₂ : 子环 Rᵐᵒᵖ}
  结论: S₁.op <= S₂ ↔ S₁ <= S₂.unop
  证明: MulOpposite.op_surjective.forall

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem op_le_iff {S₁ : Subring R} {S₂ : Subring Rᵐᵒᵖ} : S₁.op <= S₂ ↔ S₁ <= S₂.unop :=
  MulOpposite.op_surjective.forall

/--
theorem `le_op_iff` / 定理 `le_op_iff`

English:
theorem le_op_iff
  given: {S₁ : Subring Rᵐᵒᵖ} {S₂ : Subring R}
  statement: S₁ <= S₂.op ↔ S₁.unop <= S₂
  proof: MulOpposite.op_surjective.forall

@[simp]

中文:
定理 le_op_iff
  条件: {S₁ : 子环 Rᵐᵒᵖ} {S₂ : 子环 R}
  结论: S₁ <= S₂.op ↔ S₁.unop <= S₂
  证明: MulOpposite.op_surjective.forall

@[simp]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem le_op_iff {S₁ : Subring Rᵐᵒᵖ} {S₂ : Subring R} : S₁ <= S₂.op ↔ S₁.unop <= S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
/--
theorem `op_le_op_iff` / 定理 `op_le_op_iff`

English:
theorem op_le_op_iff
  given: {S₁ S₂ : Subring R}
  statement: S₁.op <= S₂.op ↔ S₁ <= S₂
  proof: MulOpposite.op_surjective.forall

@[simp]

中文:
定理 op_le_op_iff
  条件: {S₁ S₂ : 子环 R}
  结论: S₁.op <= S₂.op ↔ S₁ <= S₂
  证明: MulOpposite.op_surjective.forall

@[simp]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem op_le_op_iff {S₁ S₂ : Subring R} : S₁.op <= S₂.op ↔ S₁ <= S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
/--
theorem `unop_le_unop_iff` / 定理 `unop_le_unop_iff`

English:
theorem unop_le_unop_iff
  given: {S₁ S₂ : Subring Rᵐᵒᵖ}
  statement: S₁.unop <= S₂.unop ↔ S₁ <= S₂
  proof: MulOpposite.unop_surjective.forall

中文:
定理 unop_le_unop_iff
  条件: {S₁ S₂ : 子环 Rᵐᵒᵖ}
  结论: S₁.unop <= S₂.unop ↔ S₁ <= S₂
  证明: MulOpposite.unop_surjective.forall

Depends on / 依赖: MulOpposite, MulOpposite.unop_surjective.forall, unop_surjective
-/
theorem unop_le_unop_iff {S₁ S₂ : Subring Rᵐᵒᵖ} : S₁.unop <= S₂.unop ↔ S₁ <= S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subring `S` of `R` determines a subring `S.op` of the opposite ring `Rᵐᵒᵖ`. -/
@[simps]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : Subring R ≃o Subring Rᵐᵒᵖ where
  body: Subring.op
  invFun := Subring.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

中文:
定义 opEquiv
  签名: : 子环 R ≃o 子环 Rᵐᵒᵖ where
  定义体: Subring.op
  invFun := Subring.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

Depends on / 依赖: Subring, Subring.op
-/
def opEquiv : Subring R ≃o Subring Rᵐᵒᵖ where
  toFun := Subring.op
  invFun := Subring.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

/--
theorem `op_injective` / 定理 `op_injective`

English:
theorem op_injective
  statement: (@Subring.op R _).Injective
  proof: opEquiv.injective

中文:
定理 op_injective
  结论: (@子环.op R _).单射
  证明: opEquiv.injective

Depends on / 依赖: injective, opEquiv, opEquiv.injective
-/
theorem op_injective : (@Subring.op R _).Injective := opEquiv.injective
/--
theorem `unop_injective` / 定理 `unop_injective`

English:
theorem unop_injective
  statement: (@Subring.unop R _).Injective
  proof: opEquiv.symm.injective

中文:
定理 unop_injective
  结论: (@子环.unop R _).单射
  证明: opEquiv.symm.injective

Depends on / 依赖: injective, opEquiv, opEquiv.symm.injective
-/
theorem unop_injective : (@Subring.unop R _).Injective := opEquiv.symm.injective
/--
theorem `op_inj` / 定理 `op_inj`

English:
theorem op_inj
  given: {S T : Subring R}
  statement: S.op = T.op ↔ S = T
  proof: opEquiv.eq_iff_eq

中文:
定理 op_inj
  条件: {S T : 子环 R}
  结论: S.op = T.op ↔ S = T
  证明: opEquiv.eq_iff_eq
-/
@[simp] theorem op_inj {S T : Subring R} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq
/--
theorem `unop_inj` / 定理 `unop_inj`

English:
theorem unop_inj
  given: {S T : Subring Rᵐᵒᵖ}
  statement: S.unop = T.unop ↔ S = T
  proof: opEquiv.symm.eq_iff_eq

@[simp]

中文:
定理 unop_inj
  条件: {S T : 子环 Rᵐᵒᵖ}
  结论: S.unop = T.unop ↔ S = T
  证明: opEquiv.symm.eq_iff_eq

@[simp]
-/
@[simp] theorem unop_inj {S T : Subring Rᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

@[simp]
/--
theorem `op_bot` / 定理 `op_bot`

English:
theorem op_bot
  statement: (⊥ : Subring R).op = ⊥
  proof: opEquiv.map_bot

@[simp]

中文:
定理 op_bot
  结论: (⊥ : 子环 R).op = ⊥
  证明: opEquiv.map_bot

@[simp]

Depends on / 依赖: map_bot, opEquiv, opEquiv.map_bot
-/
theorem op_bot : (⊥ : Subring R).op = ⊥ := opEquiv.map_bot

@[simp]
/--
theorem `op_eq_bot` / 定理 `op_eq_bot`

English:
theorem op_eq_bot
  given: {S : Subring R}
  statement: S.op = ⊥ ↔ S = ⊥
  proof: op_injective.eq_iff' op_bot

@[simp]

中文:
定理 op_eq_bot
  条件: {S : 子环 R}
  结论: S.op = ⊥ ↔ S = ⊥
  证明: op_injective.eq_iff' op_bot

@[simp]

Depends on / 依赖: eq_iff, op_bot, op_injective, op_injective.eq_iff
-/
theorem op_eq_bot {S : Subring R} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' op_bot

@[simp]
/--
theorem `unop_bot` / 定理 `unop_bot`

English:
theorem unop_bot
  statement: (⊥ : Subring Rᵐᵒᵖ).unop = ⊥
  proof: opEquiv.symm.map_bot

@[simp]

中文:
定理 unop_bot
  结论: (⊥ : 子环 Rᵐᵒᵖ).unop = ⊥
  证明: opEquiv.symm.map_bot

@[simp]

Depends on / 依赖: map_bot, opEquiv, opEquiv.symm.map_bot
-/
theorem unop_bot : (⊥ : Subring Rᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[simp]
/--
theorem `unop_eq_bot` / 定理 `unop_eq_bot`

English:
theorem unop_eq_bot
  given: {S : Subring Rᵐᵒᵖ}
  statement: S.unop = ⊥ ↔ S = ⊥
  proof: unop_injective.eq_iff' unop_bot

@[simp]

中文:
定理 unop_eq_bot
  条件: {S : 子环 Rᵐᵒᵖ}
  结论: S.unop = ⊥ ↔ S = ⊥
  证明: unop_injective.eq_iff' unop_bot

@[simp]

Depends on / 依赖: eq_iff, unop_bot, unop_injective, unop_injective.eq_iff
-/
theorem unop_eq_bot {S : Subring Rᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[simp]
/--
theorem `op_top` / 定理 `op_top`

English:
theorem op_top
  statement: (⊤ : Subring R).op = ⊤
  proof: rfl

@[simp]

中文:
定理 op_top
  结论: (⊤ : 子环 R).op = ⊤
  证明: rfl

@[simp]
-/
theorem op_top : (⊤ : Subring R).op = ⊤ := rfl

@[simp]
/--
theorem `op_eq_top` / 定理 `op_eq_top`

English:
theorem op_eq_top
  given: {S : Subring R}
  statement: S.op = ⊤ ↔ S = ⊤
  proof: op_injective.eq_iff' op_top

@[simp]

中文:
定理 op_eq_top
  条件: {S : 子环 R}
  结论: S.op = ⊤ ↔ S = ⊤
  证明: op_injective.eq_iff' op_top

@[simp]

Depends on / 依赖: eq_iff, op_injective, op_injective.eq_iff, op_top
-/
theorem op_eq_top {S : Subring R} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[simp]
/--
theorem `unop_top` / 定理 `unop_top`

English:
theorem unop_top
  statement: (⊤ : Subring Rᵐᵒᵖ).unop = ⊤
  proof: rfl

@[simp]

中文:
定理 unop_top
  结论: (⊤ : 子环 Rᵐᵒᵖ).unop = ⊤
  证明: rfl

@[simp]
-/
theorem unop_top : (⊤ : Subring Rᵐᵒᵖ).unop = ⊤ := rfl

@[simp]
/--
theorem `unop_eq_top` / 定理 `unop_eq_top`

English:
theorem unop_eq_top
  given: {S : Subring Rᵐᵒᵖ}
  statement: S.unop = ⊤ ↔ S = ⊤
  proof: unop_injective.eq_iff' unop_top

中文:
定理 unop_eq_top
  条件: {S : 子环 Rᵐᵒᵖ}
  结论: S.unop = ⊤ ↔ S = ⊤
  证明: unop_injective.eq_iff' unop_top

Depends on / 依赖: eq_iff, unop_injective, unop_injective.eq_iff, unop_top
-/
theorem unop_eq_top {S : Subring Rᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' unop_top

/--
theorem `op_sup` / 定理 `op_sup`

English:
theorem op_sup
  given: (S₁ S₂ : Subring R)
  statement: (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
  proof: opEquiv.map_sup _ _

中文:
定理 op_sup
  条件: (S₁ S₂ : 子环 R)
  结论: (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
  证明: opEquiv.map_sup _ _

Depends on / 依赖: map_sup, opEquiv, opEquiv.map_sup
-/
theorem op_sup (S₁ S₂ : Subring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

/--
theorem `unop_sup` / 定理 `unop_sup`

English:
theorem unop_sup
  given: (S₁ S₂ : Subring Rᵐᵒᵖ)
  statement: (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
  proof: opEquiv.symm.map_sup _ _

中文:
定理 unop_sup
  条件: (S₁ S₂ : 子环 Rᵐᵒᵖ)
  结论: (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
  证明: opEquiv.symm.map_sup _ _

Depends on / 依赖: map_sup, opEquiv, opEquiv.symm.map_sup
-/
theorem unop_sup (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

/--
theorem `op_inf` / 定理 `op_inf`

English:
theorem op_inf
  given: (S₁ S₂ : Subring R)
  statement: (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
  proof: rfl

中文:
定理 op_inf
  条件: (S₁ S₂ : 子环 R)
  结论: (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
  证明: rfl
-/
theorem op_inf (S₁ S₂ : Subring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

/--
theorem `unop_inf` / 定理 `unop_inf`

English:
theorem unop_inf
  given: (S₁ S₂ : Subring Rᵐᵒᵖ)
  statement: (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
  proof: rfl

中文:
定理 unop_inf
  条件: (S₁ S₂ : 子环 Rᵐᵒᵖ)
  结论: (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
  证明: rfl
-/
theorem unop_inf (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

/--
theorem `op_sSup` / 定理 `op_sSup`

English:
theorem op_sSup
  given: (S : Set (Subring R))
  statement: (sSup S).op = sSup (.unop ⁻¹' S)
  proof: opEquiv.map_sSup_eq_sSup_symm_preimage _

中文:
定理 op_sSup
  条件: (S : 集合 (子环 R))
  结论: (sSup S).op = sSup (.unop ⁻¹' S)
  证明: opEquiv.map_sSup_eq_sSup_symm_preimage _

Depends on / 依赖: map_sSup_eq_sSup_symm_preimage, opEquiv, opEquiv.map_sSup_eq_sSup_symm_preimage
-/
theorem op_sSup (S : Set (Subring R)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

/--
theorem `unop_sSup` / 定理 `unop_sSup`

English:
theorem unop_sSup
  given: (S : Set (Subring Rᵐᵒᵖ))
  statement: (sSup S).unop = sSup (.op ⁻¹' S)
  proof: opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

中文:
定理 unop_sSup
  条件: (S : 集合 (子环 Rᵐᵒᵖ))
  结论: (sSup S).unop = sSup (.op ⁻¹' S)
  证明: opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

Depends on / 依赖: map_sSup_eq_sSup_symm_preimage, opEquiv, opEquiv.symm.map_sSup_eq_sSup_symm_preimage
-/
theorem unop_sSup (S : Set (Subring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

/--
theorem `op_sInf` / 定理 `op_sInf`

English:
theorem op_sInf
  given: (S : Set (Subring R))
  statement: (sInf S).op = sInf (.unop ⁻¹' S)
  proof: opEquiv.map_sInf_eq_sInf_symm_preimage _

中文:
定理 op_sInf
  条件: (S : 集合 (子环 R))
  结论: (sInf S).op = sInf (.unop ⁻¹' S)
  证明: opEquiv.map_sInf_eq_sInf_symm_preimage _

Depends on / 依赖: map_sInf_eq_sInf_symm_preimage, opEquiv, opEquiv.map_sInf_eq_sInf_symm_preimage
-/
theorem op_sInf (S : Set (Subring R)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

/--
theorem `unop_sInf` / 定理 `unop_sInf`

English:
theorem unop_sInf
  given: (S : Set (Subring Rᵐᵒᵖ))
  statement: (sInf S).unop = sInf (.op ⁻¹' S)
  proof: opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

中文:
定理 unop_sInf
  条件: (S : 集合 (子环 Rᵐᵒᵖ))
  结论: (sInf S).unop = sInf (.op ⁻¹' S)
  证明: opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

Depends on / 依赖: map_sInf_eq_sInf_symm_preimage, opEquiv, opEquiv.symm.map_sInf_eq_sInf_symm_preimage
-/
theorem unop_sInf (S : Set (Subring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

/--
theorem `op_iSup` / 定理 `op_iSup`

English:
theorem op_iSup
  given: (S : ι -> Subring R)
  statement: (iSup S).op = ⨆ i, (S i).op
  proof: opEquiv.map_iSup _

中文:
定理 op_iSup
  条件: (S : ι -> 子环 R)
  结论: (iSup S).op = ⨆ i, (S i).op
  证明: opEquiv.map_iSup _

Depends on / 依赖: map_iSup, opEquiv, opEquiv.map_iSup
-/
theorem op_iSup (S : ι -> Subring R) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

/--
theorem `unop_iSup` / 定理 `unop_iSup`

English:
theorem unop_iSup
  given: (S : ι -> Subring Rᵐᵒᵖ)
  statement: (iSup S).unop = ⨆ i, (S i).unop
  proof: opEquiv.symm.map_iSup _

中文:
定理 unop_iSup
  条件: (S : ι -> 子环 Rᵐᵒᵖ)
  结论: (iSup S).unop = ⨆ i, (S i).unop
  证明: opEquiv.symm.map_iSup _

Depends on / 依赖: map_iSup, opEquiv, opEquiv.symm.map_iSup
-/
theorem unop_iSup (S : ι -> Subring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

/--
theorem `op_iInf` / 定理 `op_iInf`

English:
theorem op_iInf
  given: (S : ι -> Subring R)
  statement: (iInf S).op = ⨅ i, (S i).op
  proof: opEquiv.map_iInf _

中文:
定理 op_iInf
  条件: (S : ι -> 子环 R)
  结论: (iInf S).op = ⨅ i, (S i).op
  证明: opEquiv.map_iInf _

Depends on / 依赖: map_iInf, opEquiv, opEquiv.map_iInf
-/
theorem op_iInf (S : ι -> Subring R) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

/--
theorem `unop_iInf` / 定理 `unop_iInf`

English:
theorem unop_iInf
  given: (S : ι -> Subring Rᵐᵒᵖ)
  statement: (iInf S).unop = ⨅ i, (S i).unop
  proof: opEquiv.symm.map_iInf _

中文:
定理 unop_iInf
  条件: (S : ι -> 子环 Rᵐᵒᵖ)
  结论: (iInf S).unop = ⨅ i, (S i).unop
  证明: opEquiv.symm.map_iInf _

Depends on / 依赖: map_iInf, opEquiv, opEquiv.symm.map_iInf
-/
theorem unop_iInf (S : ι -> Subring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

/--
theorem `op_closure` / 定理 `op_closure`

English:
theorem op_closure
  given: (s : Set R)
  statement: (closure s).op = closure (MulOpposite.unop ⁻¹' s)
  proof: by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

中文:
定理 op_closure
  条件: (s : 集合 R)
  结论: (closure s).op = closure (MulOpposite.unop ⁻¹' s)
  证明: by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

Depends on / 依赖: MulOpposite, MulOpposite.unop_surjective.forall, Set.preimage_ofPred_eq, closure, coe_unop, op_sInf, preimage_ofPred_eq, simp_rw, unop_surjective
-/
theorem op_closure (s : Set R) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

/--
theorem `unop_closure` / 定理 `unop_closure`

English:
theorem unop_closure
  given: (s : Set Rᵐᵒᵖ)
  statement: (closure s).unop = closure (MulOpposite.op ⁻¹' s)
  proof: by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

中文:
定理 unop_closure
  条件: (s : 集合 Rᵐᵒᵖ)
  结论: (closure s).unop = closure (MulOpposite.op ⁻¹' s)
  证明: by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

Depends on / 依赖: MulOpposite, MulOpposite.op_unop, Set.preimage_id, Set.preimage_preimage, op_closure, op_inj, op_unop, preimage_id, preimage_preimage, simp_rw
-/
theorem unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

/-- Bijection between a subring `S` and its opposite. -/
@[simps!]
/--
Definition of `addEquivOp` / `addEquivOp` 的定义

English:
definition addEquivOp
  signature: (S : Subring R)
  body: S.toSubsemiring.addEquivOp

中文:
定义 addEquivOp
  签名: (S : 子环 R)
  定义体: S.toSubsemiring.addEquivOp

Depends on / 依赖: S.toSubsemiring.addEquivOp, addEquivOp, toSubsemiring
-/
def addEquivOp (S : Subring R) : S ≃+ S.op := S.toSubsemiring.addEquivOp

/-- Bijection between a subring `S` and `MulOpposite` of its opposite. -/
@[simps!]
/--
Definition of `ringEquivOpMop` / `ringEquivOpMop` 的定义

English:
definition ringEquivOpMop
  signature: (S : Subring R)
  body: S.toSubsemiring.ringEquivOpMop

中文:
定义 ringEquivOpMop
  签名: (S : 子环 R)
  定义体: S.toSubsemiring.ringEquivOpMop

Depends on / 依赖: S.toSubsemiring.ringEquivOpMop, ringEquivOpMop, toSubsemiring
-/
def ringEquivOpMop (S : Subring R) : S ≃+* (S.op)ᵐᵒᵖ := S.toSubsemiring.ringEquivOpMop

/-- Bijection between `MulOpposite` of a subring `S` and its opposite. -/
@[simps!]
/--
Definition of `mopRingEquivOp` / `mopRingEquivOp` 的定义

English:
definition mopRingEquivOp
  signature: (S : Subring R)
  body: S.toSubsemiring.mopRingEquivOp

中文:
定义 mopRingEquivOp
  签名: (S : 子环 R)
  定义体: S.toSubsemiring.mopRingEquivOp

Depends on / 依赖: S.toSubsemiring.mopRingEquivOp, mopRingEquivOp, toSubsemiring
-/
def mopRingEquivOp (S : Subring R) : Sᵐᵒᵖ ≃+* S.op := S.toSubsemiring.mopRingEquivOp

end Subring
