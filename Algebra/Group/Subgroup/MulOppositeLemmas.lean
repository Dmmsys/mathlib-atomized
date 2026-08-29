/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.MulOpposite
public import Mathlib.Algebra.Group.Submonoid.MulOpposite
public import Mathlib.Logic.Encodable.Basic

/-!
# Mul-opposite subgroups

This file contains a somewhat arbitrary assortment of results on the opposite subgroup `H.op`
that rely on further theory to define. As such it is a somewhat arbitrary assortment of results,
which might be organized and split up further.

## Tags
subgroup, subgroups

-/

public section

variable {ι : Sort*} {G : Type*} [Group G]

namespace Subgroup

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: (H : Subgroup G)
  body: Submonoid.smul ..

中文:
实例 instSMul
  签名: (H : Subgroup G)
  定义体: Submonoid.smul ..
-/
@[to_additive] instance instSMul (H : Subgroup G) : SMul H.op G := Submonoid.smul ..

/-! ### Lattice results -/

@[to_additive (attr := simp)]
/--
theorem `op_bot` / 定理 `op_bot`

English:
theorem op_bot
  statement: (⊥ : Subgroup G).op = ⊥
  proof: opEquiv.map_bot

@[to_additive (attr := simp)]

中文:
定理 op_bot
  结论: (⊥ : Subgroup G).op = ⊥
  证明: opEquiv.map_bot

@[to_additive (attr := simp)]

Depends on / 依赖: map_bot, opEquiv, opEquiv.map_bot
-/
theorem op_bot : (⊥ : Subgroup G).op = ⊥ := opEquiv.map_bot

@[to_additive (attr := simp)]
/--
theorem `op_eq_bot` / 定理 `op_eq_bot`

English:
theorem op_eq_bot
  given: {S : Subgroup G}
  statement: S.op = ⊥ ↔ S = ⊥
  proof: op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]

中文:
定理 op_eq_bot
  条件: {S : Subgroup G}
  结论: S.op = ⊥ ↔ S = ⊥
  证明: op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, op_bot, op_injective, op_injective.eq_iff
-/
theorem op_eq_bot {S : Subgroup G} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]
/--
theorem `unop_bot` / 定理 `unop_bot`

English:
theorem unop_bot
  statement: (⊥ : Subgroup Gᵐᵒᵖ).unop = ⊥
  proof: opEquiv.symm.map_bot

@[to_additive (attr := simp)]

中文:
定理 unop_bot
  结论: (⊥ : Subgroup Gᵐᵒᵖ).unop = ⊥
  证明: opEquiv.symm.map_bot

@[to_additive (attr := simp)]

Depends on / 依赖: map_bot, opEquiv, opEquiv.symm.map_bot
-/
theorem unop_bot : (⊥ : Subgroup Gᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[to_additive (attr := simp)]
/--
theorem `unop_eq_bot` / 定理 `unop_eq_bot`

English:
theorem unop_eq_bot
  given: {S : Subgroup Gᵐᵒᵖ}
  statement: S.unop = ⊥ ↔ S = ⊥
  proof: unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]

中文:
定理 unop_eq_bot
  条件: {S : Subgroup Gᵐᵒᵖ}
  结论: S.unop = ⊥ ↔ S = ⊥
  证明: unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, unop_bot, unop_injective, unop_injective.eq_iff
-/
theorem unop_eq_bot {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]
/--
theorem `op_top` / 定理 `op_top`

English:
theorem op_top
  statement: (⊤ : Subgroup G).op = ⊤
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 op_top
  结论: (⊤ : Subgroup G).op = ⊤
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem op_top : (⊤ : Subgroup G).op = ⊤ := rfl

@[to_additive (attr := simp)]
/--
theorem `op_eq_top` / 定理 `op_eq_top`

English:
theorem op_eq_top
  given: {S : Subgroup G}
  statement: S.op = ⊤ ↔ S = ⊤
  proof: op_injective.eq_iff' op_top

@[to_additive (attr := simp)]

中文:
定理 op_eq_top
  条件: {S : Subgroup G}
  结论: S.op = ⊤ ↔ S = ⊤
  证明: op_injective.eq_iff' op_top

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, op_injective, op_injective.eq_iff, op_top
-/
theorem op_eq_top {S : Subgroup G} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[to_additive (attr := simp)]
/--
theorem `unop_top` / 定理 `unop_top`

English:
theorem unop_top
  statement: (⊤ : Subgroup Gᵐᵒᵖ).unop = ⊤
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unop_top
  结论: (⊤ : Subgroup Gᵐᵒᵖ).unop = ⊤
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unop_top : (⊤ : Subgroup Gᵐᵒᵖ).unop = ⊤ := rfl

@[to_additive (attr := simp)]
/--
theorem `unop_eq_top` / 定理 `unop_eq_top`

English:
theorem unop_eq_top
  given: {S : Subgroup Gᵐᵒᵖ}
  statement: S.unop = ⊤ ↔ S = ⊤
  proof: unop_injective.eq_iff' unop_top

@[to_additive]

中文:
定理 unop_eq_top
  条件: {S : Subgroup Gᵐᵒᵖ}
  结论: S.unop = ⊤ ↔ S = ⊤
  证明: unop_injective.eq_iff' unop_top

@[to_additive]

Depends on / 依赖: eq_iff, unop_injective, unop_injective.eq_iff, unop_top
-/
theorem unop_eq_top {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' unop_top

@[to_additive]
/--
theorem `op_sup` / 定理 `op_sup`

English:
theorem op_sup
  given: (S₁ S₂ : Subgroup G)
  statement: (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
  proof: opEquiv.map_sup _ _

@[to_additive]

中文:
定理 op_sup
  条件: (S₁ S₂ : Subgroup G)
  结论: (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
  证明: opEquiv.map_sup _ _

@[to_additive]

Depends on / 依赖: CanLift, Subsemigroup, map_sup, opEquiv, opEquiv.map_sup
-/
theorem op_sup (S₁ S₂ : Subgroup G) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

@[to_additive]
/--
theorem `unop_sup` / 定理 `unop_sup`

English:
theorem unop_sup
  given: (S₁ S₂ : Subgroup Gᵐᵒᵖ)
  statement: (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
  proof: opEquiv.symm.map_sup _ _

@[to_additive]

中文:
定理 unop_sup
  条件: (S₁ S₂ : Subgroup Gᵐᵒᵖ)
  结论: (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
  证明: opEquiv.symm.map_sup _ _

@[to_additive]

Depends on / 依赖: map_sup, opEquiv, opEquiv.symm.map_sup
-/
theorem unop_sup (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

@[to_additive]
/--
theorem `op_inf` / 定理 `op_inf`

English:
theorem op_inf
  given: (S₁ S₂ : Subgroup G)
  statement: (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
  proof: rfl

@[to_additive]

中文:
定理 op_inf
  条件: (S₁ S₂ : Subgroup G)
  结论: (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
  证明: rfl

@[to_additive]
-/
theorem op_inf (S₁ S₂ : Subgroup G) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

@[to_additive]
/--
theorem `unop_inf` / 定理 `unop_inf`

English:
theorem unop_inf
  given: (S₁ S₂ : Subgroup Gᵐᵒᵖ)
  statement: (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
  proof: rfl

@[to_additive]

中文:
定理 unop_inf
  条件: (S₁ S₂ : Subgroup Gᵐᵒᵖ)
  结论: (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
  证明: rfl

@[to_additive]
-/
theorem unop_inf (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

@[to_additive]
/--
theorem `op_sSup` / 定理 `op_sSup`

English:
theorem op_sSup
  given: (S : Set (Subgroup G))
  statement: (sSup S).op = sSup (.unop ⁻¹' S)
  proof: opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

中文:
定理 op_sSup
  条件: (S : Set (Subgroup G))
  结论: (sSup S).op = sSup (.unop ⁻¹' S)
  证明: opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

Depends on / 依赖: map_sSup_eq_sSup_symm_preimage, opEquiv, opEquiv.map_sSup_eq_sSup_symm_preimage
-/
theorem op_sSup (S : Set (Subgroup G)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
/--
theorem `unop_sSup` / 定理 `unop_sSup`

English:
theorem unop_sSup
  given: (S : Set (Subgroup Gᵐᵒᵖ))
  statement: (sSup S).unop = sSup (.op ⁻¹' S)
  proof: opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

中文:
定理 unop_sSup
  条件: (S : Set (Subgroup Gᵐᵒᵖ))
  结论: (sSup S).unop = sSup (.op ⁻¹' S)
  证明: opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]

Depends on / 依赖: map_sSup_eq_sSup_symm_preimage, opEquiv, opEquiv.symm.map_sSup_eq_sSup_symm_preimage
-/
theorem unop_sSup (S : Set (Subgroup Gᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
/--
theorem `op_sInf` / 定理 `op_sInf`

English:
theorem op_sInf
  given: (S : Set (Subgroup G))
  statement: (sInf S).op = sInf (.unop ⁻¹' S)
  proof: opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

中文:
定理 op_sInf
  条件: (S : Set (Subgroup G))
  结论: (sInf S).op = sInf (.unop ⁻¹' S)
  证明: opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

Depends on / 依赖: map_sInf_eq_sInf_symm_preimage, opEquiv, opEquiv.map_sInf_eq_sInf_symm_preimage
-/
theorem op_sInf (S : Set (Subgroup G)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
/--
theorem `unop_sInf` / 定理 `unop_sInf`

English:
theorem unop_sInf
  given: (S : Set (Subgroup Gᵐᵒᵖ))
  statement: (sInf S).unop = sInf (.op ⁻¹' S)
  proof: opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

中文:
定理 unop_sInf
  条件: (S : Set (Subgroup Gᵐᵒᵖ))
  结论: (sInf S).unop = sInf (.op ⁻¹' S)
  证明: opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]

Depends on / 依赖: map_sInf_eq_sInf_symm_preimage, opEquiv, opEquiv.symm.map_sInf_eq_sInf_symm_preimage
-/
theorem unop_sInf (S : Set (Subgroup Gᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
/--
theorem `op_iSup` / 定理 `op_iSup`

English:
theorem op_iSup
  given: (S : ι -> Subgroup G)
  statement: (iSup S).op = ⨆ i, (S i).op
  proof: opEquiv.map_iSup _

@[to_additive]

中文:
定理 op_iSup
  条件: (S : ι -> Subgroup G)
  结论: (iSup S).op = ⨆ i, (S i).op
  证明: opEquiv.map_iSup _

@[to_additive]

Depends on / 依赖: map_iSup, opEquiv, opEquiv.map_iSup
-/
theorem op_iSup (S : ι -> Subgroup G) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

@[to_additive]
/--
theorem `unop_iSup` / 定理 `unop_iSup`

English:
theorem unop_iSup
  given: (S : ι -> Subgroup Gᵐᵒᵖ)
  statement: (iSup S).unop = ⨆ i, (S i).unop
  proof: opEquiv.symm.map_iSup _

@[to_additive]

中文:
定理 unop_iSup
  条件: (S : ι -> Subgroup Gᵐᵒᵖ)
  结论: (iSup S).unop = ⨆ i, (S i).unop
  证明: opEquiv.symm.map_iSup _

@[to_additive]

Depends on / 依赖: map_iSup, opEquiv, opEquiv.symm.map_iSup
-/
theorem unop_iSup (S : ι -> Subgroup Gᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

@[to_additive]
/--
theorem `op_iInf` / 定理 `op_iInf`

English:
theorem op_iInf
  given: (S : ι -> Subgroup G)
  statement: (iInf S).op = ⨅ i, (S i).op
  proof: opEquiv.map_iInf _

@[to_additive]

中文:
定理 op_iInf
  条件: (S : ι -> Subgroup G)
  结论: (iInf S).op = ⨅ i, (S i).op
  证明: opEquiv.map_iInf _

@[to_additive]

Depends on / 依赖: map_iInf, opEquiv, opEquiv.map_iInf
-/
theorem op_iInf (S : ι -> Subgroup G) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

@[to_additive]
/--
theorem `unop_iInf` / 定理 `unop_iInf`

English:
theorem unop_iInf
  given: (S : ι -> Subgroup Gᵐᵒᵖ)
  statement: (iInf S).unop = ⨅ i, (S i).unop
  proof: opEquiv.symm.map_iInf _

@[to_additive]

中文:
定理 unop_iInf
  条件: (S : ι -> Subgroup Gᵐᵒᵖ)
  结论: (iInf S).unop = ⨅ i, (S i).unop
  证明: opEquiv.symm.map_iInf _

@[to_additive]

Depends on / 依赖: map_iInf, opEquiv, opEquiv.symm.map_iInf
-/
theorem unop_iInf (S : ι -> Subgroup Gᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

@[to_additive]
/--
theorem `op_closure` / 定理 `op_closure`

English:
theorem op_closure
  given: (s : Set G)
  statement: (closure s).op = closure (MulOpposite.unop ⁻¹' s)
  proof: by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Subgroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]

中文:
定理 op_closure
  条件: (s : Set G)
  结论: (closure s).op = closure (MulOpposite.unop ⁻¹' s)
  证明: by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Subgroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.unop_surjective.forall, Set.preimage_ofPred_eq, Subgroup, Subgroup.coe_unop, closure, coe_unop, op_sInf, preimage_ofPred_eq, simp_rw, unop_surjective
-/
theorem op_closure (s : Set G) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Subgroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]
/--
theorem `unop_closure` / 定理 `unop_closure`

English:
theorem unop_closure
  given: (s : Set Gᵐᵒᵖ)
  statement: (closure s).unop = closure (MulOpposite.op ⁻¹' s)
  proof: by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

@[to_additive]

中文:
定理 unop_closure
  条件: (s : Set Gᵐᵒᵖ)
  结论: (closure s).unop = closure (MulOpposite.op ⁻¹' s)
  证明: by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.op_unop, Set.preimage_id, Set.preimage_preimage, op_closure, op_inj, op_unop, preimage_id, preimage_preimage, simp_rw
-/
theorem unop_closure (s : Set Gᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj]; rw [op_unop]; rw [op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

@[to_additive]
instance (H : Subgroup G) [Encodable H] : Encodable H.op :=
  Encodable.ofEquiv H H.equivOp.symm

@[to_additive]
instance (H : Subgroup G) [Countable H] : Countable H.op :=
  Countable.of_equiv H H.equivOp

@[to_additive]
/--
theorem `smul_opposite_mul` / 定理 `smul_opposite_mul`

English:
theorem smul_opposite_mul
  given: {H : Subgroup G} (x g : G) (h : H.op)
  proof: mul_assoc _ _ _

@[to_additive (attr := simp)]

中文:
定理 smul_opposite_mul
  条件: {H : Subgroup G} (x g : G) (h : H.op)
  证明: mul_assoc _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc
-/
theorem smul_opposite_mul {H : Subgroup G} (x g : G) (h : H.op) :
    h • (g * x) = g * h • x :=
  mul_assoc _ _ _

@[to_additive (attr := simp)]
/--
theorem `normal_op` / 定理 `normal_op`

English:
theorem normal_op
  given: {H : Subgroup G}
  statement: H.op.Normal ↔ H.Normal
  proof: by
  simp only [← normalizer_eq_top_iff, ← op_normalizer, op_eq_top]

@[to_additive] alias ⟨Normal.of_op, Normal.op⟩ := normal_op

@[to_additive]

中文:
定理 normal_op
  条件: {H : Subgroup G}
  结论: H.op.Normal ↔ H.Normal
  证明: by
  simp only [← normalizer_eq_top_iff, ← op_normalizer, op_eq_top]

@[to_additive] alias ⟨Normal.of_op, Normal.op⟩ := normal_op

@[to_additive]

Depends on / 依赖: normalizer_eq_top_iff, op_eq_top, op_normalizer
-/
theorem normal_op {H : Subgroup G} : H.op.Normal ↔ H.Normal := by
  simp only [← normalizer_eq_top_iff, ← op_normalizer, op_eq_top]

@[to_additive] alias ⟨Normal.of_op, Normal.op⟩ := normal_op

@[to_additive]
/--
Instance `op.instNormal` / 实例 `op.instNormal`

English:
instance op.instNormal
  signature: {H : Subgroup G} [H.Normal]
  body: .op ‹_›

@[to_additive (attr := simp)]

中文:
实例 op.instNormal
  签名: {H : Subgroup G} [H.Normal]
  定义体: .op ‹_›

@[to_additive (attr := simp)]
-/
instance op.instNormal {H : Subgroup G} [H.Normal] : H.op.Normal := .op ‹_›

@[to_additive (attr := simp)]
/--
theorem `normal_unop` / 定理 `normal_unop`

English:
theorem normal_unop
  given: {H : Subgroup Gᵐᵒᵖ}
  statement: H.unop.Normal ↔ H.Normal
  proof: by
  rw [← normal_op]; rw [op_unop]

@[to_additive] alias ⟨Normal.of_unop, Normal.unop⟩ := normal_unop

@[to_additive]

中文:
定理 normal_unop
  条件: {H : Subgroup Gᵐᵒᵖ}
  结论: H.unop.Normal ↔ H.Normal
  证明: by
  rw [← normal_op]; rw [op_unop]

@[to_additive] alias ⟨Normal.of_unop, Normal.unop⟩ := normal_unop

@[to_additive]

Depends on / 依赖: normal_op, op_unop
-/
theorem normal_unop {H : Subgroup Gᵐᵒᵖ} : H.unop.Normal ↔ H.Normal := by
  rw [← normal_op]; rw [op_unop]

@[to_additive] alias ⟨Normal.of_unop, Normal.unop⟩ := normal_unop

@[to_additive]
/--
Instance `unop.instNormal` / 实例 `unop.instNormal`

English:
instance unop.instNormal
  signature: {H : Subgroup Gᵐᵒᵖ} [H.Normal]
  body: .unop ‹_›

中文:
实例 unop.instNormal
  签名: {H : Subgroup Gᵐᵒᵖ} [H.Normal]
  定义体: .unop ‹_›
-/
instance unop.instNormal {H : Subgroup Gᵐᵒᵖ} [H.Normal] : H.unop.Normal := .unop ‹_›

end Subgroup
