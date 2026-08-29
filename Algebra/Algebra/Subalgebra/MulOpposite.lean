/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Ring.Subring.MulOpposite

/-!

# Subalgebras of opposite rings

For every ring `A` over a commutative ring `R`, we construct an equivalence between
subalgebras of `A / R` and that of `Aᵐᵒᵖ / R`.

-/

@[expose] public section

namespace Subalgebra

section Semiring

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Pull a subalgebra back to an opposite subalgebra along `MulOpposite.unop` -/
@[simps! coe toSubsemiring]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (S : Subalgebra R A)
  body: S.toSubsemiring.op
  algebraMap_mem' := S.algebraMap_mem

中文:
定义 op
  签名: (S : Subalgebra R A)
  定义体: S.toSubsemiring.op
  algebraMap_mem' := S.algebraMap_mem
-/
protected def op (S : Subalgebra R A) : Subalgebra R Aᵐᵒᵖ where
  toSubsemiring := S.toSubsemiring.op
  algebraMap_mem' := S.algebraMap_mem

attribute [norm_cast] coe_op

@[simp]
/--
theorem `mem_op` / 定理 `mem_op`

English:
theorem mem_op
  given: {x : Aᵐᵒᵖ} {S : Subalgebra R A}
  statement: x in S.op ↔ x.unop in S
  proof: Iff.rfl

中文:
定理 mem_op
  条件: {x : Aᵐᵒᵖ} {S : Subalgebra R A}
  结论: x in S.op ↔ x.unop in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_op {x : Aᵐᵒᵖ} {S : Subalgebra R A} : x in S.op ↔ x.unop in S := Iff.rfl

/-- Pull a subalgebra back to a subalgebra along `MulOpposite.op` -/
@[simps! coe toSubsemiring]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (S : Subalgebra R Aᵐᵒᵖ)
  body: S.toSubsemiring.unop
  algebraMap_mem' := S.algebraMap_mem

中文:
定义 unop
  签名: (S : Subalgebra R Aᵐᵒᵖ)
  定义体: S.toSubsemiring.unop
  algebraMap_mem' := S.algebraMap_mem
-/
protected def unop (S : Subalgebra R Aᵐᵒᵖ) : Subalgebra R A where
  toSubsemiring := S.toSubsemiring.unop
  algebraMap_mem' := S.algebraMap_mem

attribute [norm_cast] coe_unop

@[simp]
/--
theorem `mem_unop` / 定理 `mem_unop`

English:
theorem mem_unop
  given: {x : A} {S : Subalgebra R Aᵐᵒᵖ}
  statement: x in S.unop ↔ MulOpposite.op x in S
  proof: Iff.rfl

@[simp]

中文:
定理 mem_unop
  条件: {x : A} {S : Subalgebra R Aᵐᵒᵖ}
  结论: x in S.unop ↔ MulOpposite.op x in S
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_unop {x : A} {S : Subalgebra R Aᵐᵒᵖ} : x in S.unop ↔ MulOpposite.op x in S := Iff.rfl

@[simp]
/--
theorem `unop_op` / 定理 `unop_op`

English:
theorem unop_op
  given: (S : Subalgebra R A)
  statement: S.op.unop = S
  proof: rfl

@[simp]

中文:
定理 unop_op
  条件: (S : Subalgebra R A)
  结论: S.op.unop = S
  证明: rfl

@[simp]
-/
theorem unop_op (S : Subalgebra R A) : S.op.unop = S := rfl

@[simp]
/--
theorem `op_unop` / 定理 `op_unop`

English:
theorem op_unop
  given: (S : Subalgebra R Aᵐᵒᵖ)
  statement: S.unop.op = S
  proof: rfl

中文:
定理 op_unop
  条件: (S : Subalgebra R Aᵐᵒᵖ)
  结论: S.unop.op = S
  证明: rfl
-/
theorem op_unop (S : Subalgebra R Aᵐᵒᵖ) : S.unop.op = S := rfl


/--
theorem `op_le_iff` / 定理 `op_le_iff`

English:
theorem op_le_iff
  given: {S₁ : Subalgebra R A} {S₂ : Subalgebra R Aᵐᵒᵖ}
  statement: S₁.op <= S₂ ↔ S₁ <= S₂.unop
  proof: MulOpposite.op_surjective.forall

中文:
定理 op_le_iff
  条件: {S₁ : Subalgebra R A} {S₂ : Subalgebra R Aᵐᵒᵖ}
  结论: S₁.op <= S₂ ↔ S₁ <= S₂.unop
  证明: MulOpposite.op_surjective.forall

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem op_le_iff {S₁ : Subalgebra R A} {S₂ : Subalgebra R Aᵐᵒᵖ} : S₁.op <= S₂ ↔ S₁ <= S₂.unop :=
  MulOpposite.op_surjective.forall

/--
theorem `le_op_iff` / 定理 `le_op_iff`

English:
theorem le_op_iff
  given: {S₁ : Subalgebra R Aᵐᵒᵖ} {S₂ : Subalgebra R A}
  statement: S₁ <= S₂.op ↔ S₁.unop <= S₂
  proof: MulOpposite.op_surjective.forall

@[simp]

中文:
定理 le_op_iff
  条件: {S₁ : Subalgebra R Aᵐᵒᵖ} {S₂ : Subalgebra R A}
  结论: S₁ <= S₂.op ↔ S₁.unop <= S₂
  证明: MulOpposite.op_surjective.forall

@[simp]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem le_op_iff {S₁ : Subalgebra R Aᵐᵒᵖ} {S₂ : Subalgebra R A} : S₁ <= S₂.op ↔ S₁.unop <= S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
/--
theorem `op_le_op_iff` / 定理 `op_le_op_iff`

English:
theorem op_le_op_iff
  given: {S₁ S₂ : Subalgebra R A}
  statement: S₁.op <= S₂.op ↔ S₁ <= S₂
  proof: MulOpposite.op_surjective.forall

@[simp]

中文:
定理 op_le_op_iff
  条件: {S₁ S₂ : Subalgebra R A}
  结论: S₁.op <= S₂.op ↔ S₁ <= S₂
  证明: MulOpposite.op_surjective.forall

@[simp]

Depends on / 依赖: MulOpposite, MulOpposite.op_surjective.forall, op_surjective
-/
theorem op_le_op_iff {S₁ S₂ : Subalgebra R A} : S₁.op <= S₂.op ↔ S₁ <= S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
/--
theorem `unop_le_unop_iff` / 定理 `unop_le_unop_iff`

English:
theorem unop_le_unop_iff
  given: {S₁ S₂ : Subalgebra R Aᵐᵒᵖ}
  statement: S₁.unop <= S₂.unop ↔ S₁ <= S₂
  proof: MulOpposite.unop_surjective.forall

中文:
定理 unop_le_unop_iff
  条件: {S₁ S₂ : Subalgebra R Aᵐᵒᵖ}
  结论: S₁.unop <= S₂.unop ↔ S₁ <= S₂
  证明: MulOpposite.unop_surjective.forall

Depends on / 依赖: MulOpposite, MulOpposite.unop_surjective.forall, unop_surjective
-/
theorem unop_le_unop_iff {S₁ S₂ : Subalgebra R Aᵐᵒᵖ} : S₁.unop <= S₂.unop ↔ S₁ <= S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subalgebra `S` of `A / R` determines a subalgebra `S.op` of the opposite ring `Aᵐᵒᵖ / R`. -/
@[simps]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : Subalgebra R A ≃o Subalgebra R Aᵐᵒᵖ where
  body: Subalgebra.op
  invFun := Subalgebra.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[simp]

中文:
定义 opEquiv
  签名: : Subalgebra R A ≃o Subalgebra R Aᵐᵒᵖ where
  定义体: Subalgebra.op
  invFun := Subalgebra.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.op
-/
def opEquiv : Subalgebra R A ≃o Subalgebra R Aᵐᵒᵖ where
  toFun := Subalgebra.op
  invFun := Subalgebra.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[simp]
/--
theorem `op_bot` / 定理 `op_bot`

English:
theorem op_bot
  statement: (⊥ : Subalgebra R A).op = ⊥
  proof: opEquiv.map_bot

@[simp]

中文:
定理 op_bot
  结论: (⊥ : Subalgebra R A).op = ⊥
  证明: opEquiv.map_bot

@[simp]

Depends on / 依赖: map_bot, opEquiv, opEquiv.map_bot
-/
theorem op_bot : (⊥ : Subalgebra R A).op = ⊥ := opEquiv.map_bot

@[simp]
/--
theorem `unop_bot` / 定理 `unop_bot`

English:
theorem unop_bot
  statement: (⊥ : Subalgebra R Aᵐᵒᵖ).unop = ⊥
  proof: opEquiv.symm.map_bot

@[simp]

中文:
定理 unop_bot
  结论: (⊥ : Subalgebra R Aᵐᵒᵖ).unop = ⊥
  证明: opEquiv.symm.map_bot

@[simp]

Depends on / 依赖: map_bot, opEquiv, opEquiv.symm.map_bot
-/
theorem unop_bot : (⊥ : Subalgebra R Aᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[simp]
/--
theorem `op_top` / 定理 `op_top`

English:
theorem op_top
  statement: (⊤ : Subalgebra R A).op = ⊤
  proof: opEquiv.map_top

@[simp]

中文:
定理 op_top
  结论: (⊤ : Subalgebra R A).op = ⊤
  证明: opEquiv.map_top

@[simp]

Depends on / 依赖: map_top, opEquiv, opEquiv.map_top
-/
theorem op_top : (⊤ : Subalgebra R A).op = ⊤ := opEquiv.map_top

@[simp]
/--
theorem `unop_top` / 定理 `unop_top`

English:
theorem unop_top
  statement: (⊤ : Subalgebra R Aᵐᵒᵖ).unop = ⊤
  proof: opEquiv.symm.map_top

中文:
定理 unop_top
  结论: (⊤ : Subalgebra R Aᵐᵒᵖ).unop = ⊤
  证明: opEquiv.symm.map_top

Depends on / 依赖: map_top, opEquiv, opEquiv.symm.map_top
-/
theorem unop_top : (⊤ : Subalgebra R Aᵐᵒᵖ).unop = ⊤ := opEquiv.symm.map_top

/--
theorem `op_sup` / 定理 `op_sup`

English:
theorem op_sup
  given: (S₁ S₂ : Subalgebra R A)
  statement: (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
  proof: opEquiv.map_sup _ _

中文:
定理 op_sup
  条件: (S₁ S₂ : Subalgebra R A)
  结论: (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
  证明: opEquiv.map_sup _ _

Depends on / 依赖: map_sup, opEquiv, opEquiv.map_sup
-/
theorem op_sup (S₁ S₂ : Subalgebra R A) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

/--
theorem `unop_sup` / 定理 `unop_sup`

English:
theorem unop_sup
  given: (S₁ S₂ : Subalgebra R Aᵐᵒᵖ)
  statement: (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
  proof: opEquiv.symm.map_sup _ _

中文:
定理 unop_sup
  条件: (S₁ S₂ : Subalgebra R Aᵐᵒᵖ)
  结论: (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
  证明: opEquiv.symm.map_sup _ _

Depends on / 依赖: map_sup, opEquiv, opEquiv.symm.map_sup
-/
theorem unop_sup (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

/--
theorem `op_inf` / 定理 `op_inf`

English:
theorem op_inf
  given: (S₁ S₂ : Subalgebra R A)
  statement: (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
  proof: opEquiv.map_inf _ _

中文:
定理 op_inf
  条件: (S₁ S₂ : Subalgebra R A)
  结论: (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
  证明: opEquiv.map_inf _ _

Depends on / 依赖: map_inf, opEquiv, opEquiv.map_inf
-/
theorem op_inf (S₁ S₂ : Subalgebra R A) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := opEquiv.map_inf _ _

/--
theorem `unop_inf` / 定理 `unop_inf`

English:
theorem unop_inf
  given: (S₁ S₂ : Subalgebra R Aᵐᵒᵖ)
  statement: (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
  proof: opEquiv.symm.map_inf _ _

中文:
定理 unop_inf
  条件: (S₁ S₂ : Subalgebra R Aᵐᵒᵖ)
  结论: (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
  证明: opEquiv.symm.map_inf _ _

Depends on / 依赖: map_inf, opEquiv, opEquiv.symm.map_inf
-/
theorem unop_inf (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop :=
  opEquiv.symm.map_inf _ _

/--
theorem `op_sSup` / 定理 `op_sSup`

English:
theorem op_sSup
  given: (S : Set (Subalgebra R A))
  statement: (sSup S).op = sSup (.unop ⁻¹' S)
  proof: opEquiv.map_sSup_eq_sSup_symm_preimage _

中文:
定理 op_sSup
  条件: (S : Set (Subalgebra R A))
  结论: (sSup S).op = sSup (.unop ⁻¹' S)
  证明: opEquiv.map_sSup_eq_sSup_symm_preimage _

Depends on / 依赖: map_sSup_eq_sSup_symm_preimage, opEquiv, opEquiv.map_sSup_eq_sSup_symm_preimage
-/
theorem op_sSup (S : Set (Subalgebra R A)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

/--
theorem `unop_sSup` / 定理 `unop_sSup`

English:
theorem unop_sSup
  given: (S : Set (Subalgebra R Aᵐᵒᵖ))
  statement: (sSup S).unop = sSup (.op ⁻¹' S)
  proof: opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

中文:
定理 unop_sSup
  条件: (S : Set (Subalgebra R Aᵐᵒᵖ))
  结论: (sSup S).unop = sSup (.op ⁻¹' S)
  证明: opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

Depends on / 依赖: map_sSup_eq_sSup_symm_preimage, opEquiv, opEquiv.symm.map_sSup_eq_sSup_symm_preimage
-/
theorem unop_sSup (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

/--
theorem `op_sInf` / 定理 `op_sInf`

English:
theorem op_sInf
  given: (S : Set (Subalgebra R A))
  statement: (sInf S).op = sInf (.unop ⁻¹' S)
  proof: opEquiv.map_sInf_eq_sInf_symm_preimage _

中文:
定理 op_sInf
  条件: (S : Set (Subalgebra R A))
  结论: (sInf S).op = sInf (.unop ⁻¹' S)
  证明: opEquiv.map_sInf_eq_sInf_symm_preimage _

Depends on / 依赖: map_sInf_eq_sInf_symm_preimage, opEquiv, opEquiv.map_sInf_eq_sInf_symm_preimage
-/
theorem op_sInf (S : Set (Subalgebra R A)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

/--
theorem `unop_sInf` / 定理 `unop_sInf`

English:
theorem unop_sInf
  given: (S : Set (Subalgebra R Aᵐᵒᵖ))
  statement: (sInf S).unop = sInf (.op ⁻¹' S)
  proof: opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

中文:
定理 unop_sInf
  条件: (S : Set (Subalgebra R Aᵐᵒᵖ))
  结论: (sInf S).unop = sInf (.op ⁻¹' S)
  证明: opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

Depends on / 依赖: map_sInf_eq_sInf_symm_preimage, opEquiv, opEquiv.symm.map_sInf_eq_sInf_symm_preimage
-/
theorem unop_sInf (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

/--
theorem `op_iSup` / 定理 `op_iSup`

English:
theorem op_iSup
  given: (S : ι -> Subalgebra R A)
  statement: (iSup S).op = ⨆ i, (S i).op
  proof: opEquiv.map_iSup _

中文:
定理 op_iSup
  条件: (S : ι -> Subalgebra R A)
  结论: (iSup S).op = ⨆ i, (S i).op
  证明: opEquiv.map_iSup _

Depends on / 依赖: map_iSup, opEquiv, opEquiv.map_iSup
-/
theorem op_iSup (S : ι -> Subalgebra R A) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

/--
theorem `unop_iSup` / 定理 `unop_iSup`

English:
theorem unop_iSup
  given: (S : ι -> Subalgebra R Aᵐᵒᵖ)
  statement: (iSup S).unop = ⨆ i, (S i).unop
  proof: opEquiv.symm.map_iSup _

中文:
定理 unop_iSup
  条件: (S : ι -> Subalgebra R Aᵐᵒᵖ)
  结论: (iSup S).unop = ⨆ i, (S i).unop
  证明: opEquiv.symm.map_iSup _

Depends on / 依赖: map_iSup, opEquiv, opEquiv.symm.map_iSup
-/
theorem unop_iSup (S : ι -> Subalgebra R Aᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

/--
theorem `op_iInf` / 定理 `op_iInf`

English:
theorem op_iInf
  given: (S : ι -> Subalgebra R A)
  statement: (iInf S).op = ⨅ i, (S i).op
  proof: opEquiv.map_iInf _

中文:
定理 op_iInf
  条件: (S : ι -> Subalgebra R A)
  结论: (iInf S).op = ⨅ i, (S i).op
  证明: opEquiv.map_iInf _

Depends on / 依赖: map_iInf, opEquiv, opEquiv.map_iInf
-/
theorem op_iInf (S : ι -> Subalgebra R A) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

/--
theorem `unop_iInf` / 定理 `unop_iInf`

English:
theorem unop_iInf
  given: (S : ι -> Subalgebra R Aᵐᵒᵖ)
  statement: (iInf S).unop = ⨅ i, (S i).unop
  proof: opEquiv.symm.map_iInf _

中文:
定理 unop_iInf
  条件: (S : ι -> Subalgebra R Aᵐᵒᵖ)
  结论: (iInf S).unop = ⨅ i, (S i).unop
  证明: opEquiv.symm.map_iInf _

Depends on / 依赖: map_iInf, opEquiv, opEquiv.symm.map_iInf
-/
theorem unop_iInf (S : ι -> Subalgebra R Aᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

/--
theorem `op_adjoin` / 定理 `op_adjoin`

English:
theorem op_adjoin
  given: (s : Set A)
  proof: by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, op_toSubsemiring, Subsemiring.op_closure, Set.preimage_union]
  congr with x
  simp_rw [Set.mem_preimage, Set.mem_range, MulOpposite.algebraMap_apply]
  congr!
  rw [← MulOpposite.op_injective.eq_iff (b := x.unop)]; rw [MulOpposite.op_uno

中文:
定理 op_adjoin
  条件: (s : Set A)
  证明: by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, op_toSubsemiring, Subsemiring.op_closure, Set.preimage_union]
  congr with x
  simp_rw [Set.mem_preimage, Set.mem_range, MulOpposite.algebraMap_apply]
  congr!
  rw [← MulOpposite.op_injective.eq_iff (b := x.unop)]; rw [MulOpposite.op_uno

Depends on / 依赖: Algebra, Algebra.adjoin, MulOpposite, MulOpposite.algebraMap_apply, MulOpposite.op_injective.eq_iff, MulOpposite.op_unop, Set.mem_preimage, Set.mem_range, Set.preimage_union, Subsemiring, Subsemiring.op_closure, adjoin, algebraMap_apply, eq_iff, mem_preimage, mem_range, op_closure, op_injective, op_toSubsemiring, op_unop
-/
theorem op_adjoin (s : Set A) :
    (Algebra.adjoin R s).op = Algebra.adjoin R (MulOpposite.unop ⁻¹' s) := by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, op_toSubsemiring, Subsemiring.op_closure, Set.preimage_union]
  congr with x
  simp_rw [Set.mem_preimage, Set.mem_range, MulOpposite.algebraMap_apply]
  congr!
  rw [← MulOpposite.op_injective.eq_iff (b := x.unop)]; rw [MulOpposite.op_unop]

/--
theorem `unop_adjoin` / 定理 `unop_adjoin`

English:
theorem unop_adjoin
  given: (s : Set Aᵐᵒᵖ)
  proof: by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, unop_toSubsemiring, Subsemiring.unop_closure, Set.preimage_union]
  congr with x
  simp

中文:
定理 unop_adjoin
  条件: (s : Set Aᵐᵒᵖ)
  证明: by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, unop_toSubsemiring, Subsemiring.unop_closure, Set.preimage_union]
  congr with x
  simp

Depends on / 依赖: Algebra, Algebra.adjoin, Set.preimage_union, Subsemiring, Subsemiring.unop_closure, adjoin, preimage_union, simp_rw, toSubsemiring_injective, unop_closure, unop_toSubsemiring
-/
theorem unop_adjoin (s : Set Aᵐᵒᵖ) :
    (Algebra.adjoin R s).unop = Algebra.adjoin R (MulOpposite.op ⁻¹' s) := by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, unop_toSubsemiring, Subsemiring.unop_closure, Set.preimage_union]
  congr with x
  simp

/-- Bijection between a subalgebra `S` and its opposite. -/
@[simps!]
/--
Definition of `linearEquivOp` / `linearEquivOp` 的定义

English:
definition linearEquivOp
  signature: (S : Subalgebra R A)
  body: S.toSubsemiring.addEquivOp
  map_smul' _ _ := rfl

中文:
定义 linearEquivOp
  签名: (S : Subalgebra R A)
  定义体: S.toSubsemiring.addEquivOp
  map_smul' _ _ := rfl

Depends on / 依赖: S.toSubsemiring.addEquivOp, addEquivOp, toSubsemiring
-/
def linearEquivOp (S : Subalgebra R A) : S ≃ₗ[R] S.op where
  __ := S.toSubsemiring.addEquivOp
  map_smul' _ _ := rfl

/-- Bijection between a subalgebra `S` and `MulOpposite` of its opposite. -/
@[simps!]
/--
Definition of `algEquivOpMop` / `algEquivOpMop` 的定义

English:
definition algEquivOpMop
  signature: (S : Subalgebra R A)
  body: S.toSubsemiring.ringEquivOpMop
  commutes' _ := rfl

中文:
定义 algEquivOpMop
  签名: (S : Subalgebra R A)
  定义体: S.toSubsemiring.ringEquivOpMop
  commutes' _ := rfl

Depends on / 依赖: S.toSubsemiring.ringEquivOpMop, ringEquivOpMop, toSubsemiring
-/
def algEquivOpMop (S : Subalgebra R A) : S ≃ₐ[R] (S.op)ᵐᵒᵖ where
  __ := S.toSubsemiring.ringEquivOpMop
  commutes' _ := rfl

/-- Bijection between `MulOpposite` of a subalgebra `S` and its opposite. -/
@[simps!]
/--
Definition of `mopAlgEquivOp` / `mopAlgEquivOp` 的定义

English:
definition mopAlgEquivOp
  signature: (S : Subalgebra R A)
  body: S.toSubsemiring.mopRingEquivOp
  commutes' _ := rfl

中文:
定义 mopAlgEquivOp
  签名: (S : Subalgebra R A)
  定义体: S.toSubsemiring.mopRingEquivOp
  commutes' _ := rfl

Depends on / 依赖: S.toSubsemiring.mopRingEquivOp, mopRingEquivOp, toSubsemiring
-/
def mopAlgEquivOp (S : Subalgebra R A) : Sᵐᵒᵖ ≃ₐ[R] S.op where
  __ := S.toSubsemiring.mopRingEquivOp
  commutes' _ := rfl

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

@[simp]
/--
theorem `op_toSubring` / 定理 `op_toSubring`

English:
theorem op_toSubring
  given: (S : Subalgebra R A)
  statement: S.op.toSubring = S.toSubring.op
  proof: rfl

@[simp]

中文:
定理 op_toSubring
  条件: (S : Subalgebra R A)
  结论: S.op.toSubring = S.toSubring.op
  证明: rfl

@[simp]
-/
theorem op_toSubring (S : Subalgebra R A) : S.op.toSubring = S.toSubring.op := rfl

@[simp]
/--
theorem `unop_toSubring` / 定理 `unop_toSubring`

English:
theorem unop_toSubring
  given: (S : Subalgebra R Aᵐᵒᵖ)
  statement: S.unop.toSubring = S.toSubring.unop
  proof: rfl

中文:
定理 unop_toSubring
  条件: (S : Subalgebra R Aᵐᵒᵖ)
  结论: S.unop.toSubring = S.toSubring.unop
  证明: rfl
-/
theorem unop_toSubring (S : Subalgebra R Aᵐᵒᵖ) : S.unop.toSubring = S.toSubring.unop := rfl

end Ring

end Subalgebra
