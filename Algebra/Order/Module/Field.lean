/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Ordered vector spaces
-/

@[expose] public section

open OrderDual

variable {𝕜 G : Type*}

section LinearOrderedSemifield
variable [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup G] [PartialOrder G]

-- See note [lower instance priority]
instance (priority := 100) PosSMulMono.toPosSMulReflectLE [MulAction 𝕜 G] [PosSMulMono 𝕜 G] :
    PosSMulReflectLE 𝕜 G where
  le_of_smul_le_smul_left _a ha b₁ b₂ h := by
simpa [ha.ne'] using smul_le_smul_of_nonneg_left h inv_nonneg.2 ha.le

-- See note [lower instance priority]
instance (priority := 100) PosSMulStrictMono.toPosSMulReflectLT [MulActionWithZero 𝕜 G]
    [PosSMulStrictMono 𝕜 G] : PosSMulReflectLT 𝕜 G :=
.of_pos fun a ha b₁ b₂ h => by simpa [ha.ne'] using smul_lt_smul_of_pos_left h inv_pos.2 ha

end LinearOrderedSemifield

section Field
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [Module 𝕜 G] {a : 𝕜} {b₁ b₂ : G}

section PosSMulMono
variable [PosSMulMono 𝕜 G]

/--
lemma `inv_smul_le_iff_of_neg` / 引理 `inv_smul_le_iff_of_neg`

English:
lemma inv_smul_le_iff_of_neg
  given: (h : a < 0)
  statement: a⁻¹ • b₁ <= b₂ ↔ a • b₂ <= b₁
  proof: by
  rw [← smul_le_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

中文:
引理 inv_smul_le_iff_of_neg
  条件: (h : a < 0)
  结论: a⁻¹ • b₁ <= b₂ ↔ a • b₂ <= b₁
  证明: by
  rw [← smul_le_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

Depends on / 依赖: h.ne, smul_le_smul_iff_of_neg_left
-/
lemma inv_smul_le_iff_of_neg (h : a < 0) : a⁻¹ • b₁ <= b₂ ↔ a • b₂ <= b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

/--
lemma `smul_inv_le_iff_of_neg` / 引理 `smul_inv_le_iff_of_neg`

English:
lemma smul_inv_le_iff_of_neg
  given: (h : a < 0)
  statement: b₁ <= a⁻¹ • b₂ ↔ b₂ <= a • b₁
  proof: by
  rw [← smul_le_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

中文:
引理 smul_inv_le_iff_of_neg
  条件: (h : a < 0)
  结论: b₁ <= a⁻¹ • b₂ ↔ b₂ <= a • b₁
  证明: by
  rw [← smul_le_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

Depends on / 依赖: h.ne, smul_le_smul_iff_of_neg_left
-/
lemma smul_inv_le_iff_of_neg (h : a < 0) : b₁ <= a⁻¹ • b₂ ↔ b₂ <= a • b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

variable (G)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps!]
/--
Definition of `OrderIso.smulRightDual` / `OrderIso.smulRightDual` 的定义

English:
definition OrderIso.smulRightDual
  signature: (ha : a < 0)
  body: (Equiv.smulRight ha.ne).trans toDual
map_rel_iff' := (@OrderDual.toDual_le_toDual G).trans smul_le_smul_iff_of_neg_left ha

中文:
定义 OrderIso.smulRightDual
  签名: (ha : a < 0)
  定义体: (Equiv.smulRight ha.ne).trans toDual
map_rel_iff' := (@OrderDual.toDual_le_toDual G).trans smul_le_smul_iff_of_neg_left ha

Depends on / 依赖: Equiv.smulRight, ha.ne, smulRight, toDual
-/
def OrderIso.smulRightDual (ha : a < 0) : G ≃o Gᵒᵈ where
  toEquiv := (Equiv.smulRight ha.ne).trans toDual
map_rel_iff' := (@OrderDual.toDual_le_toDual G).trans smul_le_smul_iff_of_neg_left ha

end PosSMulMono

variable [PosSMulStrictMono 𝕜 G]

/--
lemma `inv_smul_lt_iff_of_neg` / 引理 `inv_smul_lt_iff_of_neg`

English:
lemma inv_smul_lt_iff_of_neg
  given: (h : a < 0)
  statement: a⁻¹ • b₁ < b₂ ↔ a • b₂ < b₁
  proof: by
  rw [← smul_lt_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

中文:
引理 inv_smul_lt_iff_of_neg
  条件: (h : a < 0)
  结论: a⁻¹ • b₁ < b₂ ↔ a • b₂ < b₁
  证明: by
  rw [← smul_lt_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

Depends on / 依赖: h.ne, smul_lt_smul_iff_of_neg_left
-/
lemma inv_smul_lt_iff_of_neg (h : a < 0) : a⁻¹ • b₁ < b₂ ↔ a • b₂ < b₁ := by
  rw [← smul_lt_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

/--
lemma `smul_inv_lt_iff_of_neg` / 引理 `smul_inv_lt_iff_of_neg`

English:
lemma smul_inv_lt_iff_of_neg
  given: (h : a < 0)
  statement: b₁ < a⁻¹ • b₂ ↔ b₂ < a • b₁
  proof: by
  rw [← smul_lt_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

中文:
引理 smul_inv_lt_iff_of_neg
  条件: (h : a < 0)
  结论: b₁ < a⁻¹ • b₂ ↔ b₂ < a • b₁
  证明: by
  rw [← smul_lt_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

Depends on / 依赖: h.ne, smul_lt_smul_iff_of_neg_left
-/
lemma smul_inv_lt_iff_of_neg (h : a < 0) : b₁ < a⁻¹ • b₂ ↔ b₂ < a • b₁ := by
  rw [← smul_lt_smul_iff_of_neg_left h]; rw [smul_inv_smul₀ h.ne]

end Field

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

variable {α β : Type*}

section PosSMulMono
variable [Zero α] [Zero β] [SMulZeroClass α β] [Preorder α] [Preorder β] [PosSMulMono α β] {a : α}
  {b : β}

/--
theorem `smul_nonneg_of_pos_of_nonneg` / 定理 `smul_nonneg_of_pos_of_nonneg`

English:
theorem smul_nonneg_of_pos_of_nonneg
  given: (ha : 0 < a) (hb : 0 <= b)
  statement: 0 <= a • b
  proof: smul_nonneg ha.le hb

中文:
定理 smul_nonneg_of_pos_of_nonneg
  条件: (ha : 0 < a) (hb : 0 <= b)
  结论: 0 <= a • b
  证明: smul_nonneg ha.le hb

Depends on / 依赖: ha.le, smul_nonneg
-/
theorem smul_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 <= b) : 0 <= a • b :=
  smul_nonneg ha.le hb

/--
theorem `smul_nonneg_of_nonneg_of_pos` / 定理 `smul_nonneg_of_nonneg_of_pos`

English:
theorem smul_nonneg_of_nonneg_of_pos
  given: (ha : 0 <= a) (hb : 0 < b)
  statement: 0 <= a • b
  proof: smul_nonneg ha hb.le

中文:
定理 smul_nonneg_of_nonneg_of_pos
  条件: (ha : 0 <= a) (hb : 0 < b)
  结论: 0 <= a • b
  证明: smul_nonneg ha hb.le

Depends on / 依赖: hb.le, smul_nonneg
-/
theorem smul_nonneg_of_nonneg_of_pos (ha : 0 <= a) (hb : 0 < b) : 0 <= a • b :=
  smul_nonneg ha hb.le

/--
theorem `smul_nonneg_of_pos_of_pos` / 定理 `smul_nonneg_of_pos_of_pos`

English:
theorem smul_nonneg_of_pos_of_pos
  given: (ha : 0 < a) (hb : 0 < b)
  statement: 0 <= a • b
  proof: smul_nonneg ha.le hb.le

中文:
定理 smul_nonneg_of_pos_of_pos
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: 0 <= a • b
  证明: smul_nonneg ha.le hb.le

Depends on / 依赖: ha.le, hb.le, smul_nonneg
-/
theorem smul_nonneg_of_pos_of_pos (ha : 0 < a) (hb : 0 < b) : 0 <= a • b :=
  smul_nonneg ha.le hb.le

end PosSMulMono

section Module.IsTorsionFree
variable [Semiring α] [IsDomain α] [AddCommMonoid β] [Module α β] [Module.IsTorsionFree α β]
  {a : α} {b : β}

/--
theorem `smul_ne_zero_of_pos_of_ne_zero` / 定理 `smul_ne_zero_of_pos_of_ne_zero`

English:
theorem smul_ne_zero_of_pos_of_ne_zero
  given: [Preorder α] (ha : 0 < a) (hb : b != 0)
  statement: a • b != 0
  proof: smul_ne_zero ha.ne' hb

中文:
定理 smul_ne_zero_of_pos_of_ne_zero
  条件: [Preorder α] (ha : 0 < a) (hb : b != 0)
  结论: a • b != 0
  证明: smul_ne_zero ha.ne' hb

Depends on / 依赖: ha.ne, smul_ne_zero
-/
theorem smul_ne_zero_of_pos_of_ne_zero [Preorder α] (ha : 0 < a) (hb : b != 0) : a • b != 0 :=
  smul_ne_zero ha.ne' hb

/--
theorem `smul_ne_zero_of_ne_zero_of_pos` / 定理 `smul_ne_zero_of_ne_zero_of_pos`

English:
theorem smul_ne_zero_of_ne_zero_of_pos
  given: [Preorder β] (ha : a != 0) (hb : 0 < b)
  statement: a • b != 0
  proof: smul_ne_zero ha hb.ne'

中文:
定理 smul_ne_zero_of_ne_zero_of_pos
  条件: [Preorder β] (ha : a != 0) (hb : 0 < b)
  结论: a • b != 0
  证明: smul_ne_zero ha hb.ne'

Depends on / 依赖: hb.ne, smul_ne_zero
-/
theorem smul_ne_zero_of_ne_zero_of_pos [Preorder β] (ha : a != 0) (hb : 0 < b) : a • b != 0 :=
  smul_ne_zero ha hb.ne'

end Module.IsTorsionFree

/-- Positivity extension for scalar multiplication. -/
@[positivity HSMul.hSMul _ _]
meta def evalSMul : PositivityExt where eval {_u α} zα pα? (e : Q($α)) :=
  match pα? with | none => pure .none | some pα => do
  let .app (.app (.app (.app (.app (.app
        (.const ``HSMul.hSMul [u1, _, _]) (β : Q(Type u1))) _) _) _)
          (a : Q($β))) (b : Q($α)) ← whnfR e | throwError "failed to match hSMul"
  let zM : Q(Zero $β) ← synthInstanceQ q(Zero $β)
  let pM : Q(PartialOrder $β) ← synthInstanceQ q(PartialOrder $β)
  -- Using `q()` here would be impractical, as we would have to manually `synthInstanceQ` all the
  -- required typeclasses. Ideally we could tell `q()` to do this automatically.
  match ← core zM pM a, ← core zα pα b with
  | .positive pa, .positive pb =>
      try {
        let _hαβ : Q(SMul $β $α) ← synthInstanceQ q(SMul $β $α)
        let _hαβ : Q(PosSMulStrictMono $β $α) ← synthInstanceQ q(PosSMulStrictMono $β $α)
        pure (.positive (← mkAppM ``smul_pos #[pa, pb]))
      } catch _ =>
        pure (.nonnegative (← mkAppM ``smul_nonneg_of_pos_of_pos #[pa, pb]))
  | .positive pa, .nonnegative pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg_of_pos_of_nonneg #[pa, pb]))
  | .nonnegative pa, .positive pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg_of_nonneg_of_pos #[pa, pb]))
  | .nonnegative pa, .nonnegative pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg #[pa, pb]))
  | .positive pa, .nonzero pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero_of_pos_of_ne_zero #[pa, pb]))
  | .nonzero pa, .positive pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero_of_ne_zero_of_pos #[pa, pb]))
  | .nonzero pa, .nonzero pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero #[pa, pb]))
  | _, _ => pure .none

end Mathlib.Meta.Positivity
