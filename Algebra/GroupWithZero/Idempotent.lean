/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Idempotent elements of a group with zero
-/

public section

assert_not_exists Ring

variable {M₀ : Type*}

namespace IsIdempotentElem
section MulZeroClass
variable [MulZeroClass M₀]

/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  statement: IsIdempotentElem (0 : M₀)
  proof: mul_zero _

中文:
引理 zero
  结论: IsIdempotentElem (0 : M₀)
  证明: mul_zero _

Depends on / 依赖: mul_zero
-/
lemma zero : IsIdempotentElem (0 : M₀) := mul_zero _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero { p : M₀ // IsIdempotentElem p }
  body: ⟨0, zero⟩

中文:
实例 :
  签名: Zero { p : M₀ // IsIdempotentElem p }
  定义体: ⟨0, zero⟩
-/
instance : Zero { p : M₀ // IsIdempotentElem p } where zero := ⟨0, zero⟩

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ↑(0 : { p : M₀ // IsIdempotentElem p }) = (0 : M₀)
  proof: rfl

中文:
引理 coe_zero
  结论: ↑(0 : { p : M₀ // IsIdempotentElem p }) = (0 : M₀)
  证明: rfl
-/
@[simp] lemma coe_zero : ↑(0 : { p : M₀ // IsIdempotentElem p }) = (0 : M₀) := rfl

end MulZeroClass

section CancelMonoidWithZero
variable {G₀ : Type*} [MonoidWithZero G₀] [IsLeftCancelMulZero G₀]

@[simp]
/--
lemma `iff_eq_zero_or_one` / 引理 `iff_eq_zero_or_one`

English:
lemma iff_eq_zero_or_one
  given: {p : G₀}
  statement: IsIdempotentElem p ↔ p = 0 ∨ p = 1 where
  proof: or_iff_not_imp_left.mpr fun hp => mul_left_cancel₀ hp (h.trans (mul_one p).symm)
  mpr h := h.elim (fun hp => hp.symm ▸ zero) fun hp => hp.symm ▸ one

中文:
引理 iff_eq_zero_or_one
  条件: {p : G₀}
  结论: IsIdempotentElem p ↔ p = 0 ∨ p = 1 where
  证明: or_iff_not_imp_left.mpr fun hp => mul_left_cancel₀ hp (h.trans (mul_one p).symm)
  mpr h := h.elim (fun hp => hp.symm ▸ zero) fun hp => hp.symm ▸ one

Depends on / 依赖: h.trans, mul_one, or_iff_not_imp_left, or_iff_not_imp_left.mpr
-/
lemma iff_eq_zero_or_one {p : G₀} : IsIdempotentElem p ↔ p = 0 ∨ p = 1 where
  mp h := or_iff_not_imp_left.mpr fun hp => mul_left_cancel₀ hp (h.trans (mul_one p).symm)
  mpr h := h.elim (fun hp => hp.symm ▸ zero) fun hp => hp.symm ▸ one

end CancelMonoidWithZero
end IsIdempotentElem
