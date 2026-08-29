/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Field structure on the multiplicative/additive opposite
-/

@[expose] public section

assert_not_exists RelIso

variable {α : Type*}

namespace MulOpposite

/--
Instance `instNNRatCast` / 实例 `instNNRatCast`

English:
instance instNNRatCast
  signature: [NNRatCast α]
  body: ⟨fun q => op q⟩

中文:
实例 instNNRatCast
  签名: [NNRatCast α]
  定义体: ⟨fun q => op q⟩
-/
@[to_additive] instance instNNRatCast [NNRatCast α] : NNRatCast αᵐᵒᵖ := ⟨fun q => op q⟩
/--
Instance `instRatCast` / 实例 `instRatCast`

English:
instance instRatCast
  signature: [RatCast α]
  body: ⟨fun q => op q⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instRatCast
  签名: [RatCast α]
  定义体: ⟨fun q => op q⟩

@[to_additive (attr := simp, norm_cast)]
-/
@[to_additive] instance instRatCast [RatCast α] : RatCast αᵐᵒᵖ := ⟨fun q => op q⟩

@[to_additive (attr := simp, norm_cast)]
/--
lemma `op_nnratCast` / 引理 `op_nnratCast`

English:
lemma op_nnratCast
  given: [NNRatCast α] (q : Rat>=0)
  statement: op (q : α) = q
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
引理 op_nnratCast
  条件: [NNRatCast α] (q : Rat>=0)
  结论: op (q : α) = q
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
lemma op_nnratCast [NNRatCast α] (q : Rat>=0) : op (q : α) = q := rfl

@[to_additive (attr := simp, norm_cast)]
/--
lemma `unop_nnratCast` / 引理 `unop_nnratCast`

English:
lemma unop_nnratCast
  given: [NNRatCast α] (q : Rat>=0)
  statement: unop (q : αᵐᵒᵖ) = q
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
引理 unop_nnratCast
  条件: [NNRatCast α] (q : Rat>=0)
  结论: unop (q : αᵐᵒᵖ) = q
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
lemma unop_nnratCast [NNRatCast α] (q : Rat>=0) : unop (q : αᵐᵒᵖ) = q := rfl

@[to_additive (attr := simp, norm_cast)]
/--
lemma `op_ratCast` / 引理 `op_ratCast`

English:
lemma op_ratCast
  given: [RatCast α] (q : Rat)
  statement: op (q : α) = q
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
引理 op_ratCast
  条件: [RatCast α] (q : Rat)
  结论: op (q : α) = q
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
lemma op_ratCast [RatCast α] (q : Rat) : op (q : α) = q := rfl

@[to_additive (attr := simp, norm_cast)]
/--
lemma `unop_ratCast` / 引理 `unop_ratCast`

English:
lemma unop_ratCast
  given: [RatCast α] (q : Rat)
  statement: unop (q : αᵐᵒᵖ) = q
  proof: rfl

中文:
引理 unop_ratCast
  条件: [RatCast α] (q : Rat)
  结论: unop (q : αᵐᵒᵖ) = q
  证明: rfl
-/
lemma unop_ratCast [RatCast α] (q : Rat) : unop (q : αᵐᵒᵖ) = q := rfl

/--
Instance `instDivisionSemiring` / 实例 `instDivisionSemiring`

English:
instance instDivisionSemiring
  signature: [DivisionSemiring α]
  body: instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
nnratCast_def q := unop_injective by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv, Nat.cast_comm]

中文:
实例 instDivisionSemiring
  签名: [DivisionSemiring α]
  定义体: instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
nnratCast_def q := unop_injective by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv, Nat.cast_comm]

Depends on / 依赖: instSemiring
-/
instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ where
  __ := instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
nnratCast_def q := unop_injective by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv, Nat.cast_comm]

/--
Instance `instDivisionRing` / 实例 `instDivisionRing`

English:
instance instDivisionRing
  signature: [DivisionRing α]
  body: instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
ratCast_def q := unop_injective by rw [unop_ratCast, Rat.cast_def, unop_div,
    unop_natCast, unop_intCast, Int.commute_cast, div_eq_mul_inv]

中文:
实例 instDivisionRing
  签名: [DivisionRing α]
  定义体: instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
ratCast_def q := unop_injective by rw [unop_ratCast, Rat.cast_def, unop_div,
    unop_natCast, unop_intCast, Int.commute_cast, div_eq_mul_inv]

Depends on / 依赖: instRing
-/
instance instDivisionRing [DivisionRing α] : DivisionRing αᵐᵒᵖ where
  __ := instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
ratCast_def q := unop_injective by rw [unop_ratCast, Rat.cast_def, unop_div,
    unop_natCast, unop_intCast, Int.commute_cast, div_eq_mul_inv]

/--
Instance `instSemifield` / 实例 `instSemifield`

English:
instance instSemifield
  signature: [Semifield α]
  body: instCommSemiring
  __ := instDivisionSemiring

中文:
实例 instSemifield
  签名: [Semifield α]
  定义体: instCommSemiring
  __ := instDivisionSemiring

Depends on / 依赖: instCommSemiring
-/
instance instSemifield [Semifield α] : Semifield αᵐᵒᵖ where
  __ := instCommSemiring
  __ := instDivisionSemiring

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: [Field α]
  body: instCommRing
  __ := instDivisionRing

中文:
实例 instField
  签名: [Field α]
  定义体: instCommRing
  __ := instDivisionRing

Depends on / 依赖: instCommRing
-/
instance instField [Field α] : Field αᵐᵒᵖ where
  __ := instCommRing
  __ := instDivisionRing

end MulOpposite

namespace AddOpposite

/--
Instance `instDivisionSemiring` / 实例 `instDivisionSemiring`

English:
instance instDivisionSemiring
  signature: [DivisionSemiring α]
  body: instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
nnratCast_def q := unop_injective by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv]

中文:
实例 instDivisionSemiring
  签名: [DivisionSemiring α]
  定义体: instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
nnratCast_def q := unop_injective by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv]

Depends on / 依赖: instSemiring
-/
instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ where
  __ := instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
nnratCast_def q := unop_injective by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv]

/--
Instance `instDivisionRing` / 实例 `instDivisionRing`

English:
instance instDivisionRing
  signature: [DivisionRing α]
  body: instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
ratCast_def q := unop_injective by rw [unop_ratCast, Rat.cast_def, unop_div, unop_natCast,
    unop_intCast, div_eq_mul_inv]

中文:
实例 instDivisionRing
  签名: [DivisionRing α]
  定义体: instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
ratCast_def q := unop_injective by rw [unop_ratCast, Rat.cast_def, unop_div, unop_natCast,
    unop_intCast, div_eq_mul_inv]

Depends on / 依赖: instRing
-/
instance instDivisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ where
  __ := instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
ratCast_def q := unop_injective by rw [unop_ratCast, Rat.cast_def, unop_div, unop_natCast,
    unop_intCast, div_eq_mul_inv]

/--
Instance `instSemifield` / 实例 `instSemifield`

English:
instance instSemifield
  signature: [Semifield α]
  body: instCommSemiring
  __ := instDivisionSemiring

中文:
实例 instSemifield
  签名: [Semifield α]
  定义体: instCommSemiring
  __ := instDivisionSemiring

Depends on / 依赖: instCommSemiring
-/
instance instSemifield [Semifield α] : Semifield αᵃᵒᵖ where
  __ := instCommSemiring
  __ := instDivisionSemiring

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: [Field α]
  body: instCommRing
  __ := instDivisionRing

中文:
实例 instField
  签名: [Field α]
  定义体: instCommRing
  __ := instDivisionRing

Depends on / 依赖: instCommRing
-/
instance instField [Field α] : Field αᵃᵒᵖ where
  __ := instCommRing
  __ := instDivisionRing

end AddOpposite
