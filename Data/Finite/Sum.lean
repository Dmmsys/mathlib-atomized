/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Fintype.Sum

/-!
# Finiteness of sum types
-/

public section

variable {α β : Type*}

namespace Finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] [Finite β] : Finite (α oplus β)
  body: by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  infer_instance

中文:
实例 [有限
  签名: α] [有限 β] : 有限 (α oplus β)
  定义体: by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  infer_instance

Depends on / 依赖: Fintype, Fintype.ofFinite, infer_instance, ofFinite
-/
instance [Finite α] [Finite β] : Finite (α oplus β) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  infer_instance

/--
theorem `sum_left` / 定理 `sum_left`

English:
theorem sum_left
  given: (β) [Finite (α oplus β)]
  statement: Finite α
  proof: of_injective (Sum.inl : α -> α oplus β) Sum.inl_injective

中文:
定理 sum_left
  条件: (β) [有限 (α oplus β)]
  结论: 有限 α
  证明: of_injective (Sum.inl : α -> α oplus β) Sum.inl_injective

Depends on / 依赖: Sum.inl, Sum.inl_injective, inl_injective, of_injective
-/
theorem sum_left (β) [Finite (α oplus β)] : Finite α :=
  of_injective (Sum.inl : α -> α oplus β) Sum.inl_injective

/--
theorem `sum_right` / 定理 `sum_right`

English:
theorem sum_right
  given: (α) [Finite (α oplus β)]
  statement: Finite β
  proof: of_injective (Sum.inr : β -> α oplus β) Sum.inr_injective

中文:
定理 sum_right
  条件: (α) [有限 (α oplus β)]
  结论: 有限 β
  证明: of_injective (Sum.inr : β -> α oplus β) Sum.inr_injective

Depends on / 依赖: Sum.inr, Sum.inr_injective, inr_injective, of_injective
-/
theorem sum_right (α) [Finite (α oplus β)] : Finite β :=
  of_injective (Sum.inr : β -> α oplus β) Sum.inr_injective

instance {α β : Sort*} [Finite α] [Finite β] : Finite (α oplus' β) :=
  of_equiv _ ((Equiv.psumEquivSum _ _).symm.trans (Equiv.plift.psumCongr Equiv.plift))

/--
theorem `psum_left` / 定理 `psum_left`

English:
theorem psum_left
  given: {α β : Sort*} [Finite (α oplus' β)]
  statement: Finite α
  proof: of_injective (PSum.inl : α -> α oplus' β) PSum.inl_injective

中文:
定理 psum_left
  条件: {α β : 类型层*} [有限 (α oplus' β)]
  结论: 有限 α
  证明: of_injective (PSum.inl : α -> α oplus' β) PSum.inl_injective

Depends on / 依赖: PSum.inl, PSum.inl_injective, inl_injective, of_injective
-/
theorem psum_left {α β : Sort*} [Finite (α oplus' β)] : Finite α :=
  of_injective (PSum.inl : α -> α oplus' β) PSum.inl_injective

/--
theorem `psum_right` / 定理 `psum_right`

English:
theorem psum_right
  given: {α β : Sort*} [Finite (α oplus' β)]
  statement: Finite β
  proof: of_injective (PSum.inr : β -> α oplus' β) PSum.inr_injective

中文:
定理 psum_right
  条件: {α β : 类型层*} [有限 (α oplus' β)]
  结论: 有限 β
  证明: of_injective (PSum.inr : β -> α oplus' β) PSum.inr_injective

Depends on / 依赖: PSum.inr, PSum.inr_injective, inr_injective, of_injective
-/
theorem psum_right {α β : Sort*} [Finite (α oplus' β)] : Finite β :=
  of_injective (PSum.inr : β -> α oplus' β) PSum.inr_injective

end Finite
