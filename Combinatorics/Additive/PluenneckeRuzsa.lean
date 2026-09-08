/-
Copyright (c) 2022 Yaël Dillies, George Shakan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, George Shakan
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# The Plünnecke-Ruzsa inequality

This file proves Ruzsa's triangle inequality, the Plünnecke-Petridis lemma, and the Plünnecke-Ruzsa
inequality.

## Main declarations

* `Finset.ruzsa_triangle_inequality_sub_sub_sub`: The Ruzsa triangle inequality, difference version.
* `Finset.ruzsa_triangle_inequality_add_add_add`: The Ruzsa triangle inequality, sum version.
* `Finset.pluennecke_petridis_inequality_add`: The Plünnecke-Petridis inequality.
* `Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add`: The Plünnecke-Ruzsa inequality.

## References

* [Giorgis Petridis, *The Plünnecke-Ruzsa inequality: an overview*][petridis2014]
* [Terence Tao, Van Vu, *Additive Combinatorics*][tao-vu]

## See also

In general non-abelian groups, small doubling doesn't imply small powers anymore, but small tripling
does. See `Mathlib/Combinatorics/Additive/SmallTripling.lean`.
-/

public section

open MulOpposite Nat
open scoped Pointwise
namespace Finset
variable {G : Type*} [DecidableEq G]

section Group
variable [Group G] {A B C : Finset G}

/-! ### Noncommutative Ruzsa triangle inequality -/

/-- **Ruzsa's triangle inequality**. Division version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Subtraction version. -/]
/-
**Finset.ruzsa_triangle_inequality_div_div_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：ruzsa_triangle_inequality_div_div_div (A B C : Finset G) : #(A / C) * #B <
= #(A / B) * #(C / B)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.card_mul_le_card_mul`：card_mul_le_card_mul [forall a b, Decidable
 (r a b)] (hm : forall a in s, m <= #(t.bipartiteAbove r a)) (hn : forall b in t
, #(s.bipartiteBe…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_div`：mem_div : a in s / t ↔ exists b in s, exists c in t, b /
 c = a
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.mem_bipartiteAbove`：mem_bipartiteAbove {b : β} : b in t.bipartite
Above r a ↔ b in t ∧ r a b
· 使用定理 `Finset.mk_mem_product`：mk_mem_product (ha : a in s) (hb : b in t) : (a, 
b) in s ×ˢ t
· 使用定理 `Finset.div_mem_div`：div_mem_div : a in s -> b in t -> a / b in s / t
· 使用定理 `div_div_div_cancel_right`：div_div_div_cancel_right (a b c : G) : a / c /
 (b / c) = a / b
· 使用定理 `div_right_injective`：div_right_injective : Function.Injective fun a => b
 / a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_le_one_iff`：card_le_one_iff : #s <= 1 ↔ forall {a b}, a in s
 -> b in s -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_bipartiteBelow`：mem_bipartiteBelow {a : α} : a in s.bipartite
Below r b ↔ a in s ∧ r a b

--- 原说明 ---
**Ruzsa's triangle inequality**. Division version.
-/
theorem ruzsa_triangle_inequality_div_div_div (A B C : Finset G) :
    #(A / C) * #B ≤ #(A / B) * #(C / B) := by
  rw [← card_product (A / B), ← mul_one #((A / B) ×ˢ (C / B))]
  refine card_mul_le_card_mul (fun b (a, c) ↦ a / c = b) (fun x hx ↦ ?_)
    fun x _ ↦ card_le_one_iff.2 fun hu hv ↦
      ((mem_bipartiteBelow _).1 hu).2.symm.trans ?_
  · obtain ⟨a, ha, c, hc, rfl⟩ := mem_div.1 hx
    refine card_le_card_of_injOn (fun b ↦ (a / b, c / b)) (fun b hb ↦ ?_) fun b₁ _ b₂ _ h ↦ ?_
    · rw [mem_coe, mem_bipartiteAbove]
      exact ⟨mk_mem_product (div_mem_div ha hb) (div_mem_div hc hb), div_div_div_cancel_right ..⟩
    · exact div_right_injective (Prod.ext_iff.1 h).1
  · exact ((mem_bipartiteBelow _).1 hv).2

/-- **Ruzsa's triangle inequality**. Mulinv-mulinv-mulinv version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Addneg-addneg-addneg version. -/]
/-
**Finset.ruzsa_triangle_inequality_mulInv_mulInv_mulInv** 是 Mathlib 中的一个定理，位于命名空
间 `Finset`。
形式化陈述：ruzsa_triangle_inequality_mulInv_mulInv_mulInv (A B C : Finset G) : #(A * 
C⁻¹) * #B <= #(A * B⁻¹) * #(C * B⁻¹)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.ruzsa_triangle_inequality_div_div_div`：ruzsa_triangle_inequality_
div_div_div (A B C : Finset G) : #(A / C) * #B <= #(A / B) * #(C / B)

--- 原说明 ---
**Ruzsa's triangle inequality**. Mulinv-mulinv-mulinv version.
-/
theorem ruzsa_triangle_inequality_mulInv_mulInv_mulInv (A B C : Finset G) :
    #(A * C⁻¹) * #B ≤ #(A * B⁻¹) * #(C * B⁻¹) := by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_div_div_div A B C

/-- **Ruzsa's triangle inequality**. Invmul-invmul-invmul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Negadd-negadd-negadd version. -/]
/-
**Finset.ruzsa_triangle_inequality_invMul_invMul_invMul** 是 Mathlib 中的一个定理，位于命名空
间 `Finset`。
形式化陈述：ruzsa_triangle_inequality_invMul_invMul_invMul (A B C : Finset G) : #B * #
(A⁻¹ * C) <= #(B⁻¹ * A) * #(B⁻¹ * C)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.ruzsa_triangle_inequality_div_div_div`：ruzsa_triangle_inequality_
div_div_div (A B C : Finset G) : #(A / C) * #B <= #(A / B) * #(C / B)

--- 原说明 ---
**Ruzsa's triangle inequality**. Invmul-invmul-invmul version.
-/
theorem ruzsa_triangle_inequality_invMul_invMul_invMul (A B C : Finset G) :
    #B * #(A⁻¹ * C) ≤ #(B⁻¹ * A) * #(B⁻¹ * C) := by
  simpa [mul_comm, div_eq_mul_inv, ← map_op_mul, ← map_op_inv] using
    ruzsa_triangle_inequality_div_div_div (G := Gᵐᵒᵖ) (C.map opEquiv.toEmbedding)
      (B.map opEquiv.toEmbedding) (A.map opEquiv.toEmbedding)


/-- **Ruzsa's triangle inequality**. Div-mul-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Sub-add-add version. -/]
/-
**Finset.ruzsa_triangle_inequality_div_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：ruzsa_triangle_inequality_div_mul_mul (A B C : Finset G) : #(A / C) * #B <
= #(A * B) * #(C * B)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `Finset.ruzsa_triangle_inequality_div_div_div`：ruzsa_triangle_inequality_
div_div_div (A B C : Finset G) : #(A / C) * #B <= #(A / B) * #(C / B)

--- 原说明 ---
**Ruzsa's triangle inequality**. Div-mul-mul version.
-/
theorem ruzsa_triangle_inequality_div_mul_mul (A B C : Finset G) :
    #(A / C) * #B ≤ #(A * B) * #(C * B) := by
  simpa using ruzsa_triangle_inequality_div_div_div A B⁻¹ C

/-- **Ruzsa's triangle inequality**. Mulinv-mul-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Addneg-add-add version. -/]
/-
**Finset.ruzsa_triangle_inequality_mulInv_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Fin
set`。
形式化陈述：ruzsa_triangle_inequality_mulInv_mul_mul (A B C : Finset G) : #(A * C⁻¹) *
 #B <= #(A * B) * #(C * B)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Finset.ruzsa_triangle_inequality_mulInv_mulInv_mulInv`：ruzsa_triangle_in
equality_mulInv_mulInv_mulInv (A B C : Finset G) : #(A * C⁻¹) * #B <= #(A * B⁻¹)
 * #(C * B⁻¹)

--- 原说明 ---
**Ruzsa's triangle inequality**. Mulinv-mul-mul version.
-/
theorem ruzsa_triangle_inequality_mulInv_mul_mul (A B C : Finset G) :
    #(A * C⁻¹) * #B ≤ #(A * B) * #(C * B) := by
  simpa using ruzsa_triangle_inequality_mulInv_mulInv_mulInv A B⁻¹ C

/-- **Ruzsa's triangle inequality**. Invmul-mul-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Negadd-add-add version. -/]
/-
**Finset.ruzsa_triangle_inequality_invMul_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Fin
set`。
形式化陈述：ruzsa_triangle_inequality_invMul_mul_mul (A B C : Finset G) : #B * #(A⁻¹ *
 C) <= #(B * A) * #(B * C)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Finset.ruzsa_triangle_inequality_invMul_invMul_invMul`：ruzsa_triangle_in
equality_invMul_invMul_invMul (A B C : Finset G) : #B * #(A⁻¹ * C) <= #(B⁻¹ * A)
 * #(B⁻¹ * C)

--- 原说明 ---
**Ruzsa's triangle inequality**. Invmul-mul-mul version.
-/
theorem ruzsa_triangle_inequality_invMul_mul_mul (A B C : Finset G) :
    #B * #(A⁻¹ * C) ≤ #(B * A) * #(B * C) := by
  simpa using ruzsa_triangle_inequality_invMul_invMul_invMul A B⁻¹ C


/-- **Ruzsa's triangle inequality**. Mul-div-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-sub-add version. -/]
/-
**Finset.ruzsa_triangle_inequality_mul_div_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：ruzsa_triangle_inequality_mul_div_mul (A B C : Finset G) : #B * #(A * C) <
= #(B / A) * #(B * C)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Finset.ruzsa_triangle_inequality_invMul_mul_mul`：ruzsa_triangle_inequali
ty_invMul_mul_mul (A B C : Finset G) : #B * #(A⁻¹ * C) <= #(B * A) * #(B * C)

--- 原说明 ---
**Ruzsa's triangle inequality**. Mul-div-mul version.
-/
theorem ruzsa_triangle_inequality_mul_div_mul (A B C : Finset G) :
    #B * #(A * C) ≤ #(B / A) * #(B * C) := by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_invMul_mul_mul A⁻¹ B C

/-- **Ruzsa's triangle inequality**. Mul-mulinv-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-addneg-add version. -/]
/-
**Finset.ruzsa_triangle_inequality_mul_mulInv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Fin
set`。
形式化陈述：ruzsa_triangle_inequality_mul_mulInv_mul (A B C : Finset G) : #B * #(A * C
) <= #(B * A⁻¹) * #(B * C)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.ruzsa_triangle_inequality_mul_div_mul`：ruzsa_triangle_inequality_
mul_div_mul (A B C : Finset G) : #B * #(A * C) <= #(B / A) * #(B * C)

--- 原说明 ---
**Ruzsa's triangle inequality**. Mul-mulinv-mul version.
-/
theorem ruzsa_triangle_inequality_mul_mulInv_mul (A B C : Finset G) :
    #B * #(A * C) ≤ #(B * A⁻¹) * #(B * C) := by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_mul_div_mul A B C

/-- **Ruzsa's triangle inequality**. Mul-mul-invmul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-add-negadd version. -/]
/-
**Finset.ruzsa_triangle_inequality_mul_mul_invMul** 是 Mathlib 中的一个定理，位于命名空间 `Fin
set`。
形式化陈述：ruzsa_triangle_inequality_mul_mul_invMul (A B C : Finset G) : #(A * C) * #
B <= #(A * B) * #(C⁻¹ * B)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Finset.ruzsa_triangle_inequality_mulInv_mul_mul`：ruzsa_triangle_inequali
ty_mulInv_mul_mul (A B C : Finset G) : #(A * C⁻¹) * #B <= #(A * B) * #(C * B)

--- 原说明 ---
**Ruzsa's triangle inequality**. Mul-mul-invmul version.
-/
theorem ruzsa_triangle_inequality_mul_mul_invMul (A B C : Finset G) :
    #(A * C) * #B ≤ #(A * B) * #(C⁻¹ * B) := by
  simpa using ruzsa_triangle_inequality_mulInv_mul_mul A B C⁻¹

/-! ### Plünnecke-Petridis inequality -/

@[to_additive]
/-
**Finset.pluennecke_petridis_inequality_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pluennecke_petridis_inequality_mul (C : Finset G) (hA : forall A' subseteq
 A, #(A * B) * #A' <= #(A' * B) * #A) : #(C * A * B) * #A <= #(A * B) * #(C * A)
参数：C : Finset G；hA : forall A' subseteq A, #(A * B) * #A' <= #(A' * B) * #A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.empty_mul`：empty_mul (s : Finset α) : ∅ * s = ∅
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.singleton_mul_inter`：singleton_mul_inter (a : α) (s t : Finset α)
 : {a} * (s inter t) = {a} * s inter ({a} * t)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsUnit.mul_inv_cancel_left`：∀ {α : Type u} [inst : DivisionMonoid α] {a 
: α}, IsUnit a → ∀ (b : α), a * (a⁻¹ * b) = b
· 使用定理 `Finset.isUnit_singleton`：isUnit_singleton (a : α) : IsUnit ({a} : Finset
 α)
· 使用定理 `Finset.insert_eq`：insert_eq (a : α) (s : Finset α) : insert a s = {a} un
ion s
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `Finset.union_mul`：union_mul : (s₁ union s₂) * t = s₁ * t union s₂ * t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_sdiff_eq_sup`：sup_sdiff_eq_sup (h : c <= a) : a ⊔ b \ c = a ⊔ b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Finset.instMulLeftMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 
: Mul α], MulLeftMono (Finset α)
· 使用定理 `Finset.instMulRightMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Mul α], MulRightMono (Finset α)
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `add_tsub_assoc_of_le`：add_tsub_assoc_of_le (h : c <= b) (a : α) : a + b 
- c = a + (b - c)
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
### Plünnecke-Petridis inequality
-/
theorem pluennecke_petridis_inequality_mul (C : Finset G)
    (hA : ∀ A' ⊆ A, #(A * B) * #A' ≤ #(A' * B) * #A) :
    #(C * A * B) * #A ≤ #(A * B) * #(C * A) := by
  induction C using Finset.induction_on with
  | empty => simp
  | insert x C _ ih =>
    set A' := A ∩ ({x}⁻¹ * C * A) with hA'
    set C' := insert x C with hC'
    have h₀ : {x} * A' = {x} * A ∩ (C * A) := by
      rw [hA', mul_assoc, singleton_mul_inter, (isUnit_singleton x).mul_inv_cancel_left]
    have h₁ : C' * A * B = C * A * B ∪ ({x} * A * B) \ ({x} * A' * B) := by
      rw [hC', insert_eq, union_comm, union_mul, union_mul]
      refine (sup_sdiff_eq_sup ?_).symm
      rw [h₀]
      gcongr
      exact inter_subset_right
    have h₂ : {x} * A' * B ⊆ {x} * A * B := by gcongr; exact inter_subset_left
    calc
      #(C' * A * B) * #A
      _ ≤ (#(C * A * B) + #(A * B) - #(A' * B)) * #A := by
        gcongr
        rw [h₁]
        refine (card_union_le _ _).trans_eq ?_
        rw [card_sdiff_of_subset h₂, ← add_tsub_assoc_of_le (card_le_card h₂), mul_assoc {_},
          mul_assoc {_}, card_singleton_mul, card_singleton_mul]
      _ = #(C * A * B) * #A + #(A * B) * #A - #(A' * B) * #A := by rw [tsub_mul, add_mul]
      _ ≤ #(A * B) * #(C * A) + #(A * B) * #A - #(A * B) * #(A ∩ ({x}⁻¹ * C * A)) := by
        gcongr ?_ + _ - ?_; exact hA _ inter_subset_left
      _ = #(A * B) * #(C' * A) := by
        rw [← mul_add, ← mul_tsub, ← hA', hC', insert_eq, union_mul, ← card_singleton_mul x A,
          ← card_singleton_mul x A', add_comm #_, h₀,
          eq_tsub_of_add_eq (card_union_add_card_inter _ _)]

end Group

section CommGroup
variable [CommGroup G] {A B C : Finset G}

/-! ### Commutative Ruzsa triangle inequality -/

-- Auxiliary lemma for Ruzsa's triangle sum inequality, and the Plünnecke-Ruzsa inequality.
@[to_additive]
/-
**Finset.mul_aux** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_aux (hA : A.Nonempty) (hAB : A ⊆ B)
    (h : ∀ A' ∈ B.powerset.erase ∅, (#(A * C) : ℚ≥0) / #A ≤ #(A' * C) / #A') :
    ∀ A' ⊆ A, #(A * C) * #A' ≤ #(A' * C) * #A := by
  rintro A' hAA'
  obtain rfl | hA' := A'.eq_empty_or_nonempty
  · simp
  have hA₀ : (0 : ℚ≥0) < #A := cast_pos.2 hA.card_pos
  have hA₀' : (0 : ℚ≥0) < #A' := cast_pos.2 hA'.card_pos
  exact mod_cast
    (div_le_div_iff₀ hA₀ hA₀').1
      (h _ <| mem_erase_of_ne_of_mem hA'.ne_empty <| mem_powerset.2 <| hAA'.trans hAB)

/-- **Ruzsa's triangle inequality**. Multiplication version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Addition version. -/]
/-
**Finset.ruzsa_triangle_inequality_mul_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：ruzsa_triangle_inequality_mul_mul_mul (A B C : Finset G) : #(A * C) * #B <
= #(A * B) * #(B * C)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.mul_empty`：mul_empty (s : Finset α) : s * ∅ = ∅
· 使用定理 `Finset.empty_mul`：empty_mul (s : Finset α) : ∅ * s = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_erase_of_ne_of_mem`：mem_erase_of_ne_of_mem : a != b -> a in s
 -> a in erase s b
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `Finset.mem_powerset_self`：mem_powerset_self (s : Finset α) : s in powers
et s
· 使用定理 `Finset.exists_min_image`：exists_min_image (s : Finset β) (f : β -> α) (h
 : s.Nonempty) : exists x in s, forall x' in s, f x <= f x'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `mul_div_right_comm`：mul_div_right_comm : a * b / c = a / c * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
**Ruzsa's triangle inequality**. Multiplication version.
-/
theorem ruzsa_triangle_inequality_mul_mul_mul (A B C : Finset G) :
    #(A * C) * #B ≤ #(A * B) * #(B * C) := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  have hB' : B ∈ B.powerset.erase ∅ := mem_erase_of_ne_of_mem hB.ne_empty (mem_powerset_self _)
  obtain ⟨U, hU, hUA⟩ :=
    exists_min_image (B.powerset.erase ∅) (fun U ↦ #(U * A) / #U : _ → ℚ≥0) ⟨B, hB'⟩
  rw [mem_erase, mem_powerset, ← nonempty_iff_ne_empty] at hU
  refine cast_le.1 (?_ : (_ : ℚ≥0) ≤ _)
  push_cast
  rw [← le_div_iff₀ (cast_pos.2 hB.card_pos), mul_div_right_comm, mul_comm _ B]
  grw [card_le_card_mul_left hU.1, ← hUA _ hB', ← mul_subset_mul_right hU.2]
  rw [← mul_div_right_comm, ← mul_assoc, le_div_iff₀ (cast_pos.2 hU.1.card_pos), mul_comm _ C,
    ← mul_assoc, mul_comm _ C]
  exact mod_cast pluennecke_petridis_inequality_mul C (mul_aux hU.1 hU.2 hUA)

/-- **Ruzsa's triangle inequality**. Mul-div-div version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-sub-sub version. -/]
/-
**Finset.ruzsa_triangle_inequality_mul_div_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：ruzsa_triangle_inequality_mul_div_div (A B C : Finset G) : #(A * C) * #B <
= #(A / B) * #(B / C)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s
· 使用定理 `inv_div'`：inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `Finset.ruzsa_triangle_inequality_mul_mul_mul`：ruzsa_triangle_inequality_
mul_mul_mul (A B C : Finset G) : #(A * C) * #B <= #(A * B) * #(B * C)

--- 原说明 ---
**Ruzsa's triangle inequality**. Mul-div-div version.
-/
theorem ruzsa_triangle_inequality_mul_div_div (A B C : Finset G) :
    #(A * C) * #B ≤ #(A / B) * #(B / C) := by
  rw [div_eq_mul_inv, ← card_inv B, ← card_inv (B / C), inv_div', div_inv_eq_mul]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

/-- **Ruzsa's triangle inequality**. Div-mul-div version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Sub-add-sub version. -/]
/-
**Finset.ruzsa_triangle_inequality_div_mul_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：ruzsa_triangle_inequality_div_mul_div (A B C : Finset G) : #(A / C) * #B <
= #(A * B) * #(B / C)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.ruzsa_triangle_inequality_mul_mul_mul`：ruzsa_triangle_inequality_
mul_mul_mul (A B C : Finset G) : #(A * C) * #B <= #(A * B) * #(B * C)

--- 原说明 ---
**Ruzsa's triangle inequality**. Div-mul-div version.
-/
theorem ruzsa_triangle_inequality_div_mul_div (A B C : Finset G) :
    #(A / C) * #B ≤ #(A * B) * #(B / C) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

/-- **Ruzsa's triangle inequality**. Div-div-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Sub-sub-add version. -/]
/-
**Finset.card_div_mul_le_card_div_mul_card_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：card_div_mul_le_card_div_mul_card_mul (A B C : Finset G) : #(A / C) * #B <
= #(A / B) * #(B * C)
参数：A B C : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.ruzsa_triangle_inequality_mul_div_div`：ruzsa_triangle_inequality_
mul_div_div (A B C : Finset G) : #(A * C) * #B <= #(A / B) * #(B / C)

--- 原说明 ---
**Ruzsa's triangle inequality**. Div-div-mul version.
-/
theorem card_div_mul_le_card_div_mul_card_mul (A B C : Finset G) :
    #(A / C) * #B ≤ #(A / B) * #(B * C) := by
  rw [← div_inv_eq_mul, div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_div_div _ _ _

-- Auxiliary lemma towards the Plünnecke-Ruzsa inequality
@[to_additive]
/-
**Finset.card_mul_pow_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_mul_pow_le (hAB : ∀ A' ⊆ A, #(A * B) * #A' ≤ #(A' * B) * #A) (n : ℕ) :
    #(A * B ^ n) ≤ (#(A * B) / #A : ℚ≥0) ^ n * #A := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < #A)
    calc
      ((#(A * B ^ (n + 1))) * #A : ℚ≥0)
        = #(B ^ n * A * B) * #A := by rw [pow_succ, mul_left_comm, mul_assoc]
      _ ≤ #(A * B) * #(B ^ n * A) := mod_cast pluennecke_petridis_inequality_mul _ hAB
      _ ≤ #(A * B) * ((#(A * B) / #A) ^ n * #A) := by rw [mul_comm _ A]; gcongr
      _ = (#(A * B) / #A) ^ (n + 1) * #A * #A := by simp [field, pow_add]

/-- The **Plünnecke-Ruzsa inequality**. Multiplication version. Note that this is genuinely harder
than the division version because we cannot use a double counting argument. -/
@[to_additive /-- The **Plünnecke-Ruzsa inequality**. Addition version. Note that this is genuinely
harder than the subtraction version because we cannot use a double counting argument. -/]
/-
**Finset.pluennecke_ruzsa_inequality_pow_div_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `
Finset`。
形式化陈述：pluennecke_ruzsa_inequality_pow_div_pow_mul (hA : A.Nonempty) (B : Finset 
G) (m n : Nat) : #(B ^ m / B ^ n) <= (#(A * B) / #A : Rat>=0) ^ (m + n) * #A
参数：hA : A.Nonempty；B : Finset G；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_erase_of_ne_of_mem`：mem_erase_of_ne_of_mem : a != b -> a in s
 -> a in erase s b
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `Finset.mem_powerset_self`：mem_powerset_self (s : Finset α) : s in powers
et s
· 使用定理 `Finset.exists_min_image`：exists_min_image (s : Finset β) (f : β -> α) (h
 : s.Nonempty) : exists x in s, forall x' in s, f x <= f x'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.ruzsa_triangle_inequality_div_mul_mul`：ruzsa_triangle_inequality_
div_mul_mul (A B C : Finset G) : #(A / C) * #B <= #(A * B) * #(C * B)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `_private.Mathlib.Combinatorics.Additive.PluenneckeRuzsa.0.Finset.card_mu
l_pow_le`：∀ {G : Type u_1} [inst : DecidableEq G] [inst_1 : CommGroup G] {A B : 
Finset G},   (∀ A' ⊆ A, (A * B).card * A'.card ≤ (A' * B).card * A.car…
· 使用定理 `_private.Mathlib.Combinatorics.Additive.PluenneckeRuzsa.0.Finset.mul_aux
`：∀ {G : Type u_1} [inst : DecidableEq G] [inst_1 : CommGroup G] {A B C : Finset
 G},   A.Nonempty →     A ⊆ B →       (∀ A' ∈ B.powerset.erase…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 67 条，此处仅展示前 30 条）
-/
theorem pluennecke_ruzsa_inequality_pow_div_pow_mul (hA : A.Nonempty) (B : Finset G) (m n : ℕ) :
    #(B ^ m / B ^ n) ≤ (#(A * B) / #A : ℚ≥0) ^ (m + n) * #A := by
  have hA' : A ∈ A.powerset.erase ∅ := mem_erase_of_ne_of_mem hA.ne_empty (mem_powerset_self _)
  obtain ⟨C, hC, hCmin⟩ :=
    exists_min_image (A.powerset.erase ∅) (fun C ↦ #(C * B) / #C : _ → ℚ≥0) ⟨A, hA'⟩
  rw [mem_erase, mem_powerset, ← nonempty_iff_ne_empty] at hC
  obtain ⟨hC, hCA⟩ := hC
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < #C)
  calc
    (#(B ^ m / B ^ n) * #C : ℚ≥0)
      ≤ #(B ^ m * C) * #(B ^ n * C) := mod_cast ruzsa_triangle_inequality_div_mul_mul ..
    _ = #(C * B ^ m) * #(C * B ^ n) := by simp_rw [mul_comm]
    _ ≤ ((#(C * B) / #C) ^ m * #C) * ((#(C * B) / #C : ℚ≥0) ^ n * #C) := by
      gcongr <;> exact card_mul_pow_le (mul_aux hC hCA hCmin) _
    _ = (#(C * B) / #C) ^ (m + n) * #C * #C := by ring
    _ ≤ (#(A * B) / #A) ^ (m + n) * #A * #C := by gcongr (?_ ^ _) * #?_ * _; exact hCmin _ hA'

/-- The **Plünnecke-Ruzsa inequality**. Division version. -/
@[to_additive /-- The **Plünnecke-Ruzsa inequality**. Subtraction version. -/]
/-
**Finset.pluennecke_ruzsa_inequality_pow_div_pow_div** 是 Mathlib 中的一个定理，位于命名空间 `
Finset`。
形式化陈述：pluennecke_ruzsa_inequality_pow_div_pow_div (hA : A.Nonempty) (B : Finset 
G) (m n : Nat) : #(B ^ m / B ^ n) <= (#(A / B) / #A : Rat>=0) ^ (m + n) * #A
参数：hA : A.Nonempty；B : Finset G；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s
· 使用定理 `inv_div'`：inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.pluennecke_ruzsa_inequality_pow_div_pow_mul`：pluennecke_ruzsa_ine
quality_pow_div_pow_mul (hA : A.Nonempty) (B : Finset G) (m n : Nat) : #(B ^ m /
 B ^ n) <= (#(A * B) / #A : Rat>=0) ^ (m…

--- 原说明 ---
The **Plünnecke-Ruzsa inequality**. Division version.
-/
theorem pluennecke_ruzsa_inequality_pow_div_pow_div (hA : A.Nonempty) (B : Finset G) (m n : ℕ) :
    #(B ^ m / B ^ n) ≤ (#(A / B) / #A : ℚ≥0) ^ (m + n) * #A := by
  rw [← card_inv, inv_div', ← inv_pow, ← inv_pow, div_eq_mul_inv A]
  exact pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ _

/-- Special case of the **Plünnecke-Ruzsa inequality**. Multiplication version. -/
@[to_additive /-- Special case of the **Plünnecke-Ruzsa inequality**. Addition version. -/]
/-
**Finset.pluennecke_ruzsa_inequality_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pluennecke_ruzsa_inequality_pow_mul (hA : A.Nonempty) (B : Finset G) (n : 
Nat) : #(B ^ n) <= (#(A * B) / #A : Rat>=0) ^ n * #A
参数：hA : A.Nonempty；B : Finset G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Finset.pluennecke_ruzsa_inequality_pow_div_pow_mul`：pluennecke_ruzsa_ine
quality_pow_div_pow_mul (hA : A.Nonempty) (B : Finset G) (m n : Nat) : #(B ^ m /
 B ^ n) <= (#(A * B) / #A : Rat>=0) ^ (m…

--- 原说明 ---
Special case of the **Plünnecke-Ruzsa inequality**. Multiplication version.
-/
theorem pluennecke_ruzsa_inequality_pow_mul (hA : A.Nonempty) (B : Finset G) (n : ℕ) :
    #(B ^ n) ≤ (#(A * B) / #A : ℚ≥0) ^ n * #A := by
  simpa only [_root_.pow_zero, div_one] using! pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ 0

/-- Special case of the **Plünnecke-Ruzsa inequality**. Division version. -/
@[to_additive /-- Special case of the **Plünnecke-Ruzsa inequality**. Subtraction version. -/]
/-
**Finset.pluennecke_ruzsa_inequality_pow_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pluennecke_ruzsa_inequality_pow_div (hA : A.Nonempty) (B : Finset G) (n : 
Nat) : #(B ^ n) <= (#(A / B) / #A : Rat>=0) ^ n * #A
参数：hA : A.Nonempty；B : Finset G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Finset.pluennecke_ruzsa_inequality_pow_div_pow_div`：pluennecke_ruzsa_ine
quality_pow_div_pow_div (hA : A.Nonempty) (B : Finset G) (m n : Nat) : #(B ^ m /
 B ^ n) <= (#(A / B) / #A : Rat>=0) ^ (m…

--- 原说明 ---
Special case of the **Plünnecke-Ruzsa inequality**. Division version.
-/
theorem pluennecke_ruzsa_inequality_pow_div (hA : A.Nonempty) (B : Finset G) (n : ℕ) :
    #(B ^ n) ≤ (#(A / B) / #A : ℚ≥0) ^ n * #A := by
  simpa only [_root_.pow_zero, div_one] using! pluennecke_ruzsa_inequality_pow_div_pow_div hA _ _ 0

end CommGroup
end Finset

