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
/--
theorem `ruzsa_triangle_inequality_div_div_div` / 定理 `ruzsa_triangle_inequality_div_div_div`

English:
theorem ruzsa_triangle_inequality_div_div_div
  given: (A B C : Finset G)
  proof: by
  rw [← card_product (A / B)]; rw [← mul_one #((A / B) ×ˢ (C / B))]
  refine card_mul_le_card_mul (fun b (a, c) => a / c = b) (fun x hx => ?_)
    fun x _ => card_le_one_iff.2 fun hu hv =>
      ((mem_bipartiteBelow _).1 hu).2.symm.trans ?_
  · obtain ⟨a, ha, c, hc, rfl⟩ := mem_div.1 hx
    refin

中文:
定理 ruzsa_triangle_inequality_div_div_div
  条件: (A B C : Finset G)
  证明: by
  rw [← card_product (A / B)]; rw [← mul_one #((A / B) ×ˢ (C / B))]
  refine card_mul_le_card_mul (fun b (a, c) => a / c = b) (fun x hx => ?_)
    fun x _ => card_le_one_iff.2 fun hu hv =>
      ((mem_bipartiteBelow _).1 hu).2.symm.trans ?_
  · obtain ⟨a, ha, c, hc, rfl⟩ := mem_div.1 hx
    refin

Depends on / 依赖: card_le_card_of_injOn, card_le_one_iff, card_mul_le_card_mul, card_product, div_div_div_cancel_right, div_mem_div, mem_bipartiteAbove, mem_bipartiteBelow, mem_coe, mem_div, mk_mem_product, mul_one, symm.trans
-/
theorem ruzsa_triangle_inequality_div_div_div (A B C : Finset G) :
    #(A / C) * #B <= #(A / B) * #(C / B) := by
  rw [← card_product (A / B)]; rw [← mul_one #((A / B) ×ˢ (C / B))]
  refine card_mul_le_card_mul (fun b (a, c) => a / c = b) (fun x hx => ?_)
    fun x _ => card_le_one_iff.2 fun hu hv =>
      ((mem_bipartiteBelow _).1 hu).2.symm.trans ?_
  · obtain ⟨a, ha, c, hc, rfl⟩ := mem_div.1 hx
    refine card_le_card_of_injOn (fun b => (a / b, c / b)) (fun b hb => ?_) fun b₁ _ b₂ _ h => ?_
    · rw [mem_coe, mem_bipartiteAbove]
      exact ⟨mk_mem_product (div_mem_div ha hb) (div_mem_div hc hb), div_div_div_cancel_right ..⟩
    · exact div_right_injective (Prod.ext_iff.1 h).1
  · exact ((mem_bipartiteBelow _).1 hv).2

/-- **Ruzsa's triangle inequality**. Mulinv-mulinv-mulinv version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Addneg-addneg-addneg version. -/]
/--
theorem `ruzsa_triangle_inequality_mulInv_mulInv_mulInv` / 定理 `ruzsa_triangle_inequality_mulInv_mulInv_mulInv`

English:
theorem ruzsa_triangle_inequality_mulInv_mulInv_mulInv
  given: (A B C : Finset G)
  proof: by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_div_div_div A B C

中文:
定理 ruzsa_triangle_inequality_mulInv_mulInv_mulInv
  条件: (A B C : Finset G)
  证明: by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_div_div_div A B C

Depends on / 依赖: div_eq_mul_inv, ruzsa_triangle_inequality_div_div_div
-/
theorem ruzsa_triangle_inequality_mulInv_mulInv_mulInv (A B C : Finset G) :
    #(A * C⁻¹) * #B <= #(A * B⁻¹) * #(C * B⁻¹) := by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_div_div_div A B C

/-- **Ruzsa's triangle inequality**. Invmul-invmul-invmul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Negadd-negadd-negadd version. -/]
/--
theorem `ruzsa_triangle_inequality_invMul_invMul_invMul` / 定理 `ruzsa_triangle_inequality_invMul_invMul_invMul`

English:
theorem ruzsa_triangle_inequality_invMul_invMul_invMul
  given: (A B C : Finset G)
  proof: by
  simpa [mul_comm, div_eq_mul_inv, ← map_op_mul, ← map_op_inv] using
    ruzsa_triangle_inequality_div_div_div (G := Gᵐᵒᵖ) (C.map opEquiv.toEmbedding)
      (B.map opEquiv.toEmbedding) (A.map opEquiv.toEmbedding)

中文:
定理 ruzsa_triangle_inequality_invMul_invMul_invMul
  条件: (A B C : Finset G)
  证明: by
  simpa [mul_comm, div_eq_mul_inv, ← map_op_mul, ← map_op_inv] using
    ruzsa_triangle_inequality_div_div_div (G := Gᵐᵒᵖ) (C.map opEquiv.toEmbedding)
      (B.map opEquiv.toEmbedding) (A.map opEquiv.toEmbedding)

Depends on / 依赖: A.map, B.map, C.map, div_eq_mul_inv, map_op_inv, map_op_mul, mul_comm, opEquiv, opEquiv.toEmbedding, ruzsa_triangle_inequality_div_div_div, toEmbedding
-/
theorem ruzsa_triangle_inequality_invMul_invMul_invMul (A B C : Finset G) :
    #B * #(A⁻¹ * C) <= #(B⁻¹ * A) * #(B⁻¹ * C) := by
  simpa [mul_comm, div_eq_mul_inv, ← map_op_mul, ← map_op_inv] using
    ruzsa_triangle_inequality_div_div_div (G := Gᵐᵒᵖ) (C.map opEquiv.toEmbedding)
      (B.map opEquiv.toEmbedding) (A.map opEquiv.toEmbedding)


/-- **Ruzsa's triangle inequality**. Div-mul-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Sub-add-add version. -/]
/--
theorem `ruzsa_triangle_inequality_div_mul_mul` / 定理 `ruzsa_triangle_inequality_div_mul_mul`

English:
theorem ruzsa_triangle_inequality_div_mul_mul
  given: (A B C : Finset G)
  proof: by
  simpa using ruzsa_triangle_inequality_div_div_div A B⁻¹ C

中文:
定理 ruzsa_triangle_inequality_div_mul_mul
  条件: (A B C : Finset G)
  证明: by
  simpa using ruzsa_triangle_inequality_div_div_div A B⁻¹ C

Depends on / 依赖: ruzsa_triangle_inequality_div_div_div
-/
theorem ruzsa_triangle_inequality_div_mul_mul (A B C : Finset G) :
    #(A / C) * #B <= #(A * B) * #(C * B) := by
  simpa using ruzsa_triangle_inequality_div_div_div A B⁻¹ C

/-- **Ruzsa's triangle inequality**. Mulinv-mul-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Addneg-add-add version. -/]
/--
theorem `ruzsa_triangle_inequality_mulInv_mul_mul` / 定理 `ruzsa_triangle_inequality_mulInv_mul_mul`

English:
theorem ruzsa_triangle_inequality_mulInv_mul_mul
  given: (A B C : Finset G)
  proof: by
  simpa using ruzsa_triangle_inequality_mulInv_mulInv_mulInv A B⁻¹ C

中文:
定理 ruzsa_triangle_inequality_mulInv_mul_mul
  条件: (A B C : Finset G)
  证明: by
  simpa using ruzsa_triangle_inequality_mulInv_mulInv_mulInv A B⁻¹ C

Depends on / 依赖: ruzsa_triangle_inequality_mulInv_mulInv_mulInv
-/
theorem ruzsa_triangle_inequality_mulInv_mul_mul (A B C : Finset G) :
    #(A * C⁻¹) * #B <= #(A * B) * #(C * B) := by
  simpa using ruzsa_triangle_inequality_mulInv_mulInv_mulInv A B⁻¹ C

/-- **Ruzsa's triangle inequality**. Invmul-mul-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Negadd-add-add version. -/]
/--
theorem `ruzsa_triangle_inequality_invMul_mul_mul` / 定理 `ruzsa_triangle_inequality_invMul_mul_mul`

English:
theorem ruzsa_triangle_inequality_invMul_mul_mul
  given: (A B C : Finset G)
  proof: by
  simpa using ruzsa_triangle_inequality_invMul_invMul_invMul A B⁻¹ C

中文:
定理 ruzsa_triangle_inequality_invMul_mul_mul
  条件: (A B C : Finset G)
  证明: by
  simpa using ruzsa_triangle_inequality_invMul_invMul_invMul A B⁻¹ C

Depends on / 依赖: ruzsa_triangle_inequality_invMul_invMul_invMul
-/
theorem ruzsa_triangle_inequality_invMul_mul_mul (A B C : Finset G) :
    #B * #(A⁻¹ * C) <= #(B * A) * #(B * C) := by
  simpa using ruzsa_triangle_inequality_invMul_invMul_invMul A B⁻¹ C


/-- **Ruzsa's triangle inequality**. Mul-div-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-sub-add version. -/]
/--
theorem `ruzsa_triangle_inequality_mul_div_mul` / 定理 `ruzsa_triangle_inequality_mul_div_mul`

English:
theorem ruzsa_triangle_inequality_mul_div_mul
  given: (A B C : Finset G)
  proof: by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_invMul_mul_mul A⁻¹ B C

中文:
定理 ruzsa_triangle_inequality_mul_div_mul
  条件: (A B C : Finset G)
  证明: by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_invMul_mul_mul A⁻¹ B C

Depends on / 依赖: div_eq_mul_inv, ruzsa_triangle_inequality_invMul_mul_mul
-/
theorem ruzsa_triangle_inequality_mul_div_mul (A B C : Finset G) :
    #B * #(A * C) <= #(B / A) * #(B * C) := by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_invMul_mul_mul A⁻¹ B C

/-- **Ruzsa's triangle inequality**. Mul-mulinv-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-addneg-add version. -/]
/--
theorem `ruzsa_triangle_inequality_mul_mulInv_mul` / 定理 `ruzsa_triangle_inequality_mul_mulInv_mul`

English:
theorem ruzsa_triangle_inequality_mul_mulInv_mul
  given: (A B C : Finset G)
  proof: by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_mul_div_mul A B C

中文:
定理 ruzsa_triangle_inequality_mul_mulInv_mul
  条件: (A B C : Finset G)
  证明: by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_mul_div_mul A B C

Depends on / 依赖: div_eq_mul_inv, ruzsa_triangle_inequality_mul_div_mul
-/
theorem ruzsa_triangle_inequality_mul_mulInv_mul (A B C : Finset G) :
    #B * #(A * C) <= #(B * A⁻¹) * #(B * C) := by
  simpa [div_eq_mul_inv] using ruzsa_triangle_inequality_mul_div_mul A B C

/-- **Ruzsa's triangle inequality**. Mul-mul-invmul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-add-negadd version. -/]
/--
theorem `ruzsa_triangle_inequality_mul_mul_invMul` / 定理 `ruzsa_triangle_inequality_mul_mul_invMul`

English:
theorem ruzsa_triangle_inequality_mul_mul_invMul
  given: (A B C : Finset G)
  proof: by
  simpa using ruzsa_triangle_inequality_mulInv_mul_mul A B C⁻¹

中文:
定理 ruzsa_triangle_inequality_mul_mul_invMul
  条件: (A B C : Finset G)
  证明: by
  simpa using ruzsa_triangle_inequality_mulInv_mul_mul A B C⁻¹

Depends on / 依赖: ruzsa_triangle_inequality_mulInv_mul_mul
-/
theorem ruzsa_triangle_inequality_mul_mul_invMul (A B C : Finset G) :
    #(A * C) * #B <= #(A * B) * #(C⁻¹ * B) := by
  simpa using ruzsa_triangle_inequality_mulInv_mul_mul A B C⁻¹

/-! ### Plünnecke-Petridis inequality -/

@[to_additive]
/--
theorem `pluennecke_petridis_inequality_mul` / 定理 `pluennecke_petridis_inequality_mul`

English:
theorem pluennecke_petridis_inequality_mul
  statement: (C : Finset G)
  proof: by
  induction C using Finset.induction_on with
  | empty => simp
  | insert x C _ ih =>
    set A' := A inter ({x}⁻¹ * C * A) with hA'
    set C' := insert x C with hC'
    have h₀ : {x} * A' = {x} * A inter (C * A) := by
      rw [hA']; rw [mul_assoc]; rw [singleton_mul_inter]; rw [(isUnit_singlet

中文:
定理 pluennecke_petridis_inequality_mul
  结论: (C : Finset G)
  证明: by
  induction C using Finset.induction_on with
  | empty => simp
  | insert x C _ ih =>
    set A' := A inter ({x}⁻¹ * C * A) with hA'
    set C' := insert x C with hC'
    have h₀ : {x} * A' = {x} * A inter (C * A) := by
      rw [hA']; rw [mul_assoc]; rw [singleton_mul_inter]; rw [(isUnit_singlet

Depends on / 依赖: Finset, Finset.induction_on, induction_on, insert, insert_eq, isUnit_singleton, mul_assoc, mul_inv_cancel_left, singleton_mul_inter, sup_sdiff_eq_sup, union_comm, union_mul
-/
theorem pluennecke_petridis_inequality_mul (C : Finset G)
    (hA : forall A' subseteq A, #(A * B) * #A' <= #(A' * B) * #A) :
    #(C * A * B) * #A <= #(A * B) * #(C * A) := by
  induction C using Finset.induction_on with
  | empty => simp
  | insert x C _ ih =>
    set A' := A inter ({x}⁻¹ * C * A) with hA'
    set C' := insert x C with hC'
    have h₀ : {x} * A' = {x} * A inter (C * A) := by
      rw [hA']; rw [mul_assoc]; rw [singleton_mul_inter]; rw [(isUnit_singleton x).mul_inv_cancel_left]
    have h₁ : C' * A * B = C * A * B union ({x} * A * B) \ ({x} * A' * B) := by
      rw [hC']; rw [insert_eq]; rw [union_comm]; rw [union_mul]; rw [union_mul]
      refine (sup_sdiff_eq_sup ?_).symm
      rw [h₀]
      gcongr
      exact inter_subset_right
    have h₂ : {x} * A' * B subseteq {x} * A * B := by gcongr; exact inter_subset_left
    calc
      #(C' * A * B) * #A
      _ <= (#(C * A * B) + #(A * B) - #(A' * B)) * #A := by
        gcongr
        rw [h₁]
        refine (card_union_le _ _).trans_eq ?_
        rw [card_sdiff_of_subset h₂]; rw [← add_tsub_assoc_of_le (card_le_card h₂)]; rw [mul_assoc {_}]; rw [mul_assoc {_}]; rw [card_singleton_mul]; rw [card_singleton_mul]
      _ = #(C * A * B) * #A + #(A * B) * #A - #(A' * B) * #A := by rw [tsub_mul, add_mul]
      _ <= #(A * B) * #(C * A) + #(A * B) * #A - #(A * B) * #(A inter ({x}⁻¹ * C * A)) := by
        gcongr ?_ + _ - ?_; exact hA _ inter_subset_left
      _ = #(A * B) * #(C' * A) := by
        rw [← mul_add]; rw [← mul_tsub]; rw [← hA']; rw [hC']; rw [insert_eq]; rw [union_mul]; rw [← card_singleton_mul x A]; rw [← card_singleton_mul x A']; rw [add_comm #_]; rw [h₀]; rw [eq_tsub_of_add_eq (card_union_add_card_inter _ _)]

end Group

section CommGroup
variable [CommGroup G] {A B C : Finset G}

/-! ### Commutative Ruzsa triangle inequality -/

-- Auxiliary lemma for Ruzsa's triangle sum inequality, and the Plünnecke-Ruzsa inequality.
@[to_additive]
/--
theorem `mul_aux` / 定理 `mul_aux`

English:
theorem mul_aux
  statement: (hA : A.Nonempty) (hAB : A subseteq B)
  proof: by
  rintro A' hAA'
  obtain rfl | hA' := A'.eq_empty_or_nonempty
  · simp
  have hA₀ : (0 : Rat>=0) < #A := cast_pos.2 hA.card_pos
  have hA₀' : (0 : Rat>=0) < #A' := cast_pos.2 hA'.card_pos
  exact mod_cast
    (div_le_div_iff₀ hA₀ hA₀').1
      (h _ <| mem_erase_of_ne_of_mem hA'.ne_empty <| mem_p

中文:
定理 mul_aux
  结论: (hA : A.Nonempty) (hAB : A subseteq B)
  证明: by
  rintro A' hAA'
  obtain rfl | hA' := A'.eq_empty_or_nonempty
  · simp
  have hA₀ : (0 : Rat>=0) < #A := cast_pos.2 hA.card_pos
  have hA₀' : (0 : Rat>=0) < #A' := cast_pos.2 hA'.card_pos
  exact mod_cast
    (div_le_div_iff₀ hA₀ hA₀').1
      (h _ <| mem_erase_of_ne_of_mem hA'.ne_empty <| mem_p
-/
private theorem mul_aux (hA : A.Nonempty) (hAB : A subseteq B)
    (h : forall A' in B.powerset.erase ∅, (#(A * C) : Rat>=0) / #A <= #(A' * C) / #A') :
    forall A' subseteq A, #(A * C) * #A' <= #(A' * C) * #A := by
  rintro A' hAA'
  obtain rfl | hA' := A'.eq_empty_or_nonempty
  · simp
  have hA₀ : (0 : Rat>=0) < #A := cast_pos.2 hA.card_pos
  have hA₀' : (0 : Rat>=0) < #A' := cast_pos.2 hA'.card_pos
  exact mod_cast
    (div_le_div_iff₀ hA₀ hA₀').1
      (h _ <| mem_erase_of_ne_of_mem hA'.ne_empty <| mem_powerset.2 <| hAA'.trans hAB)

/-- **Ruzsa's triangle inequality**. Multiplication version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Addition version. -/]
/--
theorem `ruzsa_triangle_inequality_mul_mul_mul` / 定理 `ruzsa_triangle_inequality_mul_mul_mul`

English:
theorem ruzsa_triangle_inequality_mul_mul_mul
  given: (A B C : Finset G)
  proof: by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  have hB' : B in B.powerset.erase ∅ := mem_erase_of_ne_of_mem hB.ne_empty (mem_powerset_self _)
  obtain ⟨U, hU, hUA⟩ :=
    exists_min_image (B.powerset.erase ∅) (fun U => #(U * A) / #U : _ -> Rat>=0) ⟨B, hB'⟩
  rw [mem_erase]; rw [mem_powers

中文:
定理 ruzsa_triangle_inequality_mul_mul_mul
  条件: (A B C : Finset G)
  证明: by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  have hB' : B in B.powerset.erase ∅ := mem_erase_of_ne_of_mem hB.ne_empty (mem_powerset_self _)
  obtain ⟨U, hU, hUA⟩ :=
    exists_min_image (B.powerset.erase ∅) (fun U => #(U * A) / #U : _ -> Rat>=0) ⟨B, hB'⟩
  rw [mem_erase]; rw [mem_powers

Depends on / 依赖: B.eq_empty_or_nonempty, B.powerset.erase, card_le_card_mul_left, card_pos, cast_le, cast_pos, eq_empty_or_nonempty, exists_min_image, hB.card_pos, hB.ne_empty, mem_erase, mem_erase_of_ne_of_mem, mem_powerset, mem_powerset_self, mul_comm, mul_div_right_comm, ne_empty, nonempty_iff_ne_empty, powerset
-/
theorem ruzsa_triangle_inequality_mul_mul_mul (A B C : Finset G) :
    #(A * C) * #B <= #(A * B) * #(B * C) := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  have hB' : B in B.powerset.erase ∅ := mem_erase_of_ne_of_mem hB.ne_empty (mem_powerset_self _)
  obtain ⟨U, hU, hUA⟩ :=
    exists_min_image (B.powerset.erase ∅) (fun U => #(U * A) / #U : _ -> Rat>=0) ⟨B, hB'⟩
  rw [mem_erase]; rw [mem_powerset]; rw [← nonempty_iff_ne_empty] at hU
  refine cast_le.1 (?_ : (_ : Rat>=0) <= _)
  push_cast
  rw [← le_div_iff₀ (cast_pos.2 hB.card_pos)]; rw [mul_div_right_comm]; rw [mul_comm _ B]
  grw [card_le_card_mul_left hU.1, ← hUA _ hB', ← mul_subset_mul_right hU.2]
  rw [← mul_div_right_comm]; rw [← mul_assoc]; rw [le_div_iff₀ (cast_pos.2 hU.1.card_pos)]; rw [mul_comm _ C]; rw [← mul_assoc]; rw [mul_comm _ C]
  exact mod_cast pluennecke_petridis_inequality_mul C (mul_aux hU.1 hU.2 hUA)

/-- **Ruzsa's triangle inequality**. Mul-div-div version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Add-sub-sub version. -/]
/--
theorem `ruzsa_triangle_inequality_mul_div_div` / 定理 `ruzsa_triangle_inequality_mul_div_div`

English:
theorem ruzsa_triangle_inequality_mul_div_div
  given: (A B C : Finset G)
  proof: by
  rw [div_eq_mul_inv]; rw [← card_inv B]; rw [← card_inv (B / C)]; rw [inv_div']; rw [div_inv_eq_mul]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

中文:
定理 ruzsa_triangle_inequality_mul_div_div
  条件: (A B C : Finset G)
  证明: by
  rw [div_eq_mul_inv]; rw [← card_inv B]; rw [← card_inv (B / C)]; rw [inv_div']; rw [div_inv_eq_mul]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

Depends on / 依赖: card_inv, div_eq_mul_inv, div_inv_eq_mul, inv_div, ruzsa_triangle_inequality_mul_mul_mul
-/
theorem ruzsa_triangle_inequality_mul_div_div (A B C : Finset G) :
    #(A * C) * #B <= #(A / B) * #(B / C) := by
  rw [div_eq_mul_inv]; rw [← card_inv B]; rw [← card_inv (B / C)]; rw [inv_div']; rw [div_inv_eq_mul]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

/-- **Ruzsa's triangle inequality**. Div-mul-div version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Sub-add-sub version. -/]
/--
theorem `ruzsa_triangle_inequality_div_mul_div` / 定理 `ruzsa_triangle_inequality_div_mul_div`

English:
theorem ruzsa_triangle_inequality_div_mul_div
  given: (A B C : Finset G)
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

中文:
定理 ruzsa_triangle_inequality_div_mul_div
  条件: (A B C : Finset G)
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

Depends on / 依赖: div_eq_mul_inv, ruzsa_triangle_inequality_mul_mul_mul
-/
theorem ruzsa_triangle_inequality_div_mul_div (A B C : Finset G) :
    #(A / C) * #B <= #(A * B) * #(B / C) := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_mul_mul _ _ _

/-- **Ruzsa's triangle inequality**. Div-div-mul version. -/
@[to_additive /-- **Ruzsa's triangle inequality**. Sub-sub-add version. -/]
/--
theorem `card_div_mul_le_card_div_mul_card_mul` / 定理 `card_div_mul_le_card_div_mul_card_mul`

English:
theorem card_div_mul_le_card_div_mul_card_mul
  given: (A B C : Finset G)
  proof: by
  rw [← div_inv_eq_mul]; rw [div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_div_div _ _ _

中文:
定理 card_div_mul_le_card_div_mul_card_mul
  条件: (A B C : Finset G)
  证明: by
  rw [← div_inv_eq_mul]; rw [div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_div_div _ _ _

Depends on / 依赖: div_eq_mul_inv, div_inv_eq_mul, ruzsa_triangle_inequality_mul_div_div
-/
theorem card_div_mul_le_card_div_mul_card_mul (A B C : Finset G) :
    #(A / C) * #B <= #(A / B) * #(B * C) := by
  rw [← div_inv_eq_mul]; rw [div_eq_mul_inv]
  exact ruzsa_triangle_inequality_mul_div_div _ _ _

-- Auxiliary lemma towards the Plünnecke-Ruzsa inequality
@[to_additive]
/--
lemma `card_mul_pow_le` / 引理 `card_mul_pow_le`

English:
lemma card_mul_pow_le
  given: (hAB : forall A' subseteq A, #(A * B) * #A' <= #(A' * B) * #A) (n : Nat)
  proof: by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Rat>=0) < #A)
    calc
      ((#(A * B ^ (n + 1))) * #A : Rat>=0)
        = #(B ^ n * A * B) * #A := by rw [pow_succ, mul_left_comm,

中文:
引理 card_mul_pow_le
  条件: (hAB : 对任意 A' subseteq A, #(A * B) * #A' <= #(A' * B) * #A) (n : 自然数)
  证明: by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Rat>=0) < #A)
    calc
      ((#(A * B ^ (n + 1))) * #A : Rat>=0)
        = #(B ^ n * A * B) * #A := by rw [pow_succ, mul_left_comm,
-/
private lemma card_mul_pow_le (hAB : forall A' subseteq A, #(A * B) * #A' <= #(A' * B) * #A) (n : Nat) :
    #(A * B ^ n) <= (#(A * B) / #A : Rat>=0) ^ n * #A := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Rat>=0) < #A)
    calc
      ((#(A * B ^ (n + 1))) * #A : Rat>=0)
        = #(B ^ n * A * B) * #A := by rw [pow_succ, mul_left_comm, mul_assoc]
      _ <= #(A * B) * #(B ^ n * A) := mod_cast pluennecke_petridis_inequality_mul _ hAB
      _ <= #(A * B) * ((#(A * B) / #A) ^ n * #A) := by rw [mul_comm _ A]; gcongr
      _ = (#(A * B) / #A) ^ (n + 1) * #A * #A := by simp [field, pow_add]

/-- The **Plünnecke-Ruzsa inequality**. Multiplication version. Note that this is genuinely harder
than the division version because we cannot use a double counting argument. -/
@[to_additive /-- The **Plünnecke-Ruzsa inequality**. Addition version. Note that this is genuinely
harder than the subtraction version because we cannot use a double counting argument. -/]
/--
theorem `pluennecke_ruzsa_inequality_pow_div_pow_mul` / 定理 `pluennecke_ruzsa_inequality_pow_div_pow_mul`

English:
theorem pluennecke_ruzsa_inequality_pow_div_pow_mul
  given: (hA : A.Nonempty) (B : Finset G) (m n : Nat)
  proof: by
  have hA' : A in A.powerset.erase ∅ := mem_erase_of_ne_of_mem hA.ne_empty (mem_powerset_self _)
  obtain ⟨C, hC, hCmin⟩ :=
    exists_min_image (A.powerset.erase ∅) (fun C => #(C * B) / #C : _ -> Rat>=0) ⟨A, hA'⟩
  rw [mem_erase]; rw [mem_powerset]; rw [← nonempty_iff_ne_empty] at hC
  obtain ⟨h

中文:
定理 pluennecke_ruzsa_inequality_pow_div_pow_mul
  条件: (hA : A.Nonempty) (B : Finset G) (m n : 自然数)
  证明: by
  have hA' : A in A.powerset.erase ∅ := mem_erase_of_ne_of_mem hA.ne_empty (mem_powerset_self _)
  obtain ⟨C, hC, hCmin⟩ :=
    exists_min_image (A.powerset.erase ∅) (fun C => #(C * B) / #C : _ -> Rat>=0) ⟨A, hA'⟩
  rw [mem_erase]; rw [mem_powerset]; rw [← nonempty_iff_ne_empty] at hC
  obtain ⟨h

Depends on / 依赖: A.powerset.erase, exists_min_image, hA.ne_empty, le_of_mul_le_mul_right, mem_erase, mem_erase_of_ne_of_mem, mem_powerset, mem_powerset_self, mod_cast, ne_empty, nonempty_iff_ne_empty, powerset, ruzsa_triangle_inequality_div_mul_mul
-/
theorem pluennecke_ruzsa_inequality_pow_div_pow_mul (hA : A.Nonempty) (B : Finset G) (m n : Nat) :
    #(B ^ m / B ^ n) <= (#(A * B) / #A : Rat>=0) ^ (m + n) * #A := by
  have hA' : A in A.powerset.erase ∅ := mem_erase_of_ne_of_mem hA.ne_empty (mem_powerset_self _)
  obtain ⟨C, hC, hCmin⟩ :=
    exists_min_image (A.powerset.erase ∅) (fun C => #(C * B) / #C : _ -> Rat>=0) ⟨A, hA'⟩
  rw [mem_erase]; rw [mem_powerset]; rw [← nonempty_iff_ne_empty] at hC
  obtain ⟨hC, hCA⟩ := hC
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Rat>=0) < #C)
  calc
    (#(B ^ m / B ^ n) * #C : Rat>=0)
      <= #(B ^ m * C) * #(B ^ n * C) := mod_cast ruzsa_triangle_inequality_div_mul_mul ..
    _ = #(C * B ^ m) * #(C * B ^ n) := by simp_rw [mul_comm]
    _ <= ((#(C * B) / #C) ^ m * #C) * ((#(C * B) / #C : Rat>=0) ^ n * #C) := by
      gcongr <;> exact card_mul_pow_le (mul_aux hC hCA hCmin) _
    _ = (#(C * B) / #C) ^ (m + n) * #C * #C := by ring
    _ <= (#(A * B) / #A) ^ (m + n) * #A * #C := by gcongr (?_ ^ _) * #?_ * _; exact hCmin _ hA'

/-- The **Plünnecke-Ruzsa inequality**. Division version. -/
@[to_additive /-- The **Plünnecke-Ruzsa inequality**. Subtraction version. -/]
/--
theorem `pluennecke_ruzsa_inequality_pow_div_pow_div` / 定理 `pluennecke_ruzsa_inequality_pow_div_pow_div`

English:
theorem pluennecke_ruzsa_inequality_pow_div_pow_div
  given: (hA : A.Nonempty) (B : Finset G) (m n : Nat)
  proof: by
  rw [← card_inv]; rw [inv_div']; rw [← inv_pow]; rw [← inv_pow]; rw [div_eq_mul_inv A]
  exact pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ _

中文:
定理 pluennecke_ruzsa_inequality_pow_div_pow_div
  条件: (hA : A.Nonempty) (B : Finset G) (m n : 自然数)
  证明: by
  rw [← card_inv]; rw [inv_div']; rw [← inv_pow]; rw [← inv_pow]; rw [div_eq_mul_inv A]
  exact pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ _

Depends on / 依赖: card_inv, div_eq_mul_inv, inv_div, inv_pow, pluennecke_ruzsa_inequality_pow_div_pow_mul
-/
theorem pluennecke_ruzsa_inequality_pow_div_pow_div (hA : A.Nonempty) (B : Finset G) (m n : Nat) :
    #(B ^ m / B ^ n) <= (#(A / B) / #A : Rat>=0) ^ (m + n) * #A := by
  rw [← card_inv]; rw [inv_div']; rw [← inv_pow]; rw [← inv_pow]; rw [div_eq_mul_inv A]
  exact pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ _

/-- Special case of the **Plünnecke-Ruzsa inequality**. Multiplication version. -/
@[to_additive /-- Special case of the **Plünnecke-Ruzsa inequality**. Addition version. -/]
/--
theorem `pluennecke_ruzsa_inequality_pow_mul` / 定理 `pluennecke_ruzsa_inequality_pow_mul`

English:
theorem pluennecke_ruzsa_inequality_pow_mul
  given: (hA : A.Nonempty) (B : Finset G) (n : Nat)
  proof: by
  simpa only [_root_.pow_zero, div_one] using! pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ 0

中文:
定理 pluennecke_ruzsa_inequality_pow_mul
  条件: (hA : A.Nonempty) (B : Finset G) (n : 自然数)
  证明: by
  simpa only [_root_.pow_zero, div_one] using! pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ 0

Depends on / 依赖: _root_, _root_.pow_zero, div_one, pluennecke_ruzsa_inequality_pow_div_pow_mul, pow_zero
-/
theorem pluennecke_ruzsa_inequality_pow_mul (hA : A.Nonempty) (B : Finset G) (n : Nat) :
    #(B ^ n) <= (#(A * B) / #A : Rat>=0) ^ n * #A := by
  simpa only [_root_.pow_zero, div_one] using! pluennecke_ruzsa_inequality_pow_div_pow_mul hA _ _ 0

/-- Special case of the **Plünnecke-Ruzsa inequality**. Division version. -/
@[to_additive /-- Special case of the **Plünnecke-Ruzsa inequality**. Subtraction version. -/]
/--
theorem `pluennecke_ruzsa_inequality_pow_div` / 定理 `pluennecke_ruzsa_inequality_pow_div`

English:
theorem pluennecke_ruzsa_inequality_pow_div
  given: (hA : A.Nonempty) (B : Finset G) (n : Nat)
  proof: by
  simpa only [_root_.pow_zero, div_one] using! pluennecke_ruzsa_inequality_pow_div_pow_div hA _ _ 0

中文:
定理 pluennecke_ruzsa_inequality_pow_div
  条件: (hA : A.Nonempty) (B : Finset G) (n : 自然数)
  证明: by
  simpa only [_root_.pow_zero, div_one] using! pluennecke_ruzsa_inequality_pow_div_pow_div hA _ _ 0

Depends on / 依赖: _root_, _root_.pow_zero, div_one, pluennecke_ruzsa_inequality_pow_div_pow_div, pow_zero
-/
theorem pluennecke_ruzsa_inequality_pow_div (hA : A.Nonempty) (B : Finset G) (n : Nat) :
    #(B ^ n) <= (#(A / B) / #A : Rat>=0) ^ n * #A := by
  simpa only [_root_.pow_zero, div_one] using! pluennecke_ruzsa_inequality_pow_div_pow_div hA _ _ 0

end CommGroup
end Finset
