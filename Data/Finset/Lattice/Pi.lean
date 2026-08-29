/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Lattice.Prod
public import Mathlib.Data.Finset.Pi

/-!
# Lattice operations on finsets of functions

This file is concerned with folding binary lattice operations over finsets.
-/

public section

assert_not_exists IsOrderedMonoid MonoidWithZero

variable {α ι : Type*}

namespace Finset

variable [DistribLattice α] [BoundedOrder α] [DecidableEq ι]

--TODO: Extract out the obvious isomorphism `(insert i s).pi t ≃ t i ×ˢ s.pi t` from this proof
/--
theorem `inf_sup` / 定理 `inf_sup`

English:
theorem inf_sup
  given: {κ : ι -> Type*} (s : Finset ι) (t : forall i, Finset (κ i)) (f : forall i, κ i -> α)
  proof: by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => ?_
  rw [inf_insert]; rw [ih]; rw [attach_insert]; rw [sup_inf_sup]
  refine eq_of_forall_ge_iff fun c => ?_
  simp only [Finset.sup_le_iff, mem_product, mem_pi, and_imp, Prod.forall,
    inf_insert, inf_image]
  refine
    ⟨fun h g hg =>
      h (g i <| mem_insert_self _ _) (fun j hj => g j <| mem_insert_of_mem hj)
(hg _ <| mem_insert_self _ _) fun j hj => hg _ mem_insert_of_mem hj,
      fun h a g ha hg => ?_⟩
  -- TODO: This `have` must be named to prevent it being shadowed by the internal `this` in `simpa`
  have aux : forall j : { x // x in s }, ↑j != i := fun j : s => ne_of_mem_of_not_mem j.2 hi
  -- `simpa` doesn't support placeholders in proof terms
  have := h (fun j hj => if hji : j = i then cast (congr_arg κ hji.symm) a
else g _ mem_of_mem_insert_of_ne hj hji) (fun j hj => ?_)
  · simpa only [cast_eq, dif_pos, Function.comp_def, Subtype.coe_mk, dif_neg, aux] using! this
  rw [mem_insert] at hj
  obtain (rfl | hj) := hj
  · simpa
  · simpa [ne_of_mem_of_not_mem hj hi] using! hg _ _

中文:
定理 inf_sup
  条件: {κ : ι -> 类型} (s : 有限集 ι) (t : 对任意 i, 有限集 (κ i)) (f : 对任意 i, κ i -> α)
  证明: by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => ?_
  rw [inf_insert]; rw [ih]; rw [attach_insert]; rw [sup_inf_sup]
  refine eq_of_forall_ge_iff fun c => ?_
  simp only [Finset.sup_le_iff, mem_product, mem_pi, and_imp, Prod.forall,
    inf_insert, inf_image]
  refine
    ⟨fun h g hg =>
      h (g i <| mem_insert_self _ _) (fun j hj => g j <| mem_insert_of_mem hj)
(hg _ <| mem_insert_self _ _) fun j hj => hg _ mem_insert_of_mem hj,
      fun h a g ha hg => ?_⟩
  -- TODO: This `have` must be named to prevent it being shadowed by the internal `this` in `simpa`
  have aux : forall j : { x // x in s }, ↑j != i := fun j : s => ne_of_mem_of_not_mem j.2 hi
  -- `simpa` doesn't support placeholders in proof terms
  have := h (fun j hj => if hji : j = i then cast (congr_arg κ hji.symm) a
else g _ mem_of_mem_insert_of_ne hj hji) (fun j hj => ?_)
  · simpa only [cast_eq, dif_pos, Function.comp_def, Subtype.coe_mk, dif_neg, aux] using! this
  rw [mem_insert] at hj
  obtain (rfl | hj) := hj
  · simpa
  · simpa [ne_of_mem_of_not_mem hj hi] using! hg _ _

Depends on / 依赖: Finset, Finset.induction, Finset.sup_le_iff, Prod.forall, and_imp, attach_insert, eq_of_forall_ge_iff, inf_image, inf_insert, insert, mem_insert_of_mem, mem_insert_self, mem_pi, mem_product, sup_inf_sup, sup_le_iff
-/
theorem inf_sup {κ : ι -> Type*} (s : Finset ι) (t : forall i, Finset (κ i)) (f : forall i, κ i -> α) :
    (s.inf fun i => (t i).sup (f i)) =
(s.pi t).sup fun g => s.attach.inf fun i => f _ g _ i.2 := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => ?_
  rw [inf_insert]; rw [ih]; rw [attach_insert]; rw [sup_inf_sup]
  refine eq_of_forall_ge_iff fun c => ?_
  simp only [Finset.sup_le_iff, mem_product, mem_pi, and_imp, Prod.forall,
    inf_insert, inf_image]
  refine
    ⟨fun h g hg =>
      h (g i <| mem_insert_self _ _) (fun j hj => g j <| mem_insert_of_mem hj)
(hg _ <| mem_insert_self _ _) fun j hj => hg _ mem_insert_of_mem hj,
      fun h a g ha hg => ?_⟩
  -- TODO: This `have` must be named to prevent it being shadowed by the internal `this` in `simpa`
  have aux : forall j : { x // x in s }, ↑j != i := fun j : s => ne_of_mem_of_not_mem j.2 hi
  -- `simpa` doesn't support placeholders in proof terms
  have := h (fun j hj => if hji : j = i then cast (congr_arg κ hji.symm) a
else g _ mem_of_mem_insert_of_ne hj hji) (fun j hj => ?_)
  · simpa only [cast_eq, dif_pos, Function.comp_def, Subtype.coe_mk, dif_neg, aux] using! this
  rw [mem_insert] at hj
  obtain (rfl | hj) := hj
  · simpa
  · simpa [ne_of_mem_of_not_mem hj hi] using! hg _ _

/--
theorem `sup_inf` / 定理 `sup_inf`

English:
theorem sup_inf
  given: {κ : ι -> Type*} (s : Finset ι) (t : forall i, Finset (κ i)) (f : forall i, κ i -> α)
  proof: @inf_sup αᵒᵈ _ _ _ _ _ _ _ _

中文:
定理 sup_inf
  条件: {κ : ι -> 类型} (s : 有限集 ι) (t : 对任意 i, 有限集 (κ i)) (f : 对任意 i, κ i -> α)
  证明: @inf_sup αᵒᵈ _ _ _ _ _ _ _ _

Depends on / 依赖: inf_sup
-/
theorem sup_inf {κ : ι -> Type*} (s : Finset ι) (t : forall i, Finset (κ i)) (f : forall i, κ i -> α) :
(s.sup fun i => (t i).inf (f i)) = (s.pi t).inf fun g => s.attach.sup fun i => f _ g _ i.2 :=
  @inf_sup αᵒᵈ _ _ _ _ _ _ _ _

end Finset
