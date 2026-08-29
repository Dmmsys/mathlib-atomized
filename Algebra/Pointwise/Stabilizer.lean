/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Stabilizer of a set under a pointwise action

This file characterises the stabilizer of a set/finset under the pointwise action of a group.
-/

public section

open Function MulOpposite Set
open scoped Pointwise

namespace MulAction
variable {G H α : Type*}

/-! ### Stabilizer of a set -/

section Set
section Group
variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

@[to_additive (attr := simp)]
/--
lemma `stabilizer_empty` / 引理 `stabilizer_empty`

English:
lemma stabilizer_empty
  statement: stabilizer G (∅ : Set α) = ⊤
  proof: Subgroup.coe_eq_univ.1 eq_univ_of_forall fun _a => smul_set_empty

@[to_additive (attr := simp)]

中文:
引理 stabilizer_empty
  结论: stabilizer G (∅ : Set α) = ⊤
  证明: Subgroup.coe_eq_univ.1 eq_univ_of_forall fun _a => smul_set_empty

@[to_additive (attr := simp)]

Depends on / 依赖: Subgroup, Subgroup.coe_eq_univ, coe_eq_univ, eq_univ_of_forall, smul_set_empty
-/
lemma stabilizer_empty : stabilizer G (∅ : Set α) = ⊤ :=
Subgroup.coe_eq_univ.1 eq_univ_of_forall fun _a => smul_set_empty

@[to_additive (attr := simp)]
/--
lemma `stabilizer_univ` / 引理 `stabilizer_univ`

English:
lemma stabilizer_univ
  statement: stabilizer G (Set.univ : Set α) = ⊤
  proof: by
  ext
  simp

@[to_additive (attr := simp)]

中文:
引理 stabilizer_univ
  结论: stabilizer G (Set.univ : Set α) = ⊤
  证明: by
  ext
  simp

@[to_additive (attr := simp)]
-/
lemma stabilizer_univ : stabilizer G (Set.univ : Set α) = ⊤ := by
  ext
  simp

@[to_additive (attr := simp)]
/--
lemma `stabilizer_singleton` / 引理 `stabilizer_singleton`

English:
lemma stabilizer_singleton
  given: (b : α)
  statement: stabilizer G ({b} : Set α) = stabilizer G b
  proof: by ext; simp

@[to_additive]

中文:
引理 stabilizer_singleton
  条件: (b : α)
  结论: stabilizer G ({b} : Set α) = stabilizer G b
  证明: by ext; simp

@[to_additive]
-/
lemma stabilizer_singleton (b : α) : stabilizer G ({b} : Set α) = stabilizer G b := by ext; simp

@[to_additive]
/--
lemma `mem_stabilizer_set` / 引理 `mem_stabilizer_set`

English:
lemma mem_stabilizer_set
  given: {s : Set α}
  statement: a in stabilizer G s ↔ forall b, a • b in s ↔ b in s
  proof: by
  refine mem_stabilizer_iff.trans ⟨fun h b => ?_, fun h => ?_⟩
  · rw [← (smul_mem_smul_set_iff : a • b in _ ↔ _), h]
  simp_rw [Set.ext_iff, mem_smul_set_iff_inv_smul_mem]
  exact ((MulAction.toPerm a).forall_congr' <| by simp [Iff.comm]).1 h

@[to_additive]

中文:
引理 mem_stabilizer_set
  条件: {s : Set α}
  结论: a in stabilizer G s ↔ 对任意 b, a • b in s ↔ b in s
  证明: by
  refine mem_stabilizer_iff.trans ⟨fun h b => ?_, fun h => ?_⟩
  · rw [← (smul_mem_smul_set_iff : a • b in _ ↔ _), h]
  simp_rw [Set.ext_iff, mem_smul_set_iff_inv_smul_mem]
  exact ((MulAction.toPerm a).forall_congr' <| by simp [Iff.comm]).1 h

@[to_additive]

Depends on / 依赖: Iff.comm, MulAction, MulAction.toPerm, Set.ext_iff, ext_iff, forall_congr, mem_smul_set_iff_inv_smul_mem, mem_stabilizer_iff, mem_stabilizer_iff.trans, simp_rw, smul_mem_smul_set_iff, toPerm
-/
lemma mem_stabilizer_set {s : Set α} : a in stabilizer G s ↔ forall b, a • b in s ↔ b in s := by
  refine mem_stabilizer_iff.trans ⟨fun h b => ?_, fun h => ?_⟩
  · rw [← (smul_mem_smul_set_iff : a • b in _ ↔ _), h]
  simp_rw [Set.ext_iff, mem_smul_set_iff_inv_smul_mem]
  exact ((MulAction.toPerm a).forall_congr' <| by simp [Iff.comm]).1 h

@[to_additive]
/--
lemma `map_stabilizer_le` / 引理 `map_stabilizer_le`

English:
lemma map_stabilizer_le
  given: (f : G ->* H) (s : Set G)
  proof: by
  rintro a
  simp only [Subgroup.mem_map, mem_stabilizer_iff, forall_exists_index, and_imp]
  rintro a ha rfl
  rw [← image_smul_distrib]; rw [ha]

@[to_additive (attr := simp)]

中文:
引理 map_stabilizer_le
  条件: (f : G ->* H) (s : Set G)
  证明: by
  rintro a
  simp only [Subgroup.mem_map, mem_stabilizer_iff, forall_exists_index, and_imp]
  rintro a ha rfl
  rw [← image_smul_distrib]; rw [ha]

@[to_additive (attr := simp)]

Depends on / 依赖: Subgroup, Subgroup.mem_map, and_imp, forall_exists_index, image_smul_distrib, mem_map, mem_stabilizer_iff
-/
lemma map_stabilizer_le (f : G ->* H) (s : Set G) :
    (stabilizer G s).map f <= stabilizer H (f '' s) := by
  rintro a
  simp only [Subgroup.mem_map, mem_stabilizer_iff, forall_exists_index, and_imp]
  rintro a ha rfl
  rw [← image_smul_distrib]; rw [ha]

@[to_additive (attr := simp)]
/--
lemma `stabilizer_mul_self` / 引理 `stabilizer_mul_self`

English:
lemma stabilizer_mul_self
  given: (s : Set G)
  statement: (stabilizer G s : Set G) * s = s
  proof: by
  ext
  refine ⟨?_, fun h => ⟨_, (stabilizer G s).one_mem, _, h, one_mul _⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [← mem_stabilizer_iff.1 ha]
  exact smul_mem_smul_set hb

@[to_additive]

中文:
引理 stabilizer_mul_self
  条件: (s : Set G)
  结论: (stabilizer G s : Set G) * s = s
  证明: by
  ext
  refine ⟨?_, fun h => ⟨_, (stabilizer G s).one_mem, _, h, one_mul _⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [← mem_stabilizer_iff.1 ha]
  exact smul_mem_smul_set hb

@[to_additive]

Depends on / 依赖: mem_stabilizer_iff, one_mem, one_mul, smul_mem_smul_set, stabilizer
-/
lemma stabilizer_mul_self (s : Set G) : (stabilizer G s : Set G) * s = s := by
  ext
  refine ⟨?_, fun h => ⟨_, (stabilizer G s).one_mem, _, h, one_mul _⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [← mem_stabilizer_iff.1 ha]
  exact smul_mem_smul_set hb

@[to_additive]
/--
lemma `stabilizer_inf_stabilizer_le_stabilizer_apply₂` / 引理 `stabilizer_inf_stabilizer_le_stabilizer_apply₂`

English:
lemma stabilizer_inf_stabilizer_le_stabilizer_apply₂
  statement: {f : Set α -> Set α -> Set α}
  proof: by aesop (add simp [SetLike.le_def])

@[to_additive]

中文:
引理 stabilizer_inf_stabilizer_le_stabilizer_apply₂
  结论: {f : Set α -> Set α -> Set α}
  证明: by aesop (add simp [SetLike.le_def])

@[to_additive]

Depends on / 依赖: SetLike, SetLike.le_def, le_def
-/
lemma stabilizer_inf_stabilizer_le_stabilizer_apply₂ {f : Set α -> Set α -> Set α}
    (hf : forall a : G, a • f s t = f (a • s) (a • t)) :
    stabilizer G s ⊓ stabilizer G t <= stabilizer G (f s t) := by aesop (add simp [SetLike.le_def])

@[to_additive]
/--
lemma `stabilizer_inf_stabilizer_le_stabilizer_union` / 引理 `stabilizer_inf_stabilizer_le_stabilizer_union`

English:
lemma stabilizer_inf_stabilizer_le_stabilizer_union
  proof: stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ => smul_set_union

@[to_additive]

中文:
引理 stabilizer_inf_stabilizer_le_stabilizer_union
  证明: stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ => smul_set_union

@[to_additive]

Depends on / 依赖: smul_set_union
-/
lemma stabilizer_inf_stabilizer_le_stabilizer_union :
    stabilizer G s ⊓ stabilizer G t <= stabilizer G (s union t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ => smul_set_union

@[to_additive]
/--
lemma `stabilizer_inf_stabilizer_le_stabilizer_inter` / 引理 `stabilizer_inf_stabilizer_le_stabilizer_inter`

English:
lemma stabilizer_inf_stabilizer_le_stabilizer_inter
  proof: stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ => smul_set_inter

@[to_additive]

中文:
引理 stabilizer_inf_stabilizer_le_stabilizer_inter
  证明: stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ => smul_set_inter

@[to_additive]

Depends on / 依赖: smul_set_inter
-/
lemma stabilizer_inf_stabilizer_le_stabilizer_inter :
    stabilizer G s ⊓ stabilizer G t <= stabilizer G (s inter t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ => smul_set_inter

@[to_additive]
/--
lemma `stabilizer_inf_stabilizer_le_stabilizer_sdiff` / 引理 `stabilizer_inf_stabilizer_le_stabilizer_sdiff`

English:
lemma stabilizer_inf_stabilizer_le_stabilizer_sdiff
  proof: stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ => smul_set_sdiff

@[to_additive]

中文:
引理 stabilizer_inf_stabilizer_le_stabilizer_sdiff
  证明: stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ => smul_set_sdiff

@[to_additive]

Depends on / 依赖: smul_set_sdiff
-/
lemma stabilizer_inf_stabilizer_le_stabilizer_sdiff :
    stabilizer G s ⊓ stabilizer G t <= stabilizer G (s \ t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ => smul_set_sdiff

@[to_additive]
/--
lemma `stabilizer_union_eq_left` / 引理 `stabilizer_union_eq_left`

English:
lemma stabilizer_union_eq_left
  statement: (hdisj : Disjoint s t) (hstab : stabilizer G s <= stabilizer G t)
  proof: by
  refine le_antisymm ?_ ?_
  · calc
      stabilizer G (s union t)
        <= stabilizer G (s union t) ⊓ stabilizer G t := by simpa
      _ <= stabilizer G ((s union t) \ t) := stabilizer_inf_stabilizer_le_stabilizer_sdiff
      _ = stabilizer G s := by rw [union_sdiff_cancel_right]; simpa [← dis

中文:
引理 stabilizer_union_eq_left
  结论: (hdisj : Disjoint s t) (hstab : stabilizer G s <= stabilizer G t)
  证明: by
  refine le_antisymm ?_ ?_
  · calc
      stabilizer G (s union t)
        <= stabilizer G (s union t) ⊓ stabilizer G t := by simpa
      _ <= stabilizer G ((s union t) \ t) := stabilizer_inf_stabilizer_le_stabilizer_sdiff
      _ = stabilizer G s := by rw [union_sdiff_cancel_right]; simpa [← dis

Depends on / 依赖: disjoint_iff_inter_eq_empty, le_antisymm, stabilizer, stabilizer_inf_stabilizer_le_stabilizer_sdiff, stabilizer_inf_stabilizer_le_stabilizer_union, union_sdiff_cancel_right
-/
lemma stabilizer_union_eq_left (hdisj : Disjoint s t) (hstab : stabilizer G s <= stabilizer G t)
    (hstab_union : stabilizer G (s union t) <= stabilizer G t) :
    stabilizer G (s union t) = stabilizer G s := by
  refine le_antisymm ?_ ?_
  · calc
      stabilizer G (s union t)
        <= stabilizer G (s union t) ⊓ stabilizer G t := by simpa
      _ <= stabilizer G ((s union t) \ t) := stabilizer_inf_stabilizer_le_stabilizer_sdiff
      _ = stabilizer G s := by rw [union_sdiff_cancel_right]; simpa [← disjoint_iff_inter_eq_empty]
  · calc
      stabilizer G s
        <= stabilizer G s ⊓ stabilizer G t := by simpa
      _ <= stabilizer G (s union t) := stabilizer_inf_stabilizer_le_stabilizer_union

@[to_additive]
/--
lemma `stabilizer_union_eq_right` / 引理 `stabilizer_union_eq_right`

English:
lemma stabilizer_union_eq_right
  statement: (hdisj : Disjoint s t) (hstab : stabilizer G t <= stabilizer G s)
  proof: by
  rw [union_comm]; rw [stabilizer_union_eq_left hdisj.symm hstab (union_comm .. ▸ hstab_union)]

中文:
引理 stabilizer_union_eq_right
  结论: (hdisj : Disjoint s t) (hstab : stabilizer G t <= stabilizer G s)
  证明: by
  rw [union_comm]; rw [stabilizer_union_eq_left hdisj.symm hstab (union_comm .. ▸ hstab_union)]

Depends on / 依赖: hdisj.symm, hstab_union, stabilizer_union_eq_left, union_comm
-/
lemma stabilizer_union_eq_right (hdisj : Disjoint s t) (hstab : stabilizer G t <= stabilizer G s)
    (hstab_union : stabilizer G (s union t) <= stabilizer G s) :
    stabilizer G (s union t) = stabilizer G t := by
  rw [union_comm]; rw [stabilizer_union_eq_left hdisj.symm hstab (union_comm .. ▸ hstab_union)]

variable {s : Set G}

open scoped RightActions in
@[to_additive]
/--
lemma `op_smul_set_stabilizer_subset` / 引理 `op_smul_set_stabilizer_subset`

English:
lemma op_smul_set_stabilizer_subset
  given: (ha : a in s)
  statement: (stabilizer G s : Set G) <• a subseteq s
  proof: smul_set_subset_iff.2 fun b hb => by rw [← hb]; exact smul_mem_smul_set ha

@[to_additive]

中文:
引理 op_smul_set_stabilizer_subset
  条件: (ha : a in s)
  结论: (stabilizer G s : Set G) <• a subseteq s
  证明: smul_set_subset_iff.2 fun b hb => by rw [← hb]; exact smul_mem_smul_set ha

@[to_additive]

Depends on / 依赖: smul_mem_smul_set, smul_set_subset_iff
-/
lemma op_smul_set_stabilizer_subset (ha : a in s) : (stabilizer G s : Set G) <• a subseteq s :=
  smul_set_subset_iff.2 fun b hb => by rw [← hb]; exact smul_mem_smul_set ha

@[to_additive]
/--
lemma `stabilizer_subset_div_right` / 引理 `stabilizer_subset_div_right`

English:
lemma stabilizer_subset_div_right
  given: (ha : a in s)
  statement: ↑(stabilizer G s) subseteq s / {a}
  proof: fun b hb =>
  ⟨_, by rwa [← smul_eq_mul, mem_stabilizer_set.1 hb], _, mem_singleton _, mul_div_cancel_right _ _⟩

@[to_additive]

中文:
引理 stabilizer_subset_div_right
  条件: (ha : a in s)
  结论: ↑(stabilizer G s) subseteq s / {a}
  证明: fun b hb =>
  ⟨_, by rwa [← smul_eq_mul, mem_stabilizer_set.1 hb], _, mem_singleton _, mul_div_cancel_right _ _⟩

@[to_additive]
-/
lemma stabilizer_subset_div_right (ha : a in s) : ↑(stabilizer G s) subseteq s / {a} := fun b hb =>
  ⟨_, by rwa [← smul_eq_mul, mem_stabilizer_set.1 hb], _, mem_singleton _, mul_div_cancel_right _ _⟩

@[to_additive]
/--
lemma `stabilizer_finite` / 引理 `stabilizer_finite`

English:
lemma stabilizer_finite
  given: (hs₀ : s.Nonempty) (hs : s.Finite)
  statement: (stabilizer G s : Set G).Finite
  proof: by
  obtain ⟨a, ha⟩ := hs₀
exact (hs.div <| finite_singleton _).subset stabilizer_subset_div_right ha

中文:
引理 stabilizer_finite
  条件: (hs₀ : s.Nonempty) (hs : s.Finite)
  结论: (stabilizer G s : Set G).Finite
  证明: by
  obtain ⟨a, ha⟩ := hs₀
exact (hs.div <| finite_singleton _).subset stabilizer_subset_div_right ha

Depends on / 依赖: finite_singleton, hs.div, stabilizer_subset_div_right, subset
-/
lemma stabilizer_finite (hs₀ : s.Nonempty) (hs : s.Finite) : (stabilizer G s : Set G).Finite := by
  obtain ⟨a, ha⟩ := hs₀
exact (hs.div <| finite_singleton _).subset stabilizer_subset_div_right ha

end Group

section CommGroup
variable [CommGroup G] {s t : Set G} {a : G}

@[to_additive]
/--
lemma `smul_set_stabilizer_subset` / 引理 `smul_set_stabilizer_subset`

English:
lemma smul_set_stabilizer_subset
  given: (ha : a in s)
  statement: a • (stabilizer G s : Set G) subseteq s
  proof: by
  simpa using op_smul_set_stabilizer_subset ha

中文:
引理 smul_set_stabilizer_subset
  条件: (ha : a in s)
  结论: a • (stabilizer G s : Set G) subseteq s
  证明: by
  simpa using op_smul_set_stabilizer_subset ha

Depends on / 依赖: op_smul_set_stabilizer_subset
-/
lemma smul_set_stabilizer_subset (ha : a in s) : a • (stabilizer G s : Set G) subseteq s := by
  simpa using op_smul_set_stabilizer_subset ha

end CommGroup
end Set

variable [Group G] [Group H] [MulAction G α] {a : G}

/-! ### Stabilizer of a subgroup -/

section Subgroup

-- TODO: Is there a lemma that could unify the following three very similar lemmas?

@[to_additive (attr := simp)]
/--
lemma `stabilizer_subgroup` / 引理 `stabilizer_subgroup`

English:
lemma stabilizer_subgroup
  given: (s : Subgroup G)
  statement: stabilizer G (s : Set G) = s
  proof: by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a => ⟨fun h => ?_, fun ha b => s.mul_mem_cancel_left ha⟩
  simpa only [smul_eq_mul, SetLike.mem_coe, mul_one] using (h 1).2 s.one_mem

@[to_additive (attr := simp)]

中文:
引理 stabilizer_subgroup
  条件: (s : Subgroup G)
  结论: stabilizer G (s : Set G) = s
  证明: by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a => ⟨fun h => ?_, fun ha b => s.mul_mem_cancel_left ha⟩
  simpa only [smul_eq_mul, SetLike.mem_coe, mul_one] using (h 1).2 s.one_mem

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext_iff, SetLike.mem_coe, ext_iff, mem_coe, mem_stabilizer_set, mul_mem_cancel_left, mul_one, one_mem, s.mul_mem_cancel_left, s.one_mem, simp_rw, smul_eq_mul
-/
lemma stabilizer_subgroup (s : Subgroup G) : stabilizer G (s : Set G) = s := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a => ⟨fun h => ?_, fun ha b => s.mul_mem_cancel_left ha⟩
  simpa only [smul_eq_mul, SetLike.mem_coe, mul_one] using (h 1).2 s.one_mem

@[to_additive (attr := simp)]
/--
lemma `stabilizer_op_subgroup` / 引理 `stabilizer_op_subgroup`

English:
lemma stabilizer_op_subgroup
  given: (s : Subgroup G)
  statement: stabilizer Gᵐᵒᵖ (s : Set G) = s.op
  proof: by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  simp only [smul_eq_mul_unop, SetLike.mem_coe, Subgroup.mem_op, «forall», unop_op]
  refine fun a => ⟨fun h => ?_, fun ha b => s.mul_mem_cancel_right ha⟩
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using (h 1).2 s.one_mem

@[to_additive

中文:
引理 stabilizer_op_subgroup
  条件: (s : Subgroup G)
  结论: stabilizer Gᵐᵒᵖ (s : Set G) = s.op
  证明: by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  simp only [smul_eq_mul_unop, SetLike.mem_coe, Subgroup.mem_op, «forall», unop_op]
  refine fun a => ⟨fun h => ?_, fun ha b => s.mul_mem_cancel_right ha⟩
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using (h 1).2 s.one_mem

@[to_additive

Depends on / 依赖: SetLike, SetLike.ext_iff, SetLike.mem_coe, Subgroup, Subgroup.mem_op, ext_iff, mem_coe, mem_op, mem_stabilizer_set, mul_mem_cancel_right, one_mem, one_mul, op_smul_eq_mul, s.mul_mem_cancel_right, s.one_mem, simp_rw, smul_eq_mul_unop, unop_op
-/
lemma stabilizer_op_subgroup (s : Subgroup G) : stabilizer Gᵐᵒᵖ (s : Set G) = s.op := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  simp only [smul_eq_mul_unop, SetLike.mem_coe, Subgroup.mem_op, «forall», unop_op]
  refine fun a => ⟨fun h => ?_, fun ha b => s.mul_mem_cancel_right ha⟩
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using (h 1).2 s.one_mem

@[to_additive (attr := simp)]
/--
lemma `stabilizer_subgroup_op` / 引理 `stabilizer_subgroup_op`

English:
lemma stabilizer_subgroup_op
  given: (s : Subgroup Gᵐᵒᵖ)
  statement: stabilizer G (s : Set Gᵐᵒᵖ) = s.unop
  proof: by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a => ⟨fun h => ?_, fun ha b => s.mul_mem_cancel_right ha⟩
  have : 1 * MulOpposite.op a in s := (h 1).2 s.one_mem
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using! this

中文:
引理 stabilizer_subgroup_op
  条件: (s : Subgroup Gᵐᵒᵖ)
  结论: stabilizer G (s : Set Gᵐᵒᵖ) = s.unop
  证明: by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a => ⟨fun h => ?_, fun ha b => s.mul_mem_cancel_right ha⟩
  have : 1 * MulOpposite.op a in s := (h 1).2 s.one_mem
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using! this

Depends on / 依赖: MulOpposite, MulOpposite.op, SetLike, SetLike.ext_iff, SetLike.mem_coe, ext_iff, mem_coe, mem_stabilizer_set, mul_mem_cancel_right, one_mem, one_mul, op_smul_eq_mul, s.mul_mem_cancel_right, s.one_mem, simp_rw
-/
lemma stabilizer_subgroup_op (s : Subgroup Gᵐᵒᵖ) : stabilizer G (s : Set Gᵐᵒᵖ) = s.unop := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a => ⟨fun h => ?_, fun ha b => s.mul_mem_cancel_right ha⟩
  have : 1 * MulOpposite.op a in s := (h 1).2 s.one_mem
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using! this

end Subgroup

/-! ### Stabilizer of a finset -/

section Finset
variable [DecidableEq α]

@[to_additive (attr := simp, norm_cast)]
/--
lemma `stabilizer_coe_finset` / 引理 `stabilizer_coe_finset`

English:
lemma stabilizer_coe_finset
  given: (s : Finset α)
  statement: stabilizer G (s : Set α) = stabilizer G s
  proof: by
  ext; simp [← Finset.coe_inj]

@[to_additive (attr := simp)]

中文:
引理 stabilizer_coe_finset
  条件: (s : Finset α)
  结论: stabilizer G (s : Set α) = stabilizer G s
  证明: by
  ext; simp [← Finset.coe_inj]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.coe_inj, coe_inj
-/
lemma stabilizer_coe_finset (s : Finset α) : stabilizer G (s : Set α) = stabilizer G s := by
  ext; simp [← Finset.coe_inj]

@[to_additive (attr := simp)]
/--
lemma `stabilizer_finset_empty` / 引理 `stabilizer_finset_empty`

English:
lemma stabilizer_finset_empty
  statement: stabilizer G (∅ : Finset α) = ⊤
  proof: Subgroup.coe_eq_univ.1 eq_univ_of_forall Finset.smul_finset_empty

@[to_additive (attr := simp)]

中文:
引理 stabilizer_finset_empty
  结论: stabilizer G (∅ : Finset α) = ⊤
  证明: Subgroup.coe_eq_univ.1 eq_univ_of_forall Finset.smul_finset_empty

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.smul_finset_empty, Subgroup, Subgroup.coe_eq_univ, coe_eq_univ, eq_univ_of_forall, smul_finset_empty
-/
lemma stabilizer_finset_empty : stabilizer G (∅ : Finset α) = ⊤ :=
Subgroup.coe_eq_univ.1 eq_univ_of_forall Finset.smul_finset_empty

@[to_additive (attr := simp)]
/--
lemma `stabilizer_finset_univ` / 引理 `stabilizer_finset_univ`

English:
lemma stabilizer_finset_univ
  given: [Fintype α]
  statement: stabilizer G (Finset.univ : Finset α) = ⊤
  proof: by
  ext
  simp

@[to_additive (attr := simp)]

中文:
引理 stabilizer_finset_univ
  条件: [Fintype α]
  结论: stabilizer G (Finset.univ : Finset α) = ⊤
  证明: by
  ext
  simp

@[to_additive (attr := simp)]
-/
lemma stabilizer_finset_univ [Fintype α] : stabilizer G (Finset.univ : Finset α) = ⊤ := by
  ext
  simp

@[to_additive (attr := simp)]
/--
lemma `stabilizer_finset_singleton` / 引理 `stabilizer_finset_singleton`

English:
lemma stabilizer_finset_singleton
  given: (b : α)
  statement: stabilizer G ({b} : Finset α) = stabilizer G b
  proof: by
  ext; simp

@[to_additive]

中文:
引理 stabilizer_finset_singleton
  条件: (b : α)
  结论: stabilizer G ({b} : Finset α) = stabilizer G b
  证明: by
  ext; simp

@[to_additive]
-/
lemma stabilizer_finset_singleton (b : α) : stabilizer G ({b} : Finset α) = stabilizer G b := by
  ext; simp

@[to_additive]
/--
lemma `mem_stabilizer_finset` / 引理 `mem_stabilizer_finset`

English:
lemma mem_stabilizer_finset
  given: {s : Finset α}
  statement: a in stabilizer G s ↔ forall b, a • b in s ↔ b in s
  proof: by
  simp_rw [← stabilizer_coe_finset, mem_stabilizer_set, Finset.mem_coe]

@[to_additive]

中文:
引理 mem_stabilizer_finset
  条件: {s : Finset α}
  结论: a in stabilizer G s ↔ 对任意 b, a • b in s ↔ b in s
  证明: by
  simp_rw [← stabilizer_coe_finset, mem_stabilizer_set, Finset.mem_coe]

@[to_additive]

Depends on / 依赖: Finset, Finset.mem_coe, mem_coe, mem_stabilizer_set, simp_rw, stabilizer_coe_finset
-/
lemma mem_stabilizer_finset {s : Finset α} : a in stabilizer G s ↔ forall b, a • b in s ↔ b in s := by
  simp_rw [← stabilizer_coe_finset, mem_stabilizer_set, Finset.mem_coe]

@[to_additive]
/--
lemma `mem_stabilizer_finset_iff_subset_smul_finset` / 引理 `mem_stabilizer_finset_iff_subset_smul_finset`

English:
lemma mem_stabilizer_finset_iff_subset_smul_finset
  given: {s : Finset α}
  proof: by
  rw [mem_stabilizer_iff]; rw [Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).le]; rw [eq_comm]

@[to_additive]

中文:
引理 mem_stabilizer_finset_iff_subset_smul_finset
  条件: {s : Finset α}
  证明: by
  rw [mem_stabilizer_iff]; rw [Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).le]; rw [eq_comm]

@[to_additive]

Depends on / 依赖: Finset, Finset.card_smul_finset, Finset.subset_iff_eq_of_card_le, card_smul_finset, eq_comm, mem_stabilizer_iff, subset_iff_eq_of_card_le
-/
lemma mem_stabilizer_finset_iff_subset_smul_finset {s : Finset α} :
    a in stabilizer G s ↔ s subseteq a • s := by
  rw [mem_stabilizer_iff]; rw [Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).le]; rw [eq_comm]

@[to_additive]
/--
lemma `mem_stabilizer_finset_iff_smul_finset_subset` / 引理 `mem_stabilizer_finset_iff_smul_finset_subset`

English:
lemma mem_stabilizer_finset_iff_smul_finset_subset
  given: {s : Finset α}
  proof: by
  rw [mem_stabilizer_iff]; rw [Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).ge]

@[to_additive]

中文:
引理 mem_stabilizer_finset_iff_smul_finset_subset
  条件: {s : Finset α}
  证明: by
  rw [mem_stabilizer_iff]; rw [Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).ge]

@[to_additive]

Depends on / 依赖: Finset, Finset.card_smul_finset, Finset.subset_iff_eq_of_card_le, card_smul_finset, mem_stabilizer_iff, subset_iff_eq_of_card_le
-/
lemma mem_stabilizer_finset_iff_smul_finset_subset {s : Finset α} :
    a in stabilizer G s ↔ a • s subseteq s := by
  rw [mem_stabilizer_iff]; rw [Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).ge]

@[to_additive]
/--
lemma `mem_stabilizer_finset'` / 引理 `mem_stabilizer_finset'`

English:
lemma mem_stabilizer_finset'
  given: {s : Finset α}
  statement: a in stabilizer G s ↔ forall ⦃b⦄, b in s -> a • b in s
  proof: by
  rw [← Subgroup.inv_mem_iff]; rw [mem_stabilizer_finset_iff_subset_smul_finset]
  simp_rw [← Finset.mem_inv_smul_finset_iff, Finset.subset_iff]

中文:
引理 mem_stabilizer_finset'
  条件: {s : Finset α}
  结论: a in stabilizer G s ↔ 对任意 ⦃b⦄, b in s -> a • b in s
  证明: by
  rw [← Subgroup.inv_mem_iff]; rw [mem_stabilizer_finset_iff_subset_smul_finset]
  simp_rw [← Finset.mem_inv_smul_finset_iff, Finset.subset_iff]

Depends on / 依赖: Finset, Finset.mem_inv_smul_finset_iff, Finset.subset_iff, Subgroup, Subgroup.inv_mem_iff, inv_mem_iff, mem_inv_smul_finset_iff, mem_stabilizer_finset_iff_subset_smul_finset, simp_rw, subset_iff
-/
lemma mem_stabilizer_finset' {s : Finset α} : a in stabilizer G s ↔ forall ⦃b⦄, b in s -> a • b in s := by
  rw [← Subgroup.inv_mem_iff]; rw [mem_stabilizer_finset_iff_subset_smul_finset]
  simp_rw [← Finset.mem_inv_smul_finset_iff, Finset.subset_iff]

end Finset

/-! ### Stabilizer of a finite set -/

variable {s : Set α}

@[to_additive]
/--
lemma `mem_stabilizer_set_iff_subset_smul_set` / 引理 `mem_stabilizer_set_iff_subset_smul_set`

English:
lemma mem_stabilizer_set_iff_subset_smul_set
  given: {s : Set α} (hs : s.Finite)
  proof: by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset]; rw [mem_stabilizer_finset_iff_subset_smul_finset]; rw [← Finset.coe_smul_finset]; rw [Finset.coe_subset]

@[to_additive]

中文:
引理 mem_stabilizer_set_iff_subset_smul_set
  条件: {s : Set α} (hs : s.Finite)
  证明: by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset]; rw [mem_stabilizer_finset_iff_subset_smul_finset]; rw [← Finset.coe_smul_finset]; rw [Finset.coe_subset]

@[to_additive]

Depends on / 依赖: Finset, Finset.coe_smul_finset, Finset.coe_subset, classical, coe_smul_finset, coe_subset, mem_stabilizer_finset_iff_subset_smul_finset, stabilizer_coe_finset
-/
lemma mem_stabilizer_set_iff_subset_smul_set {s : Set α} (hs : s.Finite) :
    a in stabilizer G s ↔ s subseteq a • s := by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset]; rw [mem_stabilizer_finset_iff_subset_smul_finset]; rw [← Finset.coe_smul_finset]; rw [Finset.coe_subset]

@[to_additive]
/--
lemma `mem_stabilizer_set_iff_smul_set_subset` / 引理 `mem_stabilizer_set_iff_smul_set_subset`

English:
lemma mem_stabilizer_set_iff_smul_set_subset
  given: {s : Set α} (hs : s.Finite)
  proof: by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset]; rw [mem_stabilizer_finset_iff_smul_finset_subset]; rw [← Finset.coe_smul_finset]; rw [Finset.coe_subset]

@[to_additive]

中文:
引理 mem_stabilizer_set_iff_smul_set_subset
  条件: {s : Set α} (hs : s.Finite)
  证明: by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset]; rw [mem_stabilizer_finset_iff_smul_finset_subset]; rw [← Finset.coe_smul_finset]; rw [Finset.coe_subset]

@[to_additive]

Depends on / 依赖: Finset, Finset.coe_smul_finset, Finset.coe_subset, classical, coe_smul_finset, coe_subset, mem_stabilizer_finset_iff_smul_finset_subset, stabilizer_coe_finset
-/
lemma mem_stabilizer_set_iff_smul_set_subset {s : Set α} (hs : s.Finite) :
    a in stabilizer G s ↔ a • s subseteq s := by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset]; rw [mem_stabilizer_finset_iff_smul_finset_subset]; rw [← Finset.coe_smul_finset]; rw [Finset.coe_subset]

@[to_additive]
/--
lemma `mem_stabilizer_set'` / 引理 `mem_stabilizer_set'`

English:
lemma mem_stabilizer_set'
  given: {s : Set α} (hs : s.Finite)
  proof: by
  lift s to Finset α using hs
  classical simp [-mem_stabilizer_iff, mem_stabilizer_finset']

中文:
引理 mem_stabilizer_set'
  条件: {s : Set α} (hs : s.Finite)
  证明: by
  lift s to Finset α using hs
  classical simp [-mem_stabilizer_iff, mem_stabilizer_finset']

Depends on / 依赖: Finset, classical, mem_stabilizer_finset, mem_stabilizer_iff
-/
lemma mem_stabilizer_set' {s : Set α} (hs : s.Finite) :
    a in stabilizer G s ↔ forall ⦃b⦄, b in s -> a • b in s := by
  lift s to Finset α using hs
  classical simp [-mem_stabilizer_iff, mem_stabilizer_finset']

end MulAction

/-! ### Stabilizer in a commutative group -/

namespace MulAction
variable {G : Type*} [CommGroup G] (s : Set G)

@[to_additive (attr := simp)]
/--
lemma `mul_stabilizer_self` / 引理 `mul_stabilizer_self`

English:
lemma mul_stabilizer_self
  statement: s * stabilizer G s = s
  proof: by rw [mul_comm, stabilizer_mul_self]

local notation "Q" => G ⧸ stabilizer G s
local notation "q" => ((↑) : G -> Q)

@[to_additive]

中文:
引理 mul_stabilizer_self
  结论: s * stabilizer G s = s
  证明: by rw [mul_comm, stabilizer_mul_self]

local notation "Q" => G ⧸ stabilizer G s
local notation "q" => ((↑) : G -> Q)

@[to_additive]

Depends on / 依赖: mul_comm, stabilizer_mul_self
-/
lemma mul_stabilizer_self : s * stabilizer G s = s := by rw [mul_comm, stabilizer_mul_self]

local notation "Q" => G ⧸ stabilizer G s
local notation "q" => ((↑) : G -> Q)

@[to_additive]
/--
lemma `stabilizer_image_coe_quotient` / 引理 `stabilizer_image_coe_quotient`

English:
lemma stabilizer_image_coe_quotient
  statement: stabilizer Q (q '' s) = ⊥
  proof: by
  ext a
  induction a using QuotientGroup.induction_on with | _ a
  simp only [mem_stabilizer_iff, Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  have : q a • q '' s = q '' (a • s) :=
    (image_smul_distrib (QuotientGroup.mk' <| stabilizer G s) _ _).symm
  rw [this]
  refine ⟨fun h => ?_, fun h =

中文:
引理 stabilizer_image_coe_quotient
  结论: stabilizer Q (q '' s) = ⊥
  证明: by
  ext a
  induction a using QuotientGroup.induction_on with | _ a
  simp only [mem_stabilizer_iff, Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  have : q a • q '' s = q '' (a • s) :=
    (image_smul_distrib (QuotientGroup.mk' <| stabilizer G s) _ _).symm
  rw [this]
  refine ⟨fun h => ?_, fun h =

Depends on / 依赖: QuotientGroup, QuotientGroup.eq_one_iff, QuotientGroup.image_coe_inj, QuotientGroup.induction_on, QuotientGroup.mk, Subgroup, Subgroup.mem_bot, eq_one_iff, image_coe_inj, image_smul_distrib, induction_on, mem_bot, mem_stabilizer_iff, mul_smul_comm, stabilizer, stabilizer_mul_self
-/
lemma stabilizer_image_coe_quotient : stabilizer Q (q '' s) = ⊥ := by
  ext a
  induction a using QuotientGroup.induction_on with | _ a
  simp only [mem_stabilizer_iff, Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  have : q a • q '' s = q '' (a • s) :=
    (image_smul_distrib (QuotientGroup.mk' <| stabilizer G s) _ _).symm
  rw [this]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rwa [QuotientGroup.image_coe_inj, mul_smul_comm, stabilizer_mul_self] at h

end MulAction
