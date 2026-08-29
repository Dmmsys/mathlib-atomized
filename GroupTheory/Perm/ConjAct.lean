/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Some lemmas pertaining to the action of `ConjAct (Perm α)` on `Perm α`

We prove some lemmas related to the action of `ConjAct (Perm α)` on `Perm α`:

Let `α` be a decidable fintype.

* `conj_support_eq` relates the support of `k • g` with that of `g`

* `cycleFactorsFinset_conj_eq`, `mem_cycleFactorsFinset_conj'`
  and `cycleFactorsFinset_conj` relate the set of cycles of `g`, `g.cycleFactorsFinset`,
  with that for `k • g`

-/

public section

namespace Equiv.Perm

open scoped Pointwise

variable {α : Type*} [DecidableEq α] [Fintype α]

/--
theorem `mem_conj_support` / 定理 `mem_conj_support`

English:
theorem mem_conj_support
  given: (k : ConjAct (Perm α)) (g : Perm α) (a : α)
  proof: by
  simp only [mem_support, ConjAct.smul_def, not_iff_not, coe_mul,
    Function.comp_apply, ConjAct.ofConjAct_inv]
  exact eq_inv_iff_eq.symm

中文:
定理 mem_conj_support
  条件: (k : ConjAct (置换 α)) (g : 置换 α) (a : α)
  证明: by
  simp only [mem_support, ConjAct.smul_def, not_iff_not, coe_mul,
    Function.comp_apply, ConjAct.ofConjAct_inv]
  exact eq_inv_iff_eq.symm

Depends on / 依赖: ConjAct, ConjAct.ofConjAct_inv, ConjAct.smul_def, Function, Function.comp_apply, coe_mul, comp_apply, eq_inv_iff_eq, eq_inv_iff_eq.symm, mem_support, not_iff_not, ofConjAct_inv, smul_def
-/
theorem mem_conj_support (k : ConjAct (Perm α)) (g : Perm α) (a : α) :
    a in (k • g).support ↔ ConjAct.ofConjAct k⁻¹ a in g.support := by
  simp only [mem_support, ConjAct.smul_def, not_iff_not, coe_mul,
    Function.comp_apply, ConjAct.ofConjAct_inv]
  exact eq_inv_iff_eq.symm

/--
theorem `support_conj_eq_smul_support` / 定理 `support_conj_eq_smul_support`

English:
theorem support_conj_eq_smul_support
  given: (k : ConjAct (Perm α)) (g : Equiv.Perm α)
  proof: by
  ext
  rw [mem_conj_support]; rw [← Perm.smul_def]; rw [ConjAct.ofConjAct_inv]; rw [Finset.inv_smul_mem_iff]

中文:
定理 support_conj_eq_smul_support
  条件: (k : ConjAct (置换 α)) (g : 等价.置换 α)
  证明: by
  ext
  rw [mem_conj_support]; rw [← Perm.smul_def]; rw [ConjAct.ofConjAct_inv]; rw [Finset.inv_smul_mem_iff]

Depends on / 依赖: ConjAct, ConjAct.ofConjAct_inv, Finset, Finset.inv_smul_mem_iff, Perm.smul_def, inv_smul_mem_iff, mem_conj_support, ofConjAct_inv, smul_def
-/
theorem support_conj_eq_smul_support (k : ConjAct (Perm α)) (g : Equiv.Perm α) :
    (k • g).support = k.ofConjAct • g.support := by
  ext
  rw [mem_conj_support]; rw [← Perm.smul_def]; rw [ConjAct.ofConjAct_inv]; rw [Finset.inv_smul_mem_iff]

/--
theorem `support_toConjAct_eq_smul_support` / 定理 `support_toConjAct_eq_smul_support`

English:
theorem support_toConjAct_eq_smul_support
  given: (k g : Perm α)
  proof: by
  rw [Equiv.Perm.support_conj_eq_smul_support]; rw [ConjAct.ofConjAct_toConjAct]

中文:
定理 support_toConjAct_eq_smul_support
  条件: (k g : 置换 α)
  证明: by
  rw [Equiv.Perm.support_conj_eq_smul_support]; rw [ConjAct.ofConjAct_toConjAct]

Depends on / 依赖: ConjAct, ConjAct.ofConjAct_toConjAct, Equiv.Perm.support_conj_eq_smul_support, ofConjAct_toConjAct, support_conj_eq_smul_support
-/
theorem support_toConjAct_eq_smul_support (k g : Perm α) :
    (ConjAct.toConjAct k • g).support = k • g.support := by
  rw [Equiv.Perm.support_conj_eq_smul_support]; rw [ConjAct.ofConjAct_toConjAct]

/--
theorem `cycleFactorsFinset_conj` / 定理 `cycleFactorsFinset_conj`

English:
theorem cycleFactorsFinset_conj
  given: (g k : Perm α)
  proof: by
  ext c
  rw [ConjAct.smul_def]; rw [ConjAct.ofConjAct_toConjAct]; rw [Finset.mem_map_equiv]; rw [← mem_cycleFactorsFinset_conj g k]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  simp [mul_assoc]

中文:
定理 cycleFactorsFinset_conj
  条件: (g k : 置换 α)
  证明: by
  ext c
  rw [ConjAct.smul_def]; rw [ConjAct.ofConjAct_toConjAct]; rw [Finset.mem_map_equiv]; rw [← mem_cycleFactorsFinset_conj g k]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  simp [mul_assoc]

Depends on / 依赖: ConjAct, ConjAct.ofConjAct_toConjAct, ConjAct.smul_def, Finset, Finset.mem_map_equiv, mem_cycleFactorsFinset_conj, mem_map_equiv, ofConjAct_toConjAct, smul_def
-/
theorem cycleFactorsFinset_conj (g k : Perm α) :
    (ConjAct.toConjAct k • g).cycleFactorsFinset =
      Finset.map (MulAut.conj k).toEquiv.toEmbedding g.cycleFactorsFinset := by
  ext c
  rw [ConjAct.smul_def]; rw [ConjAct.ofConjAct_toConjAct]; rw [Finset.mem_map_equiv]; rw [← mem_cycleFactorsFinset_conj g k]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  simp [mul_assoc]

/-- A permutation `c` is a cycle of `g` iff `k • c` is a cycle of `k • g` -/
@[simp]
/--
theorem `mem_cycleFactorsFinset_conj'` / 定理 `mem_cycleFactorsFinset_conj'`

English:
theorem mem_cycleFactorsFinset_conj'
  proof: by
  simp only [ConjAct.smul_def]
  apply mem_cycleFactorsFinset_conj g k

中文:
定理 mem_cycleFactorsFinset_conj'
  证明: by
  simp only [ConjAct.smul_def]
  apply mem_cycleFactorsFinset_conj g k

Depends on / 依赖: ConjAct, ConjAct.smul_def, mem_cycleFactorsFinset_conj, smul_def
-/
theorem mem_cycleFactorsFinset_conj'
    (k : ConjAct (Perm α)) (g c : Perm α) :
    k • c in (k • g).cycleFactorsFinset ↔ c in g.cycleFactorsFinset := by
  simp only [ConjAct.smul_def]
  apply mem_cycleFactorsFinset_conj g k

/--
theorem `cycleFactorsFinset_conj_eq` / 定理 `cycleFactorsFinset_conj_eq`

English:
theorem cycleFactorsFinset_conj_eq
  proof: by
  ext c
  rw [← mem_cycleFactorsFinset_conj' k⁻¹ (k • g) c]
  simp only [inv_smul_smul]
  exact Finset.inv_smul_mem_iff

omit [Fintype α] in

中文:
定理 cycleFactorsFinset_conj_eq
  证明: by
  ext c
  rw [← mem_cycleFactorsFinset_conj' k⁻¹ (k • g) c]
  simp only [inv_smul_smul]
  exact Finset.inv_smul_mem_iff

omit [Fintype α] in

Depends on / 依赖: Finset, Finset.inv_smul_mem_iff, inv_smul_mem_iff, inv_smul_smul, mem_cycleFactorsFinset_conj
-/
theorem cycleFactorsFinset_conj_eq
    (k : ConjAct (Perm α)) (g : Perm α) :
    cycleFactorsFinset (k • g) = k • cycleFactorsFinset g := by
  ext c
  rw [← mem_cycleFactorsFinset_conj' k⁻¹ (k • g) c]
  simp only [inv_smul_smul]
  exact Finset.inv_smul_mem_iff

omit [Fintype α] in
/--
theorem `conj_smul_range_ofSubtype` / 定理 `conj_smul_range_ofSubtype`

English:
theorem conj_smul_range_ofSubtype
  given: [Finite α] (g : Perm α) (s : Finset α)
  proof: by
  have : Fintype α := Fintype.ofFinite α
  ext k
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_range_ofSubtype_iff]
  simp [support_conj_eq_smul_support, Set.subset_smul_set_iff]

中文:
定理 conj_smul_range_ofSubtype
  条件: [有限 α] (g : 置换 α) (s : 有限集 α)
  证明: by
  have : Fintype α := Fintype.ofFinite α
  ext k
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_range_ofSubtype_iff]
  simp [support_conj_eq_smul_support, Set.subset_smul_set_iff]
-/
theorem conj_smul_range_ofSubtype [Finite α] (g : Perm α) (s : Finset α) :
    ConjAct.toConjAct g • (ofSubtype (p := (· in s))).range =
      (ofSubtype (p := (· in g • s))).range := by
  have : Fintype α := Fintype.ofFinite α
  ext k
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_range_ofSubtype_iff]
  simp [support_conj_eq_smul_support, Set.subset_smul_set_iff]

end Equiv.Perm
