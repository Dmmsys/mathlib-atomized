/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Subgroup.Simple

/-! # Iwasawa criterion for simplicity

- `IwasawaStructure` : the structure underlying the Iwasawa criterion.
  For a group `G`, this consists of an action of `G` on a type `α` and,
  for every `a : α`, of a subgroup `T a`, such that the following properties hold:
  - for all `a`, `T a` is commutative
  - for all `g : G` and `a : α`, `T (g • a) = MulAut.conj g • T a`
  - the subgroups `T a` generate `G`

We then prove two versions of the Iwasawa criterion when
there is an Iwasawa structure.

- `IwasawaStructure.commutator_le` asserts that if the action of `G` on `α`
  is quasiprimitive, then every normal subgroup that acts nontrivially
  contains `commutator G`.

- `IwasawaStructure.isSimpleGroup` : the Iwasawa criterion for simplicity.
  If the action of `G` on `α` is quasiprimitive and faithful,
  and `G` is nontrivial and perfect, then `G` is simple.

## TODO

Additivize. The issue is that it requires to additivize `commutator`
(which, moreover, lives in the root namespace)
-/

public section

namespace MulAction

open scoped Pointwise

variable (M : Type*) [Group M] (α : Type*) [MulAction M α]

/--
Definition of `IwasawaStructure` / `IwasawaStructure` 的定义

English:
structure IwasawaStructure
  parameters: where
  axioms and operations (4):
    - T : α -> Subgroup M
    - is_comm : forall x : α, IsMulCommutative (T x)
    - is_conj : forall g : M, forall x : α, T (g • x) = MulAut.conj g • T x
    - is_generator : iSup T = ⊤

中文:
结构 IwasawaStructure
  参数: where
  公理与运算 (4 个):
    - T : α -> Subgroup M
    - is_comm : 对任意 x : α, IsMulCommutative (T x)
    - is_conj : 对任意 g : M, 对任意 x : α, T (g • x) = MulAut.conj g • T x
    - is_generator : iSup T = ⊤
-/
structure IwasawaStructure where
  /-- The subgroups of the Iwasawa structure -/
  T : α -> Subgroup M
  /-- The commutativity property of the subgroups -/
  is_comm : forall x : α, IsMulCommutative (T x)
  /-- The conjugacy property of the subgroups -/
  is_conj : forall g : M, forall x : α, T (g • x) = MulAut.conj g • T x
  /-- The subgroups generate the group -/
  is_generator : iSup T = ⊤

variable {M α}

namespace IwasawaStructure

/--
theorem `commutator_le` / 定理 `commutator_le`

English:
theorem commutator_le
  statement: (IwaS : IwasawaStructure M α) [IsQuasiPreprimitive M α]
  proof: by
  have is_transN := IsQuasiPreprimitive.isPretransitive_of_normal hNX
  have ntα : Nontrivial α := nontrivial_of_fixedPoints_ne_univ hNX
  obtain a : α := Nontrivial.to_nonempty.some
  apply nN.commutator_le_of_self_sup_commutative_eq_top ?_ (IwaS.is_comm a)
  -- We have to prove that N ⊔ IwaS.T 

中文:
定理 commutator_le
  结论: (IwaS : IwasawaStructure M α) [IsQuasiPreprimitive M α]
  证明: by
  have is_transN := IsQuasiPreprimitive.isPretransitive_of_normal hNX
  have ntα : Nontrivial α := nontrivial_of_fixedPoints_ne_univ hNX
  obtain a : α := Nontrivial.to_nonempty.some
  apply nN.commutator_le_of_self_sup_commutative_eq_top ?_ (IwaS.is_comm a)
  -- We have to prove that N ⊔ IwaS.T 

Depends on / 依赖: IsQuasiPreprimitive, IsQuasiPreprimitive.isPretransitive_of_normal, IwaS.is_comm, Nontrivial, Nontrivial.to_nonempty.some, commutator_le_of_self_sup_commutative_eq_top, isPretransitive_of_normal, is_comm, is_transN, nN.commutator_le_of_self_sup_commutative_eq_top, nontrivial_of_fixedPoints_ne_univ, to_nonempty
-/
theorem commutator_le (IwaS : IwasawaStructure M α) [IsQuasiPreprimitive M α]
    (N : Subgroup M) [nN : N.Normal] (hNX : MulAction.fixedPoints N α != .univ) :
    commutator M <= N := by
  have is_transN := IsQuasiPreprimitive.isPretransitive_of_normal hNX
  have ntα : Nontrivial α := nontrivial_of_fixedPoints_ne_univ hNX
  obtain a : α := Nontrivial.to_nonempty.some
  apply nN.commutator_le_of_self_sup_commutative_eq_top ?_ (IwaS.is_comm a)
  -- We have to prove that N ⊔ IwaS.T x = ⊤
  rw [eq_top_iff]; rw [← IwaS.is_generator]; rw [iSup_le_iff]
  intro x
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq N a x
  rw [Subgroup.smul_def]; rw [IwaS.is_conj g a]
  rintro _ ⟨k, hk, rfl⟩
  have hg' : ↑g in N ⊔ IwaS.T a := Subgroup.mem_sup_left (Subtype.mem g)
  have hk' : k in N ⊔ IwaS.T a := Subgroup.mem_sup_right hk
  exact (N ⊔ IwaS.T a).mul_mem ((N ⊔ IwaS.T a).mul_mem hg' hk') ((N ⊔ IwaS.T a).inv_mem hg')

/--
theorem `isSimpleGroup` / 定理 `isSimpleGroup`

English:
theorem isSimpleGroup
  statement: [Nontrivial M] (is_perfect : commutator M = ⊤)
  proof: by
  apply IsSimpleGroup.mk
  intro N nN
  cases or_iff_not_imp_left.mpr (IwaS.commutator_le N) with
  | inl h =>
    refine Or.inl (N.eq_bot_iff_forall.mpr fun n hn => ?_)
    apply is_faithful.eq_of_smul_eq_smul
    intro x
    rw [one_smul]
    exact Set.eq_univ_iff_forall.mp h x ⟨n, hn⟩
  | inr 

中文:
定理 isSimpleGroup
  结论: [Nontrivial M] (is_perfect : commutator M = ⊤)
  证明: by
  apply IsSimpleGroup.mk
  intro N nN
  cases or_iff_not_imp_left.mpr (IwaS.commutator_le N) with
  | inl h =>
    refine Or.inl (N.eq_bot_iff_forall.mpr fun n hn => ?_)
    apply is_faithful.eq_of_smul_eq_smul
    intro x
    rw [one_smul]
    exact Set.eq_univ_iff_forall.mp h x ⟨n, hn⟩
  | inr 

Depends on / 依赖: IsSimpleGroup, IsSimpleGroup.mk, IwaS.commutator_le, N.eq_bot_iff_forall.mpr, Or.inl, Or.inr, Set.eq_univ_iff_forall.mp, commutator_le, eq_bot_iff_forall, eq_of_smul_eq_smul, eq_univ_iff_forall, ge_of_eq, is_faithful, is_faithful.eq_of_smul_eq_smul, is_perfect, le_trans, one_smul, or_iff_not_imp_left, or_iff_not_imp_left.mpr, top_le_iff
-/
theorem isSimpleGroup [Nontrivial M] (is_perfect : commutator M = ⊤)
    [IsQuasiPreprimitive M α] (IwaS : IwasawaStructure M α) (is_faithful : FaithfulSMul M α) :
    IsSimpleGroup M := by
  apply IsSimpleGroup.mk
  intro N nN
  cases or_iff_not_imp_left.mpr (IwaS.commutator_le N) with
  | inl h =>
    refine Or.inl (N.eq_bot_iff_forall.mpr fun n hn => ?_)
    apply is_faithful.eq_of_smul_eq_smul
    intro x
    rw [one_smul]
    exact Set.eq_univ_iff_forall.mp h x ⟨n, hn⟩
  | inr h => exact Or.inr (top_le_iff.mp (le_trans (ge_of_eq is_perfect) h))

end MulAction.IwasawaStructure
