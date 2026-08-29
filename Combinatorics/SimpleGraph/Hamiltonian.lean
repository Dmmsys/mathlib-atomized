/-
Copyright (c) 2023 Bhavik Mehta, Rishi Mehta, Linus Sommer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Rishi Mehta, Linus Sommer, Yue Sun
-/
module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity

/-!
# Hamiltonian Graphs

In this file we introduce Hamiltonian paths, cycles and graphs.

## Main definitions

- `SimpleGraph.Walk.IsHamiltonian`: Predicate for a walk to be Hamiltonian.
- `SimpleGraph.Walk.IsHamiltonianCycle`: Predicate for a walk to be a Hamiltonian cycle.
- `SimpleGraph.IsHamiltonian`: Predicate for a graph to be Hamiltonian.
-/

@[expose] public section

open Finset Function

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}
variable {β : Type*} [DecidableEq β] {H : SimpleGraph β}
variable {a b v : α} {p : G.Walk a b} {f : G ->g H}

namespace Walk

/--
Definition of `IsHamiltonian` / `IsHamiltonian` 的定义

English:
definition IsHamiltonian
  signature: (p : G.Walk a b)
  body: forall a, p.support.count a = 1

中文:
定义 IsHamiltonian
  签名: (p : G.途径 a b)
  定义体: forall a, p.support.count a = 1

Depends on / 依赖: p.support.count, support
-/
def IsHamiltonian (p : G.Walk a b) : Prop := forall a, p.support.count a = 1

variable (f) in
/--
lemma `IsHamiltonian.map` / 引理 `IsHamiltonian.map`

English:
lemma IsHamiltonian.map
  given: (hf : Bijective f) (hp : p.IsHamiltonian)
  proof: by
  simp [IsHamiltonian, hf.surjective.forall, hf.injective, hp _]

中文:
引理 IsHamiltonian.map
  条件: (hf : 双射 f) (hp : p.IsHamiltonian)
  证明: by
  simp [IsHamiltonian, hf.surjective.forall, hf.injective, hp _]

Depends on / 依赖: IsHamiltonian, hf.injective, hf.surjective.forall, injective, surjective
-/
lemma IsHamiltonian.map (hf : Bijective f) (hp : p.IsHamiltonian) :
    (p.map f).IsHamiltonian := by
  simp [IsHamiltonian, hf.surjective.forall, hf.injective, hp _]

/--
lemma `IsHamiltonian.mem_support` / 引理 `IsHamiltonian.mem_support`

English:
lemma IsHamiltonian.mem_support
  given: (hp : p.IsHamiltonian) (c : α)
  statement: c in p.support
  proof: p.support.one_le_count_iff.mp .symm.le hp c

中文:
引理 IsHamiltonian.mem_support
  条件: (hp : p.IsHamiltonian) (c : α)
  结论: c in p.support
  证明: p.support.one_le_count_iff.mp .symm.le hp c
-/
@[simp] lemma IsHamiltonian.mem_support (hp : p.IsHamiltonian) (c : α) : c in p.support :=
p.support.one_le_count_iff.mp .symm.le hp c

/--
lemma `IsHamiltonian.isPath` / 引理 `IsHamiltonian.isPath`

English:
lemma IsHamiltonian.isPath
  given: (hp : p.IsHamiltonian)
  statement: p.IsPath
  proof: IsPath.mk' List.nodup_iff_count_le_one.2 (le_of_eq <| hp ·)

中文:
引理 IsHamiltonian.isPath
  条件: (hp : p.IsHamiltonian)
  结论: p.是道路
  证明: IsPath.mk' List.nodup_iff_count_le_one.2 (le_of_eq <| hp ·)

Depends on / 依赖: IsPath, IsPath.mk, List.nodup_iff_count_le_one, le_of_eq, nodup_iff_count_le_one
-/
lemma IsHamiltonian.isPath (hp : p.IsHamiltonian) : p.IsPath :=
IsPath.mk' List.nodup_iff_count_le_one.2 (le_of_eq <| hp ·)

/--
lemma `IsPath.isHamiltonian_of_mem` / 引理 `IsPath.isHamiltonian_of_mem`

English:
lemma IsPath.isHamiltonian_of_mem
  given: (hp : p.IsPath) (hp' : forall w, w in p.support)
  proof: fun _ =>
  le_antisymm (List.nodup_iff_count_le_one.1 hp.support_nodup _) (List.count_pos_iff.2 (hp' _))

中文:
引理 是道路.isHamiltonian_of_mem
  条件: (hp : p.是道路) (hp' : 对任意 w, w in p.support)
  证明: fun _ =>
  le_antisymm (List.nodup_iff_count_le_one.1 hp.support_nodup _) (List.count_pos_iff.2 (hp' _))
-/
lemma IsPath.isHamiltonian_of_mem (hp : p.IsPath) (hp' : forall w, w in p.support) :
    p.IsHamiltonian := fun _ =>
  le_antisymm (List.nodup_iff_count_le_one.1 hp.support_nodup _) (List.count_pos_iff.2 (hp' _))

/--
lemma `IsPath.isHamiltonian_iff` / 引理 `IsPath.isHamiltonian_iff`

English:
lemma IsPath.isHamiltonian_iff
  given: (hp : p.IsPath)
  statement: p.IsHamiltonian ↔ forall w, w in p.support
  proof: ⟨(·.mem_support), hp.isHamiltonian_of_mem⟩

中文:
引理 是道路.isHamiltonian_iff
  条件: (hp : p.是道路)
  结论: p.IsHamiltonian ↔ 对任意 w, w in p.support
  证明: ⟨(·.mem_support), hp.isHamiltonian_of_mem⟩

Depends on / 依赖: hp.isHamiltonian_of_mem, isHamiltonian_of_mem, mem_support
-/
lemma IsPath.isHamiltonian_iff (hp : p.IsPath) : p.IsHamiltonian ↔ forall w, w in p.support :=
  ⟨(·.mem_support), hp.isHamiltonian_of_mem⟩

/--
theorem `IsHamiltonian.of_subsingleton` / 定理 `IsHamiltonian.of_subsingleton`

English:
theorem IsHamiltonian.of_subsingleton
  given: [Subsingleton α]
  statement: p.IsHamiltonian
  proof: by
  intro v
  rw [nil_iff_support_eq.mp p.nil_of_subsingleton]; rw [Subsingleton.elim v a]; rw [List.count_singleton_self]

中文:
定理 IsHamiltonian.of_subsingleton
  条件: [子单例 α]
  结论: p.IsHamiltonian
  证明: by
  intro v
  rw [nil_iff_support_eq.mp p.nil_of_subsingleton]; rw [Subsingleton.elim v a]; rw [List.count_singleton_self]

Depends on / 依赖: List.count_singleton_self, Subsingleton, Subsingleton.elim, count_singleton_self, nil_iff_support_eq, nil_iff_support_eq.mp, nil_of_subsingleton, p.nil_of_subsingleton
-/
theorem IsHamiltonian.of_subsingleton [Subsingleton α] : p.IsHamiltonian := by
  intro v
  rw [nil_iff_support_eq.mp p.nil_of_subsingleton]; rw [Subsingleton.elim v a]; rw [List.count_singleton_self]

/-- If a path `p` is Hamiltonian then the graph has finitely many vertices. -/
@[instance_reducible]
/--
Definition of `IsHamiltonian.fintype` / `IsHamiltonian.fintype` 的定义

English:
definition IsHamiltonian.fintype
  signature: (hp : p.IsHamiltonian)
  body: p.support.toFinset
  complete x := List.mem_toFinset.mpr (mem_support hp x)

中文:
定义 IsHamiltonian.fintype
  签名: (hp : p.IsHamiltonian)
  定义体: p.support.toFinset
  complete x := List.mem_toFinset.mpr (mem_support hp x)
-/
protected def IsHamiltonian.fintype (hp : p.IsHamiltonian) : Fintype α where
  elems := p.support.toFinset
  complete x := List.mem_toFinset.mpr (mem_support hp x)

/--
lemma `IsHamiltonian.finite` / 引理 `IsHamiltonian.finite`

English:
lemma IsHamiltonian.finite
  given: (hp : p.IsHamiltonian)
  statement: Finite α
  proof: by
  have := hp.fintype; infer_instance

中文:
引理 IsHamiltonian.finite
  条件: (hp : p.IsHamiltonian)
  结论: 有限 α
  证明: by
  have := hp.fintype; infer_instance
-/
protected lemma IsHamiltonian.finite (hp : p.IsHamiltonian) : Finite α := by
  have := hp.fintype; infer_instance

/--
lemma `not_isHamiltonian_of_infinite` / 引理 `not_isHamiltonian_of_infinite`

English:
lemma not_isHamiltonian_of_infinite
  given: [h : Infinite α]
  statement: ¬ p.IsHamiltonian
  proof: by
  contrapose! h; exact h.finite

中文:
引理 not_isHamiltonian_of_infinite
  条件: [h : 无限 α]
  结论: ¬ p.IsHamiltonian
  证明: by
  contrapose! h; exact h.finite
-/
@[simp] lemma not_isHamiltonian_of_infinite [h : Infinite α] : ¬ p.IsHamiltonian := by
  contrapose! h; exact h.finite

section
variable [Fintype α]

/--
lemma `IsHamiltonian.toFinset_support` / 引理 `IsHamiltonian.toFinset_support`

English:
lemma IsHamiltonian.toFinset_support
  given: (hp : p.IsHamiltonian)
  statement: p.support.toFinset = Finset.univ
  proof: by
  simp [eq_univ_iff_forall, hp]

@[deprecated (since := "2026-03-11")]
alias IsHamiltonian.support_toFinset := IsHamiltonian.toFinset_support

omit [Fintype α] in

中文:
引理 IsHamiltonian.toFinset_support
  条件: (hp : p.IsHamiltonian)
  结论: p.support.toFinset = 有限集.univ
  证明: by
  simp [eq_univ_iff_forall, hp]

@[deprecated (since := "2026-03-11")]
alias IsHamiltonian.support_toFinset := IsHamiltonian.toFinset_support

omit [Fintype α] in

Depends on / 依赖: eq_univ_iff_forall
-/
lemma IsHamiltonian.toFinset_support (hp : p.IsHamiltonian) : p.support.toFinset = Finset.univ := by
  simp [eq_univ_iff_forall, hp]

@[deprecated (since := "2026-03-11")]
alias IsHamiltonian.support_toFinset := IsHamiltonian.toFinset_support

omit [Fintype α] in
/--
theorem `IsHamiltonian.setOfPred_support` / 定理 `IsHamiltonian.setOfPred_support`

English:
theorem IsHamiltonian.setOfPred_support
  given: (hp : p.IsHamiltonian)
  statement: {v | v in p.support} = Set.univ
  proof: Set.eq_univ_iff_forall.mpr hp.mem_support

@[deprecated (since := "2026-07-09")]
alias IsHamiltonian.setOf_support := IsHamiltonian.setOfPred_support

中文:
定理 IsHamiltonian.setOfPred_support
  条件: (hp : p.IsHamiltonian)
  结论: {v | v in p.support} = 集合.univ
  证明: Set.eq_univ_iff_forall.mpr hp.mem_support

@[deprecated (since := "2026-07-09")]
alias IsHamiltonian.setOf_support := IsHamiltonian.setOfPred_support

Depends on / 依赖: Set.eq_univ_iff_forall.mpr, eq_univ_iff_forall, hp.mem_support, mem_support
-/
theorem IsHamiltonian.setOfPred_support (hp : p.IsHamiltonian) : {v | v in p.support} = Set.univ :=
  Set.eq_univ_iff_forall.mpr hp.mem_support

@[deprecated (since := "2026-07-09")]
alias IsHamiltonian.setOf_support := IsHamiltonian.setOfPred_support

/--
lemma `IsHamiltonian.length_eq` / 引理 `IsHamiltonian.length_eq`

English:
lemma IsHamiltonian.length_eq
  given: (hp : p.IsHamiltonian)
  statement: p.length = Fintype.card α - 1
  proof: eq_tsub_of_add_eq by
    rw [← length_support]; rw [← List.sum_toFinset_count_eq_length]; rw [Finset.sum_congr rfl fun _ _ => hp _]; rw [← card_eq_sum_ones]; rw [hp.toFinset_support]; rw [card_univ]

中文:
引理 IsHamiltonian.length_eq
  条件: (hp : p.IsHamiltonian)
  结论: p.length = 有限类型.card α - 1
  证明: eq_tsub_of_add_eq by
    rw [← length_support]; rw [← List.sum_toFinset_count_eq_length]; rw [Finset.sum_congr rfl fun _ _ => hp _]; rw [← card_eq_sum_ones]; rw [hp.toFinset_support]; rw [card_univ]

Depends on / 依赖: Finset, Finset.sum_congr, List.sum_toFinset_count_eq_length, card_eq_sum_ones, card_univ, eq_tsub_of_add_eq, hp.toFinset_support, length_support, sum_congr, sum_toFinset_count_eq_length, toFinset_support
-/
lemma IsHamiltonian.length_eq (hp : p.IsHamiltonian) : p.length = Fintype.card α - 1 :=
eq_tsub_of_add_eq by
    rw [← length_support]; rw [← List.sum_toFinset_count_eq_length]; rw [Finset.sum_congr rfl fun _ _ => hp _]; rw [← card_eq_sum_ones]; rw [hp.toFinset_support]; rw [card_univ]

/--
lemma `IsHamiltonian.length_support` / 引理 `IsHamiltonian.length_support`

English:
lemma IsHamiltonian.length_support
  given: (hp : p.IsHamiltonian)
  statement: p.support.length = Fintype.card α
  proof: by
  have : Inhabited α := ⟨a⟩
  grind [Fintype.card_ne_zero, length_eq]

中文:
引理 IsHamiltonian.length_support
  条件: (hp : p.IsHamiltonian)
  结论: p.support.length = 有限类型.card α
  证明: by
  have : Inhabited α := ⟨a⟩
  grind [Fintype.card_ne_zero, length_eq]

Depends on / 依赖: Fintype, Fintype.card_ne_zero, Inhabited, card_ne_zero, length_eq
-/
lemma IsHamiltonian.length_support (hp : p.IsHamiltonian) : p.support.length = Fintype.card α := by
  have : Inhabited α := ⟨a⟩
  grind [Fintype.card_ne_zero, length_eq]

end

/-- If a path `p` is Hamiltonian, then `p.support.get` defines an equivalence between
`Fin p.support.length` and `α`. -/
@[simps!]
/--
Definition of `IsHamiltonian.supportGetEquiv` / `IsHamiltonian.supportGetEquiv` 的定义

English:
definition IsHamiltonian.supportGetEquiv
  signature: (hp : p.IsHamiltonian)
  body: p.support.getEquivOfForallCountEqOne hp

中文:
定义 IsHamiltonian.supportGetEquiv
  签名: (hp : p.IsHamiltonian)
  定义体: p.support.getEquivOfForallCountEqOne hp

Depends on / 依赖: getEquivOfForallCountEqOne, p.support.getEquivOfForallCountEqOne, support
-/
def IsHamiltonian.supportGetEquiv (hp : p.IsHamiltonian) : Fin p.support.length ≃ α :=
  p.support.getEquivOfForallCountEqOne hp

/-- If a path `p` is Hamiltonian, then `p.getVert` defines an equivalence between
`Fin p.support.length` and `α`. -/
@[simps]
/--
Definition of `IsHamiltonian.getVertEquiv` / `IsHamiltonian.getVertEquiv` 的定义

English:
definition IsHamiltonian.getVertEquiv
  signature: (hp : p.IsHamiltonian)
  body: p.getVert ∘ Fin.val
  invFun := hp.supportGetEquiv.invFun
  left_inv := p.getVert_comp_val_eq_get_support ▸ hp.supportGetEquiv.left_inv
  right_inv := p.getVert_comp_val_eq_get_support ▸ hp.supportGetEquiv.right_inv

中文:
定义 IsHamiltonian.getVertEquiv
  签名: (hp : p.IsHamiltonian)
  定义体: p.getVert ∘ Fin.val
  invFun := hp.supportGetEquiv.invFun
  left_inv := p.getVert_comp_val_eq_get_support ▸ hp.supportGetEquiv.left_inv
  right_inv := p.getVert_comp_val_eq_get_support ▸ hp.supportGetEquiv.right_inv

Depends on / 依赖: Fin.val, getVert, p.getVert
-/
def IsHamiltonian.getVertEquiv (hp : p.IsHamiltonian) : Fin p.support.length ≃ α where
  toFun := p.getVert ∘ Fin.val
  invFun := hp.supportGetEquiv.invFun
  left_inv := p.getVert_comp_val_eq_get_support ▸ hp.supportGetEquiv.left_inv
  right_inv := p.getVert_comp_val_eq_get_support ▸ hp.supportGetEquiv.right_inv

/--
theorem `isHamiltonian_iff_support_get_bijective` / 定理 `isHamiltonian_iff_support_get_bijective`

English:
theorem isHamiltonian_iff_support_get_bijective
  statement: p.IsHamiltonian ↔ p.support.get.Bijective
  proof: p.support.get_bijective_iff.symm

中文:
定理 isHamiltonian_iff_support_get_bijective
  结论: p.IsHamiltonian ↔ p.support.get.双射
  证明: p.support.get_bijective_iff.symm

Depends on / 依赖: get_bijective_iff, p.support.get_bijective_iff.symm, support
-/
theorem isHamiltonian_iff_support_get_bijective : p.IsHamiltonian ↔ p.support.get.Bijective :=
  p.support.get_bijective_iff.symm

/--
theorem `IsHamiltonian.getVert_surjective` / 定理 `IsHamiltonian.getVert_surjective`

English:
theorem IsHamiltonian.getVert_surjective
  given: (hp : p.IsHamiltonian)
  statement: p.getVert.Surjective
  proof: .of_comp p.getVert_comp_val_eq_get_support ▸
.surjective isHamiltonian_iff_support_get_bijective.mp hp

omit [DecidableEq β] in

中文:
定理 IsHamiltonian.getVert_surjective
  条件: (hp : p.IsHamiltonian)
  结论: p.getVert.满射
  证明: .of_comp p.getVert_comp_val_eq_get_support ▸
.surjective isHamiltonian_iff_support_get_bijective.mp hp

omit [DecidableEq β] in

Depends on / 依赖: getVert_comp_val_eq_get_support, isHamiltonian_iff_support_get_bijective, isHamiltonian_iff_support_get_bijective.mp, of_comp, p.getVert_comp_val_eq_get_support, surjective
-/
theorem IsHamiltonian.getVert_surjective (hp : p.IsHamiltonian) : p.getVert.Surjective :=
.of_comp p.getVert_comp_val_eq_get_support ▸
.surjective isHamiltonian_iff_support_get_bijective.mp hp

omit [DecidableEq β] in
/--
theorem `IsHamiltonian.injective_of_isPath_map` / 定理 `IsHamiltonian.injective_of_isPath_map`

English:
theorem IsHamiltonian.injective_of_isPath_map
  given: (hp : p.IsHamiltonian) (h : (p.map f).IsPath)
  proof: by
  rw [← Set.injOn_univ]; rw [← hp.setOfPred_support]
  exact h.injOn_support_of_isPath_map

中文:
定理 IsHamiltonian.injective_of_isPath_map
  条件: (hp : p.IsHamiltonian) (h : (p.map f).是道路)
  证明: by
  rw [← Set.injOn_univ]; rw [← hp.setOfPred_support]
  exact h.injOn_support_of_isPath_map

Depends on / 依赖: Set.injOn_univ, h.injOn_support_of_isPath_map, hp.setOfPred_support, injOn_support_of_isPath_map, injOn_univ, setOfPred_support
-/
theorem IsHamiltonian.injective_of_isPath_map (hp : p.IsHamiltonian) (h : (p.map f).IsPath) :
    Function.Injective f := by
  rw [← Set.injOn_univ]; rw [← hp.setOfPred_support]
  exact h.injOn_support_of_isPath_map

/--
lemma `isHamiltonian_iff_isPath_and_length_eq` / 引理 `isHamiltonian_iff_isPath_and_length_eq`

English:
lemma isHamiltonian_iff_isPath_and_length_eq
  given: [Fintype α]
  proof: by
  by_cases! h : IsEmpty α
  · exact h.elim' a
  refine ⟨fun h => ⟨h.isPath, h.length_eq⟩, fun ⟨hp, h⟩ => ?_⟩
  have := p.isPath_iff_injective_get_support.mp hp
  refine isHamiltonian_iff_support_get_bijective.mpr ⟨this, this.surjective_of_finite ?_⟩
  refine (Fintype.equivFinOfCardEq ?_).symm
  simp_rw [length_support, h, Nat.sub_one_add_one Fintype.card_ne_zero]

中文:
引理 isHamiltonian_iff_isPath_and_length_eq
  条件: [有限类型 α]
  证明: by
  by_cases! h : IsEmpty α
  · exact h.elim' a
  refine ⟨fun h => ⟨h.isPath, h.length_eq⟩, fun ⟨hp, h⟩ => ?_⟩
  have := p.isPath_iff_injective_get_support.mp hp
  refine isHamiltonian_iff_support_get_bijective.mpr ⟨this, this.surjective_of_finite ?_⟩
  refine (Fintype.equivFinOfCardEq ?_).symm
  simp_rw [length_support, h, Nat.sub_one_add_one Fintype.card_ne_zero]

Depends on / 依赖: Fintype, Fintype.card_ne_zero, Fintype.equivFinOfCardEq, IsEmpty, Nat.sub_one_add_one, card_ne_zero, equivFinOfCardEq, h.elim, h.isPath, h.length_eq, isHamiltonian_iff_support_get_bijective, isHamiltonian_iff_support_get_bijective.mpr, isPath, isPath_iff_injective_get_support, length_eq, length_support, p.isPath_iff_injective_get_support.mp, simp_rw, sub_one_add_one, surjective_of_finite
-/
lemma isHamiltonian_iff_isPath_and_length_eq [Fintype α] :
    p.IsHamiltonian ↔ p.IsPath ∧ p.length = Fintype.card α - 1 := by
  by_cases! h : IsEmpty α
  · exact h.elim' a
  refine ⟨fun h => ⟨h.isPath, h.length_eq⟩, fun ⟨hp, h⟩ => ?_⟩
  have := p.isPath_iff_injective_get_support.mp hp
  refine isHamiltonian_iff_support_get_bijective.mpr ⟨this, this.surjective_of_finite ?_⟩
  refine (Fintype.equivFinOfCardEq ?_).symm
  simp_rw [length_support, h, Nat.sub_one_add_one Fintype.card_ne_zero]

/--
Definition of `IsHamiltonianCycle` / `IsHamiltonianCycle` 的定义

English:
structure IsHamiltonianCycle
  parameters: (p : G.Walk a a)
  extends: p.IsCycle
  axioms and operations (1):
    - isHamiltonian_tail : p.tail.IsHamiltonian

中文:
结构 是HamiltonianCycle
  参数: (p : G.途径 a a)
  继承: p.是环
  公理与运算 (1 个):
    - isHamiltonian_tail : p.tail.IsHamiltonian
-/
structure IsHamiltonianCycle (p : G.Walk a a) : Prop extends p.IsCycle where
  isHamiltonian_tail : p.tail.IsHamiltonian

variable {p : G.Walk a a}

/--
lemma `IsHamiltonianCycle.isCycle` / 引理 `IsHamiltonianCycle.isCycle`

English:
lemma IsHamiltonianCycle.isCycle
  given: (hp : p.IsHamiltonianCycle)
  statement: p.IsCycle
  proof: hp.toIsCycle

中文:
引理 是HamiltonianCycle.isCycle
  条件: (hp : p.是HamiltonianCycle)
  结论: p.是环
  证明: hp.toIsCycle

Depends on / 依赖: hp.toIsCycle, toIsCycle
-/
lemma IsHamiltonianCycle.isCycle (hp : p.IsHamiltonianCycle) : p.IsCycle :=
  hp.toIsCycle

/--
lemma `IsHamiltonianCycle.map` / 引理 `IsHamiltonianCycle.map`

English:
lemma IsHamiltonianCycle.map
  statement: (hf : Bijective f)
  proof: hp.isCycle.map hf.injective
  isHamiltonian_tail := by
    simp only [IsHamiltonian, hf.surjective.forall]
    intro x
    rcases p with (_ | ⟨y, p⟩)
    · cases hp.ne_nil rfl
    simp only [map_cons, getVert_cons_succ, tail_cons, support_copy, support_map]
    rw [List.count_map_of_injective _ _ hf.injective]
    simpa using hp.isHamiltonian_tail x

中文:
引理 是HamiltonianCycle.map
  结论: (hf : 双射 f)
  证明: hp.isCycle.map hf.injective
  isHamiltonian_tail := by
    simp only [IsHamiltonian, hf.surjective.forall]
    intro x
    rcases p with (_ | ⟨y, p⟩)
    · cases hp.ne_nil rfl
    simp only [map_cons, getVert_cons_succ, tail_cons, support_copy, support_map]
    rw [List.count_map_of_injective _ _ hf.injective]
    simpa using hp.isHamiltonian_tail x

Depends on / 依赖: hf.injective, hp.isCycle.map, injective, isCycle
-/
lemma IsHamiltonianCycle.map (hf : Bijective f)
    (hp : p.IsHamiltonianCycle) : (p.map f).IsHamiltonianCycle where
  toIsCycle := hp.isCycle.map hf.injective
  isHamiltonian_tail := by
    simp only [IsHamiltonian, hf.surjective.forall]
    intro x
    rcases p with (_ | ⟨y, p⟩)
    · cases hp.ne_nil rfl
    simp only [map_cons, getVert_cons_succ, tail_cons, support_copy, support_map]
    rw [List.count_map_of_injective _ _ hf.injective]
    simpa using hp.isHamiltonian_tail x

/--
lemma `IsHamiltonianCycle.finite` / 引理 `IsHamiltonianCycle.finite`

English:
lemma IsHamiltonianCycle.finite
  given: (hp : p.IsHamiltonianCycle)
  statement: Finite α
  proof: hp.isHamiltonian_tail.finite

中文:
引理 是HamiltonianCycle.finite
  条件: (hp : p.是HamiltonianCycle)
  结论: 有限 α
  证明: hp.isHamiltonian_tail.finite
-/
protected lemma IsHamiltonianCycle.finite (hp : p.IsHamiltonianCycle) : Finite α :=
  hp.isHamiltonian_tail.finite

/--
lemma `not_isHamiltonianCycle_of_infinite` / 引理 `not_isHamiltonianCycle_of_infinite`

English:
lemma not_isHamiltonianCycle_of_infinite
  given: [h : Infinite α]
  statement: ¬ p.IsHamiltonianCycle
  proof: by
  contrapose! h; exact h.finite

中文:
引理 not_isHamiltonianCycle_of_infinite
  条件: [h : 无限 α]
  结论: ¬ p.是HamiltonianCycle
  证明: by
  contrapose! h; exact h.finite
-/
@[simp] lemma not_isHamiltonianCycle_of_infinite [h : Infinite α] : ¬ p.IsHamiltonianCycle := by
  contrapose! h; exact h.finite

/--
lemma `isHamiltonianCycle_isCycle_and_isHamiltonian_tail` / 引理 `isHamiltonianCycle_isCycle_and_isHamiltonian_tail`

English:
lemma isHamiltonianCycle_isCycle_and_isHamiltonian_tail
  proof: ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩

中文:
引理 isHamiltonianCycle_isCycle_and_isHamiltonian_tail
  证明: ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
-/
lemma isHamiltonianCycle_isCycle_and_isHamiltonian_tail :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.tail.IsHamiltonian :=
  ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩

/--
lemma `isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one` / 引理 `isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one`

English:
lemma isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one
  proof: by
  simp +contextual [isHamiltonianCycle_isCycle_and_isHamiltonian_tail,
    IsHamiltonian, support_tail_of_not_nil, IsCycle.not_nil]

中文:
引理 isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one
  证明: by
  simp +contextual [isHamiltonianCycle_isCycle_and_isHamiltonian_tail,
    IsHamiltonian, support_tail_of_not_nil, IsCycle.not_nil]

Depends on / 依赖: IsCycle, IsCycle.not_nil, IsHamiltonian, contextual, isHamiltonianCycle_isCycle_and_isHamiltonian_tail, not_nil, support_tail_of_not_nil
-/
lemma isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ forall a, (support p).tail.count a = 1 := by
  simp +contextual [isHamiltonianCycle_isCycle_and_isHamiltonian_tail,
    IsHamiltonian, support_tail_of_not_nil, IsCycle.not_nil]

/--
lemma `IsHamiltonianCycle.mem_support` / 引理 `IsHamiltonianCycle.mem_support`

English:
lemma IsHamiltonianCycle.mem_support
  given: (hp : p.IsHamiltonianCycle) (b : α)
  proof: List.mem_of_mem_tail
    support_tail_of_not_nil p hp.1.not_nil ▸ hp.isHamiltonian_tail.mem_support _

中文:
引理 是HamiltonianCycle.mem_support
  条件: (hp : p.是HamiltonianCycle) (b : α)
  证明: List.mem_of_mem_tail
    support_tail_of_not_nil p hp.1.not_nil ▸ hp.isHamiltonian_tail.mem_support _

Depends on / 依赖: List.mem_of_mem_tail, hp.isHamiltonian_tail.mem_support, isHamiltonian_tail, mem_of_mem_tail, mem_support, not_nil, support_tail_of_not_nil
-/
lemma IsHamiltonianCycle.mem_support (hp : p.IsHamiltonianCycle) (b : α) :
    b in p.support :=
List.mem_of_mem_tail
    support_tail_of_not_nil p hp.1.not_nil ▸ hp.isHamiltonian_tail.mem_support _

/--
lemma `IsHamiltonianCycle.length_eq` / 引理 `IsHamiltonianCycle.length_eq`

English:
lemma IsHamiltonianCycle.length_eq
  given: [Fintype α] (hp : p.IsHamiltonianCycle)
  proof: by
  rw [← length_tail_add_one hp.not_nil]; rw [hp.isHamiltonian_tail.length_eq]; rw [Nat.sub_add_cancel]
  rw [Nat.succ_le_iff]; rw [Fintype.card_pos_iff]
  exact ⟨a⟩

中文:
引理 是HamiltonianCycle.length_eq
  条件: [有限类型 α] (hp : p.是HamiltonianCycle)
  证明: by
  rw [← length_tail_add_one hp.not_nil]; rw [hp.isHamiltonian_tail.length_eq]; rw [Nat.sub_add_cancel]
  rw [Nat.succ_le_iff]; rw [Fintype.card_pos_iff]
  exact ⟨a⟩

Depends on / 依赖: Fintype, Fintype.card_pos_iff, Nat.sub_add_cancel, Nat.succ_le_iff, card_pos_iff, hp.isHamiltonian_tail.length_eq, hp.not_nil, isHamiltonian_tail, length_eq, length_tail_add_one, not_nil, sub_add_cancel, succ_le_iff
-/
lemma IsHamiltonianCycle.length_eq [Fintype α] (hp : p.IsHamiltonianCycle) :
    p.length = Fintype.card α := by
  rw [← length_tail_add_one hp.not_nil]; rw [hp.isHamiltonian_tail.length_eq]; rw [Nat.sub_add_cancel]
  rw [Nat.succ_le_iff]; rw [Fintype.card_pos_iff]
  exact ⟨a⟩

/--
lemma `IsHamiltonianCycle.count_support_self` / 引理 `IsHamiltonianCycle.count_support_self`

English:
lemma IsHamiltonianCycle.count_support_self
  given: (hp : p.IsHamiltonianCycle)
  proof: by
  rw [← cons_tail_support]; rw [List.count_cons_self]; rw [← support_tail_of_not_nil _ hp.1.not_nil]; rw [hp.isHamiltonian_tail]

中文:
引理 是HamiltonianCycle.count_support_self
  条件: (hp : p.是HamiltonianCycle)
  证明: by
  rw [← cons_tail_support]; rw [List.count_cons_self]; rw [← support_tail_of_not_nil _ hp.1.not_nil]; rw [hp.isHamiltonian_tail]

Depends on / 依赖: List.count_cons_self, cons_tail_support, count_cons_self, hp.isHamiltonian_tail, isHamiltonian_tail, not_nil, support_tail_of_not_nil
-/
lemma IsHamiltonianCycle.count_support_self (hp : p.IsHamiltonianCycle) :
    p.support.count a = 2 := by
  rw [← cons_tail_support]; rw [List.count_cons_self]; rw [← support_tail_of_not_nil _ hp.1.not_nil]; rw [hp.isHamiltonian_tail]

/--
lemma `IsHamiltonianCycle.support_count_of_ne` / 引理 `IsHamiltonianCycle.support_count_of_ne`

English:
lemma IsHamiltonianCycle.support_count_of_ne
  given: (hp : p.IsHamiltonianCycle) (h : a != b)
  proof: by
  rw [← cons_support_tail hp.1.not_nil]; rw [List.count_cons_of_ne h]; rw [hp.isHamiltonian_tail]

中文:
引理 是HamiltonianCycle.support_count_of_ne
  条件: (hp : p.是HamiltonianCycle) (h : a != b)
  证明: by
  rw [← cons_support_tail hp.1.not_nil]; rw [List.count_cons_of_ne h]; rw [hp.isHamiltonian_tail]

Depends on / 依赖: List.count_cons_of_ne, cons_support_tail, count_cons_of_ne, hp.isHamiltonian_tail, isHamiltonian_tail, not_nil
-/
lemma IsHamiltonianCycle.support_count_of_ne (hp : p.IsHamiltonianCycle) (h : a != b) :
    p.support.count b = 1 := by
  rw [← cons_support_tail hp.1.not_nil]; rw [List.count_cons_of_ne h]; rw [hp.isHamiltonian_tail]

/--
lemma `isHamiltonianCycle_iff_isCycle_and_length_eq` / 引理 `isHamiltonianCycle_iff_isCycle_and_length_eq`

English:
lemma isHamiltonianCycle_iff_isCycle_and_length_eq
  given: [Fintype α]
  proof: by
  refine ⟨fun h => ⟨h.isCycle, h.length_eq⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, ?_⟩⟩
  refine isHamiltonian_iff_isPath_and_length_eq.mpr ⟨h₁.isPath_tail, ?_⟩
  grind [length_tail_add_one, IsCycle.not_nil]

@[simp]

中文:
引理 isHamiltonianCycle_iff_isCycle_and_length_eq
  条件: [有限类型 α]
  证明: by
  refine ⟨fun h => ⟨h.isCycle, h.length_eq⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, ?_⟩⟩
  refine isHamiltonian_iff_isPath_and_length_eq.mpr ⟨h₁.isPath_tail, ?_⟩
  grind [length_tail_add_one, IsCycle.not_nil]

@[simp]

Depends on / 依赖: IsCycle, IsCycle.not_nil, h.isCycle, h.length_eq, isCycle, isHamiltonian_iff_isPath_and_length_eq, isHamiltonian_iff_isPath_and_length_eq.mpr, isPath_tail, length_eq, length_tail_add_one, not_nil
-/
lemma isHamiltonianCycle_iff_isCycle_and_length_eq [Fintype α] :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.length = Fintype.card α := by
  refine ⟨fun h => ⟨h.isCycle, h.length_eq⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, ?_⟩⟩
  refine isHamiltonian_iff_isPath_and_length_eq.mpr ⟨h₁.isPath_tail, ?_⟩
  grind [length_tail_add_one, IsCycle.not_nil]

@[simp]
/--
lemma `isHamiltonianCycle_rotate` / 引理 `isHamiltonianCycle_rotate`

English:
lemma isHamiltonianCycle_rotate
  given: (hv : v in p.support)
  proof: by
  cases (finite_or_infinite α).symm
  · simp
  cases nonempty_fintype α
  simp [isHamiltonianCycle_iff_isCycle_and_length_eq]

protected alias ⟨IsHamiltonianCycle.of_rotate, IsHamiltonianCycle.rotate⟩ :=
  isHamiltonianCycle_rotate

中文:
引理 isHamiltonianCycle_rotate
  条件: (hv : v in p.support)
  证明: by
  cases (finite_or_infinite α).symm
  · simp
  cases nonempty_fintype α
  simp [isHamiltonianCycle_iff_isCycle_and_length_eq]

protected alias ⟨IsHamiltonianCycle.of_rotate, IsHamiltonianCycle.rotate⟩ :=
  isHamiltonianCycle_rotate

Depends on / 依赖: finite_or_infinite, isHamiltonianCycle_iff_isCycle_and_length_eq, nonempty_fintype
-/
lemma isHamiltonianCycle_rotate (hv : v in p.support) :
    (p.rotate v hv).IsHamiltonianCycle ↔ p.IsHamiltonianCycle := by
  cases (finite_or_infinite α).symm
  · simp
  cases nonempty_fintype α
  simp [isHamiltonianCycle_iff_isCycle_and_length_eq]

protected alias ⟨IsHamiltonianCycle.of_rotate, IsHamiltonianCycle.rotate⟩ :=
  isHamiltonianCycle_rotate

end Walk

variable [Fintype α]

/--
Definition of `IsHamiltonian` / `IsHamiltonian` 的定义

English:
definition IsHamiltonian
  signature: (G : SimpleGraph α)
  body: Fintype.card α != 1 -> exists a, exists p : G.Walk a a, p.IsHamiltonianCycle

中文:
定义 IsHamiltonian
  签名: (G : 简单图 α)
  定义体: Fintype.card α != 1 -> exists a, exists p : G.Walk a a, p.IsHamiltonianCycle

Depends on / 依赖: Fintype, Fintype.card, G.Walk, IsHamiltonianCycle, p.IsHamiltonianCycle
-/
def IsHamiltonian (G : SimpleGraph α) : Prop :=
  Fintype.card α != 1 -> exists a, exists p : G.Walk a a, p.IsHamiltonianCycle

/--
lemma `IsHamiltonian.exists_isHamiltonianCycle` / 引理 `IsHamiltonian.exists_isHamiltonianCycle`

English:
lemma IsHamiltonian.exists_isHamiltonianCycle
  given: [Nontrivial α] (hG : G.IsHamiltonian) (v : α)
  proof: by
obtain ⟨u, p, hp⟩ := hG Fintype.one_lt_card.ne'; exact ⟨p.rotate v hp.mem_support _, by simpa⟩

中文:
引理 IsHamiltonian.存在_isHamiltonianCycle
  条件: [非平凡 α] (hG : G.IsHamiltonian) (v : α)
  证明: by
obtain ⟨u, p, hp⟩ := hG Fintype.one_lt_card.ne'; exact ⟨p.rotate v hp.mem_support _, by simpa⟩

Depends on / 依赖: Fintype, Fintype.one_lt_card.ne, hp.mem_support, mem_support, one_lt_card, p.rotate, rotate
-/
lemma IsHamiltonian.exists_isHamiltonianCycle [Nontrivial α] (hG : G.IsHamiltonian) (v : α) :
    exists p : G.Walk v v, p.IsHamiltonianCycle := by
obtain ⟨u, p, hp⟩ := hG Fintype.one_lt_card.ne'; exact ⟨p.rotate v hp.mem_support _, by simpa⟩

/--
lemma `IsHamiltonian.mono` / 引理 `IsHamiltonian.mono`

English:
lemma IsHamiltonian.mono
  given: {H : SimpleGraph α} (hGH : G <= H) (hG : G.IsHamiltonian)
  proof: fun hα => let ⟨_, p, hp⟩ := hG hα; ⟨_, p.map .ofLE hGH, hp.map bijective_id⟩

中文:
引理 IsHamiltonian.mono
  条件: {H : 简单图 α} (hGH : G <= H) (hG : G.IsHamiltonian)
  证明: fun hα => let ⟨_, p, hp⟩ := hG hα; ⟨_, p.map .ofLE hGH, hp.map bijective_id⟩

Depends on / 依赖: bijective_id, hp.map, p.map
-/
lemma IsHamiltonian.mono {H : SimpleGraph α} (hGH : G <= H) (hG : G.IsHamiltonian) :
    H.IsHamiltonian :=
fun hα => let ⟨_, p, hp⟩ := hG hα; ⟨_, p.map .ofLE hGH, hp.map bijective_id⟩

/--
lemma `not_isHamiltonian_of_isEmpty` / 引理 `not_isHamiltonian_of_isEmpty`

English:
lemma not_isHamiltonian_of_isEmpty
  given: [IsEmpty α]
  statement: ¬G.IsHamiltonian
  proof: (IsEmpty.exists_iff.mp <| · <| by simp)

中文:
引理 not_isHamiltonian_of_isEmpty
  条件: [是空 α]
  结论: ¬G.IsHamiltonian
  证明: (IsEmpty.exists_iff.mp <| · <| by simp)

Depends on / 依赖: IsEmpty, IsEmpty.exists_iff.mp, exists_iff
-/
lemma not_isHamiltonian_of_isEmpty [IsEmpty α] : ¬G.IsHamiltonian :=
  (IsEmpty.exists_iff.mp <| · <| by simp)

/--
lemma `IsHamiltonian.connected` / 引理 `IsHamiltonian.connected`

English:
lemma IsHamiltonian.connected
  given: (hG : G.IsHamiltonian)
  statement: G.Connected where
  proof: by
    obtain rfl | hab := eq_or_ne a b
    · rfl
    have : Nontrivial α := ⟨a, b, hab⟩
    obtain ⟨_, p, hp⟩ := hG Fintype.one_lt_card.ne'
    have a_mem := hp.mem_support a
    have b_mem := hp.mem_support b
    exact ((p.takeUntil a a_mem).reverse.append <| p.takeUntil b b_mem).reachable
  nonempty := not_isEmpty_iff.mp fun _ => not_isHamiltonian_of_isEmpty hG

中文:
引理 IsHamiltonian.connected
  条件: (hG : G.IsHamiltonian)
  结论: G.连通 where
  证明: by
    obtain rfl | hab := eq_or_ne a b
    · rfl
    have : Nontrivial α := ⟨a, b, hab⟩
    obtain ⟨_, p, hp⟩ := hG Fintype.one_lt_card.ne'
    have a_mem := hp.mem_support a
    have b_mem := hp.mem_support b
    exact ((p.takeUntil a a_mem).reverse.append <| p.takeUntil b b_mem).reachable
  nonempty := not_isEmpty_iff.mp fun _ => not_isHamiltonian_of_isEmpty hG

Depends on / 依赖: Fintype, Fintype.one_lt_card.ne, Nontrivial, a_mem, append, b_mem, eq_or_ne, hp.mem_support, mem_support, nonempty, not_isEmpty_iff, not_isEmpty_iff.mp, not_isHamiltonian_of_isEmpty, one_lt_card, p.takeUntil, reachable, reverse, reverse.append, takeUntil
-/
lemma IsHamiltonian.connected (hG : G.IsHamiltonian) : G.Connected where
  preconnected a b := by
    obtain rfl | hab := eq_or_ne a b
    · rfl
    have : Nontrivial α := ⟨a, b, hab⟩
    obtain ⟨_, p, hp⟩ := hG Fintype.one_lt_card.ne'
    have a_mem := hp.mem_support a
    have b_mem := hp.mem_support b
    exact ((p.takeUntil a a_mem).reverse.append <| p.takeUntil b b_mem).reachable
  nonempty := not_isEmpty_iff.mp fun _ => not_isHamiltonian_of_isEmpty hG

/--
lemma `IsHamiltonian.of_card_eq_one` / 引理 `IsHamiltonian.of_card_eq_one`

English:
lemma IsHamiltonian.of_card_eq_one
  given: (h : Fintype.card α = 1)
  statement: G.IsHamiltonian
  proof: (· h |>.elim)

中文:
引理 IsHamiltonian.of_card_eq_one
  条件: (h : 有限类型.card α = 1)
  结论: G.IsHamiltonian
  证明: (· h |>.elim)
-/
lemma IsHamiltonian.of_card_eq_one (h : Fintype.card α = 1) : G.IsHamiltonian :=
  (· h |>.elim)

/--
lemma `not_isHamiltonian_of_card_eq_two` / 引理 `not_isHamiltonian_of_card_eq_two`

English:
lemma not_isHamiltonian_of_card_eq_two
  given: (h : Fintype.card α = 2)
  statement: ¬G.IsHamiltonian
  proof: by
  intro hG
have ⟨v, p, hp⟩ := hG by lia
  grind [hp.three_le_length, hp.length_eq]

@[simp]

中文:
引理 not_isHamiltonian_of_card_eq_two
  条件: (h : 有限类型.card α = 2)
  结论: ¬G.IsHamiltonian
  证明: by
  intro hG
have ⟨v, p, hp⟩ := hG by lia
  grind [hp.three_le_length, hp.length_eq]

@[simp]

Depends on / 依赖: hp.length_eq, hp.three_le_length, length_eq, three_le_length
-/
lemma not_isHamiltonian_of_card_eq_two (h : Fintype.card α = 2) : ¬G.IsHamiltonian := by
  intro hG
have ⟨v, p, hp⟩ := hG by lia
  grind [hp.three_le_length, hp.length_eq]

@[simp]
/--
lemma `not_isHamiltonian_bot_of_card_ne_one` / 引理 `not_isHamiltonian_bot_of_card_ne_one`

English:
lemma not_isHamiltonian_bot_of_card_ne_one
  given: (h : Fintype.card α != 1)
  proof: by
  intro hG
  have ⟨v, p, hp⟩ := hG h
  exact p.adj_snd hp.not_nil

中文:
引理 not_isHamiltonian_bot_of_card_ne_one
  条件: (h : 有限类型.card α != 1)
  证明: by
  intro hG
  have ⟨v, p, hp⟩ := hG h
  exact p.adj_snd hp.not_nil

Depends on / 依赖: adj_snd, hp.not_nil, not_nil, p.adj_snd
-/
lemma not_isHamiltonian_bot_of_card_ne_one (h : Fintype.card α != 1) :
    ¬(⊥ : SimpleGraph α).IsHamiltonian := by
  intro hG
  have ⟨v, p, hp⟩ := hG h
  exact p.adj_snd hp.not_nil

/--
lemma `IsHamiltonian.of_unique` / 引理 `IsHamiltonian.of_unique`

English:
lemma IsHamiltonian.of_unique
  given: [Unique α]
  statement: G.IsHamiltonian
  proof: of_card_eq_one Fintype.card_unique

中文:
引理 IsHamiltonian.of_unique
  条件: [唯一 α]
  结论: G.IsHamiltonian
  证明: of_card_eq_one Fintype.card_unique

Depends on / 依赖: Fintype, Fintype.card_unique, card_unique, of_card_eq_one
-/
lemma IsHamiltonian.of_unique [Unique α] : G.IsHamiltonian :=
of_card_eq_one Fintype.card_unique

/--
theorem `IsBridge.not_isHamiltonian` / 定理 `IsBridge.not_isHamiltonian`

English:
theorem IsBridge.not_isHamiltonian
  given: {e : Sym2 α} (he : G.IsBridge e)
  statement: ¬G.IsHamiltonian
  proof: by
  induction e with | h u v
  have := he.nontrivial
  intro hG
  obtain ⟨p, hp⟩ := hG.exists_isHamiltonianCycle u
  refine hp.isHamiltonian_tail.isPath.isTrail.not_mem_support_of_not_reachable
    (fun huv => he <| .trans ?_ huv) he (hp.isHamiltonian_tail.mem_support v)
  apply hp.isTrail.isEdgeReachable_two <;> simp

中文:
定理 IsBridge.not_isHamiltonian
  条件: {e : Sym2 α} (he : G.IsBridge e)
  结论: ¬G.IsHamiltonian
  证明: by
  induction e with | h u v
  have := he.nontrivial
  intro hG
  obtain ⟨p, hp⟩ := hG.exists_isHamiltonianCycle u
  refine hp.isHamiltonian_tail.isPath.isTrail.not_mem_support_of_not_reachable
    (fun huv => he <| .trans ?_ huv) he (hp.isHamiltonian_tail.mem_support v)
  apply hp.isTrail.isEdgeReachable_two <;> simp

Depends on / 依赖: exists_isHamiltonianCycle, hG.exists_isHamiltonianCycle, he.nontrivial, hp.isHamiltonian_tail.isPath.isTrail.not_mem_support_of_not_reachable, hp.isHamiltonian_tail.mem_support, hp.isTrail.isEdgeReachable_two, isEdgeReachable_two, isHamiltonian_tail, isPath, isTrail, mem_support, nontrivial, not_mem_support_of_not_reachable
-/
theorem IsBridge.not_isHamiltonian {e : Sym2 α} (he : G.IsBridge e) : ¬G.IsHamiltonian := by
  induction e with | h u v
  have := he.nontrivial
  intro hG
  obtain ⟨p, hp⟩ := hG.exists_isHamiltonianCycle u
  refine hp.isHamiltonian_tail.isPath.isTrail.not_mem_support_of_not_reachable
    (fun huv => he <| .trans ?_ huv) he (hp.isHamiltonian_tail.mem_support v)
  apply hp.isTrail.isEdgeReachable_two <;> simp

end SimpleGraph
