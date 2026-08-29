/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Perm.ConjAct
public import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.GroupTheory.Rank

/-!
# Centralizer of a permutation and cardinality of conjugacy classes in the symmetric groups

Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `Equiv.Perm α`.
Every `g : Equiv.Perm α` has a `g.cycleType : Multiset ℕ`.
By `Equiv.Perm.isConj_iff_cycleType_eq`,
two permutations are conjugate in `Equiv.Perm α` iff
their cycle types are equal.
To compute the cardinality of the conjugacy classes, we could use
a purely combinatorial approach and compute the number of permutations
with given cycle type but we resorted to a more algebraic approach
based on the study of the centralizer of a permutation `g`.

Given `g : Equiv.Perm α`, the conjugacy class of `g` is the orbit
of `g` under the action `ConjAct (Equiv.Perm α)`, and we use the
orbit-stabilizer theorem
(`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`) to reduce
the computation to the computation of the centralizer of `g`, the
subgroup of `Equiv.Perm α` consisting of all permutations which
commute with `g`. It is accessed here as `MulAction.stabilizer
(ConjAct (Equiv.Perm α)) g` and `Subgroup.centralizer_eq_comap_stabilizer`.

We compute this subgroup as follows.

* If `h : Subgroup.centralizer {g}`, then the action of `ConjAct.toConjAct h`
  by conjugation on `Equiv.Perm α` stabilizes `g.cycleFactorsFinset`.
  That induces an action of `Subgroup.centralizer {g}` on
  `g.cycleFactorsFinset` which is defined as an instance.

* This action defines a group morphism `Equiv.Perm.OnCycleFactors.toPermHom g`
  from `Subgroup.centralizer {g}` to `Equiv.Perm g.cycleFactorsFinset`.

* `Equiv.Perm.OnCycleFactors.range_toPermHom'` is the subgroup of
  `Equiv.Perm g.cycleFactorsFinset` consisting of permutations that
  preserve the cardinality of the support.

* `Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom'` shows that
  the range of `Equiv.Perm.OnCycleFactors.toPermHom g`
  is the subgroup `Equiv.Perm.OnCycleFactors.toPermHom_range' g`
  of `Equiv.Perm g.cycleFactorsFinset`.

This is shown by constructing a right inverse
`Equiv.Perm.Basis.toCentralizer`, as established by
`Equiv.Perm.Basis.toPermHom_apply_toCentralizer`.

* `Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom` computes the
  cardinality of `(Equiv.Perm.OnCycleFactors.toPermHom g).range`
  as a product of factorials.

* `Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff` proves that
  `k : Subgroup.centralizer {g}` belongs to the kernel of
  `Equiv.Perm.OnCycleFactors.toPermHom g` if and only if it commutes with
  each cycle of `g`. This is equivalent to the conjunction of two properties:
  * `k` preserves the set of fixed points of `g`;
  * on each cycle `c`, `k` acts as a power of that cycle.

This allows to give a description of the kernel of
`Equiv.Perm.OnCycleFactors.toPermHom g` as the product of a
symmetric group and of a product of cyclic groups. This analysis
starts with the morphism `Equiv.Perm.OnCycleFactors.kerParam`, its
injectivity `Equiv.Perm.OnCycleFactors.kerParam_injective`, its range
`Equiv.Perm.OnCycleFactors.kerParam_range_eq`, and its cardinality
`Equiv.Perm.OnCycleFactors.kerParam_range_card`.

* `Equiv.Perm.OnCycleFactors.sign_kerParam_apply_apply` computes the signature
  of the permutation induced given by `Equiv.Perm.OnCycleFactors.kerParam`.

* `Equiv.Perm.nat_card_centralizer g` computes the cardinality
  of the centralizer of `g`.

* `Equiv.Perm.card_isConj_mul_eq g` computes the cardinality
  of the conjugacy class of `g`.

* We now can compute the cardinality of the set of permutations with given cycle type.
  The condition for this cardinality to be zero is given by
  `Equiv.Perm.card_of_cycleType_eq_zero_iff`
  which is itself derived from `Equiv.Perm.exists_with_cycleType_iff`.

* `Equiv.Perm.card_of_cycleType_mul_eq m` and `Equiv.Perm.card_of_cycleType m`
  compute this cardinality.

-/

@[expose] public section

open scoped Finset Pointwise

namespace Equiv.Perm

open MulAction Equiv Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α] {g : Equiv.Perm α}

namespace OnCycleFactors

variable (g)

variable {g} in
/--
lemma `Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset` / 引理 `Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset`

English:
lemma Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset
  statement: {k c : Perm α}
  proof: by
  suffices (g.cycleFactorsFinset : Set (Perm α)) =
    (ConjAct.toConjAct k) • g.cycleFactorsFinset by
    rw [← Finset.mem_coe]; rw [this]
    simp only [Set.smul_mem_smul_set_iff, Finset.mem_coe, c_mem]
  have := cycleFactorsFinset_conj_eq (ConjAct.toConjAct (k : Perm α)) g
  rw [ConjAct.toConj

中文:
引理 子群.中心化子.toConjAct_smul_mem_cycleFactorsFinset
  结论: {k c : 置换 α}
  证明: by
  suffices (g.cycleFactorsFinset : Set (Perm α)) =
    (ConjAct.toConjAct k) • g.cycleFactorsFinset by
    rw [← Finset.mem_coe]; rw [this]
    simp only [Set.smul_mem_smul_set_iff, Finset.mem_coe, c_mem]
  have := cycleFactorsFinset_conj_eq (ConjAct.toConjAct (k : Perm α)) g
  rw [ConjAct.toConj

Depends on / 依赖: ConjAct, ConjAct.toConjAct, ConjAct.toConjAct_smul, Finset, Finset.coe_smul_finset, Finset.mem_coe, Set.smul_mem_smul_set_iff, c_mem, coe_smul_finset, conv_lhs, cycleFactorsFinset, cycleFactorsFinset_conj_eq, g.cycleFactorsFinset, k_mem, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff.mp, mem_coe, mul_assoc, mul_inv_cancel, mul_one
-/
lemma Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset {k c : Perm α}
    (k_mem : k in centralizer {g}) (c_mem : c in g.cycleFactorsFinset) :
    ConjAct.toConjAct k • c in g.cycleFactorsFinset := by
  suffices (g.cycleFactorsFinset : Set (Perm α)) =
    (ConjAct.toConjAct k) • g.cycleFactorsFinset by
    rw [← Finset.mem_coe]; rw [this]
    simp only [Set.smul_mem_smul_set_iff, Finset.mem_coe, c_mem]
  have := cycleFactorsFinset_conj_eq (ConjAct.toConjAct (k : Perm α)) g
  rw [ConjAct.toConjAct_smul]; rw [mem_centralizer_singleton_iff.mp k_mem]; rw [mul_assoc] at this
  simp only [mul_inv_cancel, mul_one] at this
  conv_lhs => rw [this]
  simp only [Finset.coe_smul_finset]

/-- The action by conjugation of `Subgroup.centralizer {g}`
  on the cycles of a given permutation -/
@[instance_reducible]
/--
Definition of `Subgroup.Centralizer.cycleFactorsFinset_mulAction` / `Subgroup.Centralizer.cycleFactorsFinset_mulAction` 的定义

English:
definition Subgroup.Centralizer.cycleFactorsFinset_mulAction
  signature: :
  body: ⟨ConjAct.toConjAct (k : Perm α) • c.val,
    Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k.prop c.prop⟩
  one_smul c := by
    rw [← Subtype.coe_inj]
    change ConjAct.toConjAct (1 : Perm α) • c.val = c
    simp only [map_one, one_smul]
  mul_smul k l c := by
    simp only [← Subtype

中文:
定义 子群.中心化子.cycleFactorsFinset_mulAction
  签名: :
  定义体: ⟨ConjAct.toConjAct (k : Perm α) • c.val,
    Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k.prop c.prop⟩
  one_smul c := by
    rw [← Subtype.coe_inj]
    change ConjAct.toConjAct (1 : Perm α) • c.val = c
    simp only [map_one, one_smul]
  mul_smul k l c := by
    simp only [← Subtype

Depends on / 依赖: ConjAct, ConjAct.toConjAct, c.val, toConjAct
-/
def Subgroup.Centralizer.cycleFactorsFinset_mulAction :
    MulAction (centralizer {g}) g.cycleFactorsFinset where
  smul k c := ⟨ConjAct.toConjAct (k : Perm α) • c.val,
    Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k.prop c.prop⟩
  one_smul c := by
    rw [← Subtype.coe_inj]
    change ConjAct.toConjAct (1 : Perm α) • c.val = c
    simp only [map_one, one_smul]
  mul_smul k l c := by
    simp only [← Subtype.coe_inj]
    change ConjAct.toConjAct (k * l : Perm α) • c.val =
      ConjAct.toConjAct (k : Perm α) • (ConjAct.toConjAct (l : Perm α)) • c.val
    simp only [map_mul, mul_smul]

/-- The conjugation action of `Subgroup.centralizer {g}` on `g.cycleFactorsFinset` -/
scoped instance : MulAction (centralizer {g}) (g.cycleFactorsFinset) :=
  (Subgroup.Centralizer.cycleFactorsFinset_mulAction g)

/--
Definition of `toPermHom` / `toPermHom` 的定义

English:
definition toPermHom
  body: MulAction.toPermHom (centralizer {g}) g.cycleFactorsFinset

中文:
定义 toPermHom
  定义体: MulAction.toPermHom (centralizer {g}) g.cycleFactorsFinset

Depends on / 依赖: MulAction, MulAction.toPermHom, centralizer, cycleFactorsFinset, g.cycleFactorsFinset, toPermHom
-/
def toPermHom := MulAction.toPermHom (centralizer {g}) g.cycleFactorsFinset

/--
theorem `centralizer_smul_def` / 定理 `centralizer_smul_def`

English:
theorem centralizer_smul_def
  given: (k : centralizer {g}) (c : g.cycleFactorsFinset)
  proof: rfl

@[simp]

中文:
定理 centralizer_smul_def
  条件: (k : centralizer {g}) (c : g.cycleFactorsFinset)
  证明: rfl

@[simp]
-/
theorem centralizer_smul_def (k : centralizer {g}) (c : g.cycleFactorsFinset) :
    k • c = ⟨k * c * k⁻¹,
      Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k.prop c.prop⟩ :=
  rfl

@[simp]
/--
theorem `val_centralizer_smul` / 定理 `val_centralizer_smul`

English:
theorem val_centralizer_smul
  given: (k : Subgroup.centralizer {g}) (c : g.cycleFactorsFinset)
  proof: rfl

中文:
定理 val_centralizer_smul
  条件: (k : 子群.centralizer {g}) (c : g.cycleFactorsFinset)
  证明: rfl
-/
theorem val_centralizer_smul (k : Subgroup.centralizer {g}) (c : g.cycleFactorsFinset) :
    ((k • c :) : Perm α) = k * c * k⁻¹ :=
  rfl

/--
theorem `toPermHom_apply` / 定理 `toPermHom_apply`

English:
theorem toPermHom_apply
  given: (k : centralizer {g}) (c : g.cycleFactorsFinset)
  proof: rfl

中文:
定理 toPermHom_apply
  条件: (k : centralizer {g}) (c : g.cycleFactorsFinset)
  证明: rfl
-/
theorem toPermHom_apply (k : centralizer {g}) (c : g.cycleFactorsFinset) :
    (toPermHom g k c) = k • c := rfl

/--
theorem `coe_toPermHom` / 定理 `coe_toPermHom`

English:
theorem coe_toPermHom
  given: (k : centralizer {g}) (c : g.cycleFactorsFinset)
  proof: rfl

中文:
定理 coe_toPermHom
  条件: (k : centralizer {g}) (c : g.cycleFactorsFinset)
  证明: rfl
-/
theorem coe_toPermHom (k : centralizer {g}) (c : g.cycleFactorsFinset) :
    (toPermHom g k c : Perm α) = k * c * (k : Perm α)⁻¹ := rfl

/--
Definition of `range_toPermHom'` / `range_toPermHom'` 的定义

English:
definition range_toPermHom'
  signature: : Subgroup (Perm g.cycleFactorsFinset) where
  body: {τ | forall c, #(τ c).val.support = #c.val.support}
  one_mem' := by simp
  mul_mem' hσ hτ := by
    simp only [Subtype.forall, Set.mem_ofPred_eq, coe_mul, Function.comp_apply]
    simp only [Subtype.forall, Set.mem_ofPred_eq] at hσ hτ
    intro c hc
    rw [hσ]; rw [hτ]
  inv_mem' hσ := by
    simp

中文:
定义 range_toPermHom'
  签名: : 子群 (置换 g.cycleFactorsFinset) where
  定义体: {τ | forall c, #(τ c).val.support = #c.val.support}
  one_mem' := by simp
  mul_mem' hσ hτ := by
    simp only [Subtype.forall, Set.mem_ofPred_eq, coe_mul, Function.comp_apply]
    simp only [Subtype.forall, Set.mem_ofPred_eq] at hσ hτ
    intro c hc
    rw [hσ]; rw [hτ]
  inv_mem' hσ := by
    simp

Depends on / 依赖: c.val.support, support, val.support
-/
def range_toPermHom' : Subgroup (Perm g.cycleFactorsFinset) where
  carrier := {τ | forall c, #(τ c).val.support = #c.val.support}
  one_mem' := by simp
  mul_mem' hσ hτ := by
    simp only [Subtype.forall, Set.mem_ofPred_eq, coe_mul, Function.comp_apply]
    simp only [Subtype.forall, Set.mem_ofPred_eq] at hσ hτ
    intro c hc
    rw [hσ]; rw [hτ]
  inv_mem' hσ := by
    simp only [Subtype.forall, Set.mem_ofPred_eq] at hσ ⊢
    intro c hc
    rw [← hσ _ (by simp)]
    simp

variable {g} in
/--
theorem `mem_range_toPermHom'_iff` / 定理 `mem_range_toPermHom'_iff`

English:
theorem mem_range_toPermHom'_iff
  given: {τ : Perm g.cycleFactorsFinset}
  proof: Iff.rfl

中文:
定理 mem_range_toPermHom'_iff
  条件: {τ : 置换 g.cycleFactorsFinset}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_range_toPermHom'_iff {τ : Perm g.cycleFactorsFinset} :
    τ in range_toPermHom' g ↔ forall c, #(τ c).val.support = #c.val.support :=
  Iff.rfl

variable (k : centralizer {g})

/--
theorem `mem_ker_toPermHom_iff` / 定理 `mem_ker_toPermHom_iff`

English:
theorem mem_ker_toPermHom_iff
  proof: by
  simp only [toPermHom, MonoidHom.mem_ker, DFunLike.ext_iff, Subtype.forall]
  refine forall₂_congr (fun _ _ => ?_)
  simp [← Subtype.coe_inj, commute_iff_eq, mul_inv_eq_iff_eq_mul]

中文:
定理 mem_ker_toPermHom_iff
  证明: by
  simp only [toPermHom, MonoidHom.mem_ker, DFunLike.ext_iff, Subtype.forall]
  refine forall₂_congr (fun _ _ => ?_)
  simp [← Subtype.coe_inj, commute_iff_eq, mul_inv_eq_iff_eq_mul]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, MonoidHom, MonoidHom.mem_ker, Subtype, Subtype.coe_inj, Subtype.forall, coe_inj, commute_iff_eq, ext_iff, mem_ker, mul_inv_eq_iff_eq_mul, toPermHom
-/
theorem mem_ker_toPermHom_iff :
    k in (toPermHom g).ker ↔ forall c in g.cycleFactorsFinset, Commute (k : Perm α) c := by
  simp only [toPermHom, MonoidHom.mem_ker, DFunLike.ext_iff, Subtype.forall]
  refine forall₂_congr (fun _ _ => ?_)
  simp [← Subtype.coe_inj, commute_iff_eq, mul_inv_eq_iff_eq_mul]

end OnCycleFactors

open OnCycleFactors

/--
Definition of `Basis` / `Basis` 的定义

English:
structure Basis
  parameters: (g : Equiv.Perm α)
  axioms and operations (2):
    - (toFun : g.cycleFactorsFinset -> α)
    - (mem_support_self' : forall (c : g.cycleFactorsFinset), toFun c in c.val.support)

中文:
结构 基
  参数: (g : 等价.置换 α)
  公理与运算 (2 个):
    - (toFun : g.cycleFactorsFinset -> α)
    - (mem_support_self' : 对任意 (c : g.cycleFactorsFinset), toFun c in c.val.support)
-/
structure Basis (g : Equiv.Perm α) where
  /-- A choice of elements in each cycle -/
  (toFun : g.cycleFactorsFinset -> α)
  /-- For each cycle, the chosen element belongs to the cycle -/
  (mem_support_self' : forall (c : g.cycleFactorsFinset), toFun c in c.val.support)

instance (g : Perm α) : FunLike (Basis g) g.cycleFactorsFinset α where
  coe a := a.toFun
  coe_injective a a' _ := by cases a; cases a'; congr

namespace Basis

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (g : Perm α)
  statement: Nonempty (Basis g)
  proof: by
  have (c : g.cycleFactorsFinset) : c.val.support.Nonempty :=
    IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.prop).1
  exact ⟨fun c => (this c).choose, fun c => (this c).choose_spec⟩

中文:
定理 nonempty
  条件: (g : 置换 α)
  结论: 非空 (基 g)
  证明: by
  have (c : g.cycleFactorsFinset) : c.val.support.Nonempty :=
    IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.prop).1
  exact ⟨fun c => (this c).choose, fun c => (this c).choose_spec⟩

Depends on / 依赖: IsCycle, IsCycle.nonempty_support, Nonempty, c.prop, c.val.support.Nonempty, choose_spec, cycleFactorsFinset, g.cycleFactorsFinset, mem_cycleFactorsFinset_iff, mem_cycleFactorsFinset_iff.mp, nonempty_support, support
-/
theorem nonempty (g : Perm α) : Nonempty (Basis g) := by
  have (c : g.cycleFactorsFinset) : c.val.support.Nonempty :=
    IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.prop).1
  exact ⟨fun c => (this c).choose, fun c => (this c).choose_spec⟩

variable (a : Basis g) (c : g.cycleFactorsFinset)

/--
theorem `mem_support_self` / 定理 `mem_support_self`

English:
theorem mem_support_self
  proof: a.mem_support_self' c

中文:
定理 mem_support_self
  证明: a.mem_support_self' c

Depends on / 依赖: a.mem_support_self, mem_support_self
-/
theorem mem_support_self :
    a c in c.val.support := a.mem_support_self' c

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: Function.Injective a
  proof: by
  intro c d h
  rw [← Subtype.coe_inj]
  apply g.cycleFactorsFinset_pairwise_disjoint.eq c.prop d.prop
  simp only [Disjoint, not_forall, not_or]
  use a c
  conv_rhs => rw [h]
  simp only [← Perm.mem_support, a.mem_support_self c, a.mem_support_self d, and_self]

中文:
定理 injective
  结论: 函数.单射 a
  证明: by
  intro c d h
  rw [← Subtype.coe_inj]
  apply g.cycleFactorsFinset_pairwise_disjoint.eq c.prop d.prop
  simp only [Disjoint, not_forall, not_or]
  use a c
  conv_rhs => rw [h]
  simp only [← Perm.mem_support, a.mem_support_self c, a.mem_support_self d, and_self]

Depends on / 依赖: Disjoint, Perm.mem_support, Subtype, Subtype.coe_inj, a.mem_support_self, and_self, c.prop, coe_inj, conv_rhs, cycleFactorsFinset_pairwise_disjoint, d.prop, g.cycleFactorsFinset_pairwise_disjoint.eq, mem_support, mem_support_self, not_forall, not_or
-/
theorem injective : Function.Injective a := by
  intro c d h
  rw [← Subtype.coe_inj]
  apply g.cycleFactorsFinset_pairwise_disjoint.eq c.prop d.prop
  simp only [Disjoint, not_forall, not_or]
  use a c
  conv_rhs => rw [h]
  simp only [← Perm.mem_support, a.mem_support_self c, a.mem_support_self d, and_self]

/--
theorem `cycleOf_eq` / 定理 `cycleOf_eq`

English:
theorem cycleOf_eq
  statement: g.cycleOf (a c) = c
  proof: (cycle_is_cycleOf (a.mem_support_self c) c.prop).symm

中文:
定理 cycleOf_eq
  结论: g.cycleOf (a c) = c
  证明: (cycle_is_cycleOf (a.mem_support_self c) c.prop).symm

Depends on / 依赖: a.mem_support_self, c.prop, cycle_is_cycleOf, mem_support_self
-/
theorem cycleOf_eq : g.cycleOf (a c) = c :=
  (cycle_is_cycleOf (a.mem_support_self c) c.prop).symm

/--
theorem `sameCycle` / 定理 `sameCycle`

English:
theorem sameCycle
  given: {x : α} (hx : g.cycleOf x in g.cycleFactorsFinset)
  proof: (mem_support_cycleOf_iff.mp (a.mem_support_self ⟨g.cycleOf x, hx⟩)).1.symm

中文:
定理 sameCycle
  条件: {x : α} (hx : g.cycleOf x in g.cycleFactorsFinset)
  证明: (mem_support_cycleOf_iff.mp (a.mem_support_self ⟨g.cycleOf x, hx⟩)).1.symm

Depends on / 依赖: a.mem_support_self, cycleOf, g.cycleOf, mem_support_cycleOf_iff, mem_support_cycleOf_iff.mp, mem_support_self
-/
theorem sameCycle {x : α} (hx : g.cycleOf x in g.cycleFactorsFinset) :
    g.SameCycle (a ⟨g.cycleOf x, hx⟩) x :=
  (mem_support_cycleOf_iff.mp (a.mem_support_self ⟨g.cycleOf x, hx⟩)).1.symm

variable (τ : range_toPermHom' g)

/--
Definition of `ofPermHomFun` / `ofPermHomFun` 的定义

English:
definition ofPermHomFun
  signature: (x : α)
  body: if hx : g.cycleOf x in g.cycleFactorsFinset
  then
    (g ^ (Nat.find (a.sameCycle hx).exists_nat_pow_eq))
      (a ((τ : Perm g.cycleFactorsFinset) ⟨g.cycleOf x, hx⟩))
  else x

中文:
定义 ofPermHomFun
  签名: (x : α)
  定义体: if hx : g.cycleOf x in g.cycleFactorsFinset
  then
    (g ^ (Nat.find (a.sameCycle hx).exists_nat_pow_eq))
      (a ((τ : Perm g.cycleFactorsFinset) ⟨g.cycleOf x, hx⟩))
  else x

Depends on / 依赖: Nat.find, a.sameCycle, cycleFactorsFinset, cycleOf, exists_nat_pow_eq, g.cycleFactorsFinset, g.cycleOf, sameCycle
-/
def ofPermHomFun (x : α) : α :=
  if hx : g.cycleOf x in g.cycleFactorsFinset
  then
    (g ^ (Nat.find (a.sameCycle hx).exists_nat_pow_eq))
      (a ((τ : Perm g.cycleFactorsFinset) ⟨g.cycleOf x, hx⟩))
  else x

/--
theorem `mem_fixedPoints_or_exists_zpow_eq` / 定理 `mem_fixedPoints_or_exists_zpow_eq`

English:
theorem mem_fixedPoints_or_exists_zpow_eq
  given: (x : α)
  proof: by
  rw [Classical.or_iff_not_imp_left]
  intro hx
  rw [Function.mem_fixedPoints_iff]; rw [← ne_eq]; rw [← mem_support]; rw [← cycleOf_mem_cycleFactorsFinset_iff] at hx
  refine ⟨⟨g.cycleOf x, hx⟩, ?_, (a.sameCycle hx)⟩
  rw [mem_support_cycleOf_iff]; rw [← cycleOf_mem_cycleFactorsFinset_iff]
  sim

中文:
定理 mem_fixedPoints_or_存在_zpow_eq
  条件: (x : α)
  证明: by
  rw [Classical.or_iff_not_imp_left]
  intro hx
  rw [Function.mem_fixedPoints_iff]; rw [← ne_eq]; rw [← mem_support]; rw [← cycleOf_mem_cycleFactorsFinset_iff] at hx
  refine ⟨⟨g.cycleOf x, hx⟩, ?_, (a.sameCycle hx)⟩
  rw [mem_support_cycleOf_iff]; rw [← cycleOf_mem_cycleFactorsFinset_iff]
  sim

Depends on / 依赖: Classical, Classical.or_iff_not_imp_left, Function, Function.mem_fixedPoints_iff, SameCycle, SameCycle.rfl, a.sameCycle, and_self, cycleOf, cycleOf_mem_cycleFactorsFinset_iff, g.cycleOf, mem_fixedPoints_iff, mem_support, mem_support_cycleOf_iff, ne_eq, or_iff_not_imp_left, sameCycle
-/
theorem mem_fixedPoints_or_exists_zpow_eq (x : α) :
    x in Function.fixedPoints g ∨
      exists (c : g.cycleFactorsFinset) (_ : x in c.val.support) (m : Int), (g ^ m) (a c) = x := by
  rw [Classical.or_iff_not_imp_left]
  intro hx
  rw [Function.mem_fixedPoints_iff]; rw [← ne_eq]; rw [← mem_support]; rw [← cycleOf_mem_cycleFactorsFinset_iff] at hx
  refine ⟨⟨g.cycleOf x, hx⟩, ?_, (a.sameCycle hx)⟩
  rw [mem_support_cycleOf_iff]; rw [← cycleOf_mem_cycleFactorsFinset_iff]
  simp [SameCycle.rfl, hx, and_self]

/--
theorem `ofPermHomFun_apply_of_cycleOf_mem` / 定理 `ofPermHomFun_apply_of_cycleOf_mem`

English:
theorem ofPermHomFun_apply_of_cycleOf_mem
  statement: {x : α} {c : g.cycleFactorsFinset}
  proof: by
  have hx' : c = g.cycleOf x := cycle_is_cycleOf hx (Subtype.prop c)
  have hx'' : g.cycleOf x in g.cycleFactorsFinset := hx' ▸ c.prop
  set n := Nat.find (a.sameCycle hx'').exists_nat_pow_eq
  have hn : (g ^ (n : Int)) (a c) = x := by
    rw [← Nat.find_spec (a.sameCycle hx'').exists_nat_pow_eq]

中文:
定理 ofPermHomFun_apply_of_cycleOf_mem
  结论: {x : α} {c : g.cycleFactorsFinset}
  证明: by
  have hx' : c = g.cycleOf x := cycle_is_cycleOf hx (Subtype.prop c)
  have hx'' : g.cycleOf x in g.cycleFactorsFinset := hx' ▸ c.prop
  set n := Nat.find (a.sameCycle hx'').exists_nat_pow_eq
  have hn : (g ^ (n : Int)) (a c) = x := by
    rw [← Nat.find_spec (a.sameCycle hx'').exists_nat_pow_eq]

Depends on / 依赖: IsCycleOn, IsCycleOn.zpow_apply_eq_zpow_apply, Nat.find, Nat.find_spec, Subtype, Subtype.coe_inj, Subtype.prop, a.sameCycle, c.prop, coe_inj, cycleFactorsFinset, cycleOf, cycle_is_cycleOf, exists_nat_pow_eq, find_spec, g.cycleFactorsFinset, g.cycleOf, isCycleOn_sup, ofPermHomFun, sameCycle
-/
theorem ofPermHomFun_apply_of_cycleOf_mem {x : α} {c : g.cycleFactorsFinset}
    (hx : x in c.val.support) {m : Int} (hm : (g ^ m) (a c) = x) :
    ofPermHomFun a τ x = (g ^ m) (a ((τ : Perm g.cycleFactorsFinset) c)) := by
  have hx' : c = g.cycleOf x := cycle_is_cycleOf hx (Subtype.prop c)
  have hx'' : g.cycleOf x in g.cycleFactorsFinset := hx' ▸ c.prop
  set n := Nat.find (a.sameCycle hx'').exists_nat_pow_eq
  have hn : (g ^ (n : Int)) (a c) = x := by
    rw [← Nat.find_spec (a.sameCycle hx'').exists_nat_pow_eq]; rw [zpow_natCast]
    congr
    rw [← Subtype.coe_inj]; rw [hx']
  suffices ofPermHomFun a τ x = (g ^ (n : Int)) (a ((τ : Perm g.cycleFactorsFinset) c)) by
    rw [this]; rw [IsCycleOn.zpow_apply_eq_zpow_apply
      (isCycleOn_support_of_mem_cycleFactorsFinset ((τ : Perm g.cycleFactorsFinset) c).prop)
      (mem_support_self a ((τ : Perm g.cycleFactorsFinset) c))]
    simp only [τ.prop c]
    rw [← IsCycleOn.zpow_apply_eq_zpow_apply
      (isCycleOn_support_of_mem_cycleFactorsFinset c.prop) (mem_support_self a c)]
    rw [hn]; rw [hm]
  simp only [ofPermHomFun, dif_pos hx'']
  congr
  exact hx'.symm

/--
theorem `ofPermHomFun_apply_of_mem_fixedPoints` / 定理 `ofPermHomFun_apply_of_mem_fixedPoints`

English:
theorem ofPermHomFun_apply_of_mem_fixedPoints
  given: {x : α} (hx : x in Function.fixedPoints g)
  proof: by
  rw [ofPermHomFun]; rw [dif_neg]
  rw [cycleOf_mem_cycleFactorsFinset_iff]; rw [notMem_support]
  exact hx

中文:
定理 ofPermHomFun_apply_of_mem_fixedPoints
  条件: {x : α} (hx : x in 函数.fixedPoints g)
  证明: by
  rw [ofPermHomFun]; rw [dif_neg]
  rw [cycleOf_mem_cycleFactorsFinset_iff]; rw [notMem_support]
  exact hx

Depends on / 依赖: cycleOf_mem_cycleFactorsFinset_iff, dif_neg, notMem_support, ofPermHomFun
-/
theorem ofPermHomFun_apply_of_mem_fixedPoints {x : α} (hx : x in Function.fixedPoints g) :
    ofPermHomFun a τ x = x := by
  rw [ofPermHomFun]; rw [dif_neg]
  rw [cycleOf_mem_cycleFactorsFinset_iff]; rw [notMem_support]
  exact hx

/--
theorem `ofPermHomFun_apply_mem_support_cycle_iff` / 定理 `ofPermHomFun_apply_mem_support_cycle_iff`

English:
theorem ofPermHomFun_apply_mem_support_cycle_iff
  given: {x : α} {c : g.cycleFactorsFinset}
  proof: by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨d, hd, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a τ hx]
    suffices forall (d : g.cycleFactorsFinset), x ∉ (d : Perm α).support by
      simp only [this]
    intro d hx'
    rw [Function.mem_fixedPoints_iff]; rw [← no

中文:
定理 ofPermHomFun_apply_mem_support_cycle_iff
  条件: {x : α} {c : g.cycleFactorsFinset}
  证明: by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨d, hd, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a τ hx]
    suffices forall (d : g.cycleFactorsFinset), x ∉ (d : Perm α).support by
      simp only [this]
    intro d hx'
    rw [Function.mem_fixedPoints_iff]; rw [← no

Depends on / 依赖: Function, Function.mem_fixedPoints_iff, cycleFactorsFinset, d.prop, g.cycleFactorsFinset, mem_cycleFactorsFinset_support_le, mem_fixedPoints_iff, mem_fixedPoints_or_exists_zpow_eq, notMem_support, ofPermHomFun_apply_of_cycleOf_mem, ofPermHomFun_apply_of_mem_fixedPoints, support, zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff
-/
theorem ofPermHomFun_apply_mem_support_cycle_iff {x : α} {c : g.cycleFactorsFinset} :
    ofPermHomFun a τ x in ((τ : Perm g.cycleFactorsFinset) c : Perm α).support ↔
      x in c.val.support := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨d, hd, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a τ hx]
    suffices forall (d : g.cycleFactorsFinset), x ∉ (d : Perm α).support by
      simp only [this]
    intro d hx'
    rw [Function.mem_fixedPoints_iff]; rw [← notMem_support] at hx
    apply hx
    exact mem_cycleFactorsFinset_support_le d.prop hx'
  · rw [ofPermHomFun_apply_of_cycleOf_mem a τ hd hm] --
    rw [zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
    by_cases h : c = d
    · simp only [h, hd, mem_support_self]
    · have H : Disjoint c.val d.val :=
        cycleFactorsFinset_pairwise_disjoint g c.prop d.prop (Subtype.coe_ne_coe.mpr h)
      have H' : Disjoint ((τ : Perm g.cycleFactorsFinset) c : Perm α)
        ((τ : Perm g.cycleFactorsFinset) d : Perm α) :=
        cycleFactorsFinset_pairwise_disjoint g ((τ : Perm g.cycleFactorsFinset) c).prop
          ((τ : Perm g.cycleFactorsFinset) d).prop (by
          intro h'; apply h
          simpa only [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] using h')
      rw [disjoint_iff_disjoint_support]; rw [Finset.disjoint_right] at H H'
      simp only [H hd, H' (mem_support_self a _)]

/--
theorem `ofPermHomFun_commute_zpow_apply` / 定理 `ofPermHomFun_commute_zpow_apply`

English:
theorem ofPermHomFun_commute_zpow_apply
  given: (x : α) (j : Int)
  proof: by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | hx)
  · rw [ofPermHomFun_apply_of_mem_fixedPoints a τ hx, ofPermHomFun_apply_of_mem_fixedPoints]
    rw [Function.mem_fixedPoints_iff]
    simp only [← mul_apply, ← zpow_one_add, add_comm]
    conv_rhs => rw [← hx, ← mul_apply, ← zpow_add_

中文:
定理 ofPermHomFun_commute_zpow_apply
  条件: (x : α) (j : 整数)
  证明: by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | hx)
  · rw [ofPermHomFun_apply_of_mem_fixedPoints a τ hx, ofPermHomFun_apply_of_mem_fixedPoints]
    rw [Function.mem_fixedPoints_iff]
    simp only [← mul_apply, ← zpow_one_add, add_comm]
    conv_rhs => rw [← hx, ← mul_apply, ← zpow_add_

Depends on / 依赖: Function, Function.mem_fixedPoints_iff, add_comm, conv_rhs, mem_fixedPoints_iff, mem_fixedPoints_or_exists_zpow_eq, mul_apply, ofPermHomFun_apply_of_cycleOf_mem, ofPermHomFun_apply_of_mem_fixedPoints, zpow_add, zpow_add_one, zpow_one_add
-/
theorem ofPermHomFun_commute_zpow_apply (x : α) (j : Int) :
    ofPermHomFun a τ ((g ^ j) x) = (g ^ j) (ofPermHomFun a τ x) := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | hx)
  · rw [ofPermHomFun_apply_of_mem_fixedPoints a τ hx, ofPermHomFun_apply_of_mem_fixedPoints]
    rw [Function.mem_fixedPoints_iff]
    simp only [← mul_apply, ← zpow_one_add, add_comm]
    conv_rhs => rw [← hx, ← mul_apply, ← zpow_add_one]
  · obtain ⟨c, hc, m, hm⟩ := hx
    have hm' : (g ^ (j + m)) (a c) = (g ^ j) x := by rw [zpow_add, mul_apply, hm]
    rw [ofPermHomFun_apply_of_cycleOf_mem a τ hc hm]; rw [ofPermHomFun_apply_of_cycleOf_mem a τ _ hm']; rw [← mul_apply]; rw [← zpow_add]
    exact zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff.mpr hc

/--
theorem `ofPermHomFun_mul` / 定理 `ofPermHomFun_mul`

English:
theorem ofPermHomFun_mul
  given: (σ τ : range_toPermHom' g) (x)
  proof: by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a _ hx]
  · simp only [ofPermHomFun_apply_of_cycleOf_mem a _ hc hm]
    rw [ofPermHomFun_apply_of_cycleOf_mem a _ _ rfl]
    · rfl
    · rw [zpow_apply_mem_support_of_mem

中文:
定理 ofPermHomFun_mul
  条件: (σ τ : range_toPermHom' g) (x)
  证明: by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a _ hx]
  · simp only [ofPermHomFun_apply_of_cycleOf_mem a _ hc hm]
    rw [ofPermHomFun_apply_of_cycleOf_mem a _ _ rfl]
    · rfl
    · rw [zpow_apply_mem_support_of_mem

Depends on / 依赖: mem_fixedPoints_or_exists_zpow_eq, mem_support_self, ofPermHomFun_apply_of_cycleOf_mem, ofPermHomFun_apply_of_mem_fixedPoints, zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff
-/
theorem ofPermHomFun_mul (σ τ : range_toPermHom' g) (x) :
    ofPermHomFun a (σ * τ) x = (ofPermHomFun a σ) (ofPermHomFun a τ x) := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a _ hx]
  · simp only [ofPermHomFun_apply_of_cycleOf_mem a _ hc hm]
    rw [ofPermHomFun_apply_of_cycleOf_mem a _ _ rfl]
    · rfl
    · rw [zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
      apply mem_support_self

/--
theorem `ofPermHomFun_one` / 定理 `ofPermHomFun_one`

English:
theorem ofPermHomFun_one
  given: (x : α)
  statement: (ofPermHomFun a 1) x = x
  proof: by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · rw [ofPermHomFun_apply_of_mem_fixedPoints a _ hx]
  · rw [ofPermHomFun_apply_of_cycleOf_mem a _ hc hm, OneMemClass.coe_one, coe_one, id_eq, hm]

中文:
定理 ofPermHomFun_one
  条件: (x : α)
  结论: (ofPermHomFun a 1) x = x
  证明: by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · rw [ofPermHomFun_apply_of_mem_fixedPoints a _ hx]
  · rw [ofPermHomFun_apply_of_cycleOf_mem a _ hc hm, OneMemClass.coe_one, coe_one, id_eq, hm]

Depends on / 依赖: OneMemClass, OneMemClass.coe_one, coe_one, id_eq, mem_fixedPoints_or_exists_zpow_eq, ofPermHomFun_apply_of_cycleOf_mem, ofPermHomFun_apply_of_mem_fixedPoints
-/
theorem ofPermHomFun_one (x : α) : (ofPermHomFun a 1) x = x := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · rw [ofPermHomFun_apply_of_mem_fixedPoints a _ hx]
  · rw [ofPermHomFun_apply_of_cycleOf_mem a _ hc hm, OneMemClass.coe_one, coe_one, id_eq, hm]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofPermHom` / `ofPermHom` 的定义

English:
definition ofPermHom
  signature: : range_toPermHom' g ->* Perm α where
  body: {
    toFun := ofPermHomFun a τ
    invFun := ofPermHomFun a τ⁻¹
    left_inv := fun x => by rw [← ofPermHomFun_mul, inv_mul_cancel, ofPermHomFun_one]
    right_inv := fun x => by rw [← ofPermHomFun_mul, mul_inv_cancel, ofPermHomFun_one] }
  map_one' := ext fun x => ofPermHomFun_one a x
  map_mul' :

中文:
定义 ofPermHom
  签名: : range_toPermHom' g ->* 置换 α where
  定义体: {
    toFun := ofPermHomFun a τ
    invFun := ofPermHomFun a τ⁻¹
    left_inv := fun x => by rw [← ofPermHomFun_mul, inv_mul_cancel, ofPermHomFun_one]
    right_inv := fun x => by rw [← ofPermHomFun_mul, mul_inv_cancel, ofPermHomFun_one] }
  map_one' := ext fun x => ofPermHomFun_one a x
  map_mul' :
-/
noncomputable def ofPermHom : range_toPermHom' g ->* Perm α where
  toFun τ := {
    toFun := ofPermHomFun a τ
    invFun := ofPermHomFun a τ⁻¹
    left_inv := fun x => by rw [← ofPermHomFun_mul, inv_mul_cancel, ofPermHomFun_one]
    right_inv := fun x => by rw [← ofPermHomFun_mul, mul_inv_cancel, ofPermHomFun_one] }
  map_one' := ext fun x => ofPermHomFun_one a x
  map_mul' := fun σ τ => ext fun x => by simp [mul_apply, ofPermHomFun_mul a σ τ x]

/--
theorem `ofPermHom_apply` / 定理 `ofPermHom_apply`

English:
theorem ofPermHom_apply
  given: (τ) (x)
  statement: a.ofPermHom τ x = a.ofPermHomFun τ x
  proof: rfl

中文:
定理 ofPermHom_apply
  条件: (τ) (x)
  结论: a.ofPermHom τ x = a.ofPermHomFun τ x
  证明: rfl
-/
theorem ofPermHom_apply (τ) (x) : a.ofPermHom τ x = a.ofPermHomFun τ x := rfl

/--
theorem `ofPermHom_support` / 定理 `ofPermHom_support`

English:
theorem ofPermHom_support
  proof: by
  ext x
  simp only [mem_support, Finset.mem_biUnion, ofPermHom_apply]
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a τ hx, ne_eq, not_true_eq_false, false_iff,
      ← mem_support]
    rintro ⟨c, -, hc⟩
    rw [Fun

中文:
定理 ofPermHom_support
  证明: by
  ext x
  simp only [mem_support, Finset.mem_biUnion, ofPermHom_apply]
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a τ hx, ne_eq, not_true_eq_false, false_iff,
      ← mem_support]
    rintro ⟨c, -, hc⟩
    rw [Fun

Depends on / 依赖: Finset, Finset.mem_biUnion, Function, Function.mem_fixedPoints_iff, a.injecti, c.prop, conv_lhs, false_iff, injecti, injective, injective.ne_iff, mem_biUnion, mem_cycleFactorsFinset_support_le, mem_fixedPoints_iff, mem_fixedPoints_or_exists_zpow_eq, mem_support, mem_support.mp, ne_eq, ne_iff, not_true_eq_false
-/
theorem ofPermHom_support :
    (ofPermHom a τ).support =
      (τ : Perm g.cycleFactorsFinset).support.biUnion (fun c => c.val.support) := by
  ext x
  simp only [mem_support, Finset.mem_biUnion, ofPermHom_apply]
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a τ hx, ne_eq, not_true_eq_false, false_iff,
      ← mem_support]
    rintro ⟨c, -, hc⟩
    rw [Function.mem_fixedPoints_iff] at hx
    exact mem_support.mp ((mem_cycleFactorsFinset_support_le c.prop) hc) hx
  · rw [ofPermHomFun_apply_of_cycleOf_mem a τ hc hm]
    conv_lhs => rw [← hm]
    rw [(g ^ m).injective.ne_iff]; rw [a.injective.ne_iff]; rw [not_iff_comm]
    by_cases H : (τ : Perm g.cycleFactorsFinset) c = c
    · simp only [H, iff_true]
      push Not
      intro d hd
      rw [← notMem_support]
      have := g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop
      rw [disjoint_iff_disjoint_support]; rw [Finset.disjoint_left] at this
      exact this (by lia) hc
    · simpa only [H, iff_false, not_not] using ⟨c, H, mem_support.mp hc⟩

/--
theorem `card_ofPermHom_support` / 定理 `card_ofPermHom_support`

English:
theorem card_ofPermHom_support
  proof: by
  rw [ofPermHom_support]; rw [Finset.card_biUnion]
  intro c _ d _ h
  apply Equiv.Perm.Disjoint.disjoint_support
  apply g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr h)

中文:
定理 card_ofPermHom_support
  证明: by
  rw [ofPermHom_support]; rw [Finset.card_biUnion]
  intro c _ d _ h
  apply Equiv.Perm.Disjoint.disjoint_support
  apply g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr h)

Depends on / 依赖: Disjoint, Equiv.Perm.Disjoint.disjoint_support, Finset, Finset.card_biUnion, Subtype, Subtype.coe_ne_coe.mpr, c.prop, card_biUnion, coe_ne_coe, cycleFactorsFinset_pairwise_disjoint, d.prop, disjoint_support, g.cycleFactorsFinset_pairwise_disjoint, ofPermHom_support
-/
theorem card_ofPermHom_support :
    #(ofPermHom a τ).support = ∑ c in (τ : Perm g.cycleFactorsFinset).support, #c.val.support := by
  rw [ofPermHom_support]; rw [Finset.card_biUnion]
  intro c _ d _ h
  apply Equiv.Perm.Disjoint.disjoint_support
  apply g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr h)

/--
theorem `ofPermHom_mem_centralizer` / 定理 `ofPermHom_mem_centralizer`

English:
theorem ofPermHom_mem_centralizer
  proof: by
  rw [mem_centralizer_singleton_iff]
  ext x
  simp only [mul_apply]
  exact ofPermHomFun_commute_zpow_apply a τ x 1

中文:
定理 ofPermHom_mem_centralizer
  证明: by
  rw [mem_centralizer_singleton_iff]
  ext x
  simp only [mul_apply]
  exact ofPermHomFun_commute_zpow_apply a τ x 1

Depends on / 依赖: mem_centralizer_singleton_iff, mul_apply, ofPermHomFun_commute_zpow_apply
-/
theorem ofPermHom_mem_centralizer :
    a.ofPermHom τ in centralizer {g} := by
  rw [mem_centralizer_singleton_iff]
  ext x
  simp only [mul_apply]
  exact ofPermHomFun_commute_zpow_apply a τ x 1

/--
Definition of `toCentralizer` / `toCentralizer` 的定义

English:
definition toCentralizer
  signature: :
  body: ⟨ofPermHom a τ, ofPermHom_mem_centralizer a τ⟩
  map_one' := by simp only [map_one, mk_eq_one]
  map_mul' σ τ := by simp only [map_mul, MulMemClass.mk_mul_mk]

中文:
定义 toCentralizer
  签名: :
  定义体: ⟨ofPermHom a τ, ofPermHom_mem_centralizer a τ⟩
  map_one' := by simp only [map_one, mk_eq_one]
  map_mul' σ τ := by simp only [map_mul, MulMemClass.mk_mul_mk]

Depends on / 依赖: Quotient, RingCon, RingCon.Quotient, ofPermHom, ofPermHom_mem_centralizer
-/
noncomputable def toCentralizer :
    range_toPermHom' g ->* centralizer {g} where
  toFun τ := ⟨ofPermHom a τ, ofPermHom_mem_centralizer a τ⟩
  map_one' := by simp only [map_one, mk_eq_one]
  map_mul' σ τ := by simp only [map_mul, MulMemClass.mk_mul_mk]

/--
theorem `toCentralizer_apply` / 定理 `toCentralizer_apply`

English:
theorem toCentralizer_apply
  given: (x)
  statement: (toCentralizer a τ : Perm α) x = ofPermHomFun a τ x
  proof: rfl

中文:
定理 toCentralizer_apply
  条件: (x)
  结论: (toCentralizer a τ : 置换 α) x = ofPermHomFun a τ x
  证明: rfl
-/
theorem toCentralizer_apply (x) : (toCentralizer a τ : Perm α) x = ofPermHomFun a τ x := rfl

/--
theorem `toCentralizer_equivariant` / 定理 `toCentralizer_equivariant`

English:
theorem toCentralizer_equivariant
  proof: by
  simp only [← Subtype.coe_inj, val_centralizer_smul, InvMemClass.coe_inv, mul_inv_eq_iff_eq_mul]
  ext x
  simp only [mul_apply, toCentralizer_apply]
  by_cases hx : x in c.val.support
  · rw [(mem_cycleFactorsFinset_iff.mp c.prop).2 x hx]
    have := ofPermHomFun_commute_zpow_apply a τ x 1
    

中文:
定理 toCentralizer_equivariant
  证明: by
  simp only [← Subtype.coe_inj, val_centralizer_smul, InvMemClass.coe_inv, mul_inv_eq_iff_eq_mul]
  ext x
  simp only [mul_apply, toCentralizer_apply]
  by_cases hx : x in c.val.support
  · rw [(mem_cycleFactorsFinset_iff.mp c.prop).2 x hx]
    have := ofPermHomFun_commute_zpow_apply a τ x 1
    

Depends on / 依赖: InvMemClass, InvMemClass.coe_inv, Quotient, RingCon, RingCon.Quotient, SMulCommClass, Subtype, Subtype.coe_inj, c.prop, c.val.support, coe_inj, coe_inv, cycleFactorsFinset, eq_comm, g.cycleFactorsFinset, mem_cycleFactorsFinset_iff, mem_cycleFactorsFinset_iff.mp, mul_apply, mul_inv_eq_iff_eq_mul, notMem_support
-/
theorem toCentralizer_equivariant :
    (toCentralizer a τ) • c = (τ : Perm g.cycleFactorsFinset) c := by
  simp only [← Subtype.coe_inj, val_centralizer_smul, InvMemClass.coe_inv, mul_inv_eq_iff_eq_mul]
  ext x
  simp only [mul_apply, toCentralizer_apply]
  by_cases hx : x in c.val.support
  · rw [(mem_cycleFactorsFinset_iff.mp c.prop).2 x hx]
    have := ofPermHomFun_commute_zpow_apply a τ x 1
    simp only [zpow_one] at this
    rw [this]; rw [← (mem_cycleFactorsFinset_iff.mp ((τ : Perm g.cycleFactorsFinset) c).prop).2]
    rw [ofPermHomFun_apply_mem_support_cycle_iff]
    exact hx
  · rw [notMem_support.mp hx, eq_comm, ← notMem_support,
      ofPermHomFun_apply_mem_support_cycle_iff]
    exact hx

/--
theorem `toPermHom_apply_toCentralizer` / 定理 `toPermHom_apply_toCentralizer`

English:
theorem toPermHom_apply_toCentralizer
  proof: by
  apply ext
  intro c
  rw [OnCycleFactors.toPermHom_apply]; rw [toCentralizer_equivariant]

中文:
定理 toPermHom_apply_toCentralizer
  证明: by
  apply ext
  intro c
  rw [OnCycleFactors.toPermHom_apply]; rw [toCentralizer_equivariant]

Depends on / 依赖: IsScalarTower, OnCycleFactors, OnCycleFactors.toPermHom_apply, Quotient, RingCon, RingCon.Quotient, toCentralizer_equivariant, toPermHom_apply
-/
theorem toPermHom_apply_toCentralizer :
    (toPermHom g) (toCentralizer a τ) = (τ : Perm g.cycleFactorsFinset) := by
  apply ext
  intro c
  rw [OnCycleFactors.toPermHom_apply]; rw [toCentralizer_equivariant]

end Basis

namespace OnCycleFactors

open Basis Nat

/--
theorem `mem_range_toPermHom_iff` / 定理 `mem_range_toPermHom_iff`

English:
theorem mem_range_toPermHom_iff
  given: {τ}
  statement: τ in (toPermHom g).range ↔
  proof: by
  constructor
  · rintro ⟨k, rfl⟩ c
    rw [coe_toPermHom]; rw [Equiv.Perm.support_conj]
    apply Finset.card_map
  · obtain ⟨a⟩ := Basis.nonempty g
    exact fun hτ => ⟨toCentralizer a ⟨τ, hτ⟩, toPermHom_apply_toCentralizer a ⟨τ, hτ⟩⟩

中文:
定理 mem_range_toPermHom_iff
  条件: {τ}
  结论: τ in (toPermHom g).range ↔
  证明: by
  constructor
  · rintro ⟨k, rfl⟩ c
    rw [coe_toPermHom]; rw [Equiv.Perm.support_conj]
    apply Finset.card_map
  · obtain ⟨a⟩ := Basis.nonempty g
    exact fun hτ => ⟨toCentralizer a ⟨τ, hτ⟩, toPermHom_apply_toCentralizer a ⟨τ, hτ⟩⟩

Depends on / 依赖: Basis.nonempty, Equiv.Perm.support_conj, Finset, Finset.card_map, Quotient, RingCon, RingCon.Quotient, card_map, coe_toPermHom, nonempty, support_conj, toCentralizer, toPermHom_apply_toCentralizer
-/
theorem mem_range_toPermHom_iff {τ} : τ in (toPermHom g).range ↔
    forall c, #(τ c).val.support = #c.val.support := by
  constructor
  · rintro ⟨k, rfl⟩ c
    rw [coe_toPermHom]; rw [Equiv.Perm.support_conj]
    apply Finset.card_map
  · obtain ⟨a⟩ := Basis.nonempty g
    exact fun hτ => ⟨toCentralizer a ⟨τ, hτ⟩, toPermHom_apply_toCentralizer a ⟨τ, hτ⟩⟩

/--
theorem `mem_range_toPermHom_iff'` / 定理 `mem_range_toPermHom_iff'`

English:
theorem mem_range_toPermHom_iff'
  given: {τ}
  statement: τ in (toPermHom g).range ↔
  proof: by
  rw [mem_range_toPermHom_iff]; rw [funext_iff]
  simp only [Subtype.forall, Function.comp_apply]

中文:
定理 mem_range_toPermHom_iff'
  条件: {τ}
  结论: τ in (toPermHom g).range ↔
  证明: by
  rw [mem_range_toPermHom_iff]; rw [funext_iff]
  simp only [Subtype.forall, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, Subtype, Subtype.forall, comp_apply, funext_iff, mem_range_toPermHom_iff
-/
theorem mem_range_toPermHom_iff' {τ} : τ in (toPermHom g).range ↔
    (fun (c : g.cycleFactorsFinset) => #c.val.support) ∘ τ =
      fun (c : g.cycleFactorsFinset) => #c.val.support := by
  rw [mem_range_toPermHom_iff]; rw [funext_iff]
  simp only [Subtype.forall, Function.comp_apply]

/--
theorem `range_toPermHom_eq_range_toPermHom'` / 定理 `range_toPermHom_eq_range_toPermHom'`

English:
theorem range_toPermHom_eq_range_toPermHom'
  proof: by
  ext τ
  rw [mem_range_toPermHom_iff]; rw [mem_range_toPermHom'_iff]

中文:
定理 range_toPermHom_eq_range_toPermHom'
  证明: by
  ext τ
  rw [mem_range_toPermHom_iff]; rw [mem_range_toPermHom'_iff]

Depends on / 依赖: _iff, mem_range_toPermHom, mem_range_toPermHom_iff
-/
theorem range_toPermHom_eq_range_toPermHom' :
    (toPermHom g).range = range_toPermHom' g := by
  ext τ
  rw [mem_range_toPermHom_iff]; rw [mem_range_toPermHom'_iff]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `nat_card_range_toPermHom` / 定理 `nat_card_range_toPermHom`

English:
theorem nat_card_range_toPermHom
  proof: by
  classical
  set sc := fun (c : g.cycleFactorsFinset) => #c.val.support with hsc
  suffices Fintype.card (toPermHom g).range =
    Fintype.card { k : Perm g.cycleFactorsFinset | sc ∘ k = sc } by
    simp only [Nat.card_eq_fintype_card, this, Set.coe_ofPred, DomMulAct.stabilizer_card', hsc,
     

中文:
定理 nat_card_range_toPermHom
  证明: by
  classical
  set sc := fun (c : g.cycleFactorsFinset) => #c.val.support with hsc
  suffices Fintype.card (toPermHom g).range =
    Fintype.card { k : Perm g.cycleFactorsFinset | sc ∘ k = sc } by
    simp only [Nat.card_eq_fintype_card, this, Set.coe_ofPred, DomMulAct.stabilizer_card', hsc,
     

Depends on / 依赖: CycleType, CycleType.count_def, DomMulAct, DomMulAct.stabilizer_card, Finset, Finset.mem_attach, Finset.mem_image, Finset.prod_congr, Finset.univ_eq_attach, Fintype, Fintype.card, Multiset, Multiset.mem_toFinset, Nat.card_eq_fintype_card, Set.coe_ofPred, Subtype, Subtype.exists, c.val.support, card_eq_fintype_card, classical
-/
theorem nat_card_range_toPermHom :
    Nat.card (toPermHom g).range =
      ∏ n in g.cycleType.toFinset, (g.cycleType.count n)! := by
  classical
  set sc := fun (c : g.cycleFactorsFinset) => #c.val.support with hsc
  suffices Fintype.card (toPermHom g).range =
    Fintype.card { k : Perm g.cycleFactorsFinset | sc ∘ k = sc } by
    simp only [Nat.card_eq_fintype_card, this, Set.coe_ofPred, DomMulAct.stabilizer_card', hsc,
      Finset.univ_eq_attach]
    simp_rw [← CycleType.count_def]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_image, Finset.mem_attach,
        true_and, Subtype.exists, exists_prop, Multiset.mem_toFinset]
    simp only [cycleType_def, Function.comp_apply, Multiset.mem_map, Finset.mem_val]
  simp only [Fintype.card_eq_nat_card]
  congr
  ext
  rw [mem_range_toPermHom_iff']; rw [Set.mem_ofPred_eq]

section Kernel
/- Here, we describe the kernel of `g.OnCycleFactors.toPermHom` -/

variable (g) in
/--
Definition of `kerParam` / `kerParam` 的定义

English:
definition kerParam
  signature: : (Perm (Function.fixedPoints g)) ×
  body: MonoidHom.noncommCoprod ofSubtype (Subgroup.noncommPiCoprod g.pairwise_commute_of_mem_zpowers)
    g.commute_ofSubtype_noncommPiCoprod

中文:
定义 kerParam
  签名: : (置换 (函数.fixedPoints g)) ×
  定义体: MonoidHom.noncommCoprod ofSubtype (Subgroup.noncommPiCoprod g.pairwise_commute_of_mem_zpowers)
    g.commute_ofSubtype_noncommPiCoprod

Depends on / 依赖: MonoidHom, MonoidHom.noncommCoprod, Subgroup, Subgroup.noncommPiCoprod, commute_ofSubtype_noncommPiCoprod, g.commute_ofSubtype_noncommPiCoprod, g.pairwise_commute_of_mem_zpowers, noncommCoprod, noncommPiCoprod, ofSubtype, pairwise_commute_of_mem_zpowers
-/
def kerParam : (Perm (Function.fixedPoints g)) ×
    ((c : g.cycleFactorsFinset) -> Subgroup.zpowers c.val) ->* Perm α :=
  MonoidHom.noncommCoprod ofSubtype (Subgroup.noncommPiCoprod g.pairwise_commute_of_mem_zpowers)
    g.commute_ofSubtype_noncommPiCoprod

set_option backward.isDefEq.respectTransparency false in
/--
theorem `kerParam_apply` / 定理 `kerParam_apply`

English:
theorem kerParam_apply
  statement: {u : Perm (Function.fixedPoints g)}
  proof: by
  split_ifs with hx
  · have hx' := hx
    rw [cycleOf_mem_cycleFactorsFinset_iff]; rw [mem_support]; rw [Ne]; rw [← Function.mem_fixedPoints_iff] at hx'
    rw [kerParam]; rw [MonoidHom.noncommCoprod_apply']; rw [mul_apply]; rw [ofSubtype_apply_of_not_mem u hx']; rw [noncommPiCoprod_apply]; rw [

中文:
定理 kerParam_apply
  结论: {u : 置换 (函数.fixedPoints g)}
  证明: by
  split_ifs with hx
  · have hx' := hx
    rw [cycleOf_mem_cycleFactorsFinset_iff]; rw [mem_support]; rw [Ne]; rw [← Function.mem_fixedPoints_iff] at hx'
    rw [kerParam]; rw [MonoidHom.noncommCoprod_apply']; rw [mul_apply]; rw [ofSubtype_apply_of_not_mem u hx']; rw [noncommPiCoprod_apply]; rw [

Depends on / 依赖: Finset, Finset.mem_univ, Finset.noncommProd_erase_mul, Function, Function.mem_fixedPoints_iff, MonoidHom, MonoidHom.noncommCoprod_apply, contrapose, cycleOf, cycleOf_mem_cycleFactorsFinset_iff, g.cycleOf, kerParam, mem_fixedPoints_iff, mem_support, mem_support_of_mem_noncommProd_support, mem_univ, mul_apply, noncommCoprod_apply, noncommPiCoprod_apply, noncommProd_erase_mul
-/
theorem kerParam_apply {u : Perm (Function.fixedPoints g)}
    {v : (c : g.cycleFactorsFinset) -> Subgroup.zpowers c.val} {x : α} :
    kerParam g (u, v) x =
    if hx : g.cycleOf x in g.cycleFactorsFinset
    then (v ⟨g.cycleOf x, hx⟩ : Perm α) x
    else ofSubtype u x := by
  split_ifs with hx
  · have hx' := hx
    rw [cycleOf_mem_cycleFactorsFinset_iff]; rw [mem_support]; rw [Ne]; rw [← Function.mem_fixedPoints_iff] at hx'
    rw [kerParam]; rw [MonoidHom.noncommCoprod_apply']; rw [mul_apply]; rw [ofSubtype_apply_of_not_mem u hx']; rw [noncommPiCoprod_apply]; rw [← Finset.noncommProd_erase_mul _ (Finset.mem_univ ⟨g.cycleOf x]; rw [hx⟩)]; rw [mul_apply]; rw [← notMem_support]
    contrapose hx'
    obtain ⟨a, ha1, ha2⟩ := mem_support_of_mem_noncommProd_support hx'
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Ne, Subtype.ext_iff] at ha1
    have key := cycleFactorsFinset_pairwise_disjoint g a.2 hx ha1
    rw [disjoint_iff_disjoint_support]; rw [Finset.disjoint_left] at key
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (v a).2
    replace ha2 := key (support_zpow_le a.1 k (hk ▸ ha2))
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (v ⟨g.cycleOf x, hx⟩).2
    rwa [← hk, zpow_apply_mem_support, notMem_support, cycleOf_apply_self] at ha2
  · rw [cycleOf_mem_cycleFactorsFinset_iff] at hx
    rw [kerParam]; rw [MonoidHom.noncommCoprod_apply]; rw [mul_apply]; rw [Equiv.apply_eq_iff_eq]; rw [← notMem_support]
    contrapose hx
    obtain ⟨a, -, ha⟩ := mem_support_of_mem_noncommProd_support
      (comm := fun a ha b hb h => g.pairwise_commute_of_mem_zpowers h (v a) (v b) (v a).2 (v b).2) hx
    exact support_zpowers_of_mem_cycleFactorsFinset_le (v a) ha

/--
theorem `kerParam_injective` / 定理 `kerParam_injective`

English:
theorem kerParam_injective
  given: (g : Perm α)
  statement: Function.Injective (kerParam g)
  proof: by
  rw [kerParam]; rw [MonoidHom.noncommCoprod_injective]
  refine ⟨ofSubtype_injective, ?_, ?_⟩
  · apply MonoidHom.injective_noncommPiCoprod_of_iSupIndep
    · intro a
      simp only [range_subtype, ne_eq]
      simp only [zpowers_eq_closure, ← closure_iUnion]
      apply disjoint_closure_of_dis

中文:
定理 kerParam_injective
  条件: (g : 置换 α)
  结论: 函数.单射 (kerParam g)
  证明: by
  rw [kerParam]; rw [MonoidHom.noncommCoprod_injective]
  refine ⟨ofSubtype_injective, ?_, ?_⟩
  · apply MonoidHom.injective_noncommPiCoprod_of_iSupIndep
    · intro a
      simp only [range_subtype, ne_eq]
      simp only [zpowers_eq_closure, ← closure_iUnion]
      apply disjoint_closure_of_dis

Depends on / 依赖: MonoidHom, MonoidHom.injective_noncommPiCoprod_of_iSupIndep, MonoidHom.noncommCoprod_injective, Subtype, Subtype.ext_iff, closure_iUnion, cycleFactorsFinset_pairwise_disjoint, disjoint_closure_of_disjoint_support, disjoint_iff_disjoint_support, ext_iff, injective_noncommPiCoprod_of_iSupIndep, kerParam, ne_comm, ne_comm.mp, ne_eq, noncommCoprod_injective, ofSubtype_injective, range_subtype, zpowers_eq_closure
-/
theorem kerParam_injective (g : Perm α) : Function.Injective (kerParam g) := by
  rw [kerParam]; rw [MonoidHom.noncommCoprod_injective]
  refine ⟨ofSubtype_injective, ?_, ?_⟩
  · apply MonoidHom.injective_noncommPiCoprod_of_iSupIndep
    · intro a
      simp only [range_subtype, ne_eq]
      simp only [zpowers_eq_closure, ← closure_iUnion]
      apply disjoint_closure_of_disjoint_support
      rintro - ⟨-⟩ - ⟨-, ⟨b, rfl⟩, -, ⟨h, rfl⟩, ⟨-⟩⟩
      rw [← disjoint_iff_disjoint_support]
      apply cycleFactorsFinset_pairwise_disjoint g a.2 b.2
      simp only [ne_eq, ← Subtype.ext_iff]
      exact ne_comm.mp h
    · exact fun i => subtype_injective _
  · rw [noncommPiCoprod_range, ← ofSubtype.range.closure_eq]
    simp only [zpowers_eq_closure, ← closure_iUnion]
    apply disjoint_closure_of_disjoint_support
    rintro - ⟨a, rfl⟩ - ⟨-, ⟨b, rfl⟩, ⟨-⟩⟩
    exact (ofSubtype_support_disjoint a).mono_right (mem_cycleFactorsFinset_support_le b.2)

/--
theorem `kerParam_range_eq` / 定理 `kerParam_range_eq`

English:
theorem kerParam_range_eq
  proof: by
  apply le_antisymm
  · rw [kerParam, MonoidHom.noncommCoprod_range, sup_le_iff, noncommPiCoprod_range, iSup_le_iff]
    simp only [zpowers_le]
    constructor
    · rintro - ⟨a, rfl⟩
      refine ⟨⟨ofSubtype a, ?_⟩, ?_, rfl⟩
      · rw [mem_centralizer_singleton_iff]
        exact Disjoint.commu

中文:
定理 kerParam_range_eq
  证明: by
  apply le_antisymm
  · rw [kerParam, MonoidHom.noncommCoprod_range, sup_le_iff, noncommPiCoprod_range, iSup_le_iff]
    simp only [zpowers_le]
    constructor
    · rintro - ⟨a, rfl⟩
      refine ⟨⟨ofSubtype a, ?_⟩, ?_, rfl⟩
      · rw [mem_centralizer_singleton_iff]
        exact Disjoint.commu

Depends on / 依赖: Disjoint, Disjoint.commute, MonoidHom, MonoidHom.noncommCoprod_range, Perm.ext, Subtype, Subtype.ext, commute, disjoint_iff_disjoint_support, disjoint_iff_disjoint_support.mpr, iSup_le_iff, kerParam, le_antisymm, mem_centralizer_singleton_iff, mem_cycleFactorsFinset_support_le, mono_right, noncommCoprod_range, noncommPiCoprod_range, ofSubtype, ofSubtype_support_disjoint
-/
theorem kerParam_range_eq :
    (kerParam g).range = (toPermHom g).ker.map (Subgroup.subtype _) := by
  apply le_antisymm
  · rw [kerParam, MonoidHom.noncommCoprod_range, sup_le_iff, noncommPiCoprod_range, iSup_le_iff]
    simp only [zpowers_le]
    constructor
    · rintro - ⟨a, rfl⟩
      refine ⟨⟨ofSubtype a, ?_⟩, ?_, rfl⟩
      · rw [mem_centralizer_singleton_iff]
        exact Disjoint.commute (disjoint_iff_disjoint_support.mpr (ofSubtype_support_disjoint a))
      · exact Perm.ext fun x => Subtype.ext (disjoint_iff_disjoint_support.mpr
          ((ofSubtype_support_disjoint a).mono_right
            (mem_cycleFactorsFinset_support_le x.2))).commute.mul_inv_cancel
    · intro i
      refine ⟨⟨i, mem_centralizer_singleton_iff.mpr (self_mem_cycle_factors_commute i.2)⟩, ?_, rfl⟩
      exact Perm.ext fun x => Subtype.ext (cycleFactorsFinset_mem_commute' g i.2 x.2).mul_inv_cancel
  · rintro - ⟨p, hp, rfl⟩
    simp only [coe_subtype]
    set u : Perm (Function.fixedPoints g) :=
      subtypePerm p (fun x => apply_mem_fixedPoints_iff_mem_of_mem_centralizer p.2)
    simp only [SetLike.mem_coe, mem_ker_toPermHom_iff, IsCycle.forall_commute_iff] at hp
    set v : (c : g.cycleFactorsFinset) -> (Subgroup.zpowers c.val) :=
      fun c => ⟨ofSubtype
          (p.1.subtypePerm (Classical.choose (hp c.val c.prop))),
            Classical.choose_spec (hp c.val c.prop)⟩
    use (u, v)
    ext x
    rw [kerParam_apply]
    split_ifs with hx
    · rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support] at hx
      rw [ofSubtype_apply_of_mem]; rw [subtypePerm_apply]
      rwa [mem_support, cycleOf_apply_self, ne_eq]
    · rw [cycleOf_mem_cycleFactorsFinset_iff, notMem_support] at hx
      rwa [ofSubtype_apply_of_mem, subtypePerm_apply]

/--
theorem `kerParam_range_le_centralizer` / 定理 `kerParam_range_le_centralizer`

English:
theorem kerParam_range_le_centralizer
  proof: by
  rw [kerParam_range_eq]
  exact map_subtype_le (toPermHom g).ker

中文:
定理 kerParam_range_le_centralizer
  证明: by
  rw [kerParam_range_eq]
  exact map_subtype_le (toPermHom g).ker

Depends on / 依赖: kerParam_range_eq, map_subtype_le, toPermHom
-/
theorem kerParam_range_le_centralizer :
    (kerParam g).range <= Subgroup.centralizer {g} := by
  rw [kerParam_range_eq]
  exact map_subtype_le (toPermHom g).ker

/--
theorem `kerParam_range_card` / 定理 `kerParam_range_card`

English:
theorem kerParam_range_card
  given: (g : Equiv.Perm α)
  proof: by
  rw [Fintype.card_coeSort_range (kerParam_injective g)]
  rw [Fintype.card_prod]; rw [Fintype.card_perm]; rw [Fintype.card_pi]; rw [card_fixedPoints]
  apply congr_arg
  rw [Finset.univ_eq_attach]; rw [g.cycleFactorsFinset.prod_attach (fun i => Fintype.card (zpowers i))]; rw [cycleType]; rw [Fin

中文:
定理 kerParam_range_card
  条件: (g : 等价.置换 α)
  证明: by
  rw [Fintype.card_coeSort_range (kerParam_injective g)]
  rw [Fintype.card_prod]; rw [Fintype.card_perm]; rw [Fintype.card_pi]; rw [card_fixedPoints]
  apply congr_arg
  rw [Finset.univ_eq_attach]; rw [g.cycleFactorsFinset.prod_attach (fun i => Fintype.card (zpowers i))]; rw [cycleType]; rw [Fin

Depends on / 依赖: Finset, Finset.prod_congr, Finset.prod_map_val, Finset.univ_eq_attach, Fintype, Fintype.card, Fintype.card_coeSort_range, Fintype.card_perm, Fintype.card_pi, Fintype.card_prod, Fintype.card_zpowers, Function, Function.comp_apply, card_coeSort_range, card_fixedPoints, card_perm, card_pi, card_prod, card_zpowers, comp_apply
-/
theorem kerParam_range_card (g : Equiv.Perm α) :
    Fintype.card (kerParam g).range = (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod := by
  rw [Fintype.card_coeSort_range (kerParam_injective g)]
  rw [Fintype.card_prod]; rw [Fintype.card_perm]; rw [Fintype.card_pi]; rw [card_fixedPoints]
  apply congr_arg
  rw [Finset.univ_eq_attach]; rw [g.cycleFactorsFinset.prod_attach (fun i => Fintype.card (zpowers i))]; rw [cycleType]; rw [Finset.prod_map_val]
  refine Finset.prod_congr rfl (fun x hx => ?_)
  rw [Fintype.card_zpowers]; rw [(mem_cycleFactorsFinset_iff.mp hx).1.orderOf]; rw [Function.comp_apply]

end Kernel

section Sign

open Function

variable {a : Type*} (g : Perm α) (k : Perm (fixedPoints g))
    (v : (c : g.cycleFactorsFinset) -> Subgroup.zpowers (c : Perm α))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sign_kerParam_apply_apply` / 定理 `sign_kerParam_apply_apply`

English:
theorem sign_kerParam_apply_apply
  proof: by
  rw [kerParam]; rw [MonoidHom.noncommCoprod_apply]; rw [← Prod.fst_mul_snd ⟨k]; rw [v⟩]; rw [Prod.mk_mul_mk]; rw [mul_one]; rw [one_mul]; rw [map_mul]; rw [sign_ofSubtype]; rw [Finset.univ_eq_attach]; rw [mul_right_inj]; rw [← MonoidHom.comp_apply]; rw [Subgroup.noncommPiCoprod]; rw [MonoidHom.c

中文:
定理 sign_kerParam_apply_apply
  证明: by
  rw [kerParam]; rw [MonoidHom.noncommCoprod_apply]; rw [← Prod.fst_mul_snd ⟨k]; rw [v⟩]; rw [Prod.mk_mul_mk]; rw [mul_one]; rw [one_mul]; rw [map_mul]; rw [sign_ofSubtype]; rw [Finset.univ_eq_attach]; rw [mul_right_inj]; rw [← MonoidHom.comp_apply]; rw [Subgroup.noncommPiCoprod]; rw [MonoidHom.c

Depends on / 依赖: Finset, Finset.noncommProd_eq_prod, Finset.univ_eq_attach, MonoidHom, MonoidHom.comp_apply, MonoidHom.comp_noncommPiCoprod, MonoidHom.noncommCoprod_apply, MonoidHom.noncommPiCoprod_apply, Prod.fst_mul_snd, Prod.mk_mul_mk, Subgroup, Subgroup.noncommPiCoprod, comp_apply, comp_noncommPiCoprod, fst_mul_snd, kerParam, map_mul, mk_mul_mk, mul_one, mul_right_inj
-/
theorem sign_kerParam_apply_apply :
    sign (kerParam g ⟨k, v⟩) = sign k * ∏ c, sign (v c).val := by
  rw [kerParam]; rw [MonoidHom.noncommCoprod_apply]; rw [← Prod.fst_mul_snd ⟨k]; rw [v⟩]; rw [Prod.mk_mul_mk]; rw [mul_one]; rw [one_mul]; rw [map_mul]; rw [sign_ofSubtype]; rw [Finset.univ_eq_attach]; rw [mul_right_inj]; rw [← MonoidHom.comp_apply]; rw [Subgroup.noncommPiCoprod]; rw [MonoidHom.comp_noncommPiCoprod _]; rw [MonoidHom.noncommPiCoprod_apply]; rw [Finset.univ_eq_attach]; rw [Finset.noncommProd_eq_prod]
  simp

/--
theorem `cycleType_kerParam_apply_apply` / 定理 `cycleType_kerParam_apply_apply`

English:
theorem cycleType_kerParam_apply_apply
  proof: by
  let U := SetLike.coe (Finset.univ : Finset { x // x in g.cycleFactorsFinset })
  have hU : U.Pairwise fun i j => (v i).val.Disjoint (v j).val := fun c _ d _ h => by
    obtain ⟨m, hm⟩ := (v c).prop
    obtain ⟨n, hn⟩ := (v d).prop
    simp only [← hm, ← hn]
    apply Disjoint.zpow_disjoint_zpow

中文:
定理 cycleType_kerParam_apply_apply
  证明: by
  let U := SetLike.coe (Finset.univ : Finset { x // x in g.cycleFactorsFinset })
  have hU : U.Pairwise fun i j => (v i).val.Disjoint (v j).val := fun c _ d _ h => by
    obtain ⟨m, hm⟩ := (v c).prop
    obtain ⟨n, hn⟩ := (v d).prop
    simp only [← hm, ← hn]
    apply Disjoint.zpow_disjoint_zpow

Depends on / 依赖: Disjoint, Disjoint.zpow_disjoint_zpow, Finset, Finset.univ, MonoidHom, MonoidHom.noncommCoprod_apply, Pairwise, Prod.fst_mul_snd, Prod.mk_mul_mk, SetLike, SetLike.coe, Subtype, Subtype.coe_ne_coe.mpr, U.Pairwise, c.prop, coe_ne_coe, cycleFactorsFinset, cycleFactorsFinset_pairwise_disjoint, d.prop, fst_mul_snd
-/
theorem cycleType_kerParam_apply_apply :
    cycleType (kerParam g ⟨k, v⟩) = cycleType k + ∑ c, (v c).val.cycleType := by
  let U := SetLike.coe (Finset.univ : Finset { x // x in g.cycleFactorsFinset })
  have hU : U.Pairwise fun i j => (v i).val.Disjoint (v j).val := fun c _ d _ h => by
    obtain ⟨m, hm⟩ := (v c).prop
    obtain ⟨n, hn⟩ := (v d).prop
    simp only [← hm, ← hn]
    apply Disjoint.zpow_disjoint_zpow
    apply cycleFactorsFinset_pairwise_disjoint g c.prop d.prop
    exact Subtype.coe_ne_coe.mpr h
  rw [kerParam]; rw [MonoidHom.noncommCoprod_apply]; rw [← Prod.fst_mul_snd ⟨k]; rw [v⟩]; rw [Prod.mk_mul_mk]; rw [mul_one]; rw [one_mul]; rw [Finset.univ_eq_attach]; rw [Disjoint.cycleType_mul (disjoint_ofSubtype_noncommPiCoprod g k v)]; rw [Subgroup.noncommPiCoprod_apply]; rw [Disjoint.cycleType_noncommProd hU]; rw [Finset.univ_eq_attach]
  exact congr_arg₂ _ cycleType_ofSubtype rfl

end Sign

end OnCycleFactors

open Nat

variable (g : Perm α)

-- Should one parenthesize the product ?
/--
theorem `nat_card_centralizer` / 定理 `nat_card_centralizer`

English:
theorem nat_card_centralizer
  proof: by
  rw [← (toPermHom g).ker.card_mul_index]; rw [index_ker]; rw [nat_card_range_toPermHom]; rw [← kerParam_range_card]; rw [← Nat.card_eq_fintype_card]; rw [kerParam_range_eq]; rw [card_subtype]

中文:
定理 nat_card_centralizer
  证明: by
  rw [← (toPermHom g).ker.card_mul_index]; rw [index_ker]; rw [nat_card_range_toPermHom]; rw [← kerParam_range_card]; rw [← Nat.card_eq_fintype_card]; rw [kerParam_range_eq]; rw [card_subtype]

Depends on / 依赖: Nat.card_eq_fintype_card, card_eq_fintype_card, card_mul_index, card_subtype, index_ker, ker.card_mul_index, kerParam_range_card, kerParam_range_eq, nat_card_range_toPermHom, toPermHom
-/
theorem nat_card_centralizer :
    Nat.card (centralizer {g}) =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!) := by
  rw [← (toPermHom g).ker.card_mul_index]; rw [index_ker]; rw [nat_card_range_toPermHom]; rw [← kerParam_range_card]; rw [← Nat.card_eq_fintype_card]; rw [kerParam_range_eq]; rw [card_subtype]

/--
theorem `card_isConj_mul_eq` / 定理 `card_isConj_mul_eq`

English:
theorem card_isConj_mul_eq
  proof: by
  classical
  rw [Nat.card_eq_fintype_card]; rw [← nat_card_centralizer g]
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]; rw [Nat.card_eq_fintype_card]
  convert! MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Perm α)) g
  · ext h
    simp only [Set.mem_ofPred_eq, Con

中文:
定理 card_isConj_mul_eq
  证明: by
  classical
  rw [Nat.card_eq_fintype_card]; rw [← nat_card_centralizer g]
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]; rw [Nat.card_eq_fintype_card]
  convert! MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Perm α)) g
  · ext h
    simp only [Set.mem_ofPred_eq, Con

Depends on / 依赖: ConjAct, ConjAct.card, ConjAct.mem_orbit_conjAct, Fintype, Fintype.card_perm, MulAction, MulAction.card_orbit_mul_card_stabilizer_eq_card_group, Nat.card_eq_fintype_card, Set.mem_ofPred_eq, Subgroup, Subgroup.nat_card_centralizer_nat_card_stabilizer, card_eq_fintype_card, card_orbit_mul_card_stabilizer_eq_card_group, card_perm, classical, convert, isConj_comm, mem_ofPred_eq, mem_orbit_conjAct, nat_card_centralizer
-/
theorem card_isConj_mul_eq :
    Nat.card {h : Perm α | IsConj g h} *
      ((Fintype.card α - g.cycleType.sum)! *
      g.cycleType.prod *
      (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!)) =
    (Fintype.card α)! := by
  classical
  rw [Nat.card_eq_fintype_card]; rw [← nat_card_centralizer g]
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]; rw [Nat.card_eq_fintype_card]
  convert! MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Perm α)) g
  · ext h
    simp only [Set.mem_ofPred_eq, ConjAct.mem_orbit_conjAct, isConj_comm]
  · rw [ConjAct.card, Fintype.card_perm]

/--
theorem `card_isConj_eq` / 定理 `card_isConj_eq`

English:
theorem card_isConj_eq
  proof: by
  rw [← card_isConj_mul_eq g]; rw [Nat.div_eq_of_eq_mul_left _]
  · rfl
  -- This is the cardinal of the centralizer
  · rw [← nat_card_centralizer g]
    apply Nat.card_pos

中文:
定理 card_isConj_eq
  证明: by
  rw [← card_isConj_mul_eq g]; rw [Nat.div_eq_of_eq_mul_left _]
  · rfl
  -- This is the cardinal of the centralizer
  · rw [← nat_card_centralizer g]
    apply Nat.card_pos

Depends on / 依赖: Nat.div_eq_of_eq_mul_left, card_isConj_mul_eq, div_eq_of_eq_mul_left
-/
theorem card_isConj_eq :
    Nat.card {h : Perm α | IsConj g h} =
      (Fintype.card α)! /
        ((Fintype.card α - g.cycleType.sum)! *
          g.cycleType.prod *
          (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!)) := by
  rw [← card_isConj_mul_eq g]; rw [Nat.div_eq_of_eq_mul_left _]
  · rfl
  -- This is the cardinal of the centralizer
  · rw [← nat_card_centralizer g]
    apply Nat.card_pos

variable (α)

/--
theorem `card_of_cycleType_eq_zero_iff` / 定理 `card_of_cycleType_eq_zero_iff`

English:
theorem card_of_cycleType_eq_zero_iff
  given: {m : Multiset Nat}
  proof: by
  rw [Finset.card_eq_zero]; rw [Finset.filter_eq_empty_iff]; rw [← exists_with_cycleType_iff]; rw [not_exists]
  simp

中文:
定理 card_of_cycleType_eq_zero_iff
  条件: {m : Multiset 自然数}
  证明: by
  rw [Finset.card_eq_zero]; rw [Finset.filter_eq_empty_iff]; rw [← exists_with_cycleType_iff]; rw [not_exists]
  simp

Depends on / 依赖: Finset, Finset.card_eq_zero, Finset.filter_eq_empty_iff, card_eq_zero, exists_with_cycleType_iff, filter_eq_empty_iff, not_exists
-/
theorem card_of_cycleType_eq_zero_iff {m : Multiset Nat} :
    #({g | g.cycleType = m} : Finset (Perm α)) = 0
      ↔ ¬ ((m.sum <= Fintype.card α ∧ forall a in m, 2 <= a)) := by
  rw [Finset.card_eq_zero]; rw [Finset.filter_eq_empty_iff]; rw [← exists_with_cycleType_iff]; rw [not_exists]
  simp

/--
theorem `card_of_cycleType_mul_eq` / 定理 `card_of_cycleType_mul_eq`

English:
theorem card_of_cycleType_mul_eq
  given: (m : Multiset Nat)
  proof: by
  split_ifs with hm
  · -- nonempty case
    classical
    obtain ⟨g, rfl⟩ := (exists_with_cycleType_iff α).mpr hm
    convert! card_isConj_mul_eq g
    simp_rw [Set.coe_ofPred, Nat.card_eq_fintype_card, ← Fintype.card_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, ← isConj_iff_cycleTyp

中文:
定理 card_of_cycleType_mul_eq
  条件: (m : Multiset 自然数)
  证明: by
  split_ifs with hm
  · -- nonempty case
    classical
    obtain ⟨g, rfl⟩ := (exists_with_cycleType_iff α).mpr hm
    convert! card_isConj_mul_eq g
    simp_rw [Set.coe_ofPred, Nat.card_eq_fintype_card, ← Fintype.card_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, ← isConj_iff_cycleTyp

Depends on / 依赖: Finset, Finset.mem_filter, Finset.mem_univ, Fintype, Fintype.card_coe, Nat.card_eq_fintype_card, Set.coe_ofPred, card_coe, card_eq_fintype_card, card_isConj_mul_eq, card_of_cycleType_eq_zero_iff, classical, coe_ofPred, convert, exists_with_cycleType_iff, isConj_comm, isConj_iff_cycleType_eq, mem_filter, mem_univ, nonempty
-/
theorem card_of_cycleType_mul_eq (m : Multiset Nat) :
    #({g | g.cycleType = m} : Finset (Perm α)) *
      ((Fintype.card α - m.sum)! * m.prod * (∏ n in m.toFinset, (m.count n)!)) =
      if (m.sum <= Fintype.card α ∧ forall a in m, 2 <= a) then (Fintype.card α)! else 0 := by
  split_ifs with hm
  · -- nonempty case
    classical
    obtain ⟨g, rfl⟩ := (exists_with_cycleType_iff α).mpr hm
    convert! card_isConj_mul_eq g
    simp_rw [Set.coe_ofPred, Nat.card_eq_fintype_card, ← Fintype.card_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, ← isConj_iff_cycleType_eq, isConj_comm (g := g)]
  · -- empty case
    rw [(card_of_cycleType_eq_zero_iff α).mpr hm]; rw [zero_mul]

/--
theorem `card_of_cycleType` / 定理 `card_of_cycleType`

English:
theorem card_of_cycleType
  given: (m : Multiset Nat)
  proof: by
  split_ifs with hm
  · -- nonempty case
    apply symm
    apply Nat.div_eq_of_eq_mul_left
· have : 0 < m.prod := Multiset.prod_pos fun a ha => zero_lt_two.trans_le (hm.2 a ha)
      positivity
    rw [card_of_cycleType_mul_eq]; rw [if_pos hm]
  · -- empty case
    exact (card_of_cycleType_eq_ze

中文:
定理 card_of_cycleType
  条件: (m : Multiset 自然数)
  证明: by
  split_ifs with hm
  · -- nonempty case
    apply symm
    apply Nat.div_eq_of_eq_mul_left
· have : 0 < m.prod := Multiset.prod_pos fun a ha => zero_lt_two.trans_le (hm.2 a ha)
      positivity
    rw [card_of_cycleType_mul_eq]; rw [if_pos hm]
  · -- empty case
    exact (card_of_cycleType_eq_ze

Depends on / 依赖: Multiset, Multiset.prod_pos, Nat.div_eq_of_eq_mul_left, card_of_cycleType_eq_zero_iff, card_of_cycleType_mul_eq, div_eq_of_eq_mul_left, if_pos, m.prod, nonempty, prod_pos, split_ifs, trans_le, zero_lt_two, zero_lt_two.trans_le
-/
theorem card_of_cycleType (m : Multiset Nat) :
    #({g | g.cycleType = m} : Finset (Perm α)) =
      if m.sum <= Fintype.card α ∧ forall a in m, 2 <= a then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! * m.prod * (∏ n in m.toFinset, (m.count n)!))
      else 0 := by
  split_ifs with hm
  · -- nonempty case
    apply symm
    apply Nat.div_eq_of_eq_mul_left
· have : 0 < m.prod := Multiset.prod_pos fun a ha => zero_lt_two.trans_le (hm.2 a ha)
      positivity
    rw [card_of_cycleType_mul_eq]; rw [if_pos hm]
  · -- empty case
    exact (card_of_cycleType_eq_zero_iff α).mpr hm

open Fintype in
variable {α} in
/--
lemma `card_of_cycleType_singleton` / 引理 `card_of_cycleType_singleton`

English:
lemma card_of_cycleType_singleton
  given: {n : Nat} (hn' : 2 <= n) (hα : n <= card α)
  proof: by
  have hn₀ : n != 0 := by lia
  have aux : n ! = (n - 1)! * n := by rw [mul_comm, mul_factorial_pred hn₀]
  rw [mul_comm]; rw [← Nat.mul_left_inj hn₀]; rw [mul_assoc]; rw [← aux]; rw [← Nat.mul_left_inj (factorial_ne_zero _)]; rw [Nat.choose_mul_factorial_mul_factorial hα]; rw [mul_assoc]
  simpa

中文:
引理 card_of_cycleType_singleton
  条件: {n : 自然数} (hn' : 2 <= n) (hα : n <= card α)
  证明: by
  have hn₀ : n != 0 := by lia
  have aux : n ! = (n - 1)! * n := by rw [mul_comm, mul_factorial_pred hn₀]
  rw [mul_comm]; rw [← Nat.mul_left_inj hn₀]; rw [mul_assoc]; rw [← aux]; rw [← Nat.mul_left_inj (factorial_ne_zero _)]; rw [Nat.choose_mul_factorial_mul_factorial hα]; rw [mul_assoc]
  simpa

Depends on / 依赖: Nat.choose_mul_factorial_mul_factorial, Nat.mul_left_inj, card_of_cycleType_mul_eq, choose_mul_factorial_mul_factorial, factorial_ne_zero, if_pos, ite_and, mul_assoc, mul_comm, mul_factorial_pred, mul_left_inj
-/
lemma card_of_cycleType_singleton {n : Nat} (hn' : 2 <= n) (hα : n <= card α) :
    #({g | g.cycleType = {n}} : Finset (Perm α)) = (n - 1)! * (choose (card α) n) := by
  have hn₀ : n != 0 := by lia
  have aux : n ! = (n - 1)! * n := by rw [mul_comm, mul_factorial_pred hn₀]
  rw [mul_comm]; rw [← Nat.mul_left_inj hn₀]; rw [mul_assoc]; rw [← aux]; rw [← Nat.mul_left_inj (factorial_ne_zero _)]; rw [Nat.choose_mul_factorial_mul_factorial hα]; rw [mul_assoc]
  simpa [ite_and, if_pos hα, if_pos hn', mul_comm _ n, mul_assoc]
    using card_of_cycleType_mul_eq α {n}

end Equiv.Perm
