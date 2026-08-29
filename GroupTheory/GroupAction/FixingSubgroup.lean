/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!

# Fixing submonoid, fixing subgroup of an action

In the presence of an action of a monoid or a group,
this file defines the fixing submonoid or the fixing subgroup,
and relates it to the set of fixed points via a Galois connection.

## Main definitions

* `fixingSubmonoid M s` : in the presence of `MulAction M α` (with `Monoid M`)
  it is the `Submonoid M` consisting of elements which fix `s : Set α` pointwise.

* `fixingSubmonoid_fixedPoints_gc M α` is the `GaloisConnection`
  that relates `fixingSubmonoid` with `fixedPoints`.

* `fixingSubgroup M s` : in the presence of `MulAction M α` (with `Group M`)
  it is the `Subgroup M` consisting of elements which fix `s : Set α` pointwise.

* `fixingSubgroup_fixedPoints_gc M α` is the `GaloisConnection`
  that relates `fixingSubgroup` with `fixedPoints`.

TODO :

* Maybe other lemmas are useful

* Treat semigroups ?

-/

@[expose] public section


section Monoid

open MulAction

variable (M : Type*) {α : Type*} [Monoid M] [MulAction M α]

/-- The submonoid fixing a set under a `MulAction`. -/
@[to_additive /-- The additive submonoid fixing a set under an `AddAction`. -/]
/--
Definition of `fixingSubmonoid` / `fixingSubmonoid` 的定义

English:
definition fixingSubmonoid
  signature: (s : Set α)
  body: { ϕ : M | forall x : s, ϕ • (x : α) = x }
  one_mem' _ := one_smul _ _
  mul_mem' {x y} hx hy z := by rw [mul_smul, hy z, hx z]

@[to_additive]

中文:
定义 fixingSubmonoid
  签名: (s : 集合 α)
  定义体: { ϕ : M | forall x : s, ϕ • (x : α) = x }
  one_mem' _ := one_smul _ _
  mul_mem' {x y} hx hy z := by rw [mul_smul, hy z, hx z]

@[to_additive]
-/
def fixingSubmonoid (s : Set α) : Submonoid M where
  carrier := { ϕ : M | forall x : s, ϕ • (x : α) = x }
  one_mem' _ := one_smul _ _
  mul_mem' {x y} hx hy z := by rw [mul_smul, hy z, hx z]

@[to_additive]
/--
theorem `mem_fixingSubmonoid_iff` / 定理 `mem_fixingSubmonoid_iff`

English:
theorem mem_fixingSubmonoid_iff
  given: {s : Set α} {m : M}
  proof: ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

中文:
定理 mem_fixingSubmonoid_iff
  条件: {s : 集合 α} {m : M}
  证明: ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩
-/
theorem mem_fixingSubmonoid_iff {s : Set α} {m : M} :
    m in fixingSubmonoid M s ↔ forall y in s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

variable (α)

/-- The Galois connection between fixing submonoids and fixed points of a monoid action -/
@[to_additive]
/--
theorem `fixingSubmonoid_fixedPoints_gc` / 定理 `fixingSubmonoid_fixedPoints_gc`

English:
theorem fixingSubmonoid_fixedPoints_gc
  proof: fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

@[to_additive]

中文:
定理 fixingSubmonoid_fixedPoints_gc
  证明: fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

@[to_additive]
-/
theorem fixingSubmonoid_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubmonoid M)
      ((fun P : Submonoid M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

@[to_additive]
/--
theorem `fixingSubmonoid_antitone` / 定理 `fixingSubmonoid_antitone`

English:
theorem fixingSubmonoid_antitone
  statement: Antitone fun s : Set α => fixingSubmonoid M s
  proof: (fixingSubmonoid_fixedPoints_gc M α).monotone_l

@[to_additive fixedPoints_antitone_addSubmonoid]

中文:
定理 fixingSubmonoid_antitone
  结论: 递减 fun s : 集合 α => fixingSubmonoid M s
  证明: (fixingSubmonoid_fixedPoints_gc M α).monotone_l

@[to_additive fixedPoints_antitone_addSubmonoid]

Depends on / 依赖: fixingSubmonoid_fixedPoints_gc, monotone_l
-/
theorem fixingSubmonoid_antitone : Antitone fun s : Set α => fixingSubmonoid M s :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_l

@[to_additive fixedPoints_antitone_addSubmonoid]
/--
theorem `fixedPoints_antitone` / 定理 `fixedPoints_antitone`

English:
theorem fixedPoints_antitone
  statement: Antitone fun P : Submonoid M => fixedPoints P α
  proof: (fixingSubmonoid_fixedPoints_gc M α).monotone_u.dual_left

中文:
定理 fixedPoints_antitone
  结论: 递减 fun P : 子幺半群 M => fixedPoints P α
  证明: (fixingSubmonoid_fixedPoints_gc M α).monotone_u.dual_left

Depends on / 依赖: dual_left, fixingSubmonoid_fixedPoints_gc, monotone_u, monotone_u.dual_left
-/
theorem fixedPoints_antitone : Antitone fun P : Submonoid M => fixedPoints P α :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_u.dual_left

/-- Fixing submonoid of union is intersection -/
@[to_additive]
/--
theorem `fixingSubmonoid_union` / 定理 `fixingSubmonoid_union`

English:
theorem fixingSubmonoid_union
  given: {s t : Set α}
  proof: (fixingSubmonoid_fixedPoints_gc M α).l_sup

中文:
定理 fixingSubmonoid_union
  条件: {s t : 集合 α}
  证明: (fixingSubmonoid_fixedPoints_gc M α).l_sup

Depends on / 依赖: fixingSubmonoid_fixedPoints_gc, l_sup
-/
theorem fixingSubmonoid_union {s t : Set α} :
    fixingSubmonoid M (s union t) = fixingSubmonoid M s ⊓ fixingSubmonoid M t :=
  (fixingSubmonoid_fixedPoints_gc M α).l_sup

/-- Fixing submonoid of iUnion is intersection -/
@[to_additive]
/--
theorem `fixingSubmonoid_iUnion` / 定理 `fixingSubmonoid_iUnion`

English:
theorem fixingSubmonoid_iUnion
  given: {ι : Sort*} {s : ι -> Set α}
  proof: (fixingSubmonoid_fixedPoints_gc M α).l_iSup

中文:
定理 fixingSubmonoid_iUnion
  条件: {ι : 类型层*} {s : ι -> 集合 α}
  证明: (fixingSubmonoid_fixedPoints_gc M α).l_iSup

Depends on / 依赖: fixingSubmonoid_fixedPoints_gc, l_iSup
-/
theorem fixingSubmonoid_iUnion {ι : Sort*} {s : ι -> Set α} :
    fixingSubmonoid M (⋃ i, s i) = ⨅ i, fixingSubmonoid M (s i) :=
  (fixingSubmonoid_fixedPoints_gc M α).l_iSup

/-- Fixed points of sup of submonoids is intersection -/
@[to_additive]
/--
theorem `fixedPoints_submonoid_sup` / 定理 `fixedPoints_submonoid_sup`

English:
theorem fixedPoints_submonoid_sup
  given: {P Q : Submonoid M}
  proof: (fixingSubmonoid_fixedPoints_gc M α).u_inf

中文:
定理 fixedPoints_submonoid_sup
  条件: {P Q : 子幺半群 M}
  证明: (fixingSubmonoid_fixedPoints_gc M α).u_inf

Depends on / 依赖: fixingSubmonoid_fixedPoints_gc, u_inf
-/
theorem fixedPoints_submonoid_sup {P Q : Submonoid M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α inter fixedPoints Q α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_inf

/-- Fixed points of iSup of submonoids is intersection -/
@[to_additive]
/--
theorem `fixedPoints_submonoid_iSup` / 定理 `fixedPoints_submonoid_iSup`

English:
theorem fixedPoints_submonoid_iSup
  given: {ι : Sort*} {P : ι -> Submonoid M}
  proof: (fixingSubmonoid_fixedPoints_gc M α).u_iInf

中文:
定理 fixedPoints_submonoid_iSup
  条件: {ι : 类型层*} {P : ι -> 子幺半群 M}
  证明: (fixingSubmonoid_fixedPoints_gc M α).u_iInf

Depends on / 依赖: fixingSubmonoid_fixedPoints_gc, u_iInf
-/
theorem fixedPoints_submonoid_iSup {ι : Sort*} {P : ι -> Submonoid M} :
    fixedPoints (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_iInf

end Monoid

section Group

open MulAction

variable (M : Type*) {α : Type*} [Group M] [MulAction M α]

/-- The subgroup fixing a set under a `MulAction`. -/
@[to_additive /-- The additive subgroup fixing a set under an `AddAction`. -/]
/--
Definition of `fixingSubgroup` / `fixingSubgroup` 的定义

English:
definition fixingSubgroup
  signature: (s : Set α)
  body: { fixingSubmonoid M s with inv_mem' := fun hx z => by rw [inv_smul_eq_iff, hx z] }

@[to_additive]

中文:
定义 fixingSubgroup
  签名: (s : 集合 α)
  定义体: { fixingSubmonoid M s with inv_mem' := fun hx z => by rw [inv_smul_eq_iff, hx z] }

@[to_additive]

Depends on / 依赖: fixingSubmonoid, inv_mem, inv_smul_eq_iff
-/
def fixingSubgroup (s : Set α) : Subgroup M :=
  { fixingSubmonoid M s with inv_mem' := fun hx z => by rw [inv_smul_eq_iff, hx z] }

@[to_additive]
/--
theorem `mem_fixingSubgroup_iff` / 定理 `mem_fixingSubgroup_iff`

English:
theorem mem_fixingSubgroup_iff
  given: {s : Set α} {m : M}
  statement: m in fixingSubgroup M s ↔ forall y in s, m • y = y
  proof: ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

@[to_additive]

中文:
定理 mem_fixingSubgroup_iff
  条件: {s : 集合 α} {m : M}
  结论: m in fixingSubgroup M s ↔ 对任意 y in s, m • y = y
  证明: ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

@[to_additive]
-/
theorem mem_fixingSubgroup_iff {s : Set α} {m : M} : m in fixingSubgroup M s ↔ forall y in s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

@[to_additive]
/--
theorem `mem_fixingSubgroup_iff_subset_fixedBy` / 定理 `mem_fixingSubgroup_iff_subset_fixedBy`

English:
theorem mem_fixingSubgroup_iff_subset_fixedBy
  given: {s : Set α} {m : M}
  proof: by
  simp_rw [mem_fixingSubgroup_iff, Set.subset_def, mem_fixedBy]

@[to_additive]

中文:
定理 mem_fixingSubgroup_iff_subset_fixedBy
  条件: {s : 集合 α} {m : M}
  证明: by
  simp_rw [mem_fixingSubgroup_iff, Set.subset_def, mem_fixedBy]

@[to_additive]

Depends on / 依赖: Set.subset_def, mem_fixedBy, mem_fixingSubgroup_iff, simp_rw, subset_def
-/
theorem mem_fixingSubgroup_iff_subset_fixedBy {s : Set α} {m : M} :
    m in fixingSubgroup M s ↔ s subseteq fixedBy α m := by
  simp_rw [mem_fixingSubgroup_iff, Set.subset_def, mem_fixedBy]

@[to_additive]
/--
theorem `mem_fixingSubgroup_compl_iff_movedBy_subset` / 定理 `mem_fixingSubgroup_compl_iff_movedBy_subset`

English:
theorem mem_fixingSubgroup_compl_iff_movedBy_subset
  given: {s : Set α} {m : M}
  proof: by
  rw [mem_fixingSubgroup_iff_subset_fixedBy]; rw [Set.compl_subset_comm]

中文:
定理 mem_fixingSubgroup_compl_iff_movedBy_subset
  条件: {s : 集合 α} {m : M}
  证明: by
  rw [mem_fixingSubgroup_iff_subset_fixedBy]; rw [Set.compl_subset_comm]

Depends on / 依赖: Set.compl_subset_comm, compl_subset_comm, mem_fixingSubgroup_iff_subset_fixedBy
-/
theorem mem_fixingSubgroup_compl_iff_movedBy_subset {s : Set α} {m : M} :
    m in fixingSubgroup M sᶜ ↔ (fixedBy α m)ᶜ subseteq s := by
  rw [mem_fixingSubgroup_iff_subset_fixedBy]; rw [Set.compl_subset_comm]

variable (α)

/-- The Galois connection between fixing subgroups and fixed points of a group action -/
@[to_additive]
/--
theorem `fixingSubgroup_fixedPoints_gc` / 定理 `fixingSubgroup_fixedPoints_gc`

English:
theorem fixingSubgroup_fixedPoints_gc
  proof: fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

@[to_additive (attr := simp)]

中文:
定理 fixingSubgroup_fixedPoints_gc
  证明: fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

@[to_additive (attr := simp)]
-/
theorem fixingSubgroup_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubgroup M)
      ((fun P : Subgroup M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

@[to_additive (attr := simp)]
/--
lemma `fixingSubgroup_empty` / 引理 `fixingSubgroup_empty`

English:
lemma fixingSubgroup_empty
  statement: fixingSubgroup M (∅ : Set α) = ⊤
  proof: GaloisConnection.l_bot (fixingSubgroup_fixedPoints_gc M α)

@[to_additive]

中文:
引理 fixingSubgroup_empty
  结论: fixingSubgroup M (∅ : 集合 α) = ⊤
  证明: GaloisConnection.l_bot (fixingSubgroup_fixedPoints_gc M α)

@[to_additive]

Depends on / 依赖: GaloisConnection, GaloisConnection.l_bot, fixingSubgroup_fixedPoints_gc, l_bot
-/
lemma fixingSubgroup_empty : fixingSubgroup M (∅ : Set α) = ⊤ :=
  GaloisConnection.l_bot (fixingSubgroup_fixedPoints_gc M α)

@[to_additive]
/--
theorem `fixingSubgroup_antitone` / 定理 `fixingSubgroup_antitone`

English:
theorem fixingSubgroup_antitone
  statement: Antitone (fixingSubgroup M : Set α -> Subgroup M)
  proof: (fixingSubgroup_fixedPoints_gc M α).monotone_l

@[to_additive]

中文:
定理 fixingSubgroup_antitone
  结论: 递减 (fixingSubgroup M : 集合 α -> 子群 M)
  证明: (fixingSubgroup_fixedPoints_gc M α).monotone_l

@[to_additive]

Depends on / 依赖: fixingSubgroup_fixedPoints_gc, monotone_l
-/
theorem fixingSubgroup_antitone : Antitone (fixingSubgroup M : Set α -> Subgroup M) :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_l

@[to_additive]
/--
theorem `fixedPoints_subgroup_antitone` / 定理 `fixedPoints_subgroup_antitone`

English:
theorem fixedPoints_subgroup_antitone
  statement: Antitone fun P : Subgroup M => fixedPoints P α
  proof: (fixingSubgroup_fixedPoints_gc M α).monotone_u.dual_left

中文:
定理 fixedPoints_subgroup_antitone
  结论: 递减 fun P : 子群 M => fixedPoints P α
  证明: (fixingSubgroup_fixedPoints_gc M α).monotone_u.dual_left

Depends on / 依赖: dual_left, fixingSubgroup_fixedPoints_gc, monotone_u, monotone_u.dual_left
-/
theorem fixedPoints_subgroup_antitone : Antitone fun P : Subgroup M => fixedPoints P α :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_u.dual_left

/-- Fixing subgroup of union is intersection -/
@[to_additive]
/--
theorem `fixingSubgroup_union` / 定理 `fixingSubgroup_union`

English:
theorem fixingSubgroup_union
  given: {s t : Set α}
  proof: (fixingSubgroup_fixedPoints_gc M α).l_sup

中文:
定理 fixingSubgroup_union
  条件: {s t : 集合 α}
  证明: (fixingSubgroup_fixedPoints_gc M α).l_sup

Depends on / 依赖: fixingSubgroup_fixedPoints_gc, l_sup
-/
theorem fixingSubgroup_union {s t : Set α} :
    fixingSubgroup M (s union t) = fixingSubgroup M s ⊓ fixingSubgroup M t :=
  (fixingSubgroup_fixedPoints_gc M α).l_sup

/-- Fixing subgroup of iUnion is intersection -/
@[to_additive]
/--
theorem `fixingSubgroup_iUnion` / 定理 `fixingSubgroup_iUnion`

English:
theorem fixingSubgroup_iUnion
  given: {ι : Sort*} {s : ι -> Set α}
  proof: (fixingSubgroup_fixedPoints_gc M α).l_iSup

中文:
定理 fixingSubgroup_iUnion
  条件: {ι : 类型层*} {s : ι -> 集合 α}
  证明: (fixingSubgroup_fixedPoints_gc M α).l_iSup

Depends on / 依赖: fixingSubgroup_fixedPoints_gc, l_iSup
-/
theorem fixingSubgroup_iUnion {ι : Sort*} {s : ι -> Set α} :
    fixingSubgroup M (⋃ i, s i) = ⨅ i, fixingSubgroup M (s i) :=
  (fixingSubgroup_fixedPoints_gc M α).l_iSup

/-- Fixed points of sup of subgroups is intersection -/
@[to_additive]
/--
theorem `fixedPoints_subgroup_sup` / 定理 `fixedPoints_subgroup_sup`

English:
theorem fixedPoints_subgroup_sup
  given: {P Q : Subgroup M}
  proof: (fixingSubgroup_fixedPoints_gc M α).u_inf

中文:
定理 fixedPoints_subgroup_sup
  条件: {P Q : 子群 M}
  证明: (fixingSubgroup_fixedPoints_gc M α).u_inf

Depends on / 依赖: fixingSubgroup_fixedPoints_gc, u_inf
-/
theorem fixedPoints_subgroup_sup {P Q : Subgroup M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α inter fixedPoints Q α :=
  (fixingSubgroup_fixedPoints_gc M α).u_inf

/-- Fixed points of iSup of subgroups is intersection -/
@[to_additive]
/--
theorem `fixedPoints_subgroup_iSup` / 定理 `fixedPoints_subgroup_iSup`

English:
theorem fixedPoints_subgroup_iSup
  given: {ι : Sort*} {P : ι -> Subgroup M}
  proof: (fixingSubgroup_fixedPoints_gc M α).u_iInf

中文:
定理 fixedPoints_subgroup_iSup
  条件: {ι : 类型层*} {P : ι -> 子群 M}
  证明: (fixingSubgroup_fixedPoints_gc M α).u_iInf

Depends on / 依赖: fixingSubgroup_fixedPoints_gc, u_iInf
-/
theorem fixedPoints_subgroup_iSup {ι : Sort*} {P : ι -> Subgroup M} :
    fixedPoints (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubgroup_fixedPoints_gc M α).u_iInf

/-- The orbit of the fixing subgroup of `sᶜ` (i.e. the moving subgroup of `s`) is a subset of `s` -/
@[to_additive]
/--
theorem `orbit_fixingSubgroup_compl_subset` / 定理 `orbit_fixingSubgroup_compl_subset`

English:
theorem orbit_fixingSubgroup_compl_subset
  given: {s : Set α} {a : α} (a_in_s : a in s)
  proof: by
  intro b b_in_orbit
  let ⟨⟨g, g_fixing⟩, g_eq⟩ := MulAction.mem_orbit_iff.mp b_in_orbit
  rw [Submonoid.mk_smul] at g_eq
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at g_fixing
  rwa [← g_eq, smul_mem_of_set_mem_fixedBy (set_mem_fixedBy_of_movedBy_subset g_fixing)]

中文:
定理 orbit_fixingSubgroup_compl_subset
  条件: {s : 集合 α} {a : α} (a_in_s : a in s)
  证明: by
  intro b b_in_orbit
  let ⟨⟨g, g_fixing⟩, g_eq⟩ := MulAction.mem_orbit_iff.mp b_in_orbit
  rw [Submonoid.mk_smul] at g_eq
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at g_fixing
  rwa [← g_eq, smul_mem_of_set_mem_fixedBy (set_mem_fixedBy_of_movedBy_subset g_fixing)]

Depends on / 依赖: MulAction, MulAction.mem_orbit_iff.mp, Submonoid, Submonoid.mk_smul, b_in_orbit, g_eq, g_fixing, mem_fixingSubgroup_compl_iff_movedBy_subset, mem_orbit_iff, mk_smul, set_mem_fixedBy_of_movedBy_subset, smul_mem_of_set_mem_fixedBy
-/
theorem orbit_fixingSubgroup_compl_subset {s : Set α} {a : α} (a_in_s : a in s) :
    MulAction.orbit (fixingSubgroup M sᶜ) a subseteq s := by
  intro b b_in_orbit
  let ⟨⟨g, g_fixing⟩, g_eq⟩ := MulAction.mem_orbit_iff.mp b_in_orbit
  rw [Submonoid.mk_smul] at g_eq
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at g_fixing
  rwa [← g_eq, smul_mem_of_set_mem_fixedBy (set_mem_fixedBy_of_movedBy_subset g_fixing)]

end Group
