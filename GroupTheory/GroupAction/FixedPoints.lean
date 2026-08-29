/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Properties of `fixedPoints` and `fixedBy`

This module contains some useful properties of `MulAction.fixedPoints` and `MulAction.fixedBy`
that don't directly belong to `Mathlib/GroupTheory/GroupAction/Basic.lean`,
as well as their interaction with `MulActionHom`.

## Main theorems

* `MulAction.fixedBy_mul`: `fixedBy α (g * h) ⊆ fixedBy α g ∪ fixedBy α h`
* `MulAction.fixedBy_conj` and `MulAction.smul_fixedBy`: the pointwise group action of `h` on
  `fixedBy α g` is equal to the `fixedBy` set of the conjugation of `h` with `g`
  (`fixedBy α (h * g * h⁻¹)`).
* `MulAction.set_mem_fixedBy_of_movedBy_subset` shows that if a set `s` is a superset of
  `(fixedBy α g)ᶜ`, then the group action of `g` cannot send elements of `s` outside of `s`.
  This is expressed as `s ∈ fixedBy (Set α) g`, and `MulAction.set_mem_fixedBy_iff` allows one
  to convert the relationship back to `g • x ∈ s ↔ x ∈ s`.
* `MulAction.not_commute_of_disjoint_smul_movedBy` allows one to prove that `g` and `h`
  do not commute from the disjointness of the `(fixedBy α g)ᶜ` set and `h • (fixedBy α g)ᶜ`,
  which is a property used in the proof of Rubin's theorem.

The theorems above are also available for `AddAction`.

## Pointwise group action and `fixedBy (Set α) g`

Since `fixedBy α g = { x | g • x = x }` by definition, properties about the pointwise action of
a set `s : Set α` can be expressed using `fixedBy (Set α) g`.
To properly use theorems using `fixedBy (Set α) g`, you should `open Pointwise` in your file.

`s ∈ fixedBy (Set α) g` means that `g • s = s`, which is equivalent to say that
`∀ x, g • x ∈ s ↔ x ∈ s` (the translation can be done using `MulAction.set_mem_fixedBy_iff`).

`s ∈ fixedBy (Set α) g` is a weaker statement than `s ⊆ fixedBy α g`: the latter requires that
all points in `s` are fixed by `g`, whereas the former only requires that `g • x ∈ s`.
-/

public section

namespace MulAction
open scoped Pointwise

variable {α : Type*}
variable {G : Type*} [Group G] [MulAction G α]
variable {M : Type*} [Monoid M] [MulAction M α]


section FixedPoints

variable (α) in
/-- In a multiplicative group action, the points fixed by `g` are also fixed by `g⁻¹` -/
@[to_additive (attr := simp)
  /-- In an additive group action, the points fixed by `g` are also fixed by `g⁻¹` -/]
/--
theorem `fixedBy_inv` / 定理 `fixedBy_inv`

English:
theorem fixedBy_inv
  given: (g : G)
  statement: fixedBy α g⁻¹ = fixedBy α g
  proof: by
  ext
  rw [mem_fixedBy]; rw [mem_fixedBy]; rw [inv_smul_eq_iff]; rw [eq_comm]

@[to_additive]

中文:
定理 fixedBy_inv
  条件: (g : G)
  结论: fixedBy α g⁻¹ = fixedBy α g
  证明: by
  ext
  rw [mem_fixedBy]; rw [mem_fixedBy]; rw [inv_smul_eq_iff]; rw [eq_comm]

@[to_additive]

Depends on / 依赖: eq_comm, inv_smul_eq_iff, mem_fixedBy
-/
theorem fixedBy_inv (g : G) : fixedBy α g⁻¹ = fixedBy α g := by
  ext
  rw [mem_fixedBy]; rw [mem_fixedBy]; rw [inv_smul_eq_iff]; rw [eq_comm]

@[to_additive]
/--
theorem `smul_mem_fixedBy_iff_mem_fixedBy` / 定理 `smul_mem_fixedBy_iff_mem_fixedBy`

English:
theorem smul_mem_fixedBy_iff_mem_fixedBy
  given: {a : α} {g : G}
  proof: by
  rw [mem_fixedBy]; rw [smul_left_cancel_iff]
  rfl

@[to_additive]

中文:
定理 smul_mem_fixedBy_iff_mem_fixedBy
  条件: {a : α} {g : G}
  证明: by
  rw [mem_fixedBy]; rw [smul_left_cancel_iff]
  rfl

@[to_additive]

Depends on / 依赖: mem_fixedBy, smul_left_cancel_iff
-/
theorem smul_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} :
    g • a in fixedBy α g ↔ a in fixedBy α g := by
  rw [mem_fixedBy]; rw [smul_left_cancel_iff]
  rfl

@[to_additive]
/--
theorem `smul_inv_mem_fixedBy_iff_mem_fixedBy` / 定理 `smul_inv_mem_fixedBy_iff_mem_fixedBy`

English:
theorem smul_inv_mem_fixedBy_iff_mem_fixedBy
  given: {a : α} {g : G}
  proof: by
  rw [← fixedBy_inv]; rw [smul_mem_fixedBy_iff_mem_fixedBy]; rw [fixedBy_inv]

@[to_additive minimalPeriod_eq_one_iff_fixedBy]

中文:
定理 smul_inv_mem_fixedBy_iff_mem_fixedBy
  条件: {a : α} {g : G}
  证明: by
  rw [← fixedBy_inv]; rw [smul_mem_fixedBy_iff_mem_fixedBy]; rw [fixedBy_inv]

@[to_additive minimalPeriod_eq_one_iff_fixedBy]

Depends on / 依赖: fixedBy_inv, smul_mem_fixedBy_iff_mem_fixedBy
-/
theorem smul_inv_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} :
    g⁻¹ • a in fixedBy α g ↔ a in fixedBy α g := by
  rw [← fixedBy_inv]; rw [smul_mem_fixedBy_iff_mem_fixedBy]; rw [fixedBy_inv]

@[to_additive minimalPeriod_eq_one_iff_fixedBy]
/--
theorem `minimalPeriod_eq_one_iff_fixedBy` / 定理 `minimalPeriod_eq_one_iff_fixedBy`

English:
theorem minimalPeriod_eq_one_iff_fixedBy
  given: {a : α} {g : G}
  proof: Function.minimalPeriod_eq_one_iff_isFixedPt

@[to_additive]

中文:
定理 minimalPeriod_eq_one_iff_fixedBy
  条件: {a : α} {g : G}
  证明: Function.minimalPeriod_eq_one_iff_isFixedPt

@[to_additive]

Depends on / 依赖: Function, Function.minimalPeriod_eq_one_iff_isFixedPt, minimalPeriod_eq_one_iff_isFixedPt
-/
theorem minimalPeriod_eq_one_iff_fixedBy {a : α} {g : G} :
    Function.minimalPeriod (fun x => g • x) a = 1 ↔ a in fixedBy α g :=
  Function.minimalPeriod_eq_one_iff_isFixedPt

@[to_additive]
/--
theorem `mem_fixedBy_zpow` / 定理 `mem_fixedBy_zpow`

English:
theorem mem_fixedBy_zpow
  given: {g : G} {a : α} (h : a in fixedBy α g) (j : Int)
  proof: by
  rw [mem_fixedBy]; rw [zpow_smul_eq_iff_minimalPeriod_dvd]; rw [minimalPeriod_eq_one_iff_fixedBy.mpr h]; rw [Int.natCast_one]
  exact one_dvd j

@[to_additive]

中文:
定理 mem_fixedBy_zpow
  条件: {g : G} {a : α} (h : a in fixedBy α g) (j : 整数)
  证明: by
  rw [mem_fixedBy]; rw [zpow_smul_eq_iff_minimalPeriod_dvd]; rw [minimalPeriod_eq_one_iff_fixedBy.mpr h]; rw [Int.natCast_one]
  exact one_dvd j

@[to_additive]

Depends on / 依赖: Int.natCast_one, mem_fixedBy, minimalPeriod_eq_one_iff_fixedBy, minimalPeriod_eq_one_iff_fixedBy.mpr, natCast_one, one_dvd, zpow_smul_eq_iff_minimalPeriod_dvd
-/
theorem mem_fixedBy_zpow {g : G} {a : α} (h : a in fixedBy α g) (j : Int) :
    a in fixedBy α (g ^ j) := by
  rw [mem_fixedBy]; rw [zpow_smul_eq_iff_minimalPeriod_dvd]; rw [minimalPeriod_eq_one_iff_fixedBy.mpr h]; rw [Int.natCast_one]
  exact one_dvd j

@[to_additive]
/--
theorem `mem_fixedBy_zpowers_iff_mem_fixedBy` / 定理 `mem_fixedBy_zpowers_iff_mem_fixedBy`

English:
theorem mem_fixedBy_zpowers_iff_mem_fixedBy
  given: {g : G} {a : α}
  proof: ⟨fun h => by simpa using h 1, fun h j => mem_fixedBy_zpow h j⟩

中文:
定理 mem_fixedBy_zpowers_iff_mem_fixedBy
  条件: {g : G} {a : α}
  证明: ⟨fun h => by simpa using h 1, fun h j => mem_fixedBy_zpow h j⟩

Depends on / 依赖: mem_fixedBy_zpow
-/
theorem mem_fixedBy_zpowers_iff_mem_fixedBy {g : G} {a : α} :
    (forall j : Int, a in fixedBy α (g ^ j)) ↔ a in fixedBy α g :=
  ⟨fun h => by simpa using h 1, fun h j => mem_fixedBy_zpow h j⟩

variable (α) in
@[to_additive]
/--
theorem `fixedBy_subset_fixedBy_zpow` / 定理 `fixedBy_subset_fixedBy_zpow`

English:
theorem fixedBy_subset_fixedBy_zpow
  given: (g : G) (j : Int)
  proof: fun _ h => mem_fixedBy_zpow h j

中文:
定理 fixedBy_subset_fixedBy_zpow
  条件: (g : G) (j : 整数)
  证明: fun _ h => mem_fixedBy_zpow h j

Depends on / 依赖: mem_fixedBy_zpow
-/
theorem fixedBy_subset_fixedBy_zpow (g : G) (j : Int) :
    fixedBy α g subseteq fixedBy α (g ^ j) :=
  fun _ h => mem_fixedBy_zpow h j

variable (M α) in
@[to_additive (attr := simp)]
/--
theorem `fixedBy_one_eq_univ` / 定理 `fixedBy_one_eq_univ`

English:
theorem fixedBy_one_eq_univ
  statement: fixedBy α (1 : M) = Set.univ
  proof: Set.eq_univ_iff_forall.mpr one_smul M

中文:
定理 fixedBy_one_eq_univ
  结论: fixedBy α (1 : M) = 集合.univ
  证明: Set.eq_univ_iff_forall.mpr one_smul M

Depends on / 依赖: Set.eq_univ_iff_forall.mpr, eq_univ_iff_forall, one_smul
-/
theorem fixedBy_one_eq_univ : fixedBy α (1 : M) = Set.univ :=
Set.eq_univ_iff_forall.mpr one_smul M

variable (α) in
@[to_additive]
/--
theorem `fixedBy_mul` / 定理 `fixedBy_mul`

English:
theorem fixedBy_mul
  given: (m₁ m₂ : M)
  statement: fixedBy α m₁ inter fixedBy α m₂ subseteq fixedBy α (m₁ * m₂)
  proof: by
  intro a ⟨h₁, h₂⟩
  rw [mem_fixedBy]; rw [mul_smul]; rw [h₂]; rw [h₁]

中文:
定理 fixedBy_mul
  条件: (m₁ m₂ : M)
  结论: fixedBy α m₁ inter fixedBy α m₂ subseteq fixedBy α (m₁ * m₂)
  证明: by
  intro a ⟨h₁, h₂⟩
  rw [mem_fixedBy]; rw [mul_smul]; rw [h₂]; rw [h₁]

Depends on / 依赖: mem_fixedBy, mul_smul
-/
theorem fixedBy_mul (m₁ m₂ : M) : fixedBy α m₁ inter fixedBy α m₂ subseteq fixedBy α (m₁ * m₂) := by
  intro a ⟨h₁, h₂⟩
  rw [mem_fixedBy]; rw [mul_smul]; rw [h₂]; rw [h₁]

variable (α) in
@[to_additive]
/--
theorem `smul_fixedBy` / 定理 `smul_fixedBy`

English:
theorem smul_fixedBy
  given: (g h : G)
  proof: by
  ext a
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem, mem_fixedBy, mul_smul, smul_eq_iff_eq_inv_smul h]

中文:
定理 smul_fixedBy
  条件: (g h : G)
  证明: by
  ext a
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem, mem_fixedBy, mul_smul, smul_eq_iff_eq_inv_smul h]

Depends on / 依赖: Set.mem_smul_set_iff_inv_smul_mem, mem_fixedBy, mem_smul_set_iff_inv_smul_mem, mul_smul, simp_rw, smul_eq_iff_eq_inv_smul
-/
theorem smul_fixedBy (g h : G) :
    h • fixedBy α g = fixedBy α (h * g * h⁻¹) := by
  ext a
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem, mem_fixedBy, mul_smul, smul_eq_iff_eq_inv_smul h]

/--
lemma `fixedBy_mul_eq_empty_iff` / 引理 `fixedBy_mul_eq_empty_iff`

English:
lemma fixedBy_mul_eq_empty_iff
  given: [IsRightCancelMul M] {m : M}
  proof: by
  simp [MulAction.fixedBy, Set.eq_empty_iff_forall_notMem]

中文:
引理 fixedBy_mul_eq_empty_iff
  条件: [右乘消去 M] {m : M}
  证明: by
  simp [MulAction.fixedBy, Set.eq_empty_iff_forall_notMem]

Depends on / 依赖: MulAction, MulAction.fixedBy, Set.eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem, fixedBy
-/
lemma fixedBy_mul_eq_empty_iff [IsRightCancelMul M] {m : M} :
    fixedBy M m = ∅ ↔ m != 1 := by
  simp [MulAction.fixedBy, Set.eq_empty_iff_forall_notMem]

/--
lemma `fixedBy_mul_op_eq_empty_iff` / 引理 `fixedBy_mul_op_eq_empty_iff`

English:
lemma fixedBy_mul_op_eq_empty_iff
  given: [IsLeftCancelMul M] {m : M}
  proof: by
  simp [MulAction.fixedBy, Set.eq_empty_iff_forall_notMem]

中文:
引理 fixedBy_mul_op_eq_empty_iff
  条件: [左乘消去 M] {m : M}
  证明: by
  simp [MulAction.fixedBy, Set.eq_empty_iff_forall_notMem]

Depends on / 依赖: MulAction, MulAction.fixedBy, Set.eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem, fixedBy
-/
lemma fixedBy_mul_op_eq_empty_iff [IsLeftCancelMul M] {m : M} :
    fixedBy M (MulOpposite.op m) = ∅ ↔ m != 1 := by
  simp [MulAction.fixedBy, Set.eq_empty_iff_forall_notMem]

end FixedPoints

section Pointwise

/-!
### `fixedBy` sets of the pointwise group action

The theorems below need the `Pointwise` scoped to be opened (using `open Pointwise`)
to be used effectively.
-/

/--
If a set `s : Set α` is in `fixedBy (Set α) g`, then all points of `s` will stay in `s` after being
moved by `g`.
-/
@[to_additive /-- If a set `s : Set α` is in `fixedBy (Set α) g`, then all points of `s` will stay
in `s` after being moved by `g`. -/]
/--
theorem `set_mem_fixedBy_iff` / 定理 `set_mem_fixedBy_iff`

English:
theorem set_mem_fixedBy_iff
  given: (s : Set α) (g : G)
  proof: by
  simp_rw [mem_fixedBy, ← eq_inv_smul_iff, Set.ext_iff, Set.mem_inv_smul_set_iff, Iff.comm]

@[to_additive]

中文:
定理 set_mem_fixedBy_iff
  条件: (s : 集合 α) (g : G)
  证明: by
  simp_rw [mem_fixedBy, ← eq_inv_smul_iff, Set.ext_iff, Set.mem_inv_smul_set_iff, Iff.comm]

@[to_additive]

Depends on / 依赖: Iff.comm, Set.ext_iff, Set.mem_inv_smul_set_iff, eq_inv_smul_iff, ext_iff, mem_fixedBy, mem_inv_smul_set_iff, simp_rw
-/
theorem set_mem_fixedBy_iff (s : Set α) (g : G) :
    s in fixedBy (Set α) g ↔ forall x, g • x in s ↔ x in s := by
  simp_rw [mem_fixedBy, ← eq_inv_smul_iff, Set.ext_iff, Set.mem_inv_smul_set_iff, Iff.comm]

@[to_additive]
/--
theorem `smul_mem_of_set_mem_fixedBy` / 定理 `smul_mem_of_set_mem_fixedBy`

English:
theorem smul_mem_of_set_mem_fixedBy
  statement: {s : Set α} {g : G} (s_in_fixedBy : s in fixedBy (Set α) g)
  proof: (set_mem_fixedBy_iff s g).mp s_in_fixedBy x

中文:
定理 smul_mem_of_set_mem_fixedBy
  结论: {s : 集合 α} {g : G} (s_in_fixedBy : s in fixedBy (集合 α) g)
  证明: (set_mem_fixedBy_iff s g).mp s_in_fixedBy x

Depends on / 依赖: s_in_fixedBy, set_mem_fixedBy_iff
-/
theorem smul_mem_of_set_mem_fixedBy {s : Set α} {g : G} (s_in_fixedBy : s in fixedBy (Set α) g)
    {x : α} : g • x in s ↔ x in s := (set_mem_fixedBy_iff s g).mp s_in_fixedBy x

/--
If `s ⊆ fixedBy α g`, then `g • s = s`, which means that `s ∈ fixedBy (Set α) g`.

Note that the reverse implication is in general not true, as `s ∈ fixedBy (Set α) g` is a
weaker statement (it allows for points `x ∈ s` for which `g • x ≠ x` and `g • x ∈ s`).
-/
@[to_additive /-- If `s ⊆ fixedBy α g`, then `g +ᵥ s = s`, which means that `s ∈ fixedBy (Set α) g`.

Note that the reverse implication is in general not true, as `s ∈ fixedBy (Set α) g` is a
weaker statement (it allows for points `x ∈ s` for which `g +ᵥ x ≠ x` and `g +ᵥ x ∈ s`). -/]
/--
theorem `set_mem_fixedBy_of_subset_fixedBy` / 定理 `set_mem_fixedBy_of_subset_fixedBy`

English:
theorem set_mem_fixedBy_of_subset_fixedBy
  given: {s : Set α} {g : G} (s_ss_fixedBy : s subseteq fixedBy α g)
  proof: by
  rw [← fixedBy_inv]
  ext x
  rw [Set.mem_inv_smul_set_iff]
  refine ⟨fun gxs => ?xs, fun xs => (s_ss_fixedBy xs).symm ▸ xs⟩
  rw [← fixedBy_inv] at s_ss_fixedBy
  rwa [← s_ss_fixedBy gxs, inv_smul_smul] at gxs

中文:
定理 set_mem_fixedBy_of_subset_fixedBy
  条件: {s : 集合 α} {g : G} (s_ss_fixedBy : s subseteq fixedBy α g)
  证明: by
  rw [← fixedBy_inv]
  ext x
  rw [Set.mem_inv_smul_set_iff]
  refine ⟨fun gxs => ?xs, fun xs => (s_ss_fixedBy xs).symm ▸ xs⟩
  rw [← fixedBy_inv] at s_ss_fixedBy
  rwa [← s_ss_fixedBy gxs, inv_smul_smul] at gxs

Depends on / 依赖: Set.mem_inv_smul_set_iff, fixedBy_inv, inv_smul_smul, mem_inv_smul_set_iff, s_ss_fixedBy
-/
theorem set_mem_fixedBy_of_subset_fixedBy {s : Set α} {g : G} (s_ss_fixedBy : s subseteq fixedBy α g) :
    s in fixedBy (Set α) g := by
  rw [← fixedBy_inv]
  ext x
  rw [Set.mem_inv_smul_set_iff]
  refine ⟨fun gxs => ?xs, fun xs => (s_ss_fixedBy xs).symm ▸ xs⟩
  rw [← fixedBy_inv] at s_ss_fixedBy
  rwa [← s_ss_fixedBy gxs, inv_smul_smul] at gxs

/--
theorem `smul_subset_of_set_mem_fixedBy` / 定理 `smul_subset_of_set_mem_fixedBy`

English:
theorem smul_subset_of_set_mem_fixedBy
  statement: {s t : Set α} {g : G} (t_ss_s : t subseteq s)
  proof: (Set.smul_set_subset_smul_set_iff.mpr t_ss_s).trans s_in_fixedBy.subset

中文:
定理 smul_subset_of_set_mem_fixedBy
  结论: {s t : 集合 α} {g : G} (t_ss_s : t subseteq s)
  证明: (Set.smul_set_subset_smul_set_iff.mpr t_ss_s).trans s_in_fixedBy.subset

Depends on / 依赖: Set.smul_set_subset_smul_set_iff.mpr, s_in_fixedBy, s_in_fixedBy.subset, smul_set_subset_smul_set_iff, subset, t_ss_s
-/
theorem smul_subset_of_set_mem_fixedBy {s t : Set α} {g : G} (t_ss_s : t subseteq s)
    (s_in_fixedBy : s in fixedBy (Set α) g) : g • t subseteq s :=
  (Set.smul_set_subset_smul_set_iff.mpr t_ss_s).trans s_in_fixedBy.subset

/-!
If a set `s : Set α` is a superset of `(MulAction.fixedBy α g)ᶜ` (resp. `(AddAction.fixedBy α g)ᶜ`),
then no point or subset of `s` can be moved outside of `s` by the group action of `g`.
-/

/-- If `(fixedBy α g)ᶜ ⊆ s`, then `g` cannot move a point of `s` outside of `s`. -/
@[to_additive /-- If `(fixedBy α g)ᶜ ⊆ s`, then `g` cannot move a point of `s` outside of `s`. -/]
/--
theorem `set_mem_fixedBy_of_movedBy_subset` / 定理 `set_mem_fixedBy_of_movedBy_subset`

English:
theorem set_mem_fixedBy_of_movedBy_subset
  given: {s : Set α} {g : G} (s_subset : (fixedBy α g)ᶜ subseteq s)
  proof: by
  rw [← fixedBy_inv]
  ext a
  rw [Set.mem_inv_smul_set_iff]
  by_cases a in fixedBy α g
  case pos a_fixed =>
    rw [a_fixed]
  case neg a_moved =>
    constructor <;> (intro; apply s_subset)
    · exact a_moved
    · rwa [Set.mem_compl_iff, smul_mem_fixedBy_iff_mem_fixedBy]

中文:
定理 set_mem_fixedBy_of_movedBy_subset
  条件: {s : 集合 α} {g : G} (s_subset : (fixedBy α g)ᶜ subseteq s)
  证明: by
  rw [← fixedBy_inv]
  ext a
  rw [Set.mem_inv_smul_set_iff]
  by_cases a in fixedBy α g
  case pos a_fixed =>
    rw [a_fixed]
  case neg a_moved =>
    constructor <;> (intro; apply s_subset)
    · exact a_moved
    · rwa [Set.mem_compl_iff, smul_mem_fixedBy_iff_mem_fixedBy]

Depends on / 依赖: Set.mem_compl_iff, Set.mem_inv_smul_set_iff, a_fixed, a_moved, fixedBy, fixedBy_inv, mem_compl_iff, mem_inv_smul_set_iff, s_subset, smul_mem_fixedBy_iff_mem_fixedBy
-/
theorem set_mem_fixedBy_of_movedBy_subset {s : Set α} {g : G} (s_subset : (fixedBy α g)ᶜ subseteq s) :
    s in fixedBy (Set α) g := by
  rw [← fixedBy_inv]
  ext a
  rw [Set.mem_inv_smul_set_iff]
  by_cases a in fixedBy α g
  case pos a_fixed =>
    rw [a_fixed]
  case neg a_moved =>
    constructor <;> (intro; apply s_subset)
    · exact a_moved
    · rwa [Set.mem_compl_iff, smul_mem_fixedBy_iff_mem_fixedBy]

end Pointwise

section Commute

/-!
## Pointwise image of the `fixedBy` set by a commuting group element

If two group elements `g` and `h` commute, then `g` fixes `h • x` (resp. `h +ᵥ x`)
if and only if `g` fixes `x`.

This is equivalent to say that if `Commute g h`, then `fixedBy α g ∈ fixedBy (Set α) h` and
`(fixedBy α g)ᶜ ∈ fixedBy (Set α) h`.
-/

/--
If `g` and `h` commute, then `g` fixes `h • x` iff `g` fixes `x`.
This is equivalent to say that the set `fixedBy α g` is fixed by `h`.
-/
@[to_additive /-- If `g` and `h` commute, then `g` fixes `h +ᵥ x` iff `g` fixes `x`.
This is equivalent to say that the set `fixedBy α g` is fixed by `h`. -/]
/--
theorem `fixedBy_mem_fixedBy_of_commute` / 定理 `fixedBy_mem_fixedBy_of_commute`

English:
theorem fixedBy_mem_fixedBy_of_commute
  given: {g h : G} (comm : Commute g h)
  proof: by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]; rw [mem_fixedBy]; rw [← mul_smul]; rw [comm.inv_right]; rw [mul_smul]; rw [smul_left_cancel_iff]; rw [mem_fixedBy]

中文:
定理 fixedBy_mem_fixedBy_of_commute
  条件: {g h : G} (comm : Commute g h)
  证明: by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]; rw [mem_fixedBy]; rw [← mul_smul]; rw [comm.inv_right]; rw [mul_smul]; rw [smul_left_cancel_iff]; rw [mem_fixedBy]

Depends on / 依赖: Set.mem_smul_set_iff_inv_smul_mem, comm.inv_right, inv_right, mem_fixedBy, mem_smul_set_iff_inv_smul_mem, mul_smul, smul_left_cancel_iff
-/
theorem fixedBy_mem_fixedBy_of_commute {g h : G} (comm : Commute g h) :
    (fixedBy α g) in fixedBy (Set α) h := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]; rw [mem_fixedBy]; rw [← mul_smul]; rw [comm.inv_right]; rw [mul_smul]; rw [smul_left_cancel_iff]; rw [mem_fixedBy]

/--
If `g` and `h` commute, then `g` fixes `(h ^ j) • x` iff `g` fixes `x`.
-/
@[to_additive /-- If `g` and `h` commute, then `g` fixes `(j • h) +ᵥ x` iff `g` fixes `x`. -/]
/--
theorem `smul_zpow_fixedBy_eq_of_commute` / 定理 `smul_zpow_fixedBy_eq_of_commute`

English:
theorem smul_zpow_fixedBy_eq_of_commute
  given: {g h : G} (comm : Commute g h) (j : Int)
  proof: fixedBy_subset_fixedBy_zpow (Set α) h j (fixedBy_mem_fixedBy_of_commute comm)

中文:
定理 smul_zpow_fixedBy_eq_of_commute
  条件: {g h : G} (comm : Commute g h) (j : 整数)
  证明: fixedBy_subset_fixedBy_zpow (Set α) h j (fixedBy_mem_fixedBy_of_commute comm)

Depends on / 依赖: fixedBy_mem_fixedBy_of_commute, fixedBy_subset_fixedBy_zpow
-/
theorem smul_zpow_fixedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : Int) :
    h ^ j • fixedBy α g = fixedBy α g :=
  fixedBy_subset_fixedBy_zpow (Set α) h j (fixedBy_mem_fixedBy_of_commute comm)

/--
If `g` and `h` commute, then `g` moves `h • x` iff `g` moves `x`.
This is equivalent to say that the set `(fixedBy α g)ᶜ` is fixed by `h`.
-/
@[to_additive /-- If `g` and `h` commute, then `g` moves `h +ᵥ x` iff `g` moves `x`.
This is equivalent to say that the set `(fixedBy α g)ᶜ` is fixed by `h`. -/]
/--
theorem `movedBy_mem_fixedBy_of_commute` / 定理 `movedBy_mem_fixedBy_of_commute`

English:
theorem movedBy_mem_fixedBy_of_commute
  given: {g h : G} (comm : Commute g h)
  proof: by
  rw [mem_fixedBy]; rw [Set.smul_set_compl]; rw [fixedBy_mem_fixedBy_of_commute comm]

中文:
定理 movedBy_mem_fixedBy_of_commute
  条件: {g h : G} (comm : Commute g h)
  证明: by
  rw [mem_fixedBy]; rw [Set.smul_set_compl]; rw [fixedBy_mem_fixedBy_of_commute comm]

Depends on / 依赖: Set.smul_set_compl, fixedBy_mem_fixedBy_of_commute, mem_fixedBy, smul_set_compl
-/
theorem movedBy_mem_fixedBy_of_commute {g h : G} (comm : Commute g h) :
    (fixedBy α g)ᶜ in fixedBy (Set α) h := by
  rw [mem_fixedBy]; rw [Set.smul_set_compl]; rw [fixedBy_mem_fixedBy_of_commute comm]

/--
If `g` and `h` commute, then `g` moves `h ^ j • x` iff `g` moves `x`.
-/
@[to_additive /-- If `g` and `h` commute, then `g` moves `(j • h) +ᵥ x` iff `g` moves `x`. -/]
/--
theorem `smul_zpow_movedBy_eq_of_commute` / 定理 `smul_zpow_movedBy_eq_of_commute`

English:
theorem smul_zpow_movedBy_eq_of_commute
  given: {g h : G} (comm : Commute g h) (j : Int)
  proof: fixedBy_subset_fixedBy_zpow (Set α) h j (movedBy_mem_fixedBy_of_commute comm)

中文:
定理 smul_zpow_movedBy_eq_of_commute
  条件: {g h : G} (comm : Commute g h) (j : 整数)
  证明: fixedBy_subset_fixedBy_zpow (Set α) h j (movedBy_mem_fixedBy_of_commute comm)

Depends on / 依赖: fixedBy_subset_fixedBy_zpow, movedBy_mem_fixedBy_of_commute
-/
theorem smul_zpow_movedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : Int) :
    h ^ j • (fixedBy α g)ᶜ = (fixedBy α g)ᶜ :=
  fixedBy_subset_fixedBy_zpow (Set α) h j (movedBy_mem_fixedBy_of_commute comm)

end Commute

section Faithful

variable [FaithfulSMul G α]
variable [FaithfulSMul M α]

/-- If the multiplicative action of `M` on `α` is faithful,
then `fixedBy α m = Set.univ` implies that `m = 1`. -/
@[to_additive /-- If the additive action of `M` on `α` is faithful,
then `fixedBy α m = Set.univ` implies that `m = 1`. -/]
/--
theorem `fixedBy_eq_univ_iff_eq_one` / 定理 `fixedBy_eq_univ_iff_eq_one`

English:
theorem fixedBy_eq_univ_iff_eq_one
  given: {m : M}
  statement: fixedBy α m = Set.univ ↔ m = 1
  proof: by
  rw [← (smul_left_injective' (M := M) (α := α)).eq_iff]; rw [Set.eq_univ_iff_forall]
  simp_rw [funext_iff, one_smul, mem_fixedBy]

中文:
定理 fixedBy_eq_univ_iff_eq_one
  条件: {m : M}
  结论: fixedBy α m = 集合.univ ↔ m = 1
  证明: by
  rw [← (smul_left_injective' (M := M) (α := α)).eq_iff]; rw [Set.eq_univ_iff_forall]
  simp_rw [funext_iff, one_smul, mem_fixedBy]

Depends on / 依赖: Set.eq_univ_iff_forall, eq_iff, eq_univ_iff_forall, funext_iff, mem_fixedBy, one_smul, simp_rw, smul_left_injective
-/
theorem fixedBy_eq_univ_iff_eq_one {m : M} : fixedBy α m = Set.univ ↔ m = 1 := by
  rw [← (smul_left_injective' (M := M) (α := α)).eq_iff]; rw [Set.eq_univ_iff_forall]
  simp_rw [funext_iff, one_smul, mem_fixedBy]

/--
If the image of the `(fixedBy α g)ᶜ` set by the pointwise action of `h: G`
is disjoint from `(fixedBy α g)ᶜ`, then `g` and `h` cannot commute.
-/
@[to_additive /-- If the image of the `(fixedBy α g)ᶜ` set by the pointwise action of `h: G`
is disjoint from `(fixedBy α g)ᶜ`, then `g` and `h` cannot commute. -/]
/--
theorem `not_commute_of_disjoint_movedBy_preimage` / 定理 `not_commute_of_disjoint_movedBy_preimage`

English:
theorem not_commute_of_disjoint_movedBy_preimage
  statement: {g h : G} (ne_one : g != 1)
  proof: by
  contrapose ne_one with comm
  rwa [movedBy_mem_fixedBy_of_commute comm, disjoint_self, Set.bot_eq_empty, ← Set.compl_univ,
    compl_inj_iff, fixedBy_eq_univ_iff_eq_one] at disjoint

中文:
定理 not_commute_of_disjoint_movedBy_preimage
  结论: {g h : G} (ne_one : g != 1)
  证明: by
  contrapose ne_one with comm
  rwa [movedBy_mem_fixedBy_of_commute comm, disjoint_self, Set.bot_eq_empty, ← Set.compl_univ,
    compl_inj_iff, fixedBy_eq_univ_iff_eq_one] at disjoint

Depends on / 依赖: Set.bot_eq_empty, Set.compl_univ, bot_eq_empty, compl_inj_iff, compl_univ, contrapose, disjoint, disjoint_self, fixedBy_eq_univ_iff_eq_one, movedBy_mem_fixedBy_of_commute, ne_one
-/
theorem not_commute_of_disjoint_movedBy_preimage {g h : G} (ne_one : g != 1)
    (disjoint : Disjoint (fixedBy α g)ᶜ (h • (fixedBy α g)ᶜ)) : ¬Commute g h := by
  contrapose ne_one with comm
  rwa [movedBy_mem_fixedBy_of_commute comm, disjoint_self, Set.bot_eq_empty, ← Set.compl_univ,
    compl_inj_iff, fixedBy_eq_univ_iff_eq_one] at disjoint

end Faithful

end MulAction

namespace MulActionHom

/-- `MulActionHom` maps `fixedPoints` to `fixedPoints`. -/
@[to_additive /-- `AddActionHom` maps `fixedPoints` to `fixedPoints`. -/]
/--
lemma `map_mem_fixedPoints` / 引理 `map_mem_fixedPoints`

English:
lemma map_mem_fixedPoints
  statement: {G A B : Type*} [Monoid G] [MulAction G A] [MulAction G B]
  proof: by
  intro ⟨h, _⟩
  simp_all [← f.map_smul h a]

中文:
引理 map_mem_fixedPoints
  结论: {G A B : 类型} [幺半群 G] [乘法作用 G A] [乘法作用 G B]
  证明: by
  intro ⟨h, _⟩
  simp_all [← f.map_smul h a]

Depends on / 依赖: f.map_smul, map_smul
-/
lemma map_mem_fixedPoints {G A B : Type*} [Monoid G] [MulAction G A] [MulAction G B]
    (f : A ->[G] B) {H : Submonoid G} {a : A} (ha : a in MulAction.fixedPoints H A) :
    f a in MulAction.fixedPoints H B := by
  intro ⟨h, _⟩
  simp_all [← f.map_smul h a]

/-- `MulActionHom` maps `fixedBy` to `fixedBy`. -/
@[to_additive /-- `AddActionHom` maps `fixedBy` to `fixedBy`. -/]
/--
lemma `map_mem_fixedBy` / 引理 `map_mem_fixedBy`

English:
lemma map_mem_fixedBy
  statement: {G A B : Type*} [Monoid G] [MulAction G A] [MulAction G B]
  proof: by
  simpa using congr_arg f ha

中文:
引理 map_mem_fixedBy
  结论: {G A B : 类型} [幺半群 G] [乘法作用 G A] [乘法作用 G B]
  证明: by
  simpa using congr_arg f ha

Depends on / 依赖: congr_arg
-/
lemma map_mem_fixedBy {G A B : Type*} [Monoid G] [MulAction G A] [MulAction G B]
    (f : A ->[G] B) {g : G} {a : A} (ha : a in MulAction.fixedBy A g) :
    f a in MulAction.fixedBy B g := by
  simpa using congr_arg f ha

end MulActionHom
