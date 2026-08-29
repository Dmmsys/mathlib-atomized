/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Yaël Dillies
-/
module

public import Mathlib.Data.Set.Monotone
public import Mathlib.Order.Cover
public import Mathlib.Order.LatticeIntervals
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Modular Lattices

This file defines (semi)modular lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Typeclasses

We define (semi)modularity typeclasses as Prop-valued mixins.

* `IsWeakUpperModularLattice`: Weakly upper modular lattices. Lattice where `a ⊔ b` covers `a`
  and `b` if `a` and `b` both cover `a ⊓ b`.
* `IsWeakLowerModularLattice`: Weakly lower modular lattices. Lattice where `a` and `b` cover
  `a ⊓ b` if `a ⊔ b` covers both `a` and `b`
* `IsUpperModularLattice`: Upper modular lattices. Lattices where `a ⊔ b` covers `a` if `b`
  covers `a ⊓ b`.
* `IsLowerModularLattice`: Lower modular lattices. Lattices where `a` covers `a ⊓ b` if `a ⊔ b`
  covers `b`.
- `IsModularLattice`: Modular lattices. Lattices where `a ≤ c → (a ⊔ b) ⊓ c = a ⊔ (b ⊓ c)`. We
  only require an inequality because the other direction holds in all lattices.

## Main Definitions

- `infIccOrderIsoIccSup` gives an order isomorphism between the intervals
  `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results

- `isModularLattice_iff_inf_sup_inf_assoc`:
  Modularity is equivalent to the `inf_sup_inf_assoc`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `DistribLattice.isModularLattice`: Distributive lattices are modular.

## References

* [Manfred Stern, *Semimodular lattices. Theory and applications*][stern2009]
* [Wikipedia, Modular Lattice](https://en.wikipedia.org/wiki/Modular_lattice)

## TODO

- Relate atoms and coatoms in modular lattices
-/

@[expose] public section


open Set

variable {α : Type*}

/--
Definition of `IsWeakUpperModularLattice` / `IsWeakUpperModularLattice` 的定义

English:
class IsWeakUpperModularLattice
  parameters: (α : Type*) [Lattice α]
  (no additional axioms)

中文:
类 是WeakUpperModular格
  参数: (α : 类型) [格 α]
  (无附加公理)
-/
class IsWeakUpperModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a ⊔ b` covers `a` and `b` if `a` and `b` both cover `a ⊓ b`. -/
  covBy_sup_of_inf_covBy_covBy {a b : α} : a ⊓ b ⋖ a -> a ⊓ b ⋖ b -> a ⋖ a ⊔ b

/-- A weakly lower modular lattice is a lattice where `a` and `b` cover `a ⊓ b` if `a ⊔ b` covers
both `a` and `b`. -/
@[to_dual existing]
/--
Definition of `IsWeakLowerModularLattice` / `IsWeakLowerModularLattice` 的定义

English:
class IsWeakLowerModularLattice
  parameters: (α : Type*) [Lattice α]
  (no additional axioms)

中文:
类 是WeakLowerModular格
  参数: (α : 类型) [格 α]
  (无附加公理)
-/
class IsWeakLowerModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a` and `b` cover `a ⊓ b` if `a ⊔ b` covers both `a` and `b` -/
  inf_covBy_of_covBy_covBy_sup {a b : α} : a ⋖ a ⊔ b -> b ⋖ a ⊔ b -> a ⊓ b ⋖ a

/--
Definition of `IsUpperModularLattice` / `IsUpperModularLattice` 的定义

English:
class IsUpperModularLattice
  parameters: (α : Type*) [Lattice α]
  (no additional axioms)

中文:
类 是UpperModular格
  参数: (α : 类型) [格 α]
  (无附加公理)
-/
class IsUpperModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a ⊔ b` covers `a` and `b` if either `a` or `b` covers `a ⊓ b` -/
  covBy_sup_of_inf_covBy {a b : α} : a ⊓ b ⋖ a -> b ⋖ a ⊔ b

/-- A lower modular lattice is a lattice where `a` and `b` both cover `a ⊓ b` if `a ⊔ b` covers
either `a` or `b`. -/
@[to_dual existing]
/--
Definition of `IsLowerModularLattice` / `IsLowerModularLattice` 的定义

English:
class IsLowerModularLattice
  parameters: (α : Type*) [Lattice α]
  (no additional axioms)

中文:
类 是LowerModular格
  参数: (α : 类型) [格 α]
  (无附加公理)
-/
class IsLowerModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a` and `b` both cover `a ⊓ b` if `a ⊔ b` covers either `a` or `b` -/
  inf_covBy_of_covBy_sup {a b : α} : a ⋖ a ⊔ b -> a ⊓ b ⋖ b

/--
Definition of `IsModularLattice` / `IsModularLattice` 的定义

English:
class IsModularLattice
  parameters: (α : Type*) [Lattice α]
  (no additional axioms)

中文:
类 是Modular格
  参数: (α : 类型) [格 α]
  (无附加公理)
-/
class IsModularLattice (α : Type*) [Lattice α] : Prop where
/-- Whenever `x ≤ z`, then for any `y`, `(x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z)` -/
  sup_inf_le_assoc_of_le : forall {x : α} (y : α) {z : α}, x <= z -> (x ⊔ y) ⊓ z <= x ⊔ y ⊓ z

section WeakUpperModular

variable [Lattice α] [IsWeakUpperModularLattice α] {a b : α}

@[to_dual inf_covBy_of_covBy_sup_of_covBy_sup_left]
/--
theorem `covBy_sup_of_inf_covBy_of_inf_covBy_left` / 定理 `covBy_sup_of_inf_covBy_of_inf_covBy_left`

English:
theorem covBy_sup_of_inf_covBy_of_inf_covBy_left
  statement: a ⊓ b ⋖ a -> a ⊓ b ⋖ b -> a ⋖ a ⊔ b
  proof: IsWeakUpperModularLattice.covBy_sup_of_inf_covBy_covBy

@[to_dual inf_covBy_of_covBy_sup_of_covBy_sup_right]

中文:
定理 covBy_sup_of_inf_covBy_of_inf_covBy_left
  结论: a ⊓ b ⋖ a -> a ⊓ b ⋖ b -> a ⋖ a ⊔ b
  证明: IsWeakUpperModularLattice.covBy_sup_of_inf_covBy_covBy

@[to_dual inf_covBy_of_covBy_sup_of_covBy_sup_right]

Depends on / 依赖: IsWeakUpperModularLattice, IsWeakUpperModularLattice.covBy_sup_of_inf_covBy_covBy, covBy_sup_of_inf_covBy_covBy
-/
theorem covBy_sup_of_inf_covBy_of_inf_covBy_left : a ⊓ b ⋖ a -> a ⊓ b ⋖ b -> a ⋖ a ⊔ b :=
  IsWeakUpperModularLattice.covBy_sup_of_inf_covBy_covBy

@[to_dual inf_covBy_of_covBy_sup_of_covBy_sup_right]
/--
theorem `covBy_sup_of_inf_covBy_of_inf_covBy_right` / 定理 `covBy_sup_of_inf_covBy_of_inf_covBy_right`

English:
theorem covBy_sup_of_inf_covBy_of_inf_covBy_right
  statement: a ⊓ b ⋖ a -> a ⊓ b ⋖ b -> b ⋖ a ⊔ b
  proof: by
  rw [inf_comm]; rw [sup_comm]
  exact fun ha hb => covBy_sup_of_inf_covBy_of_inf_covBy_left hb ha

@[to_dual]
alias CovBy.sup_of_inf_of_inf_left := covBy_sup_of_inf_covBy_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_of_inf_right := covBy_sup_of_inf_covBy_of_inf_covBy_right

@[to_dual]

中文:
定理 covBy_sup_of_inf_covBy_of_inf_covBy_right
  结论: a ⊓ b ⋖ a -> a ⊓ b ⋖ b -> b ⋖ a ⊔ b
  证明: by
  rw [inf_comm]; rw [sup_comm]
  exact fun ha hb => covBy_sup_of_inf_covBy_of_inf_covBy_left hb ha

@[to_dual]
alias CovBy.sup_of_inf_of_inf_left := covBy_sup_of_inf_covBy_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_of_inf_right := covBy_sup_of_inf_covBy_of_inf_covBy_right

@[to_dual]

Depends on / 依赖: covBy_sup_of_inf_covBy_of_inf_covBy_left, inf_comm, sup_comm
-/
theorem covBy_sup_of_inf_covBy_of_inf_covBy_right : a ⊓ b ⋖ a -> a ⊓ b ⋖ b -> b ⋖ a ⊔ b := by
  rw [inf_comm]; rw [sup_comm]
  exact fun ha hb => covBy_sup_of_inf_covBy_of_inf_covBy_left hb ha

@[to_dual]
alias CovBy.sup_of_inf_of_inf_left := covBy_sup_of_inf_covBy_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_of_inf_right := covBy_sup_of_inf_covBy_of_inf_covBy_right

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsWeakLowerModularLattice (OrderDual α)
  body: ⟨fun ha hb => (ha.ofDual.sup_of_inf_of_inf_left hb.ofDual).toDual⟩

中文:
实例 :
  签名: 是WeakLowerModular格 (OrderDual α)
  定义体: ⟨fun ha hb => (ha.ofDual.sup_of_inf_of_inf_left hb.ofDual).toDual⟩

Depends on / 依赖: ha.ofDual.sup_of_inf_of_inf_left, hb.ofDual, ofDual, sup_of_inf_of_inf_left, toDual
-/
instance : IsWeakLowerModularLattice (OrderDual α) :=
  ⟨fun ha hb => (ha.ofDual.sup_of_inf_of_inf_left hb.ofDual).toDual⟩

end WeakUpperModular

section UpperModular

variable [Lattice α] [IsUpperModularLattice α] {a b : α}

@[to_dual inf_covBy_of_covBy_sup_left]
/--
theorem `covBy_sup_of_inf_covBy_left` / 定理 `covBy_sup_of_inf_covBy_left`

English:
theorem covBy_sup_of_inf_covBy_left
  statement: a ⊓ b ⋖ a -> b ⋖ a ⊔ b
  proof: IsUpperModularLattice.covBy_sup_of_inf_covBy

@[to_dual inf_covBy_of_covBy_sup_right]

中文:
定理 covBy_sup_of_inf_covBy_left
  结论: a ⊓ b ⋖ a -> b ⋖ a ⊔ b
  证明: IsUpperModularLattice.covBy_sup_of_inf_covBy

@[to_dual inf_covBy_of_covBy_sup_right]

Depends on / 依赖: IsUpperModularLattice, IsUpperModularLattice.covBy_sup_of_inf_covBy, covBy_sup_of_inf_covBy
-/
theorem covBy_sup_of_inf_covBy_left : a ⊓ b ⋖ a -> b ⋖ a ⊔ b :=
  IsUpperModularLattice.covBy_sup_of_inf_covBy

@[to_dual inf_covBy_of_covBy_sup_right]
/--
theorem `covBy_sup_of_inf_covBy_right` / 定理 `covBy_sup_of_inf_covBy_right`

English:
theorem covBy_sup_of_inf_covBy_right
  statement: a ⊓ b ⋖ b -> a ⋖ a ⊔ b
  proof: by
  rw [sup_comm]; rw [inf_comm]
  exact covBy_sup_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_left := covBy_sup_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_right := covBy_sup_of_inf_covBy_right

中文:
定理 covBy_sup_of_inf_covBy_right
  结论: a ⊓ b ⋖ b -> a ⋖ a ⊔ b
  证明: by
  rw [sup_comm]; rw [inf_comm]
  exact covBy_sup_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_left := covBy_sup_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_right := covBy_sup_of_inf_covBy_right

Depends on / 依赖: covBy_sup_of_inf_covBy_left, inf_comm, sup_comm
-/
theorem covBy_sup_of_inf_covBy_right : a ⊓ b ⋖ b -> a ⋖ a ⊔ b := by
  rw [sup_comm]; rw [inf_comm]
  exact covBy_sup_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_left := covBy_sup_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_right := covBy_sup_of_inf_covBy_right

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) IsUpperModularLattice.to_isWeakUpperModularLattice :
    IsWeakUpperModularLattice α :=
  ⟨fun _ => CovBy.sup_of_inf_right⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLowerModularLattice (OrderDual α)
  body: ⟨fun h => h.ofDual.sup_of_inf_left.toDual⟩

中文:
实例 :
  签名: 是LowerModular格 (OrderDual α)
  定义体: ⟨fun h => h.ofDual.sup_of_inf_left.toDual⟩

Depends on / 依赖: h.ofDual.sup_of_inf_left.toDual, ofDual, sup_of_inf_left, toDual
-/
instance : IsLowerModularLattice (OrderDual α) :=
  ⟨fun h => h.ofDual.sup_of_inf_left.toDual⟩

end UpperModular

section IsModularLattice

variable [Lattice α] [IsModularLattice α]

/--
theorem `sup_inf_le_assoc_of_le` / 定理 `sup_inf_le_assoc_of_le`

English:
theorem sup_inf_le_assoc_of_le
  given: {x z : α} (y : α)
  statement: x <= z -> (x ⊔ y) ⊓ z <= x ⊔ y ⊓ z
  proof: IsModularLattice.sup_inf_le_assoc_of_le y

@[to_dual existing]

中文:
定理 sup_inf_le_assoc_of_le
  条件: {x z : α} (y : α)
  结论: x <= z -> (x ⊔ y) ⊓ z <= x ⊔ y ⊓ z
  证明: IsModularLattice.sup_inf_le_assoc_of_le y

@[to_dual existing]

Depends on / 依赖: IsModularLattice, IsModularLattice.sup_inf_le_assoc_of_le, sup_inf_le_assoc_of_le
-/
theorem sup_inf_le_assoc_of_le {x z : α} (y : α) : x <= z -> (x ⊔ y) ⊓ z <= x ⊔ y ⊓ z :=
  IsModularLattice.sup_inf_le_assoc_of_le y

@[to_dual existing]
/--
theorem `inf_sup_le_assoc_of_le` / 定理 `inf_sup_le_assoc_of_le`

English:
theorem inf_sup_le_assoc_of_le
  given: {x z : α} (y : α)
  statement: z <= x -> x ⊓ (y ⊔ z) <= x ⊓ y ⊔ z
  proof: by
  simp_rw [inf_comm x, sup_comm _ z]
  exact sup_inf_le_assoc_of_le y

@[to_dual]

中文:
定理 inf_sup_le_assoc_of_le
  条件: {x z : α} (y : α)
  结论: z <= x -> x ⊓ (y ⊔ z) <= x ⊓ y ⊔ z
  证明: by
  simp_rw [inf_comm x, sup_comm _ z]
  exact sup_inf_le_assoc_of_le y

@[to_dual]

Depends on / 依赖: inf_comm, simp_rw, sup_comm, sup_inf_le_assoc_of_le
-/
theorem inf_sup_le_assoc_of_le {x z : α} (y : α) : z <= x -> x ⊓ (y ⊔ z) <= x ⊓ y ⊔ z := by
  simp_rw [inf_comm x, sup_comm _ z]
  exact sup_inf_le_assoc_of_le y

@[to_dual]
/--
theorem `sup_inf_assoc_of_le` / 定理 `sup_inf_assoc_of_le`

English:
theorem sup_inf_assoc_of_le
  given: {x : α} (y : α) {z : α} (h : x <= z)
  statement: (x ⊔ y) ⊓ z = x ⊔ y ⊓ z
  proof: le_antisymm (sup_inf_le_assoc_of_le y h)
    (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))

@[to_dual]

中文:
定理 sup_inf_assoc_of_le
  条件: {x : α} (y : α) {z : α} (h : x <= z)
  结论: (x ⊔ y) ⊓ z = x ⊔ y ⊓ z
  证明: le_antisymm (sup_inf_le_assoc_of_le y h)
    (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))

@[to_dual]

Depends on / 依赖: inf_le_left, inf_le_right, le_antisymm, le_inf, sup_inf_le_assoc_of_le, sup_le, sup_le_sup_left
-/
theorem sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x <= z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z :=
  le_antisymm (sup_inf_le_assoc_of_le y h)
    (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))

@[to_dual]
/--
theorem `IsModularLattice.inf_sup_inf_assoc` / 定理 `IsModularLattice.inf_sup_inf_assoc`

English:
theorem IsModularLattice.inf_sup_inf_assoc
  given: {x y z : α}
  statement: x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z
  proof: (sup_inf_assoc_of_le y inf_le_right).symm

中文:
定理 是Modular格.inf_sup_inf_assoc
  条件: {x y z : α}
  结论: x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z
  证明: (sup_inf_assoc_of_le y inf_le_right).symm

Depends on / 依赖: inf_le_right, sup_inf_assoc_of_le
-/
theorem IsModularLattice.inf_sup_inf_assoc {x y z : α} : x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  (sup_inf_assoc_of_le y inf_le_right).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsModularLattice αᵒᵈ
  body: ⟨fun y z xz =>
    le_of_eq
      (by
        rw [inf_comm]; rw [sup_comm]; rw [eq_comm]; rw [inf_comm]; rw [sup_comm]
        exact @sup_inf_assoc_of_le α _ _ _ y _ xz)⟩

中文:
实例 :
  签名: 是Modular格 αᵒᵈ
  定义体: ⟨fun y z xz =>
    le_of_eq
      (by
        rw [inf_comm]; rw [sup_comm]; rw [eq_comm]; rw [inf_comm]; rw [sup_comm]
        exact @sup_inf_assoc_of_le α _ _ _ y _ xz)⟩

Depends on / 依赖: eq_comm, inf_comm, le_of_eq, sup_comm, sup_inf_assoc_of_le
-/
instance : IsModularLattice αᵒᵈ :=
  ⟨fun y z xz =>
    le_of_eq
      (by
        rw [inf_comm]; rw [sup_comm]; rw [eq_comm]; rw [inf_comm]; rw [sup_comm]
        exact @sup_inf_assoc_of_le α _ _ _ y _ xz)⟩

variable {x y z : α}

@[to_dual]
/--
theorem `eq_of_le_of_inf_le_of_le_sup` / 定理 `eq_of_le_of_inf_le_of_le_sup`

English:
theorem eq_of_le_of_inf_le_of_le_sup
  given: (hxy : x <= y) (hinf : y ⊓ z <= x) (hsup : y <= x ⊔ z)
  proof: by
  refine hxy.antisymm ?_
  rw [← inf_eq_right]; rw [sup_inf_assoc_of_le _ hxy] at hsup
  rwa [← hsup, sup_le_iff, and_iff_right rfl.le, inf_comm]

@[to_dual]

中文:
定理 eq_of_le_of_inf_le_of_le_sup
  条件: (hxy : x <= y) (hinf : y ⊓ z <= x) (hsup : y <= x ⊔ z)
  证明: by
  refine hxy.antisymm ?_
  rw [← inf_eq_right]; rw [sup_inf_assoc_of_le _ hxy] at hsup
  rwa [← hsup, sup_le_iff, and_iff_right rfl.le, inf_comm]

@[to_dual]

Depends on / 依赖: and_iff_right, antisymm, hxy.antisymm, inf_comm, inf_eq_right, rfl.le, sup_inf_assoc_of_le, sup_le_iff
-/
theorem eq_of_le_of_inf_le_of_le_sup (hxy : x <= y) (hinf : y ⊓ z <= x) (hsup : y <= x ⊔ z) :
    x = y := by
  refine hxy.antisymm ?_
  rw [← inf_eq_right]; rw [sup_inf_assoc_of_le _ hxy] at hsup
  rwa [← hsup, sup_le_iff, and_iff_right rfl.le, inf_comm]

@[to_dual]
/--
theorem `eq_of_le_of_inf_le_of_sup_le` / 定理 `eq_of_le_of_inf_le_of_sup_le`

English:
theorem eq_of_le_of_inf_le_of_sup_le
  given: (hxy : x <= y) (hinf : y ⊓ z <= x ⊓ z) (hsup : y ⊔ z <= x ⊔ z)
  proof: eq_of_le_of_inf_le_of_le_sup hxy (hinf.trans inf_le_left) (le_sup_left.trans hsup)

@[to_dual]

中文:
定理 eq_of_le_of_inf_le_of_sup_le
  条件: (hxy : x <= y) (hinf : y ⊓ z <= x ⊓ z) (hsup : y ⊔ z <= x ⊔ z)
  证明: eq_of_le_of_inf_le_of_le_sup hxy (hinf.trans inf_le_left) (le_sup_left.trans hsup)

@[to_dual]

Depends on / 依赖: eq_of_le_of_inf_le_of_le_sup, hinf.trans, inf_le_left, le_sup_left, le_sup_left.trans
-/
theorem eq_of_le_of_inf_le_of_sup_le (hxy : x <= y) (hinf : y ⊓ z <= x ⊓ z) (hsup : y ⊔ z <= x ⊔ z) :
    x = y :=
  eq_of_le_of_inf_le_of_le_sup hxy (hinf.trans inf_le_left) (le_sup_left.trans hsup)

@[to_dual]
/--
theorem `sup_lt_sup_of_lt_of_inf_le_inf` / 定理 `sup_lt_sup_of_lt_of_inf_le_inf`

English:
theorem sup_lt_sup_of_lt_of_inf_le_inf
  given: (hxy : y < x) (hinf : x ⊓ z <= y ⊓ z)
  statement: y ⊔ z < x ⊔ z
  proof: lt_of_le_of_ne (sup_le_sup_right (le_of_lt hxy) _) fun hsup =>
ne_of_lt hxy eq_of_le_of_inf_le_of_sup_le (le_of_lt hxy) hinf (le_of_eq hsup.symm)

中文:
定理 sup_lt_sup_of_lt_of_inf_le_inf
  条件: (hxy : y < x) (hinf : x ⊓ z <= y ⊓ z)
  结论: y ⊔ z < x ⊔ z
  证明: lt_of_le_of_ne (sup_le_sup_right (le_of_lt hxy) _) fun hsup =>
ne_of_lt hxy eq_of_le_of_inf_le_of_sup_le (le_of_lt hxy) hinf (le_of_eq hsup.symm)

Depends on / 依赖: eq_of_le_of_inf_le_of_sup_le, hsup.symm, le_of_eq, le_of_lt, lt_of_le_of_ne, ne_of_lt, sup_le_sup_right
-/
theorem sup_lt_sup_of_lt_of_inf_le_inf (hxy : y < x) (hinf : x ⊓ z <= y ⊓ z) : y ⊔ z < x ⊔ z :=
  lt_of_le_of_ne (sup_le_sup_right (le_of_lt hxy) _) fun hsup =>
ne_of_lt hxy eq_of_le_of_inf_le_of_sup_le (le_of_lt hxy) hinf (le_of_eq hsup.symm)

/--
theorem `strictMono_inf_prod_sup` / 定理 `strictMono_inf_prod_sup`

English:
theorem strictMono_inf_prod_sup
  statement: StrictMono fun x => (x ⊓ z, x ⊔ z)
  proof: fun _x _y hxy =>
  ⟨⟨inf_le_inf_right _ hxy.le, sup_le_sup_right hxy.le _⟩,
    fun ⟨inf_le, sup_le⟩ => (sup_lt_sup_of_lt_of_inf_le_inf hxy inf_le).not_ge sup_le⟩

中文:
定理 strictMono_inf_prod_sup
  结论: 严格递增 fun x => (x ⊓ z, x ⊔ z)
  证明: fun _x _y hxy =>
  ⟨⟨inf_le_inf_right _ hxy.le, sup_le_sup_right hxy.le _⟩,
    fun ⟨inf_le, sup_le⟩ => (sup_lt_sup_of_lt_of_inf_le_inf hxy inf_le).not_ge sup_le⟩
-/
theorem strictMono_inf_prod_sup : StrictMono fun x => (x ⊓ z, x ⊔ z) := fun _x _y hxy =>
  ⟨⟨inf_le_inf_right _ hxy.le, sup_le_sup_right hxy.le _⟩,
    fun ⟨inf_le, sup_le⟩ => (sup_lt_sup_of_lt_of_inf_le_inf hxy inf_le).not_ge sup_le⟩

/--
theorem `wellFounded_lt_exact_sequence` / 定理 `wellFounded_lt_exact_sequence`

English:
theorem wellFounded_lt_exact_sequence
  statement: {β γ : Type*} [Preorder β] [Preorder γ]
  proof: StrictMono.wellFoundedLT (f := fun A => (f₂ A, g₂ A)) fun A B hAB => by
    simp only [Prod.le_def, lt_iff_le_not_ge, ← gci.l_le_l_iff, ← gi.u_le_u_iff, hf, hg]
    exact strictMono_inf_prod_sup hAB

中文:
定理 wellFounded_lt_exact_sequence
  结论: {β γ : 类型} [预序 β] [预序 γ]
  证明: StrictMono.wellFoundedLT (f := fun A => (f₂ A, g₂ A)) fun A B hAB => by
    simp only [Prod.le_def, lt_iff_le_not_ge, ← gci.l_le_l_iff, ← gi.u_le_u_iff, hf, hg]
    exact strictMono_inf_prod_sup hAB

Depends on / 依赖: Prod.le_def, StrictMono, StrictMono.wellFoundedLT, gci.l_le_l_iff, gi.u_le_u_iff, l_le_l_iff, le_def, lt_iff_le_not_ge, strictMono_inf_prod_sup, u_le_u_iff, wellFoundedLT
-/
theorem wellFounded_lt_exact_sequence {β γ : Type*} [Preorder β] [Preorder γ]
    [h₁ : WellFoundedLT β] [h₂ : WellFoundedLT γ] (K : α)
    (f₁ : β -> α) (f₂ : α -> β) (g₁ : γ -> α) (g₂ : α -> γ) (gci : GaloisCoinsertion f₁ f₂)
    (gi : GaloisInsertion g₂ g₁) (hf : forall a, f₁ (f₂ a) = a ⊓ K) (hg : forall a, g₁ (g₂ a) = a ⊔ K) :
    WellFoundedLT α :=
  StrictMono.wellFoundedLT (f := fun A => (f₂ A, g₂ A)) fun A B hAB => by
    simp only [Prod.le_def, lt_iff_le_not_ge, ← gci.l_le_l_iff, ← gi.u_le_u_iff, hf, hg]
    exact strictMono_inf_prod_sup hAB

/--
theorem `wellFounded_gt_exact_sequence` / 定理 `wellFounded_gt_exact_sequence`

English:
theorem wellFounded_gt_exact_sequence
  statement: {β γ : Type*} [Preorder β] [Preorder γ]
  proof: wellFounded_lt_exact_sequence (α := αᵒᵈ) (β := γᵒᵈ) (γ := βᵒᵈ)
    K g₁ g₂ f₁ f₂ gi.dual gci.dual hg hf

中文:
定理 wellFounded_gt_exact_sequence
  结论: {β γ : 类型} [预序 β] [预序 γ]
  证明: wellFounded_lt_exact_sequence (α := αᵒᵈ) (β := γᵒᵈ) (γ := βᵒᵈ)
    K g₁ g₂ f₁ f₂ gi.dual gci.dual hg hf

Depends on / 依赖: gci.dual, gi.dual, wellFounded_lt_exact_sequence
-/
theorem wellFounded_gt_exact_sequence {β γ : Type*} [Preorder β] [Preorder γ]
    [WellFoundedGT β] [WellFoundedGT γ] (K : α)
    (f₁ : β -> α) (f₂ : α -> β) (g₁ : γ -> α) (g₂ : α -> γ) (gci : GaloisCoinsertion f₁ f₂)
    (gi : GaloisInsertion g₂ g₁) (hf : forall a, f₁ (f₂ a) = a ⊓ K) (hg : forall a, g₁ (g₂ a) = a ⊔ K) :
    WellFoundedGT α :=
  wellFounded_lt_exact_sequence (α := αᵒᵈ) (β := γᵒᵈ) (γ := βᵒᵈ)
    K g₁ g₂ f₁ f₂ gi.dual gci.dual hg hf

set_option backward.isDefEq.respectTransparency false in
/-- The diamond isomorphism between the closed intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
@[simps]
/--
Definition of `infIccOrderIsoIccSup` / `infIccOrderIsoIccSup` 的定义

English:
definition infIccOrderIsoIccSup
  signature: (a b : α)
  body: ⟨x ⊔ b, ⟨le_sup_right, sup_le_sup_right x.prop.2 b⟩⟩
  invFun x := ⟨a ⊓ x, ⟨inf_le_inf_left a x.prop.1, inf_le_left⟩⟩
  left_inv x :=
    Subtype.ext
      (by
        change a ⊓ (↑x ⊔ b) = ↑x
        rw [sup_comm]; rw [← inf_sup_assoc_of_le _ x.prop.2]; rw [sup_eq_right.2 x.prop.1])
  right_inv x :

中文:
定义 infIccOrderIsoIccSup
  签名: (a b : α)
  定义体: ⟨x ⊔ b, ⟨le_sup_right, sup_le_sup_right x.prop.2 b⟩⟩
  invFun x := ⟨a ⊓ x, ⟨inf_le_inf_left a x.prop.1, inf_le_left⟩⟩
  left_inv x :=
    Subtype.ext
      (by
        change a ⊓ (↑x ⊔ b) = ↑x
        rw [sup_comm]; rw [← inf_sup_assoc_of_le _ x.prop.2]; rw [sup_eq_right.2 x.prop.1])
  right_inv x :

Depends on / 依赖: le_sup_right, sup_le_sup_right, x.prop
-/
def infIccOrderIsoIccSup (a b : α) : Icc (a ⊓ b) a ≃o Icc b (a ⊔ b) where
  toFun x := ⟨x ⊔ b, ⟨le_sup_right, sup_le_sup_right x.prop.2 b⟩⟩
  invFun x := ⟨a ⊓ x, ⟨inf_le_inf_left a x.prop.1, inf_le_left⟩⟩
  left_inv x :=
    Subtype.ext
      (by
        change a ⊓ (↑x ⊔ b) = ↑x
        rw [sup_comm]; rw [← inf_sup_assoc_of_le _ x.prop.2]; rw [sup_eq_right.2 x.prop.1])
  right_inv x :=
    Subtype.ext
      (by
        change a ⊓ ↑x ⊔ b = ↑x
        rw [inf_comm]; rw [inf_sup_assoc_of_le _ x.prop.1]; rw [inf_eq_left.2 x.prop.2])
  map_rel_iff' {x y} := by
    simp only [Subtype.mk_le_mk, Equiv.coe_fn_mk]
    rw [← Subtype.coe_le_coe]
    refine ⟨fun h => ?_, fun h => sup_le_sup_right h _⟩
    rw [← sup_eq_right.2 x.prop.1]; rw [inf_sup_assoc_of_le _ x.prop.2]; rw [sup_comm]; rw [←
      sup_eq_right.2 y.prop.1]; rw [inf_sup_assoc_of_le _ y.prop.2]; rw [sup_comm b]
    exact inf_le_inf_left _ h

set_option backward.isDefEq.respectTransparency false in
/-- The diamond isomorphism between the closed intervals `[a ⊓ b, b]` and `[a, a ⊔ b]` -/
@[simps!]
/--
Definition of `infIccOrderIsoIccSup'` / `infIccOrderIsoIccSup'` 的定义

English:
definition infIccOrderIsoIccSup'
  signature: (a b : α)
  body: (OrderIso.setCongr _ _ (by rw [inf_comm])).trans (infIccOrderIsoIccSup b a).trans
    OrderIso.setCongr _ _ (by rw [sup_comm])

中文:
定义 infIccOrderIsoIccSup'
  签名: (a b : α)
  定义体: (OrderIso.setCongr _ _ (by rw [inf_comm])).trans (infIccOrderIsoIccSup b a).trans
    OrderIso.setCongr _ _ (by rw [sup_comm])

Depends on / 依赖: OrderIso, OrderIso.setCongr, infIccOrderIsoIccSup, inf_comm, setCongr, sup_comm
-/
def infIccOrderIsoIccSup' (a b : α) : Icc (a ⊓ b) b ≃o Icc a (a ⊔ b) :=
(OrderIso.setCongr _ _ (by rw [inf_comm])).trans (infIccOrderIsoIccSup b a).trans
    OrderIso.setCongr _ _ (by rw [sup_comm])

/--
theorem `inf_strictMonoOn_Icc_sup` / 定理 `inf_strictMonoOn_Icc_sup`

English:
theorem inf_strictMonoOn_Icc_sup
  given: {a b : α}
  statement: StrictMonoOn (fun c => a ⊓ c) (Icc b (a ⊔ b))
  proof: StrictMono.of_domRestrict (infIccOrderIsoIccSup a b).symm.strictMono

中文:
定理 inf_strictMonoOn_Icc_sup
  条件: {a b : α}
  结论: StrictMonoOn (fun c => a ⊓ c) (闭区间 b (a ⊔ b))
  证明: StrictMono.of_domRestrict (infIccOrderIsoIccSup a b).symm.strictMono

Depends on / 依赖: StrictMono, StrictMono.of_domRestrict, infIccOrderIsoIccSup, of_domRestrict, strictMono, symm.strictMono
-/
theorem inf_strictMonoOn_Icc_sup {a b : α} : StrictMonoOn (fun c => a ⊓ c) (Icc b (a ⊔ b)) :=
  StrictMono.of_domRestrict (infIccOrderIsoIccSup a b).symm.strictMono

/--
theorem `sup_strictMonoOn_Icc_inf` / 定理 `sup_strictMonoOn_Icc_inf`

English:
theorem sup_strictMonoOn_Icc_inf
  given: {a b : α}
  statement: StrictMonoOn (fun c => c ⊔ b) (Icc (a ⊓ b) a)
  proof: StrictMono.of_domRestrict (infIccOrderIsoIccSup a b).strictMono

中文:
定理 sup_strictMonoOn_Icc_inf
  条件: {a b : α}
  结论: StrictMonoOn (fun c => c ⊔ b) (闭区间 (a ⊓ b) a)
  证明: StrictMono.of_domRestrict (infIccOrderIsoIccSup a b).strictMono

Depends on / 依赖: StrictMono, StrictMono.of_domRestrict, infIccOrderIsoIccSup, of_domRestrict, strictMono
-/
theorem sup_strictMonoOn_Icc_inf {a b : α} : StrictMonoOn (fun c => c ⊔ b) (Icc (a ⊓ b) a) :=
  StrictMono.of_domRestrict (infIccOrderIsoIccSup a b).strictMono

set_option backward.isDefEq.respectTransparency false in
/-- The diamond isomorphism between the open intervals `(a ⊓ b, a)` and `(b, a ⊔ b)`. -/
@[simps]
/--
Definition of `infIooOrderIsoIooSup` / `infIooOrderIsoIooSup` 的定义

English:
definition infIooOrderIsoIooSup
  signature: (a b : α)
  body: ⟨c ⊔ b,
le_sup_right.trans_lt
        sup_strictMonoOn_Icc_inf (left_mem_Icc.2 inf_le_left) (Ioo_subset_Icc_self c.2) c.2.1,
      sup_strictMonoOn_Icc_inf (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 inf_le_left) c.2.2⟩
  invFun c :=
    ⟨a ⊓ c,
      inf_strictMonoOn_Icc_sup (left_mem_Icc.2 le_sup_r

中文:
定义 infIooOrderIsoIooSup
  签名: (a b : α)
  定义体: ⟨c ⊔ b,
le_sup_right.trans_lt
        sup_strictMonoOn_Icc_inf (left_mem_Icc.2 inf_le_left) (Ioo_subset_Icc_self c.2) c.2.1,
      sup_strictMonoOn_Icc_inf (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 inf_le_left) c.2.2⟩
  invFun c :=
    ⟨a ⊓ c,
      inf_strictMonoOn_Icc_sup (left_mem_Icc.2 le_sup_r

Depends on / 依赖: Ioo_subset_Icc_self, Subtype, Subtype.ext, inf_le_left, inf_le_left.trans_lt, inf_strictMonoOn_Icc_sup, inf_sup_assoc_of_le, invFun, le_sup_right, le_sup_right.trans_lt, left_inv, left_mem_Icc, right_mem_Icc, sup_comm, sup_strictMonoOn_Icc_inf, trans_lt
-/
def infIooOrderIsoIooSup (a b : α) : Ioo (a ⊓ b) a ≃o Ioo b (a ⊔ b) where
  toFun c :=
    ⟨c ⊔ b,
le_sup_right.trans_lt
        sup_strictMonoOn_Icc_inf (left_mem_Icc.2 inf_le_left) (Ioo_subset_Icc_self c.2) c.2.1,
      sup_strictMonoOn_Icc_inf (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 inf_le_left) c.2.2⟩
  invFun c :=
    ⟨a ⊓ c,
      inf_strictMonoOn_Icc_sup (left_mem_Icc.2 le_sup_right) (Ioo_subset_Icc_self c.2) c.2.1,
inf_le_left.trans_lt'
        inf_strictMonoOn_Icc_sup (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 le_sup_right) c.2.2⟩
  left_inv c :=
Subtype.ext by
      dsimp
      rw [sup_comm]; rw [← inf_sup_assoc_of_le _ c.prop.2.le]; rw [sup_eq_right.2 c.prop.1.le]
  right_inv c :=
Subtype.ext by
      dsimp
      rw [inf_comm]; rw [inf_sup_assoc_of_le _ c.prop.1.le]; rw [inf_eq_left.2 c.prop.2.le]
  map_rel_iff' := @fun c d =>
    @OrderIso.le_iff_le _ _ _ _ (infIccOrderIsoIccSup _ _) ⟨c.1, Ioo_subset_Icc_self c.2⟩
      ⟨d.1, Ioo_subset_Icc_self d.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The diamond isomorphism between the open intervals `(a ⊓ b, b)` and `(a, a ⊔ b)`. -/
@[simps!]
/--
Definition of `infIooOrderIsoIooSup'` / `infIooOrderIsoIooSup'` 的定义

English:
definition infIooOrderIsoIooSup'
  signature: (a b : α)
  body: (OrderIso.setCongr _ _ (by rw [inf_comm])).trans (infIooOrderIsoIooSup b a).trans
    OrderIso.setCongr _ _ (by rw [sup_comm])

中文:
定义 infIooOrderIsoIooSup'
  签名: (a b : α)
  定义体: (OrderIso.setCongr _ _ (by rw [inf_comm])).trans (infIooOrderIsoIooSup b a).trans
    OrderIso.setCongr _ _ (by rw [sup_comm])

Depends on / 依赖: OrderIso, OrderIso.setCongr, infIooOrderIsoIooSup, inf_comm, setCongr, sup_comm
-/
def infIooOrderIsoIooSup' (a b : α) : Ioo (a ⊓ b) b ≃o Ioo a (a ⊔ b) :=
(OrderIso.setCongr _ _ (by rw [inf_comm])).trans (infIooOrderIsoIooSup b a).trans
    OrderIso.setCongr _ _ (by rw [sup_comm])

-- See note [lower instance priority]
instance (priority := 100) IsModularLattice.to_isLowerModularLattice : IsLowerModularLattice α :=
  ⟨fun {a b} => by
    simp_rw [covBy_iff_Ioo_eq, sup_comm a, inf_comm a, ← isEmpty_coe_sort, right_lt_sup,
      inf_lt_left, (infIooOrderIsoIooSup b a).symm.toEquiv.isEmpty_congr]
    exact id⟩

-- See note [lower instance priority]
@[to_dual existing]
instance (priority := 100) IsModularLattice.to_isUpperModularLattice : IsUpperModularLattice α :=
  ⟨fun {a b} => by
    simp_rw [covBy_iff_Ioo_eq, ← isEmpty_coe_sort, right_lt_sup, inf_lt_left,
      (infIooOrderIsoIooSup a b).toEquiv.isEmpty_congr]
    exact id⟩

end IsModularLattice

namespace IsCompl

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

/--
Definition of `IicOrderIsoIci` / `IicOrderIsoIci` 的定义

English:
definition IicOrderIsoIci
  signature: {a b : α} (h : IsCompl a b)
  body: (OrderIso.setCongr (Set.Iic a) (Set.Icc (a ⊓ b) a)
        (h.inf_eq_bot.symm ▸ Set.Icc_bot.symm)).trans <|
    (infIccOrderIsoIccSup a b).trans
      (OrderIso.setCongr (Set.Icc b (a ⊔ b)) (Set.Ici b) (h.sup_eq_top.symm ▸ Set.Icc_top))

中文:
定义 IicOrderIsoIci
  签名: {a b : α} (h : 是补集 a b)
  定义体: (OrderIso.setCongr (Set.Iic a) (Set.Icc (a ⊓ b) a)
        (h.inf_eq_bot.symm ▸ Set.Icc_bot.symm)).trans <|
    (infIccOrderIsoIccSup a b).trans
      (OrderIso.setCongr (Set.Icc b (a ⊔ b)) (Set.Ici b) (h.sup_eq_top.symm ▸ Set.Icc_top))

Depends on / 依赖: Icc_bot, Icc_top, OrderIso, OrderIso.setCongr, Set.Icc, Set.Icc_bot.symm, Set.Icc_top, Set.Ici, Set.Iic, h.inf_eq_bot.symm, h.sup_eq_top.symm, infIccOrderIsoIccSup, inf_eq_bot, setCongr, sup_eq_top
-/
def IicOrderIsoIci {a b : α} (h : IsCompl a b) : Set.Iic a ≃o Set.Ici b :=
  (OrderIso.setCongr (Set.Iic a) (Set.Icc (a ⊓ b) a)
        (h.inf_eq_bot.symm ▸ Set.Icc_bot.symm)).trans <|
    (infIccOrderIsoIccSup a b).trans
      (OrderIso.setCongr (Set.Icc b (a ⊔ b)) (Set.Ici b) (h.sup_eq_top.symm ▸ Set.Icc_top))

end IsCompl

/--
lemma `le_iff_eq_of_codisjoint_of_disjoint` / 引理 `le_iff_eq_of_codisjoint_of_disjoint`

English:
lemma le_iff_eq_of_codisjoint_of_disjoint
  statement: [Lattice α] [BoundedOrder α] [IsModularLattice α]
  proof: ⟨fun h₂ => le_antisymm h₂ by simpa [h₀.eq_top, h₁.eq_bot] using sup_inf_le_assoc_of_le b h₂,
   le_of_eq⟩

中文:
引理 le_iff_eq_of_codisjoint_of_disjoint
  结论: [格 α] [有界序 α] [是Modular格 α]
  证明: ⟨fun h₂ => le_antisymm h₂ by simpa [h₀.eq_top, h₁.eq_bot] using sup_inf_le_assoc_of_le b h₂,
   le_of_eq⟩

Depends on / 依赖: eq_bot, eq_top, le_antisymm, le_of_eq, sup_inf_le_assoc_of_le
-/
lemma le_iff_eq_of_codisjoint_of_disjoint [Lattice α] [BoundedOrder α] [IsModularLattice α]
    {a b c : α} (h₀ : Codisjoint a b) (h₁ : Disjoint b c) :
    a <= c ↔ a = c :=
⟨fun h₂ => le_antisymm h₂ by simpa [h₀.eq_top, h₁.eq_bot] using sup_inf_le_assoc_of_le b h₂,
   le_of_eq⟩

/--
theorem `isModularLattice_iff_inf_sup_inf_assoc` / 定理 `isModularLattice_iff_inf_sup_inf_assoc`

English:
theorem isModularLattice_iff_inf_sup_inf_assoc
  given: [Lattice α]
  proof: ⟨fun h => @IsModularLattice.inf_sup_inf_assoc _ _ h, fun h =>
    ⟨fun y z xz => by rw [← inf_eq_left.2 xz, h]⟩⟩

中文:
定理 isModularLattice_iff_inf_sup_inf_assoc
  条件: [格 α]
  证明: ⟨fun h => @IsModularLattice.inf_sup_inf_assoc _ _ h, fun h =>
    ⟨fun y z xz => by rw [← inf_eq_left.2 xz, h]⟩⟩

Depends on / 依赖: IsModularLattice, IsModularLattice.inf_sup_inf_assoc, inf_eq_left, inf_sup_inf_assoc
-/
theorem isModularLattice_iff_inf_sup_inf_assoc [Lattice α] :
    IsModularLattice α ↔ forall x y z : α, x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  ⟨fun h => @IsModularLattice.inf_sup_inf_assoc _ _ h, fun h =>
    ⟨fun y z xz => by rw [← inf_eq_left.2 xz, h]⟩⟩

namespace DistribLattice

instance (priority := 100) [DistribLattice α] : IsModularLattice α :=
  ⟨fun y z xz => by rw [inf_sup_right, inf_eq_left.2 xz]⟩

end DistribLattice

namespace Disjoint

variable {a b c : α}

@[to_dual]
/--
theorem `disjoint_sup_right_of_disjoint_sup_left` / 定理 `disjoint_sup_right_of_disjoint_sup_left`

English:
theorem disjoint_sup_right_of_disjoint_sup_left
  statement: [Lattice α] [OrderBot α]
  proof: by
  rw [disjoint_iff_inf_le]; rw [← h.eq_bot]; rw [sup_comm]
  apply le_inf inf_le_left
  apply (inf_le_inf_right (c ⊔ b) le_sup_right).trans
  rw [sup_comm]; rw [IsModularLattice.sup_inf_sup_assoc]; rw [hsup.eq_bot]; rw [bot_sup_eq]

@[to_dual]

中文:
定理 disjoint_sup_right_of_disjoint_sup_left
  结论: [格 α] [有底序 α]
  证明: by
  rw [disjoint_iff_inf_le]; rw [← h.eq_bot]; rw [sup_comm]
  apply le_inf inf_le_left
  apply (inf_le_inf_right (c ⊔ b) le_sup_right).trans
  rw [sup_comm]; rw [IsModularLattice.sup_inf_sup_assoc]; rw [hsup.eq_bot]; rw [bot_sup_eq]

@[to_dual]

Depends on / 依赖: IsModularLattice, IsModularLattice.sup_inf_sup_assoc, bot_sup_eq, disjoint_iff_inf_le, eq_bot, h.eq_bot, hsup.eq_bot, inf_le_inf_right, inf_le_left, le_inf, le_sup_right, sup_comm, sup_inf_sup_assoc
-/
theorem disjoint_sup_right_of_disjoint_sup_left [Lattice α] [OrderBot α]
    [IsModularLattice α] (h : Disjoint a b) (hsup : Disjoint (a ⊔ b) c) :
    Disjoint a (b ⊔ c) := by
  rw [disjoint_iff_inf_le]; rw [← h.eq_bot]; rw [sup_comm]
  apply le_inf inf_le_left
  apply (inf_le_inf_right (c ⊔ b) le_sup_right).trans
  rw [sup_comm]; rw [IsModularLattice.sup_inf_sup_assoc]; rw [hsup.eq_bot]; rw [bot_sup_eq]

@[to_dual]
/--
theorem `disjoint_sup_left_of_disjoint_sup_right` / 定理 `disjoint_sup_left_of_disjoint_sup_right`

English:
theorem disjoint_sup_left_of_disjoint_sup_right
  statement: [Lattice α] [OrderBot α]
  proof: by
  rw [disjoint_comm]; rw [sup_comm]
  apply Disjoint.disjoint_sup_right_of_disjoint_sup_left h.symm
  rwa [sup_comm, disjoint_comm] at hsup

@[to_dual]

中文:
定理 disjoint_sup_left_of_disjoint_sup_right
  结论: [格 α] [有底序 α]
  证明: by
  rw [disjoint_comm]; rw [sup_comm]
  apply Disjoint.disjoint_sup_right_of_disjoint_sup_left h.symm
  rwa [sup_comm, disjoint_comm] at hsup

@[to_dual]

Depends on / 依赖: Disjoint, Disjoint.disjoint_sup_right_of_disjoint_sup_left, disjoint_comm, disjoint_sup_right_of_disjoint_sup_left, h.symm, sup_comm
-/
theorem disjoint_sup_left_of_disjoint_sup_right [Lattice α] [OrderBot α]
    [IsModularLattice α] (h : Disjoint b c) (hsup : Disjoint a (b ⊔ c)) :
    Disjoint (a ⊔ b) c := by
  rw [disjoint_comm]; rw [sup_comm]
  apply Disjoint.disjoint_sup_right_of_disjoint_sup_left h.symm
  rwa [sup_comm, disjoint_comm] at hsup

@[to_dual]
/--
lemma `_root_.disjoint_sup_right_of_disjoint_sup_right` / 引理 `_root_.disjoint_sup_right_of_disjoint_sup_right`

English:
lemma _root_.disjoint_sup_right_of_disjoint_sup_right
  statement: [Lattice α] [OrderBot α] [IsModularLattice α]
  proof: by
  rw [sup_comm] at h₂ ⊢
  rw [disjoint_comm]
  exact (h₁.mono_right le_sup_right).disjoint_sup_left_of_disjoint_sup_right h₂

@[to_dual]

中文:
引理 _root_.disjoint_sup_right_of_disjoint_sup_right
  结论: [格 α] [有底序 α] [是Modular格 α]
  证明: by
  rw [sup_comm] at h₂ ⊢
  rw [disjoint_comm]
  exact (h₁.mono_right le_sup_right).disjoint_sup_left_of_disjoint_sup_right h₂

@[to_dual]

Depends on / 依赖: disjoint_comm, disjoint_sup_left_of_disjoint_sup_right, le_sup_right, mono_right, sup_comm
-/
lemma _root_.disjoint_sup_right_of_disjoint_sup_right [Lattice α] [OrderBot α] [IsModularLattice α]
    (h₁ : Disjoint a (b ⊔ c)) (h₂ : Disjoint b (c ⊔ a)) :
    Disjoint c (a ⊔ b) := by
  rw [sup_comm] at h₂ ⊢
  rw [disjoint_comm]
  exact (h₁.mono_right le_sup_right).disjoint_sup_left_of_disjoint_sup_right h₂

@[to_dual]
/--
theorem `isCompl_sup_right_of_isCompl_sup_left` / 定理 `isCompl_sup_right_of_isCompl_sup_left`

English:
theorem isCompl_sup_right_of_isCompl_sup_left
  statement: [Lattice α] [BoundedOrder α] [IsModularLattice α]
  proof: ⟨h.disjoint_sup_right_of_disjoint_sup_left hcomp.disjoint, codisjoint_assoc.mp hcomp.codisjoint⟩

@[to_dual]

中文:
定理 isCompl_sup_right_of_isCompl_sup_left
  结论: [格 α] [有界序 α] [是Modular格 α]
  证明: ⟨h.disjoint_sup_right_of_disjoint_sup_left hcomp.disjoint, codisjoint_assoc.mp hcomp.codisjoint⟩

@[to_dual]

Depends on / 依赖: codisjoint, codisjoint_assoc, codisjoint_assoc.mp, disjoint, disjoint_sup_right_of_disjoint_sup_left, h.disjoint_sup_right_of_disjoint_sup_left, hcomp.codisjoint, hcomp.disjoint
-/
theorem isCompl_sup_right_of_isCompl_sup_left [Lattice α] [BoundedOrder α] [IsModularLattice α]
    (h : Disjoint a b) (hcomp : IsCompl (a ⊔ b) c) :
    IsCompl a (b ⊔ c) :=
  ⟨h.disjoint_sup_right_of_disjoint_sup_left hcomp.disjoint, codisjoint_assoc.mp hcomp.codisjoint⟩

@[to_dual]
/--
theorem `isCompl_sup_left_of_isCompl_sup_right` / 定理 `isCompl_sup_left_of_isCompl_sup_right`

English:
theorem isCompl_sup_left_of_isCompl_sup_right
  statement: [Lattice α] [BoundedOrder α] [IsModularLattice α]
  proof: ⟨h.disjoint_sup_left_of_disjoint_sup_right hcomp.disjoint, codisjoint_assoc.mpr hcomp.codisjoint⟩

中文:
定理 isCompl_sup_left_of_isCompl_sup_right
  结论: [格 α] [有界序 α] [是Modular格 α]
  证明: ⟨h.disjoint_sup_left_of_disjoint_sup_right hcomp.disjoint, codisjoint_assoc.mpr hcomp.codisjoint⟩

Depends on / 依赖: codisjoint, codisjoint_assoc, codisjoint_assoc.mpr, disjoint, disjoint_sup_left_of_disjoint_sup_right, h.disjoint_sup_left_of_disjoint_sup_right, hcomp.codisjoint, hcomp.disjoint
-/
theorem isCompl_sup_left_of_isCompl_sup_right [Lattice α] [BoundedOrder α] [IsModularLattice α]
    (h : Disjoint b c) (hcomp : IsCompl a (b ⊔ c)) :
    IsCompl (a ⊔ b) c :=
  ⟨h.disjoint_sup_left_of_disjoint_sup_right hcomp.disjoint, codisjoint_assoc.mpr hcomp.codisjoint⟩

end Disjoint

/--
lemma `Set.Iic.isCompl_inf_inf_of_isCompl_of_le` / 引理 `Set.Iic.isCompl_inf_inf_of_isCompl_of_le`

English:
lemma Set.Iic.isCompl_inf_inf_of_isCompl_of_le
  statement: [Lattice α] [BoundedOrder α] [IsModularLattice α]
  proof: by
  constructor
  · simp [disjoint_iff, Subtype.ext_iff, inf_comm a c, inf_assoc a, ← inf_assoc b, h₁.inf_eq_bot]
  · simp only [Iic.codisjoint_iff, inf_comm a, IsModularLattice.inf_sup_inf_assoc]
    simp [inf_of_le_left h₂, h₁.sup_eq_top]

中文:
引理 集合.左无界右闭区间.isCompl_inf_inf_of_isCompl_of_le
  结论: [格 α] [有界序 α] [是Modular格 α]
  证明: by
  constructor
  · simp [disjoint_iff, Subtype.ext_iff, inf_comm a c, inf_assoc a, ← inf_assoc b, h₁.inf_eq_bot]
  · simp only [Iic.codisjoint_iff, inf_comm a, IsModularLattice.inf_sup_inf_assoc]
    simp [inf_of_le_left h₂, h₁.sup_eq_top]

Depends on / 依赖: Iic.codisjoint_iff, IsModularLattice, IsModularLattice.inf_sup_inf_assoc, Subtype, Subtype.ext_iff, codisjoint_iff, disjoint_iff, ext_iff, inf_assoc, inf_comm, inf_eq_bot, inf_of_le_left, inf_sup_inf_assoc, sup_eq_top
-/
lemma Set.Iic.isCompl_inf_inf_of_isCompl_of_le [Lattice α] [BoundedOrder α] [IsModularLattice α]
    {a b c : α} (h₁ : IsCompl b c) (h₂ : b <= a) :
    IsCompl (⟨a ⊓ b, inf_le_left⟩ : Iic a) (⟨a ⊓ c, inf_le_left⟩ : Iic a) := by
  constructor
  · simp [disjoint_iff, Subtype.ext_iff, inf_comm a c, inf_assoc a, ← inf_assoc b, h₁.inf_eq_bot]
  · simp only [Iic.codisjoint_iff, inf_comm a, IsModularLattice.inf_sup_inf_assoc]
    simp [inf_of_le_left h₂, h₁.sup_eq_top]

namespace IsModularLattice

variable [Lattice α] [IsModularLattice α] {a b c : α}

/--
Instance `isModularLattice_Iic` / 实例 `isModularLattice_Iic`

English:
instance isModularLattice_Iic
  signature: : IsModularLattice (Set.Iic a)
  body: ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z <= ↑x ⊔ ↑y ⊓ ↑z)⟩

中文:
实例 isModularLattice_Iic
  签名: : 是Modular格 (集合.左无界右闭区间 a)
  定义体: ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z <= ↑x ⊔ ↑y ⊓ ↑z)⟩

Depends on / 依赖: sup_inf_le_assoc_of_le
-/
instance isModularLattice_Iic : IsModularLattice (Set.Iic a) :=
  ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z <= ↑x ⊔ ↑y ⊓ ↑z)⟩

/--
Instance `isModularLattice_Ici` / 实例 `isModularLattice_Ici`

English:
instance isModularLattice_Ici
  signature: : IsModularLattice (Set.Ici a)
  body: ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z <= ↑x ⊔ ↑y ⊓ ↑z)⟩

中文:
实例 isModularLattice_Ici
  签名: : 是Modular格 (集合.左闭右无界区间 a)
  定义体: ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z <= ↑x ⊔ ↑y ⊓ ↑z)⟩

Depends on / 依赖: sup_inf_le_assoc_of_le
-/
instance isModularLattice_Ici : IsModularLattice (Set.Ici a) :=
  ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z <= ↑x ⊔ ↑y ⊓ ↑z)⟩

section ComplementedLattice

variable [BoundedOrder α] [ComplementedLattice α]

/--
theorem `exists_inf_eq_and_sup_eq` / 定理 `exists_inf_eq_and_sup_eq`

English:
theorem exists_inf_eq_and_sup_eq
  given: (hb : a <= b) (hc : b <= c)
  statement: exists b', b ⊓ b' = a ∧ b ⊔ b' = c
  proof: by
  obtain ⟨d, hdisjoint, hcodisjoint⟩ := exists_isCompl b
  refine ⟨(d ⊔ a) ⊓ c, ?_, ?_⟩
  · simpa [← inf_assoc, ← inf_sup_assoc_of_le _ hb, hdisjoint.eq_bot] using hb.trans hc
  · simp [← sup_inf_assoc_of_le _ hc, ← sup_assoc, hcodisjoint.eq_top]

中文:
定理 存在_inf_eq_and_sup_eq
  条件: (hb : a <= b) (hc : b <= c)
  结论: 存在 b', b ⊓ b' = a ∧ b ⊔ b' = c
  证明: by
  obtain ⟨d, hdisjoint, hcodisjoint⟩ := exists_isCompl b
  refine ⟨(d ⊔ a) ⊓ c, ?_, ?_⟩
  · simpa [← inf_assoc, ← inf_sup_assoc_of_le _ hb, hdisjoint.eq_bot] using hb.trans hc
  · simp [← sup_inf_assoc_of_le _ hc, ← sup_assoc, hcodisjoint.eq_top]

Depends on / 依赖: eq_bot, eq_top, exists_isCompl, hb.trans, hcodisjoint, hcodisjoint.eq_top, hdisjoint, hdisjoint.eq_bot, inf_assoc, inf_sup_assoc_of_le, sup_assoc, sup_inf_assoc_of_le
-/
theorem exists_inf_eq_and_sup_eq (hb : a <= b) (hc : b <= c) : exists b', b ⊓ b' = a ∧ b ⊔ b' = c := by
  obtain ⟨d, hdisjoint, hcodisjoint⟩ := exists_isCompl b
  refine ⟨(d ⊔ a) ⊓ c, ?_, ?_⟩
  · simpa [← inf_assoc, ← inf_sup_assoc_of_le _ hb, hdisjoint.eq_bot] using hb.trans hc
  · simp [← sup_inf_assoc_of_le _ hc, ← sup_assoc, hcodisjoint.eq_top]

/--
theorem `exists_disjoint_and_sup_eq` / 定理 `exists_disjoint_and_sup_eq`

English:
theorem exists_disjoint_and_sup_eq
  given: (h : a <= b)
  statement: exists a', Disjoint a a' ∧ a ⊔ a' = b
  proof: by
  simp_rw [disjoint_iff]
  apply exists_inf_eq_and_sup_eq (by simp) h

中文:
定理 存在_disjoint_and_sup_eq
  条件: (h : a <= b)
  结论: 存在 a', Disjoint a a' ∧ a ⊔ a' = b
  证明: by
  simp_rw [disjoint_iff]
  apply exists_inf_eq_and_sup_eq (by simp) h

Depends on / 依赖: disjoint_iff, exists_inf_eq_and_sup_eq, simp_rw
-/
theorem exists_disjoint_and_sup_eq (h : a <= b) : exists a', Disjoint a a' ∧ a ⊔ a' = b := by
  simp_rw [disjoint_iff]
  apply exists_inf_eq_and_sup_eq (by simp) h

/--
theorem `exists_inf_eq_and_codisjoint` / 定理 `exists_inf_eq_and_codisjoint`

English:
theorem exists_inf_eq_and_codisjoint
  given: (h : a <= b)
  statement: exists b', b ⊓ b' = a ∧ Codisjoint b b'
  proof: by
  simp_rw [codisjoint_iff]
  apply exists_inf_eq_and_sup_eq h (by simp)

中文:
定理 存在_inf_eq_and_codisjoint
  条件: (h : a <= b)
  结论: 存在 b', b ⊓ b' = a ∧ Codisjoint b b'
  证明: by
  simp_rw [codisjoint_iff]
  apply exists_inf_eq_and_sup_eq h (by simp)

Depends on / 依赖: codisjoint_iff, exists_inf_eq_and_sup_eq, simp_rw
-/
theorem exists_inf_eq_and_codisjoint (h : a <= b) : exists b', b ⊓ b' = a ∧ Codisjoint b b' := by
  simp_rw [codisjoint_iff]
  apply exists_inf_eq_and_sup_eq h (by simp)

/--
Instance `complementedLattice_Icc` / 实例 `complementedLattice_Icc`

English:
instance complementedLattice_Icc
  signature: [Fact (a <= b)]
  body: fun ⟨x, ha, hb⟩ => by
    simp_rw [Set.Icc.isCompl_iff]
    obtain ⟨y, rfl, rfl⟩ := exists_inf_eq_and_sup_eq ha hb
    exact ⟨⟨y, inf_le_right, le_sup_right⟩, rfl, rfl⟩

中文:
实例 complementedLattice_Icc
  签名: [Fact (a <= b)]
  定义体: fun ⟨x, ha, hb⟩ => by
    simp_rw [Set.Icc.isCompl_iff]
    obtain ⟨y, rfl, rfl⟩ := exists_inf_eq_and_sup_eq ha hb
    exact ⟨⟨y, inf_le_right, le_sup_right⟩, rfl, rfl⟩

Depends on / 依赖: Set.Icc.isCompl_iff, exists_inf_eq_and_sup_eq, inf_le_right, isCompl_iff, le_sup_right, simp_rw
-/
instance complementedLattice_Icc [Fact (a <= b)] : ComplementedLattice (Set.Icc a b) where
  exists_isCompl := fun ⟨x, ha, hb⟩ => by
    simp_rw [Set.Icc.isCompl_iff]
    obtain ⟨y, rfl, rfl⟩ := exists_inf_eq_and_sup_eq ha hb
    exact ⟨⟨y, inf_le_right, le_sup_right⟩, rfl, rfl⟩

/--
Instance `complementedLattice_Iic` / 实例 `complementedLattice_Iic`

English:
instance complementedLattice_Iic
  signature: : ComplementedLattice (Set.Iic a) where
  body: fun ⟨x, hx⟩ => by
    simp_rw [Set.Iic.isCompl_iff]
    obtain ⟨y, hdisjoint, rfl⟩ := exists_disjoint_and_sup_eq hx
    exact ⟨⟨y, le_sup_right⟩, hdisjoint, rfl⟩

中文:
实例 complementedLattice_Iic
  签名: : 有补格 (集合.左无界右闭区间 a) where
  定义体: fun ⟨x, hx⟩ => by
    simp_rw [Set.Iic.isCompl_iff]
    obtain ⟨y, hdisjoint, rfl⟩ := exists_disjoint_and_sup_eq hx
    exact ⟨⟨y, le_sup_right⟩, hdisjoint, rfl⟩

Depends on / 依赖: Set.Iic.isCompl_iff, exists_disjoint_and_sup_eq, hdisjoint, isCompl_iff, le_sup_right, simp_rw
-/
instance complementedLattice_Iic : ComplementedLattice (Set.Iic a) where
  exists_isCompl := fun ⟨x, hx⟩ => by
    simp_rw [Set.Iic.isCompl_iff]
    obtain ⟨y, hdisjoint, rfl⟩ := exists_disjoint_and_sup_eq hx
    exact ⟨⟨y, le_sup_right⟩, hdisjoint, rfl⟩

/--
Instance `complementedLattice_Ici` / 实例 `complementedLattice_Ici`

English:
instance complementedLattice_Ici
  signature: : ComplementedLattice (Set.Ici a) where
  body: fun ⟨x, hx⟩ => by
    simp_rw [Set.Ici.isCompl_iff]
    obtain ⟨y, rfl, hcodisjoint⟩ := exists_inf_eq_and_codisjoint hx
    exact ⟨⟨y, inf_le_right⟩, rfl, hcodisjoint⟩

中文:
实例 complementedLattice_Ici
  签名: : 有补格 (集合.左闭右无界区间 a) where
  定义体: fun ⟨x, hx⟩ => by
    simp_rw [Set.Ici.isCompl_iff]
    obtain ⟨y, rfl, hcodisjoint⟩ := exists_inf_eq_and_codisjoint hx
    exact ⟨⟨y, inf_le_right⟩, rfl, hcodisjoint⟩

Depends on / 依赖: Set.Ici.isCompl_iff, exists_inf_eq_and_codisjoint, hcodisjoint, inf_le_right, isCompl_iff, simp_rw
-/
instance complementedLattice_Ici : ComplementedLattice (Set.Ici a) where
  exists_isCompl := fun ⟨x, hx⟩ => by
    simp_rw [Set.Ici.isCompl_iff]
    obtain ⟨y, rfl, hcodisjoint⟩ := exists_inf_eq_and_codisjoint hx
    exact ⟨⟨y, inf_le_right⟩, rfl, hcodisjoint⟩

/-- A disjoint element can be enlarged to a complementary element. -/
@[to_dual /-- A codisjoint element can be shrunk to a complementary element. -/]
/--
theorem `_root_.Disjoint.exists_isCompl` / 定理 `_root_.Disjoint.exists_isCompl`

English:
theorem _root_.Disjoint.exists_isCompl
  given: {a b : α} (hab : Disjoint a b)
  proof: by
  obtain ⟨u, hu⟩ := ComplementedLattice.exists_isCompl (a ⊔ b)
  exact ⟨u ⊔ a, le_sup_right, hab.isCompl_sup_left_of_isCompl_sup_right hu.symm⟩

中文:
定理 _root_.Disjoint.存在_isCompl
  条件: {a b : α} (hab : Disjoint a b)
  证明: by
  obtain ⟨u, hu⟩ := ComplementedLattice.exists_isCompl (a ⊔ b)
  exact ⟨u ⊔ a, le_sup_right, hab.isCompl_sup_left_of_isCompl_sup_right hu.symm⟩

Depends on / 依赖: ComplementedLattice, ComplementedLattice.exists_isCompl, exists_isCompl, hab.isCompl_sup_left_of_isCompl_sup_right, hu.symm, isCompl_sup_left_of_isCompl_sup_right, le_sup_right
-/
theorem _root_.Disjoint.exists_isCompl {a b : α} (hab : Disjoint a b) :
    exists a' : α, a <= a' ∧ IsCompl a' b := by
  obtain ⟨u, hu⟩ := ComplementedLattice.exists_isCompl (a ⊔ b)
  exact ⟨u ⊔ a, le_sup_right, hab.isCompl_sup_left_of_isCompl_sup_right hu.symm⟩

end ComplementedLattice

end IsModularLattice
