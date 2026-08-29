/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Bool.Basic
public import Mathlib.Logic.Pairwise
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.ULift

/-!
# (Semi-)lattices

Semilattices are partially ordered sets with join (least upper bound, or `sup`) or meet (greatest
lower bound, or `inf`) operations. Lattices are posets that are both join-semilattices and
meet-semilattices.

Distributive lattices are lattices which satisfy any of four equivalent distributivity properties,
of `sup` over `inf`, on the left or on the right.

## Main declarations

* `SemilatticeSup`: a type class for join semilattices
* `SemilatticeSup.mk'`: an alternative constructor for `SemilatticeSup` via proofs that `⊔` is
  commutative, associative and idempotent.
* `SemilatticeInf`: a type class for meet semilattices
* `SemilatticeSup.mk'`: an alternative constructor for `SemilatticeInf` via proofs that `⊓` is
  commutative, associative and idempotent.

* `Lattice`: a type class for lattices
* `Lattice.mk'`: an alternative constructor for `Lattice` via proofs that `⊔` and `⊓` are
  commutative, associative and satisfy a pair of "absorption laws".

* `DistribLattice`: a type class for distributive lattices.

## Notation

* `a ⊔ b`: the supremum or join of `a` and `b`
* `a ⊓ b`: the infimum or meet of `a` and `b`

## TODO

* (Semi-)lattice homomorphisms
* Alternative constructors for distributive lattices from the other distributive properties

## Tags

semilattice, lattice

-/

@[expose] public section

universe u v w

variable {α : Type u} {β : Type v}

/-!
### Join-semilattices
-/

/--
Definition of `SemilatticeSup` / `SemilatticeSup` 的定义

English:
class SemilatticeSup
  parameters: (α : Type u)
  extends: PartialOrder α
  axioms and operations (4):
    - sup : α -> α -> α
    - le_sup_left : forall a b : α, a <= sup a b
    - le_sup_right : forall a b : α, b <= sup a b
    - sup_le : forall a b c : α, a <= c -> b <= c -> sup a b <= c

中文:
类 SemilatticeSup
  参数: (α : 类型u)
  继承: 偏序 α
  公理与运算 (4 个):
    - sup : α -> α -> α
    - le_sup_left : 对任意 a b : α, a <= 上确界 a b
    - le_sup_right : 对任意 a b : α, b <= 上确界 a b
    - sup_le : 对任意 a b c : α, a <= c -> b <= c -> 上确界 a b <= c
-/
class SemilatticeSup (α : Type u) extends PartialOrder α where
  /-- The binary supremum, used to derive `Max α` -/
  sup : α -> α -> α
  /-- The supremum is an upper bound on the first argument -/
  protected le_sup_left : forall a b : α, a <= sup a b
  /-- The supremum is an upper bound on the second argument -/
  protected le_sup_right : forall a b : α, b <= sup a b
  /-- The supremum is the *least* upper bound -/
  protected sup_le : forall a b c : α, a <= c -> b <= c -> sup a b <= c

/-- A `SemilatticeInf` is a meet-semilattice, that is, a partial order
  with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
  `⊓` which is the greatest element smaller than both factors. -/
@[to_dual]
/--
Definition of `SemilatticeInf` / `SemilatticeInf` 的定义

English:
class SemilatticeInf
  parameters: (α : Type u)
  extends: PartialOrder α
  axioms and operations (4):
    - inf : α -> α -> α
    - inf_le_left : forall a b : α, inf a b <= a
    - inf_le_right : forall a b : α, inf a b <= b
    - le_inf : forall a b c : α, a <= b -> a <= c -> a <= inf b c

中文:
类 SemilatticeInf
  参数: (α : 类型u)
  继承: 偏序 α
  公理与运算 (4 个):
    - inf : α -> α -> α
    - inf_le_left : 对任意 a b : α, 下确界 a b <= a
    - inf_le_right : 对任意 a b : α, 下确界 a b <= b
    - le_inf : 对任意 a b c : α, a <= b -> a <= c -> a <= 下确界 b c
-/
class SemilatticeInf (α : Type u) extends PartialOrder α where
  /-- The binary infimum, used to derive `Min α` -/
  inf : α -> α -> α
  /-- The infimum is a lower bound on the first argument -/
  protected inf_le_left : forall a b : α, inf a b <= a
  /-- The infimum is a lower bound on the second argument -/
  protected inf_le_right : forall a b : α, inf a b <= b
  /-- The infimum is the *greatest* lower bound -/
  protected le_inf : forall a b c : α, a <= b -> a <= c -> a <= inf b c

attribute [to_dual existing] SemilatticeSup.casesOn

@[to_dual]
/--
Instance `SemilatticeSup.toMax` / 实例 `SemilatticeSup.toMax`

English:
instance SemilatticeSup.toMax
  signature: [SemilatticeSup α]
  body: SemilatticeSup.sup a b

中文:
实例 SemilatticeSup.toMax
  签名: [SemilatticeSup α]
  定义体: SemilatticeSup.sup a b

Depends on / 依赖: SemilatticeSup, SemilatticeSup.sup
-/
instance SemilatticeSup.toMax [SemilatticeSup α] : Max α where max a b := SemilatticeSup.sup a b

-- Note: it is not possible for `to_dual` to translate `le a b := a ⊔ b = b` consistently.
/--
A type with a commutative, associative and idempotent binary `sup` operation has the structure of a
join-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
@[instance_reducible]
/--
Definition of `SemilatticeSup.mk'` / `SemilatticeSup.mk'` 的定义

English:
definition SemilatticeSup.mk'
  signature: {α : Type*} [Max α] (sup_comm : forall a b : α, a ⊔ b = b ⊔ a)
  body: (· ⊔ ·)
  le a b := a ⊔ b = b
  le_refl := sup_idem
  le_trans a b c hab hbc := by rw [← hbc, ← sup_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, sup_comm]
  le_sup_left a b := by rw [← sup_assoc, sup_idem]
  le_sup_right a b := by rw [sup_comm, sup_assoc, sup_idem]
  sup_le a b c hac hbc := by rwa [sup_assoc, hbc]

中文:
定义 SemilatticeSup.mk'
  签名: {α : 类型} [最大值 α] (sup_comm : 对任意 a b : α, a ⊔ b = b ⊔ a)
  定义体: (· ⊔ ·)
  le a b := a ⊔ b = b
  le_refl := sup_idem
  le_trans a b c hab hbc := by rw [← hbc, ← sup_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, sup_comm]
  le_sup_left a b := by rw [← sup_assoc, sup_idem]
  le_sup_right a b := by rw [sup_comm, sup_assoc, sup_idem]
  sup_le a b c hac hbc := by rwa [sup_assoc, hbc]
-/
def SemilatticeSup.mk' {α : Type*} [Max α] (sup_comm : forall a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : forall a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (sup_idem : forall a : α, a ⊔ a = a) :
    SemilatticeSup α where
  sup := (· ⊔ ·)
  le a b := a ⊔ b = b
  le_refl := sup_idem
  le_trans a b c hab hbc := by rw [← hbc, ← sup_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, sup_comm]
  le_sup_left a b := by rw [← sup_assoc, sup_idem]
  le_sup_right a b := by rw [sup_comm, sup_assoc, sup_idem]
  sup_le a b c hac hbc := by rwa [sup_assoc, hbc]

/--
A type with a commutative, associative and idempotent binary `inf` operation has the structure of a
meet-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `b ⊓ a = a`; cf. `inf_eq_right`.
-/
@[instance_reducible]
/--
Definition of `SemilatticeInf.mk'` / `SemilatticeInf.mk'` 的定义

English:
definition SemilatticeInf.mk'
  signature: {α : Type*} [Min α] (inf_comm : forall a b : α, a ⊓ b = b ⊓ a)
  body: (· ⊓ ·)
  le b a := a ⊓ b = b
  le_refl := inf_idem
  le_trans c b a hbc hab := by rw [← hbc, ← inf_assoc, hab]
  le_antisymm a b hba hab := by rwa [← hba, inf_comm]
  inf_le_left a b := by rw [← inf_assoc, inf_idem]
  inf_le_right a b := by rw [inf_comm, inf_assoc, inf_idem]
  le_inf a b c hac hbc := by rwa [inf_assoc, hbc]

中文:
定义 SemilatticeInf.mk'
  签名: {α : 类型} [最小值 α] (inf_comm : 对任意 a b : α, a ⊓ b = b ⊓ a)
  定义体: (· ⊓ ·)
  le b a := a ⊓ b = b
  le_refl := inf_idem
  le_trans c b a hbc hab := by rw [← hbc, ← inf_assoc, hab]
  le_antisymm a b hba hab := by rwa [← hba, inf_comm]
  inf_le_left a b := by rw [← inf_assoc, inf_idem]
  inf_le_right a b := by rw [inf_comm, inf_assoc, inf_idem]
  le_inf a b c hac hbc := by rwa [inf_assoc, hbc]
-/
def SemilatticeInf.mk' {α : Type*} [Min α] (inf_comm : forall a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : forall a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : forall a : α, a ⊓ a = a) :
    SemilatticeInf α where
  inf := (· ⊓ ·)
  le b a := a ⊓ b = b
  le_refl := inf_idem
  le_trans c b a hbc hab := by rw [← hbc, ← inf_assoc, hab]
  le_antisymm a b hba hab := by rwa [← hba, inf_comm]
  inf_le_left a b := by rw [← inf_assoc, inf_idem]
  inf_le_right a b := by rw [inf_comm, inf_assoc, inf_idem]
  le_inf a b c hac hbc := by rwa [inf_assoc, hbc]

section SemilatticeSup

variable [SemilatticeSup α] {a b c d : α}

@[to_dual (attr := simp) inf_le_left]
/--
theorem `le_sup_left` / 定理 `le_sup_left`

English:
theorem le_sup_left
  statement: a <= a ⊔ b
  proof: SemilatticeSup.le_sup_left a b

@[to_dual (attr := simp) inf_le_right]

中文:
定理 le_sup_left
  结论: a <= a ⊔ b
  证明: SemilatticeSup.le_sup_left a b

@[to_dual (attr := simp) inf_le_right]

Depends on / 依赖: SemilatticeSup, SemilatticeSup.le_sup_left, le_sup_left
-/
theorem le_sup_left : a <= a ⊔ b :=
  SemilatticeSup.le_sup_left a b

@[to_dual (attr := simp) inf_le_right]
/--
theorem `le_sup_right` / 定理 `le_sup_right`

English:
theorem le_sup_right
  statement: b <= a ⊔ b
  proof: SemilatticeSup.le_sup_right a b

@[to_dual (reorder := a b c) le_inf]

中文:
定理 le_sup_right
  结论: b <= a ⊔ b
  证明: SemilatticeSup.le_sup_right a b

@[to_dual (reorder := a b c) le_inf]

Depends on / 依赖: SemilatticeSup, SemilatticeSup.le_sup_right, le_sup_right
-/
theorem le_sup_right : b <= a ⊔ b :=
  SemilatticeSup.le_sup_right a b

@[to_dual (reorder := a b c) le_inf]
/--
theorem `sup_le` / 定理 `sup_le`

English:
theorem sup_le
  statement: a <= c -> b <= c -> a ⊔ b <= c
  proof: SemilatticeSup.sup_le a b c

@[to_dual inf_le_of_left_le]

中文:
定理 sup_le
  结论: a <= c -> b <= c -> a ⊔ b <= c
  证明: SemilatticeSup.sup_le a b c

@[to_dual inf_le_of_left_le]

Depends on / 依赖: SemilatticeSup, SemilatticeSup.sup_le, sup_le
-/
theorem sup_le : a <= c -> b <= c -> a ⊔ b <= c :=
  SemilatticeSup.sup_le a b c

@[to_dual inf_le_of_left_le]
/--
theorem `le_sup_of_le_left` / 定理 `le_sup_of_le_left`

English:
theorem le_sup_of_le_left
  given: (h : c <= a)
  statement: c <= a ⊔ b
  proof: le_trans h le_sup_left

@[to_dual inf_le_of_right_le]

中文:
定理 le_sup_of_le_left
  条件: (h : c <= a)
  结论: c <= a ⊔ b
  证明: le_trans h le_sup_left

@[to_dual inf_le_of_right_le]

Depends on / 依赖: le_sup_left, le_trans
-/
theorem le_sup_of_le_left (h : c <= a) : c <= a ⊔ b :=
  le_trans h le_sup_left

@[to_dual inf_le_of_right_le]
/--
theorem `le_sup_of_le_right` / 定理 `le_sup_of_le_right`

English:
theorem le_sup_of_le_right
  given: (h : c <= b)
  statement: c <= a ⊔ b
  proof: le_trans h le_sup_right

@[to_dual inf_lt_of_left_lt]

中文:
定理 le_sup_of_le_right
  条件: (h : c <= b)
  结论: c <= a ⊔ b
  证明: le_trans h le_sup_right

@[to_dual inf_lt_of_left_lt]

Depends on / 依赖: le_sup_right, le_trans
-/
theorem le_sup_of_le_right (h : c <= b) : c <= a ⊔ b :=
  le_trans h le_sup_right

@[to_dual inf_lt_of_left_lt]
/--
theorem `lt_sup_of_lt_left` / 定理 `lt_sup_of_lt_left`

English:
theorem lt_sup_of_lt_left
  given: (h : c < a)
  statement: c < a ⊔ b
  proof: h.trans_le le_sup_left

@[to_dual inf_lt_of_right_lt]

中文:
定理 lt_sup_of_lt_left
  条件: (h : c < a)
  结论: c < a ⊔ b
  证明: h.trans_le le_sup_left

@[to_dual inf_lt_of_right_lt]

Depends on / 依赖: h.trans_le, le_sup_left, trans_le
-/
theorem lt_sup_of_lt_left (h : c < a) : c < a ⊔ b :=
  h.trans_le le_sup_left

@[to_dual inf_lt_of_right_lt]
/--
theorem `lt_sup_of_lt_right` / 定理 `lt_sup_of_lt_right`

English:
theorem lt_sup_of_lt_right
  given: (h : c < b)
  statement: c < a ⊔ b
  proof: h.trans_le le_sup_right

@[to_dual (attr := simp) (reorder := a b c) le_inf_iff]

中文:
定理 lt_sup_of_lt_right
  条件: (h : c < b)
  结论: c < a ⊔ b
  证明: h.trans_le le_sup_right

@[to_dual (attr := simp) (reorder := a b c) le_inf_iff]

Depends on / 依赖: h.trans_le, le_sup_right, trans_le
-/
theorem lt_sup_of_lt_right (h : c < b) : c < a ⊔ b :=
  h.trans_le le_sup_right

@[to_dual (attr := simp) (reorder := a b c) le_inf_iff]
/--
theorem `sup_le_iff` / 定理 `sup_le_iff`

English:
theorem sup_le_iff
  statement: a ⊔ b <= c ↔ a <= c ∧ b <= c
  proof: ⟨fun h : a ⊔ b <= c => ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩,
   fun ⟨h₁, h₂⟩ => sup_le h₁ h₂⟩

@[to_dual (attr := simp)]

中文:
定理 sup_le_iff
  结论: a ⊔ b <= c ↔ a <= c ∧ b <= c
  证明: ⟨fun h : a ⊔ b <= c => ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩,
   fun ⟨h₁, h₂⟩ => sup_le h₁ h₂⟩

@[to_dual (attr := simp)]

Depends on / 依赖: le_sup_left, le_sup_right, le_trans, sup_le
-/
theorem sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c :=
  ⟨fun h : a ⊔ b <= c => ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩,
   fun ⟨h₁, h₂⟩ => sup_le h₁ h₂⟩

@[to_dual (attr := simp)]
/--
theorem `sup_eq_left` / 定理 `sup_eq_left`

English:
theorem sup_eq_left
  statement: a ⊔ b = a ↔ b <= a
  proof: le_antisymm_iff.trans by simp

@[to_dual (attr := simp)]

中文:
定理 sup_eq_left
  结论: a ⊔ b = a ↔ b <= a
  证明: le_antisymm_iff.trans by simp

@[to_dual (attr := simp)]

Depends on / 依赖: le_antisymm_iff, le_antisymm_iff.trans
-/
theorem sup_eq_left : a ⊔ b = a ↔ b <= a :=
le_antisymm_iff.trans by simp

@[to_dual (attr := simp)]
/--
theorem `sup_eq_right` / 定理 `sup_eq_right`

English:
theorem sup_eq_right
  statement: a ⊔ b = b ↔ a <= b
  proof: le_antisymm_iff.trans by simp

@[to_dual (attr := simp)]

中文:
定理 sup_eq_right
  结论: a ⊔ b = b ↔ a <= b
  证明: le_antisymm_iff.trans by simp

@[to_dual (attr := simp)]

Depends on / 依赖: le_antisymm_iff, le_antisymm_iff.trans
-/
theorem sup_eq_right : a ⊔ b = b ↔ a <= b :=
le_antisymm_iff.trans by simp

@[to_dual (attr := simp)]
/--
theorem `left_eq_sup` / 定理 `left_eq_sup`

English:
theorem left_eq_sup
  statement: a = a ⊔ b ↔ b <= a
  proof: eq_comm.trans sup_eq_left

@[to_dual (attr := simp)]

中文:
定理 left_eq_sup
  结论: a = a ⊔ b ↔ b <= a
  证明: eq_comm.trans sup_eq_left

@[to_dual (attr := simp)]

Depends on / 依赖: eq_comm, eq_comm.trans, sup_eq_left
-/
theorem left_eq_sup : a = a ⊔ b ↔ b <= a :=
  eq_comm.trans sup_eq_left

@[to_dual (attr := simp)]
/--
theorem `right_eq_sup` / 定理 `right_eq_sup`

English:
theorem right_eq_sup
  statement: b = a ⊔ b ↔ a <= b
  proof: eq_comm.trans sup_eq_right

alias ⟨le_of_sup_eq', sup_of_le_left⟩ := sup_eq_left

alias ⟨le_of_sup_eq, sup_of_le_right⟩ := sup_eq_right

中文:
定理 right_eq_sup
  结论: b = a ⊔ b ↔ a <= b
  证明: eq_comm.trans sup_eq_right

alias ⟨le_of_sup_eq', sup_of_le_left⟩ := sup_eq_left

alias ⟨le_of_sup_eq, sup_of_le_right⟩ := sup_eq_right

Depends on / 依赖: eq_comm, eq_comm.trans, sup_eq_right
-/
theorem right_eq_sup : b = a ⊔ b ↔ a <= b :=
  eq_comm.trans sup_eq_right

alias ⟨le_of_sup_eq', sup_of_le_left⟩ := sup_eq_left

alias ⟨le_of_sup_eq, sup_of_le_right⟩ := sup_eq_right

attribute [to_dual (attr := simp)] sup_of_le_left sup_of_le_right
attribute [to_dual le_of_inf_eq'] le_of_sup_eq
attribute [to_dual le_of_inf_eq] le_of_sup_eq'

@[to_dual (attr := simp) inf_lt_left]
/--
theorem `left_lt_sup` / 定理 `left_lt_sup`

English:
theorem left_lt_sup
  statement: a < a ⊔ b ↔ ¬b <= a
  proof: le_sup_left.lt_iff_ne.trans not_congr left_eq_sup

@[to_dual (attr := simp) inf_lt_right]

中文:
定理 left_lt_sup
  结论: a < a ⊔ b ↔ ¬b <= a
  证明: le_sup_left.lt_iff_ne.trans not_congr left_eq_sup

@[to_dual (attr := simp) inf_lt_right]

Depends on / 依赖: le_sup_left, le_sup_left.lt_iff_ne.trans, left_eq_sup, lt_iff_ne, not_congr
-/
theorem left_lt_sup : a < a ⊔ b ↔ ¬b <= a :=
le_sup_left.lt_iff_ne.trans not_congr left_eq_sup

@[to_dual (attr := simp) inf_lt_right]
/--
theorem `right_lt_sup` / 定理 `right_lt_sup`

English:
theorem right_lt_sup
  statement: b < a ⊔ b ↔ ¬a <= b
  proof: le_sup_right.lt_iff_ne.trans not_congr right_eq_sup

@[to_dual inf_lt_left_or_right]

中文:
定理 right_lt_sup
  结论: b < a ⊔ b ↔ ¬a <= b
  证明: le_sup_right.lt_iff_ne.trans not_congr right_eq_sup

@[to_dual inf_lt_left_or_right]

Depends on / 依赖: le_sup_right, le_sup_right.lt_iff_ne.trans, lt_iff_ne, not_congr, right_eq_sup
-/
theorem right_lt_sup : b < a ⊔ b ↔ ¬a <= b :=
le_sup_right.lt_iff_ne.trans not_congr right_eq_sup

@[to_dual inf_lt_left_or_right]
/--
theorem `left_or_right_lt_sup` / 定理 `left_or_right_lt_sup`

English:
theorem left_or_right_lt_sup
  given: (h : a != b)
  statement: a < a ⊔ b ∨ b < a ⊔ b
  proof: h.not_le_or_not_ge.symm.imp left_lt_sup.2 right_lt_sup.2

@[to_dual]

中文:
定理 left_or_right_lt_sup
  条件: (h : a != b)
  结论: a < a ⊔ b ∨ b < a ⊔ b
  证明: h.not_le_or_not_ge.symm.imp left_lt_sup.2 right_lt_sup.2

@[to_dual]

Depends on / 依赖: h.not_le_or_not_ge.symm.imp, left_lt_sup, not_le_or_not_ge, right_lt_sup
-/
theorem left_or_right_lt_sup (h : a != b) : a < a ⊔ b ∨ b < a ⊔ b :=
  h.not_le_or_not_ge.symm.imp left_lt_sup.2 right_lt_sup.2

@[to_dual]
/--
theorem `le_iff_exists_sup` / 定理 `le_iff_exists_sup`

English:
theorem le_iff_exists_sup
  statement: a <= b ↔ exists c, b = a ⊔ c
  proof: by
  constructor
  · intro h
    exact ⟨b, (sup_eq_right.mpr h).symm⟩
  · rintro ⟨c, rfl : _ = _ ⊔ _⟩
    exact le_sup_left

@[to_dual (attr := gcongr)]

中文:
定理 le_iff_存在_sup
  结论: a <= b ↔ 存在 c, b = a ⊔ c
  证明: by
  constructor
  · intro h
    exact ⟨b, (sup_eq_right.mpr h).symm⟩
  · rintro ⟨c, rfl : _ = _ ⊔ _⟩
    exact le_sup_left

@[to_dual (attr := gcongr)]

Depends on / 依赖: le_sup_left, sup_eq_right, sup_eq_right.mpr
-/
theorem le_iff_exists_sup : a <= b ↔ exists c, b = a ⊔ c := by
  constructor
  · intro h
    exact ⟨b, (sup_eq_right.mpr h).symm⟩
  · rintro ⟨c, rfl : _ = _ ⊔ _⟩
    exact le_sup_left

@[to_dual (attr := gcongr)]
/--
theorem `sup_le_sup` / 定理 `sup_le_sup`

English:
theorem sup_le_sup
  given: (h₁ : a <= b) (h₂ : c <= d)
  statement: a ⊔ c <= b ⊔ d
  proof: sup_le (le_sup_of_le_left h₁) (le_sup_of_le_right h₂)

中文:
定理 sup_le_sup
  条件: (h₁ : a <= b) (h₂ : c <= d)
  结论: a ⊔ c <= b ⊔ d
  证明: sup_le (le_sup_of_le_left h₁) (le_sup_of_le_right h₂)

Depends on / 依赖: le_sup_of_le_left, le_sup_of_le_right, sup_le
-/
theorem sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d :=
  sup_le (le_sup_of_le_left h₁) (le_sup_of_le_right h₂)

-- FIXME: these theorems use the wrong `left`/`right` naming convention.
-- FIXME: the fact that the following theorems use `(reorder := h₁ c)` is not good.
-- Instead, we should use a consistent argument ordering.
@[to_dual (reorder := h₁ c)]
/--
theorem `sup_le_sup_left` / 定理 `sup_le_sup_left`

English:
theorem sup_le_sup_left
  given: (h₁ : a <= b) (c)
  statement: c ⊔ a <= c ⊔ b
  proof: sup_le_sup le_rfl h₁

@[to_dual (reorder := h₁ c)]

中文:
定理 sup_le_sup_left
  条件: (h₁ : a <= b) (c)
  结论: c ⊔ a <= c ⊔ b
  证明: sup_le_sup le_rfl h₁

@[to_dual (reorder := h₁ c)]

Depends on / 依赖: le_rfl, sup_le_sup
-/
theorem sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b :=
  sup_le_sup le_rfl h₁

@[to_dual (reorder := h₁ c)]
/--
theorem `sup_le_sup_right` / 定理 `sup_le_sup_right`

English:
theorem sup_le_sup_right
  given: (h₁ : a <= b) (c)
  statement: a ⊔ c <= b ⊔ c
  proof: sup_le_sup h₁ le_rfl

@[to_dual]

中文:
定理 sup_le_sup_right
  条件: (h₁ : a <= b) (c)
  结论: a ⊔ c <= b ⊔ c
  证明: sup_le_sup h₁ le_rfl

@[to_dual]

Depends on / 依赖: le_rfl, sup_le_sup
-/
theorem sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c :=
  sup_le_sup h₁ le_rfl

@[to_dual]
/--
theorem `sup_idem` / 定理 `sup_idem`

English:
theorem sup_idem
  given: (a : α)
  statement: a ⊔ a = a
  proof: by simp

@[to_dual]

中文:
定理 sup_idem
  条件: (a : α)
  结论: a ⊔ a = a
  证明: by simp

@[to_dual]
-/
theorem sup_idem (a : α) : a ⊔ a = a := by simp

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.IdempotentOp (α := α) (· ⊔ ·)
  body: ⟨sup_idem⟩

@[to_dual]

中文:
实例 :
  签名: Std.IdempotentOp (α := α) (· ⊔ ·)
  定义体: ⟨sup_idem⟩

@[to_dual]

Depends on / 依赖: sup_idem
-/
instance : Std.IdempotentOp (α := α) (· ⊔ ·) := ⟨sup_idem⟩

@[to_dual]
/--
theorem `sup_comm` / 定理 `sup_comm`

English:
theorem sup_comm
  given: (a b : α)
  statement: a ⊔ b = b ⊔ a
  proof: by apply le_antisymm <;> simp

@[to_dual]

中文:
定理 sup_comm
  条件: (a b : α)
  结论: a ⊔ b = b ⊔ a
  证明: by apply le_antisymm <;> simp

@[to_dual]

Depends on / 依赖: le_antisymm
-/
theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by apply le_antisymm <;> simp

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Commutative (α := α) (· ⊔ ·)
  body: ⟨sup_comm⟩

@[to_dual]

中文:
实例 :
  签名: Std.交换 (α := α) (· ⊔ ·)
  定义体: ⟨sup_comm⟩

@[to_dual]

Depends on / 依赖: sup_comm
-/
instance : Std.Commutative (α := α) (· ⊔ ·) := ⟨sup_comm⟩

@[to_dual]
/--
theorem `sup_assoc` / 定理 `sup_assoc`

English:
theorem sup_assoc
  given: (a b c : α)
  statement: a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
  proof: eq_of_forall_ge_iff fun x => by simp only [sup_le_iff]; rw [and_assoc]

@[to_dual]

中文:
定理 sup_assoc
  条件: (a b c : α)
  结论: a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
  证明: eq_of_forall_ge_iff fun x => by simp only [sup_le_iff]; rw [and_assoc]

@[to_dual]

Depends on / 依赖: and_assoc, eq_of_forall_ge_iff, sup_le_iff
-/
theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
  eq_of_forall_ge_iff fun x => by simp only [sup_le_iff]; rw [and_assoc]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Associative (α := α) (· ⊔ ·)
  body: ⟨sup_assoc⟩

@[to_dual]

中文:
实例 :
  签名: Std.结合 (α := α) (· ⊔ ·)
  定义体: ⟨sup_assoc⟩

@[to_dual]

Depends on / 依赖: sup_assoc
-/
instance : Std.Associative (α := α) (· ⊔ ·) := ⟨sup_assoc⟩

@[to_dual]
/--
theorem `sup_left_right_swap` / 定理 `sup_left_right_swap`

English:
theorem sup_left_right_swap
  given: (a b c : α)
  statement: a ⊔ b ⊔ c = c ⊔ b ⊔ a
  proof: by
  rw [sup_comm]; rw [sup_comm a]; rw [sup_assoc]

@[to_dual]

中文:
定理 sup_left_right_swap
  条件: (a b c : α)
  结论: a ⊔ b ⊔ c = c ⊔ b ⊔ a
  证明: by
  rw [sup_comm]; rw [sup_comm a]; rw [sup_assoc]

@[to_dual]

Depends on / 依赖: sup_assoc, sup_comm
-/
theorem sup_left_right_swap (a b c : α) : a ⊔ b ⊔ c = c ⊔ b ⊔ a := by
  rw [sup_comm]; rw [sup_comm a]; rw [sup_assoc]

@[to_dual]
/--
theorem `sup_left_idem` / 定理 `sup_left_idem`

English:
theorem sup_left_idem
  given: (a b : α)
  statement: a ⊔ (a ⊔ b) = a ⊔ b
  proof: by simp

@[to_dual]

中文:
定理 sup_left_idem
  条件: (a b : α)
  结论: a ⊔ (a ⊔ b) = a ⊔ b
  证明: by simp

@[to_dual]
-/
theorem sup_left_idem (a b : α) : a ⊔ (a ⊔ b) = a ⊔ b := by simp

@[to_dual]
/--
theorem `sup_right_idem` / 定理 `sup_right_idem`

English:
theorem sup_right_idem
  given: (a b : α)
  statement: a ⊔ b ⊔ b = a ⊔ b
  proof: by simp

@[to_dual]

中文:
定理 sup_right_idem
  条件: (a b : α)
  结论: a ⊔ b ⊔ b = a ⊔ b
  证明: by simp

@[to_dual]
-/
theorem sup_right_idem (a b : α) : a ⊔ b ⊔ b = a ⊔ b := by simp

@[to_dual]
/--
theorem `sup_left_comm` / 定理 `sup_left_comm`

English:
theorem sup_left_comm
  given: (a b c : α)
  statement: a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
  proof: by
  rw [← sup_assoc]; rw [← sup_assoc]; rw [@sup_comm α _ a]

@[to_dual]

中文:
定理 sup_left_comm
  条件: (a b c : α)
  结论: a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
  证明: by
  rw [← sup_assoc]; rw [← sup_assoc]; rw [@sup_comm α _ a]

@[to_dual]

Depends on / 依赖: sup_assoc, sup_comm
-/
theorem sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) := by
  rw [← sup_assoc]; rw [← sup_assoc]; rw [@sup_comm α _ a]

@[to_dual]
/--
theorem `sup_right_comm` / 定理 `sup_right_comm`

English:
theorem sup_right_comm
  given: (a b c : α)
  statement: a ⊔ b ⊔ c = a ⊔ c ⊔ b
  proof: by
  rw [sup_assoc]; rw [sup_assoc]; rw [sup_comm b]

@[to_dual]

中文:
定理 sup_right_comm
  条件: (a b c : α)
  结论: a ⊔ b ⊔ c = a ⊔ c ⊔ b
  证明: by
  rw [sup_assoc]; rw [sup_assoc]; rw [sup_comm b]

@[to_dual]

Depends on / 依赖: sup_assoc, sup_comm
-/
theorem sup_right_comm (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ b := by
  rw [sup_assoc]; rw [sup_assoc]; rw [sup_comm b]

@[to_dual]
/--
theorem `sup_sup_sup_comm` / 定理 `sup_sup_sup_comm`

English:
theorem sup_sup_sup_comm
  given: (a b c d : α)
  statement: a ⊔ b ⊔ (c ⊔ d) = a ⊔ c ⊔ (b ⊔ d)
  proof: by
  rw [sup_assoc]; rw [sup_left_comm b]; rw [← sup_assoc]

@[to_dual]

中文:
定理 sup_sup_sup_comm
  条件: (a b c d : α)
  结论: a ⊔ b ⊔ (c ⊔ d) = a ⊔ c ⊔ (b ⊔ d)
  证明: by
  rw [sup_assoc]; rw [sup_left_comm b]; rw [← sup_assoc]

@[to_dual]

Depends on / 依赖: sup_assoc, sup_left_comm
-/
theorem sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔ c ⊔ (b ⊔ d) := by
  rw [sup_assoc]; rw [sup_left_comm b]; rw [← sup_assoc]

@[to_dual]
/--
theorem `sup_rotate` / 定理 `sup_rotate`

English:
theorem sup_rotate
  given: (a b c : α)
  statement: a ⊔ b ⊔ c = b ⊔ c ⊔ a
  proof: by
  rw [sup_assoc]; rw [sup_comm]

@[to_dual]

中文:
定理 sup_rotate
  条件: (a b c : α)
  结论: a ⊔ b ⊔ c = b ⊔ c ⊔ a
  证明: by
  rw [sup_assoc]; rw [sup_comm]

@[to_dual]

Depends on / 依赖: sup_assoc, sup_comm
-/
theorem sup_rotate (a b c : α) : a ⊔ b ⊔ c = b ⊔ c ⊔ a := by
  rw [sup_assoc]; rw [sup_comm]

@[to_dual]
/--
theorem `sup_rotate'` / 定理 `sup_rotate'`

English:
theorem sup_rotate'
  given: (a b c : α)
  statement: a ⊔ (b ⊔ c) = b ⊔ (c ⊔ a)
  proof: by
  rw [sup_comm]; rw [sup_assoc]

@[to_dual]

中文:
定理 sup_rotate'
  条件: (a b c : α)
  结论: a ⊔ (b ⊔ c) = b ⊔ (c ⊔ a)
  证明: by
  rw [sup_comm]; rw [sup_assoc]

@[to_dual]

Depends on / 依赖: sup_assoc, sup_comm
-/
theorem sup_rotate' (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (c ⊔ a) := by
  rw [sup_comm]; rw [sup_assoc]

@[to_dual]
/--
theorem `sup_sup_distrib_left` / 定理 `sup_sup_distrib_left`

English:
theorem sup_sup_distrib_left
  given: (a b c : α)
  statement: a ⊔ (b ⊔ c) = a ⊔ b ⊔ (a ⊔ c)
  proof: by
  rw [sup_sup_sup_comm]; rw [sup_idem]

@[to_dual]

中文:
定理 sup_sup_distrib_left
  条件: (a b c : α)
  结论: a ⊔ (b ⊔ c) = a ⊔ b ⊔ (a ⊔ c)
  证明: by
  rw [sup_sup_sup_comm]; rw [sup_idem]

@[to_dual]

Depends on / 依赖: sup_idem, sup_sup_sup_comm
-/
theorem sup_sup_distrib_left (a b c : α) : a ⊔ (b ⊔ c) = a ⊔ b ⊔ (a ⊔ c) := by
  rw [sup_sup_sup_comm]; rw [sup_idem]

@[to_dual]
/--
theorem `sup_sup_distrib_right` / 定理 `sup_sup_distrib_right`

English:
theorem sup_sup_distrib_right
  given: (a b c : α)
  statement: a ⊔ b ⊔ c = a ⊔ c ⊔ (b ⊔ c)
  proof: by
  rw [sup_sup_sup_comm]; rw [sup_idem]

中文:
定理 sup_sup_distrib_right
  条件: (a b c : α)
  结论: a ⊔ b ⊔ c = a ⊔ c ⊔ (b ⊔ c)
  证明: by
  rw [sup_sup_sup_comm]; rw [sup_idem]

Depends on / 依赖: sup_idem, sup_sup_sup_comm
-/
theorem sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ (b ⊔ c) := by
  rw [sup_sup_sup_comm]; rw [sup_idem]

-- FIXME: These theorems use the wrong `left`/`right` naming convention.
@[to_dual]
/--
theorem `sup_congr_left` / 定理 `sup_congr_left`

English:
theorem sup_congr_left
  given: (hb : b <= a ⊔ c) (hc : c <= a ⊔ b)
  statement: a ⊔ b = a ⊔ c
  proof: (sup_le le_sup_left hb).antisymm sup_le le_sup_left hc

@[to_dual]

中文:
定理 sup_congr_left
  条件: (hb : b <= a ⊔ c) (hc : c <= a ⊔ b)
  结论: a ⊔ b = a ⊔ c
  证明: (sup_le le_sup_left hb).antisymm sup_le le_sup_left hc

@[to_dual]

Depends on / 依赖: antisymm, le_sup_left, sup_le
-/
theorem sup_congr_left (hb : b <= a ⊔ c) (hc : c <= a ⊔ b) : a ⊔ b = a ⊔ c :=
(sup_le le_sup_left hb).antisymm sup_le le_sup_left hc

@[to_dual]
/--
theorem `sup_congr_right` / 定理 `sup_congr_right`

English:
theorem sup_congr_right
  given: (ha : a <= b ⊔ c) (hb : b <= a ⊔ c)
  statement: a ⊔ c = b ⊔ c
  proof: (sup_le ha le_sup_right).antisymm sup_le hb le_sup_right

@[to_dual]

中文:
定理 sup_congr_right
  条件: (ha : a <= b ⊔ c) (hb : b <= a ⊔ c)
  结论: a ⊔ c = b ⊔ c
  证明: (sup_le ha le_sup_right).antisymm sup_le hb le_sup_right

@[to_dual]

Depends on / 依赖: antisymm, le_sup_right, sup_le
-/
theorem sup_congr_right (ha : a <= b ⊔ c) (hb : b <= a ⊔ c) : a ⊔ c = b ⊔ c :=
(sup_le ha le_sup_right).antisymm sup_le hb le_sup_right

@[to_dual]
/--
theorem `sup_eq_sup_iff_left` / 定理 `sup_eq_sup_iff_left`

English:
theorem sup_eq_sup_iff_left
  statement: a ⊔ b = a ⊔ c ↔ b <= a ⊔ c ∧ c <= a ⊔ b
  proof: ⟨fun h => ⟨h ▸ le_sup_right, h.symm ▸ le_sup_right⟩, fun h => sup_congr_left h.1 h.2⟩

@[to_dual]

中文:
定理 sup_eq_sup_iff_left
  结论: a ⊔ b = a ⊔ c ↔ b <= a ⊔ c ∧ c <= a ⊔ b
  证明: ⟨fun h => ⟨h ▸ le_sup_right, h.symm ▸ le_sup_right⟩, fun h => sup_congr_left h.1 h.2⟩

@[to_dual]

Depends on / 依赖: h.symm, le_sup_right, sup_congr_left
-/
theorem sup_eq_sup_iff_left : a ⊔ b = a ⊔ c ↔ b <= a ⊔ c ∧ c <= a ⊔ b :=
  ⟨fun h => ⟨h ▸ le_sup_right, h.symm ▸ le_sup_right⟩, fun h => sup_congr_left h.1 h.2⟩

@[to_dual]
/--
theorem `sup_eq_sup_iff_right` / 定理 `sup_eq_sup_iff_right`

English:
theorem sup_eq_sup_iff_right
  statement: a ⊔ c = b ⊔ c ↔ a <= b ⊔ c ∧ b <= a ⊔ c
  proof: ⟨fun h => ⟨h ▸ le_sup_left, h.symm ▸ le_sup_left⟩, fun h => sup_congr_right h.1 h.2⟩

@[to_dual inf_lt_or_inf_lt]

中文:
定理 sup_eq_sup_iff_right
  结论: a ⊔ c = b ⊔ c ↔ a <= b ⊔ c ∧ b <= a ⊔ c
  证明: ⟨fun h => ⟨h ▸ le_sup_left, h.symm ▸ le_sup_left⟩, fun h => sup_congr_right h.1 h.2⟩

@[to_dual inf_lt_or_inf_lt]

Depends on / 依赖: h.symm, le_sup_left, sup_congr_right
-/
theorem sup_eq_sup_iff_right : a ⊔ c = b ⊔ c ↔ a <= b ⊔ c ∧ b <= a ⊔ c :=
  ⟨fun h => ⟨h ▸ le_sup_left, h.symm ▸ le_sup_left⟩, fun h => sup_congr_right h.1 h.2⟩

@[to_dual inf_lt_or_inf_lt]
/--
theorem `Ne.lt_sup_or_lt_sup` / 定理 `Ne.lt_sup_or_lt_sup`

English:
theorem Ne.lt_sup_or_lt_sup
  given: (hab : a != b)
  statement: a < a ⊔ b ∨ b < a ⊔ b
  proof: hab.symm.not_le_or_not_ge.imp left_lt_sup.2 right_lt_sup.2

@[to_dual inf_le_ite]

中文:
定理 不等.lt_sup_or_lt_sup
  条件: (hab : a != b)
  结论: a < a ⊔ b ∨ b < a ⊔ b
  证明: hab.symm.not_le_or_not_ge.imp left_lt_sup.2 right_lt_sup.2

@[to_dual inf_le_ite]

Depends on / 依赖: hab.symm.not_le_or_not_ge.imp, left_lt_sup, not_le_or_not_ge, right_lt_sup
-/
theorem Ne.lt_sup_or_lt_sup (hab : a != b) : a < a ⊔ b ∨ b < a ⊔ b :=
  hab.symm.not_le_or_not_ge.imp left_lt_sup.2 right_lt_sup.2

@[to_dual inf_le_ite]
/--
theorem `ite_le_sup` / 定理 `ite_le_sup`

English:
theorem ite_le_sup
  given: (a b : α) (P : Prop) [Decidable P]
  statement: ite P a b <= a ⊔ b
  proof: if h : P then (if_pos h).trans_le le_sup_left else (if_neg h).trans_le le_sup_right

@[to_dual (reorder := H (x y))]

中文:
定理 ite_le_sup
  条件: (a b : α) (P : 命题) [可判定 P]
  结论: ite P a b <= a ⊔ b
  证明: if h : P then (if_pos h).trans_le le_sup_left else (if_neg h).trans_le le_sup_right

@[to_dual (reorder := H (x y))]

Depends on / 依赖: if_neg, if_pos, le_sup_left, le_sup_right, trans_le
-/
theorem ite_le_sup (a b : α) (P : Prop) [Decidable P] : ite P a b <= a ⊔ b :=
  if h : P then (if_pos h).trans_le le_sup_left else (if_neg h).trans_le le_sup_right

@[to_dual (reorder := H (x y))]
/--
theorem `SemilatticeSup.ext_sup` / 定理 `SemilatticeSup.ext_sup`

English:
theorem SemilatticeSup.ext_sup
  statement: {α} {A B : SemilatticeSup α}
  proof: eq_of_forall_ge_iff fun c => by simp only [sup_le_iff]; rw [← H, @sup_le_iff α A, H, H]

@[to_dual (reorder := H (x y))]

中文:
定理 SemilatticeSup.ext_sup
  结论: {α} {A B : SemilatticeSup α}
  证明: eq_of_forall_ge_iff fun c => by simp only [sup_le_iff]; rw [← H, @sup_le_iff α A, H, H]

@[to_dual (reorder := H (x y))]
-/
theorem SemilatticeSup.ext_sup {α} {A B : SemilatticeSup α}
    (H : forall x y : α, (haveI := A; x <= y) ↔ x <= y)
    (x y : α) :
    (haveI := A; x ⊔ y) = x ⊔ y :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff]; rw [← H, @sup_le_iff α A, H, H]

@[to_dual (reorder := H (x y))]
/--
theorem `SemilatticeSup.ext` / 定理 `SemilatticeSup.ext`

English:
theorem SemilatticeSup.ext
  statement: {α} {A B : SemilatticeSup α}
  proof: by
  cases A
  cases B
  cases PartialOrder.ext H
  congr
  ext; apply SemilatticeSup.ext_sup H

@[to_dual]

中文:
定理 SemilatticeSup.ext
  结论: {α} {A B : SemilatticeSup α}
  证明: by
  cases A
  cases B
  cases PartialOrder.ext H
  congr
  ext; apply SemilatticeSup.ext_sup H

@[to_dual]
-/
theorem SemilatticeSup.ext {α} {A B : SemilatticeSup α}
    (H : forall x y : α, (haveI := A; x <= y) ↔ x <= y) :
    A = B := by
  cases A
  cases B
  cases PartialOrder.ext H
  congr
  ext; apply SemilatticeSup.ext_sup H

@[to_dual]
/--
Instance `OrderDual.instSemilatticeSup` / 实例 `OrderDual.instSemilatticeSup`

English:
instance OrderDual.instSemilatticeSup
  signature: (α) [h : SemilatticeInf α]
  body: h.inf a b
  le_sup_left := h.inf_le_left
  le_sup_right := h.inf_le_right
  sup_le _ _ _ := h.le_inf _ _ _

@[to_dual]

中文:
实例 OrderDual.instSemilatticeSup
  签名: (α) [h : SemilatticeInf α]
  定义体: h.inf a b
  le_sup_left := h.inf_le_left
  le_sup_right := h.inf_le_right
  sup_le _ _ _ := h.le_inf _ _ _

@[to_dual]

Depends on / 依赖: h.inf
-/
instance OrderDual.instSemilatticeSup (α) [h : SemilatticeInf α] : SemilatticeSup αᵒᵈ where
  sup a b := h.inf a b
  le_sup_left := h.inf_le_left
  le_sup_right := h.inf_le_right
  sup_le _ _ _ := h.le_inf _ _ _

@[to_dual]
/--
theorem `SemilatticeSup.dual_dual` / 定理 `SemilatticeSup.dual_dual`

English:
theorem SemilatticeSup.dual_dual
  given: (α : Type*) [H : SemilatticeSup α]
  proof: SemilatticeSup.ext fun _ _ => Iff.rfl

中文:
定理 SemilatticeSup.dual_dual
  条件: (α : 类型) [H : SemilatticeSup α]
  证明: SemilatticeSup.ext fun _ _ => Iff.rfl

Depends on / 依赖: Iff.rfl, SemilatticeSup, SemilatticeSup.ext
-/
theorem SemilatticeSup.dual_dual (α : Type*) [H : SemilatticeSup α] :
    OrderDual.instSemilatticeSup αᵒᵈ = H :=
  SemilatticeSup.ext fun _ _ => Iff.rfl

end SemilatticeSup

/-!
### Lattices
-/


/--
Definition of `Lattice` / `Lattice` 的定义

English:
class Lattice
  parameters: (α : Type u)
  extends: SemilatticeSup α, SemilatticeInf α
  (no additional axioms)

中文:
类 格
  参数: (α : 类型u)
  继承: SemilatticeSup α, SemilatticeInf α
  (无附加公理)
-/
class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α

attribute [to_dual existing] Lattice.toSemilatticeInf

/--
Instance `OrderDual.instLattice` / 实例 `OrderDual.instLattice`

English:
instance OrderDual.instLattice
  signature: (α) [Lattice α]

中文:
实例 OrderDual.instLattice
  签名: (α) [格 α]
-/
instance OrderDual.instLattice (α) [Lattice α] : Lattice αᵒᵈ where

/--
theorem `semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder` / 定理 `semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder`

English:
theorem semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder
  proof: PartialOrder.ext fun a b =>
    show a ⊔ b = b ↔ b ⊓ a = a from
      ⟨fun h => by rw [← h, inf_comm, inf_sup_self], fun h => by rw [← h, sup_comm, sup_inf_self]⟩

中文:
定理 semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder
  证明: PartialOrder.ext fun a b =>
    show a ⊔ b = b ↔ b ⊓ a = a from
      ⟨fun h => by rw [← h, inf_comm, inf_sup_self], fun h => by rw [← h, sup_comm, sup_inf_self]⟩

Depends on / 依赖: PartialOrder, PartialOrder.ext, inf_comm, inf_sup_self, sup_comm, sup_inf_self
-/
theorem semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder
    {α : Type*} [Max α] [Min α]
    (sup_comm : forall a b : α, a ⊔ b = b ⊔ a) (sup_assoc : forall a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c))
    (sup_idem : forall a : α, a ⊔ a = a) (inf_comm : forall a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : forall a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : forall a : α, a ⊓ a = a)
    (sup_inf_self : forall a b : α, a ⊔ a ⊓ b = a) (inf_sup_self : forall a b : α, a ⊓ (a ⊔ b) = a) :
    @SemilatticeSup.toPartialOrder _ (SemilatticeSup.mk' sup_comm sup_assoc sup_idem) =
      @SemilatticeInf.toPartialOrder _ (SemilatticeInf.mk' inf_comm inf_assoc inf_idem) :=
  PartialOrder.ext fun a b =>
    show a ⊔ b = b ↔ b ⊓ a = a from
      ⟨fun h => by rw [← h, inf_comm, inf_sup_self], fun h => by rw [← h, sup_comm, sup_inf_self]⟩

/-- A type with a pair of commutative and associative binary operations which satisfy two absorption
laws relating the two operations has the structure of a lattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
@[instance_reducible]
/--
Definition of `Lattice.mk'` / `Lattice.mk'` 的定义

English:
definition Lattice.mk'
  signature: {α : Type*} [Max α] [Min α] (sup_comm : forall a b : α, a ⊔ b = b ⊔ a)
  body: have sup_idem : forall b : α, b ⊔ b = b := fun b =>
    calc
      b ⊔ b = b ⊔ b ⊓ (b ⊔ b) := by rw [inf_sup_self]
      _ = b := by rw [sup_inf_self]
  have inf_idem : forall b : α, b ⊓ b = b := fun b =>
    calc
      b ⊓ b = b ⊓ (b ⊔ b ⊓ b) := by rw [sup_inf_self]
      _ = b := by rw [inf_sup_self]
  let semilatt_inf_inst := SemilatticeInf.mk' inf_comm inf_assoc inf_idem
  let semilatt_sup_inst := SemilatticeSup.mk' sup_comm sup_assoc sup_idem
  have partial_order_eq : @SemilatticeSup.toPartialOrder _ semilatt_sup_inst =
                          @SemilatticeInf.toPartialOrder _ semilatt_inf_inst :=
    semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder _ _ _ _ _ _
      sup_inf_self inf_sup_self
  { semilatt_sup_inst, semilatt_inf_inst with
    inf_le_left := fun a b => by
      rw [partial_order_eq]
      apply inf_le_left,
    inf_le_right := fun a b => by
      rw [partial_order_eq]
      apply inf_le_right,
    le_inf := fun a b c => by
      rw [partial_order_eq]
      apply le_inf }

中文:
定义 格.mk'
  签名: {α : 类型} [最大值 α] [最小值 α] (sup_comm : 对任意 a b : α, a ⊔ b = b ⊔ a)
  定义体: have sup_idem : forall b : α, b ⊔ b = b := fun b =>
    calc
      b ⊔ b = b ⊔ b ⊓ (b ⊔ b) := by rw [inf_sup_self]
      _ = b := by rw [sup_inf_self]
  have inf_idem : forall b : α, b ⊓ b = b := fun b =>
    calc
      b ⊓ b = b ⊓ (b ⊔ b ⊓ b) := by rw [sup_inf_self]
      _ = b := by rw [inf_sup_self]
  let semilatt_inf_inst := SemilatticeInf.mk' inf_comm inf_assoc inf_idem
  let semilatt_sup_inst := SemilatticeSup.mk' sup_comm sup_assoc sup_idem
  have partial_order_eq : @SemilatticeSup.toPartialOrder _ semilatt_sup_inst =
                          @SemilatticeInf.toPartialOrder _ semilatt_inf_inst :=
    semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder _ _ _ _ _ _
      sup_inf_self inf_sup_self
  { semilatt_sup_inst, semilatt_inf_inst with
    inf_le_left := fun a b => by
      rw [partial_order_eq]
      apply inf_le_left,
    inf_le_right := fun a b => by
      rw [partial_order_eq]
      apply inf_le_right,
    le_inf := fun a b c => by
      rw [partial_order_eq]
      apply le_inf }

Depends on / 依赖: Semilatt, SemilatticeInf, SemilatticeInf.mk, SemilatticeSup, SemilatticeSup.mk, SemilatticeSup.toPartialOrder, inf_assoc, inf_comm, inf_idem, inf_sup_self, partial_order_eq, semilatt_inf_inst, semilatt_sup_inst, sup_assoc, sup_comm, sup_idem, sup_inf_self, toPartialOrder
-/
def Lattice.mk' {α : Type*} [Max α] [Min α] (sup_comm : forall a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : forall a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (inf_comm : forall a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : forall a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (sup_inf_self : forall a b : α, a ⊔ a ⊓ b = a)
    (inf_sup_self : forall a b : α, a ⊓ (a ⊔ b) = a) : Lattice α :=
  have sup_idem : forall b : α, b ⊔ b = b := fun b =>
    calc
      b ⊔ b = b ⊔ b ⊓ (b ⊔ b) := by rw [inf_sup_self]
      _ = b := by rw [sup_inf_self]
  have inf_idem : forall b : α, b ⊓ b = b := fun b =>
    calc
      b ⊓ b = b ⊓ (b ⊔ b ⊓ b) := by rw [sup_inf_self]
      _ = b := by rw [inf_sup_self]
  let semilatt_inf_inst := SemilatticeInf.mk' inf_comm inf_assoc inf_idem
  let semilatt_sup_inst := SemilatticeSup.mk' sup_comm sup_assoc sup_idem
  have partial_order_eq : @SemilatticeSup.toPartialOrder _ semilatt_sup_inst =
                          @SemilatticeInf.toPartialOrder _ semilatt_inf_inst :=
    semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder _ _ _ _ _ _
      sup_inf_self inf_sup_self
  { semilatt_sup_inst, semilatt_inf_inst with
    inf_le_left := fun a b => by
      rw [partial_order_eq]
      apply inf_le_left,
    inf_le_right := fun a b => by
      rw [partial_order_eq]
      apply inf_le_right,
    le_inf := fun a b c => by
      rw [partial_order_eq]
      apply le_inf }

section Lattice

variable [Lattice α] {a b c : α}

/--
theorem `inf_le_sup` / 定理 `inf_le_sup`

English:
theorem inf_le_sup
  statement: a ⊓ b <= a ⊔ b
  proof: inf_le_left.trans le_sup_left

中文:
定理 inf_le_sup
  结论: a ⊓ b <= a ⊔ b
  证明: inf_le_left.trans le_sup_left

Depends on / 依赖: inf_le_left, inf_le_left.trans, le_sup_left
-/
theorem inf_le_sup : a ⊓ b <= a ⊔ b :=
  inf_le_left.trans le_sup_left

/--
theorem `sup_le_inf` / 定理 `sup_le_inf`

English:
theorem sup_le_inf
  statement: a ⊔ b <= a ⊓ b ↔ a = b
  proof: by simp [le_antisymm_iff, and_comm]

@[to_dual (attr := simp)]

中文:
定理 sup_le_inf
  结论: a ⊔ b <= a ⊓ b ↔ a = b
  证明: by simp [le_antisymm_iff, and_comm]

@[to_dual (attr := simp)]

Depends on / 依赖: and_comm, le_antisymm_iff
-/
theorem sup_le_inf : a ⊔ b <= a ⊓ b ↔ a = b := by simp [le_antisymm_iff, and_comm]

@[to_dual (attr := simp)]
/--
lemma `inf_eq_sup` / 引理 `inf_eq_sup`

English:
lemma inf_eq_sup
  statement: a ⊓ b = a ⊔ b ↔ a = b
  proof: by rw [← inf_le_sup.ge_iff_eq, sup_le_inf]

中文:
引理 inf_eq_sup
  结论: a ⊓ b = a ⊔ b ↔ a = b
  证明: by rw [← inf_le_sup.ge_iff_eq, sup_le_inf]

Depends on / 依赖: ge_iff_eq, inf_le_sup, inf_le_sup.ge_iff_eq, sup_le_inf
-/
lemma inf_eq_sup : a ⊓ b = a ⊔ b ↔ a = b := by rw [← inf_le_sup.ge_iff_eq, sup_le_inf]

/--
lemma `inf_lt_sup` / 引理 `inf_lt_sup`

English:
lemma inf_lt_sup
  statement: a ⊓ b < a ⊔ b ↔ a != b
  proof: by rw [inf_le_sup.lt_iff_ne, Ne, inf_eq_sup]

@[to_dual (attr := simp) inf_right_le_sup_left]

中文:
引理 inf_lt_sup
  结论: a ⊓ b < a ⊔ b ↔ a != b
  证明: by rw [inf_le_sup.lt_iff_ne, Ne, inf_eq_sup]

@[to_dual (attr := simp) inf_right_le_sup_left]
-/
@[simp] lemma inf_lt_sup : a ⊓ b < a ⊔ b ↔ a != b := by rw [inf_le_sup.lt_iff_ne, Ne, inf_eq_sup]

@[to_dual (attr := simp) inf_right_le_sup_left]
/--
lemma `inf_left_le_sup_right` / 引理 `inf_left_le_sup_right`

English:
lemma inf_left_le_sup_right
  statement: (a ⊓ b) <= (b ⊔ c)
  proof: le_trans inf_le_right le_sup_left

@[simp, to_dual self]

中文:
引理 inf_left_le_sup_right
  结论: (a ⊓ b) <= (b ⊔ c)
  证明: le_trans inf_le_right le_sup_left

@[simp, to_dual self]

Depends on / 依赖: inf_le_right, le_sup_left, le_trans
-/
lemma inf_left_le_sup_right : (a ⊓ b) <= (b ⊔ c) := le_trans inf_le_right le_sup_left

@[simp, to_dual self]
/--
lemma `inf_right_le_sup_right` / 引理 `inf_right_le_sup_right`

English:
lemma inf_right_le_sup_right
  statement: (b ⊓ a) <= (b ⊔ c)
  proof: le_trans inf_le_left le_sup_left

@[simp, to_dual self]

中文:
引理 inf_right_le_sup_right
  结论: (b ⊓ a) <= (b ⊔ c)
  证明: le_trans inf_le_left le_sup_left

@[simp, to_dual self]

Depends on / 依赖: inf_le_left, le_sup_left, le_trans
-/
lemma inf_right_le_sup_right : (b ⊓ a) <= (b ⊔ c) := le_trans inf_le_left le_sup_left

@[simp, to_dual self]
/--
lemma `inf_left_le_sup_left` / 引理 `inf_left_le_sup_left`

English:
lemma inf_left_le_sup_left
  statement: (a ⊓ b) <= (c ⊔ b)
  proof: le_trans inf_le_right le_sup_right

@[to_dual]

中文:
引理 inf_left_le_sup_left
  结论: (a ⊓ b) <= (c ⊔ b)
  证明: le_trans inf_le_right le_sup_right

@[to_dual]

Depends on / 依赖: inf_le_right, le_sup_right, le_trans
-/
lemma inf_left_le_sup_left : (a ⊓ b) <= (c ⊔ b) := le_trans inf_le_right le_sup_right

@[to_dual]
/--
lemma `inf_eq_and_sup_eq_iff` / 引理 `inf_eq_and_sup_eq_iff`

English:
lemma inf_eq_and_sup_eq_iff
  statement: a ⊓ b = c ∧ a ⊔ b = c ↔ a = c ∧ b = c
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl := sup_eq_inf.1 (h.2.trans h.1.symm)
    simpa using h
  · rintro ⟨rfl, rfl⟩
    exact ⟨inf_idem _, sup_idem _⟩

中文:
引理 inf_eq_and_sup_eq_iff
  结论: a ⊓ b = c ∧ a ⊔ b = c ↔ a = c ∧ b = c
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl := sup_eq_inf.1 (h.2.trans h.1.symm)
    simpa using h
  · rintro ⟨rfl, rfl⟩
    exact ⟨inf_idem _, sup_idem _⟩

Depends on / 依赖: inf_idem, sup_eq_inf, sup_idem
-/
lemma inf_eq_and_sup_eq_iff : a ⊓ b = c ∧ a ⊔ b = c ↔ a = c ∧ b = c := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl := sup_eq_inf.1 (h.2.trans h.1.symm)
    simpa using h
  · rintro ⟨rfl, rfl⟩
    exact ⟨inf_idem _, sup_idem _⟩

/-!
#### Distributivity laws
-/


-- TODO: better names?
@[to_dual le_inf_sup]
/--
theorem `sup_inf_le` / 定理 `sup_inf_le`

English:
theorem sup_inf_le
  statement: a ⊔ b ⊓ c <= (a ⊔ b) ⊓ (a ⊔ c)
  proof: le_inf (sup_le_sup_left inf_le_left _) (sup_le_sup_left inf_le_right _)

@[to_dual]

中文:
定理 sup_inf_le
  结论: a ⊔ b ⊓ c <= (a ⊔ b) ⊓ (a ⊔ c)
  证明: le_inf (sup_le_sup_left inf_le_left _) (sup_le_sup_left inf_le_right _)

@[to_dual]

Depends on / 依赖: inf_le_left, inf_le_right, le_inf, sup_le_sup_left
-/
theorem sup_inf_le : a ⊔ b ⊓ c <= (a ⊔ b) ⊓ (a ⊔ c) :=
  le_inf (sup_le_sup_left inf_le_left _) (sup_le_sup_left inf_le_right _)

@[to_dual]
/--
theorem `inf_sup_self` / 定理 `inf_sup_self`

English:
theorem inf_sup_self
  statement: a ⊓ (a ⊔ b) = a
  proof: by simp

@[to_dual]

中文:
定理 inf_sup_self
  结论: a ⊓ (a ⊔ b) = a
  证明: by simp

@[to_dual]
-/
theorem inf_sup_self : a ⊓ (a ⊔ b) = a := by simp

@[to_dual]
/--
theorem `sup_eq_iff_inf_eq` / 定理 `sup_eq_iff_inf_eq`

English:
theorem sup_eq_iff_inf_eq
  statement: a ⊔ b = b ↔ a ⊓ b = a
  proof: by rw [sup_eq_right, ← inf_eq_left]

@[to_dual self]

中文:
定理 sup_eq_iff_inf_eq
  结论: a ⊔ b = b ↔ a ⊓ b = a
  证明: by rw [sup_eq_right, ← inf_eq_left]

@[to_dual self]

Depends on / 依赖: inf_eq_left, sup_eq_right
-/
theorem sup_eq_iff_inf_eq : a ⊔ b = b ↔ a ⊓ b = a := by rw [sup_eq_right, ← inf_eq_left]

@[to_dual self]
/--
theorem `Lattice.ext` / 定理 `Lattice.ext`

English:
theorem Lattice.ext
  given: {α} {A B : Lattice α} (H : forall x y : α, (haveI := A; x <= y) ↔ x <= y)
  proof: by
  cases A
  cases B
  cases SemilatticeSup.ext H
  cases SemilatticeInf.ext H
  congr

中文:
定理 格.ext
  条件: {α} {A B : 格 α} (H : 对任意 x y : α, (haveI := A; x <= y) ↔ x <= y)
  证明: by
  cases A
  cases B
  cases SemilatticeSup.ext H
  cases SemilatticeInf.ext H
  congr
-/
theorem Lattice.ext {α} {A B : Lattice α} (H : forall x y : α, (haveI := A; x <= y) ↔ x <= y) :
    A = B := by
  cases A
  cases B
  cases SemilatticeSup.ext H
  cases SemilatticeInf.ext H
  congr

end Lattice

/-!
### Distributive lattices
-/


/--
Definition of `DistribLattice` / `DistribLattice` 的定义

English:
class DistribLattice
  parameters: (α)
  extends: Lattice α
  axioms and operations (1):
    - le_sup_inf : forall x y z : α, (x ⊔ y) ⊓ (x ⊔ z) <= x ⊔ y ⊓ z

中文:
类 Distrib格
  参数: (α)
  继承: 格 α
  公理与运算 (1 个):
    - le_sup_inf : 对任意 x y z : α, (x ⊔ y) ⊓ (x ⊔ z) <= x ⊔ y ⊓ z
-/
class DistribLattice (α) extends Lattice α where
  /-- The infimum distributes over the supremum -/
  protected le_sup_inf : forall x y z : α, (x ⊔ y) ⊓ (x ⊔ z) <= x ⊔ y ⊓ z

section DistribLattice

variable [DistribLattice α] {x y z : α}

/--
theorem `le_sup_inf` / 定理 `le_sup_inf`

English:
theorem le_sup_inf
  given: {x y z : α}
  statement: (x ⊔ y) ⊓ (x ⊔ z) <= x ⊔ y ⊓ z
  proof: DistribLattice.le_sup_inf x y z

中文:
定理 le_sup_inf
  条件: {x y z : α}
  结论: (x ⊔ y) ⊓ (x ⊔ z) <= x ⊔ y ⊓ z
  证明: DistribLattice.le_sup_inf x y z

Depends on / 依赖: DistribLattice, DistribLattice.le_sup_inf, le_sup_inf
-/
theorem le_sup_inf {x y z : α} : (x ⊔ y) ⊓ (x ⊔ z) <= x ⊔ y ⊓ z :=
  DistribLattice.le_sup_inf x y z

/--
theorem `sup_inf_left` / 定理 `sup_inf_left`

English:
theorem sup_inf_left
  given: (a b c : α)
  statement: a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
  proof: le_antisymm sup_inf_le le_sup_inf

中文:
定理 sup_inf_left
  条件: (a b c : α)
  结论: a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
  证明: le_antisymm sup_inf_le le_sup_inf

Depends on / 依赖: le_antisymm, le_sup_inf, sup_inf_le
-/
theorem sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) :=
  le_antisymm sup_inf_le le_sup_inf

/--
theorem `sup_inf_right` / 定理 `sup_inf_right`

English:
theorem sup_inf_right
  given: (a b c : α)
  statement: a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
  proof: by
  simp only [sup_inf_left, sup_comm _ c]

@[to_dual existing]

中文:
定理 sup_inf_right
  条件: (a b c : α)
  结论: a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
  证明: by
  simp only [sup_inf_left, sup_comm _ c]

@[to_dual existing]

Depends on / 依赖: sup_comm, sup_inf_left
-/
theorem sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) := by
  simp only [sup_inf_left, sup_comm _ c]

@[to_dual existing]
/--
theorem `inf_sup_left` / 定理 `inf_sup_left`

English:
theorem inf_sup_left
  given: (a b c : α)
  statement: a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
  proof: calc
    a ⊓ (b ⊔ c) = a ⊓ (a ⊔ c) ⊓ (b ⊔ c) := by rw [inf_sup_self]
    _ = a ⊓ (a ⊓ b ⊔ c) := by simp only [inf_assoc, sup_inf_right]
    _ = (a ⊔ a ⊓ b) ⊓ (a ⊓ b ⊔ c) := by rw [sup_inf_self]
    _ = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm]
    _ = a ⊓ b ⊔ a ⊓ c := by rw [sup_inf_left]

@[to_dual existing le_sup_inf]

中文:
定理 inf_sup_left
  条件: (a b c : α)
  结论: a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
  证明: calc
    a ⊓ (b ⊔ c) = a ⊓ (a ⊔ c) ⊓ (b ⊔ c) := by rw [inf_sup_self]
    _ = a ⊓ (a ⊓ b ⊔ c) := by simp only [inf_assoc, sup_inf_right]
    _ = (a ⊔ a ⊓ b) ⊓ (a ⊓ b ⊔ c) := by rw [sup_inf_self]
    _ = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm]
    _ = a ⊓ b ⊔ a ⊓ c := by rw [sup_inf_left]

@[to_dual existing le_sup_inf]

Depends on / 依赖: inf_assoc, inf_sup_self, sup_comm, sup_inf_left, sup_inf_right, sup_inf_self
-/
theorem inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c :=
  calc
    a ⊓ (b ⊔ c) = a ⊓ (a ⊔ c) ⊓ (b ⊔ c) := by rw [inf_sup_self]
    _ = a ⊓ (a ⊓ b ⊔ c) := by simp only [inf_assoc, sup_inf_right]
    _ = (a ⊔ a ⊓ b) ⊓ (a ⊓ b ⊔ c) := by rw [sup_inf_self]
    _ = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm]
    _ = a ⊓ b ⊔ a ⊓ c := by rw [sup_inf_left]

@[to_dual existing le_sup_inf]
/--
theorem `inf_sup_le` / 定理 `inf_sup_le`

English:
theorem inf_sup_le
  given: {x y z : α}
  statement: x ⊓ (y ⊔ z) <= (x ⊓ y) ⊔ (x ⊓ z)
  proof: by
  rw [inf_sup_left]

中文:
定理 inf_sup_le
  条件: {x y z : α}
  结论: x ⊓ (y ⊔ z) <= (x ⊓ y) ⊔ (x ⊓ z)
  证明: by
  rw [inf_sup_left]

Depends on / 依赖: inf_sup_left
-/
theorem inf_sup_le {x y z : α} : x ⊓ (y ⊔ z) <= (x ⊓ y) ⊔ (x ⊓ z) := by
  rw [inf_sup_left]

/--
Instance `OrderDual.instDistribLattice` / 实例 `OrderDual.instDistribLattice`

English:
instance OrderDual.instDistribLattice
  signature: (α : Type*) [DistribLattice α]
  body: inf_sup_le

@[to_dual existing]

中文:
实例 OrderDual.instDistribLattice
  签名: (α : 类型) [Distrib格 α]
  定义体: inf_sup_le

@[to_dual existing]

Depends on / 依赖: inf_sup_le
-/
instance OrderDual.instDistribLattice (α : Type*) [DistribLattice α] : DistribLattice αᵒᵈ where
  le_sup_inf _ _ _ := inf_sup_le

@[to_dual existing]
/--
theorem `inf_sup_right` / 定理 `inf_sup_right`

English:
theorem inf_sup_right
  given: (a b c : α)
  statement: (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
  proof: by
  simp only [inf_sup_left, inf_comm _ c]

@[to_dual self (reorder := x y, h₁ h₂)]

中文:
定理 inf_sup_right
  条件: (a b c : α)
  结论: (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
  证明: by
  simp only [inf_sup_left, inf_comm _ c]

@[to_dual self (reorder := x y, h₁ h₂)]

Depends on / 依赖: inf_comm, inf_sup_left
-/
theorem inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c := by
  simp only [inf_sup_left, inf_comm _ c]

@[to_dual self (reorder := x y, h₁ h₂)]
/--
theorem `le_of_inf_le_sup_le` / 定理 `le_of_inf_le_sup_le`

English:
theorem le_of_inf_le_sup_le
  given: (h₁ : x ⊓ z <= y ⊓ z) (h₂ : x ⊔ z <= y ⊔ z)
  statement: x <= y
  proof: calc
    x <= y ⊓ z ⊔ x := le_sup_right
    _ = (y ⊔ x) ⊓ (x ⊔ z) := by rw [sup_inf_right, sup_comm x]
    _ <= (y ⊔ x) ⊓ (y ⊔ z) := inf_le_inf_left _ h₂
    _ = y ⊔ x ⊓ z := by rw [← sup_inf_left]
    _ <= y ⊔ y ⊓ z := sup_le_sup_left h₁ _
    _ <= _ := sup_le (le_refl y) inf_le_left

@[to_dual self (reorder := h₁ h₂)]

中文:
定理 le_of_inf_le_sup_le
  条件: (h₁ : x ⊓ z <= y ⊓ z) (h₂ : x ⊔ z <= y ⊔ z)
  结论: x <= y
  证明: calc
    x <= y ⊓ z ⊔ x := le_sup_right
    _ = (y ⊔ x) ⊓ (x ⊔ z) := by rw [sup_inf_right, sup_comm x]
    _ <= (y ⊔ x) ⊓ (y ⊔ z) := inf_le_inf_left _ h₂
    _ = y ⊔ x ⊓ z := by rw [← sup_inf_left]
    _ <= y ⊔ y ⊓ z := sup_le_sup_left h₁ _
    _ <= _ := sup_le (le_refl y) inf_le_left

@[to_dual self (reorder := h₁ h₂)]

Depends on / 依赖: inf_le_inf_left, inf_le_left, le_refl, le_sup_right, sup_comm, sup_inf_left, sup_inf_right, sup_le, sup_le_sup_left
-/
theorem le_of_inf_le_sup_le (h₁ : x ⊓ z <= y ⊓ z) (h₂ : x ⊔ z <= y ⊔ z) : x <= y :=
  calc
    x <= y ⊓ z ⊔ x := le_sup_right
    _ = (y ⊔ x) ⊓ (x ⊔ z) := by rw [sup_inf_right, sup_comm x]
    _ <= (y ⊔ x) ⊓ (y ⊔ z) := inf_le_inf_left _ h₂
    _ = y ⊔ x ⊓ z := by rw [← sup_inf_left]
    _ <= y ⊔ y ⊓ z := sup_le_sup_left h₁ _
    _ <= _ := sup_le (le_refl y) inf_le_left

@[to_dual self (reorder := h₁ h₂)]
/--
theorem `eq_of_inf_eq_sup_eq` / 定理 `eq_of_inf_eq_sup_eq`

English:
theorem eq_of_inf_eq_sup_eq
  given: {a b c : α} (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a)
  statement: b = c
  proof: le_antisymm (le_of_inf_le_sup_le (le_of_eq h₁) (le_of_eq h₂))
    (le_of_inf_le_sup_le (le_of_eq h₁.symm) (le_of_eq h₂.symm))

中文:
定理 eq_of_inf_eq_sup_eq
  条件: {a b c : α} (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a)
  结论: b = c
  证明: le_antisymm (le_of_inf_le_sup_le (le_of_eq h₁) (le_of_eq h₂))
    (le_of_inf_le_sup_le (le_of_eq h₁.symm) (le_of_eq h₂.symm))

Depends on / 依赖: le_antisymm, le_of_eq, le_of_inf_le_sup_le
-/
theorem eq_of_inf_eq_sup_eq {a b c : α} (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) : b = c :=
  le_antisymm (le_of_inf_le_sup_le (le_of_eq h₁) (le_of_eq h₂))
    (le_of_inf_le_sup_le (le_of_eq h₁.symm) (le_of_eq h₂.symm))

end DistribLattice

-- See note [reducible non-instances]
/-- Prove distributivity of an existing lattice from the dual distributive law. -/
@[to_dual existing mk]
/--
Definition of `DistribLattice.ofInfSupLe` / `DistribLattice.ofInfSupLe` 的定义

English:
abbreviation DistribLattice.ofInfSupLe
  body: (@OrderDual.instDistribLattice αᵒᵈ { (inferInstance : Lattice αᵒᵈ) with
      le_sup_inf := inf_sup_le }).le_sup_inf

中文:
缩写 Distrib格.ofInfSupLe
  定义体: (@OrderDual.instDistribLattice αᵒᵈ { (inferInstance : Lattice αᵒᵈ) with
      le_sup_inf := inf_sup_le }).le_sup_inf

Depends on / 依赖: Lattice, OrderDual, OrderDual.instDistribLattice, instDistribLattice
-/
abbrev DistribLattice.ofInfSupLe
    [Lattice α] (inf_sup_le : forall a b c : α, a ⊓ (b ⊔ c) <= a ⊓ b ⊔ a ⊓ c) : DistribLattice α where
  le_sup_inf := (@OrderDual.instDistribLattice αᵒᵈ { (inferInstance : Lattice αᵒᵈ) with
      le_sup_inf := inf_sup_le }).le_sup_inf

/-!
### Lattices derived from linear orders
-/

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.toLattice {α : Type u} [LinearOrder α] : Lattice α where
  sup := max
  inf := min
  le_sup_left := le_max_left; le_sup_right := le_max_right; sup_le _ _ _ := max_le
  inf_le_left := min_le_left; inf_le_right := min_le_right; le_inf _ _ _ := le_min

section LinearOrder

variable [LinearOrder α] {a b c d : α}

@[to_dual]
/--
theorem `sup_ind` / 定理 `sup_ind`

English:
theorem sup_ind
  given: (a b : α) {p : α -> Prop} (ha : p a) (hb : p b)
  statement: p (a ⊔ b)
  proof: (Std.Total.total a b).elim (fun h : a <= b => by rwa [sup_eq_right.2 h]) fun h => by
  rwa [sup_eq_left.2 h]

@[to_dual (attr := simp) inf_le_iff]

中文:
定理 sup_ind
  条件: (a b : α) {p : α -> 命题} (ha : p a) (hb : p b)
  结论: p (a ⊔ b)
  证明: (Std.Total.total a b).elim (fun h : a <= b => by rwa [sup_eq_right.2 h]) fun h => by
  rwa [sup_eq_left.2 h]

@[to_dual (attr := simp) inf_le_iff]

Depends on / 依赖: Std.Total.total, sup_eq_left, sup_eq_right
-/
theorem sup_ind (a b : α) {p : α -> Prop} (ha : p a) (hb : p b) : p (a ⊔ b) :=
  (Std.Total.total a b).elim (fun h : a <= b => by rwa [sup_eq_right.2 h]) fun h => by
  rwa [sup_eq_left.2 h]

@[to_dual (attr := simp) inf_le_iff]
/--
theorem `le_sup_iff` / 定理 `le_sup_iff`

English:
theorem le_sup_iff
  statement: a <= b ⊔ c ↔ a <= b ∨ a <= c
  proof: by
  grind

@[to_dual (attr := simp) inf_lt_iff]

中文:
定理 le_sup_iff
  结论: a <= b ⊔ c ↔ a <= b ∨ a <= c
  证明: by
  grind

@[to_dual (attr := simp) inf_lt_iff]
-/
theorem le_sup_iff : a <= b ⊔ c ↔ a <= b ∨ a <= c := by
  grind

@[to_dual (attr := simp) inf_lt_iff]
/--
theorem `lt_sup_iff` / 定理 `lt_sup_iff`

English:
theorem lt_sup_iff
  statement: a < b ⊔ c ↔ a < b ∨ a < c
  proof: by
  grind

@[to_dual (attr := simp) lt_inf_iff]

中文:
定理 lt_sup_iff
  结论: a < b ⊔ c ↔ a < b ∨ a < c
  证明: by
  grind

@[to_dual (attr := simp) lt_inf_iff]
-/
theorem lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c := by
  grind

@[to_dual (attr := simp) lt_inf_iff]
/--
theorem `sup_lt_iff` / 定理 `sup_lt_iff`

English:
theorem sup_lt_iff
  statement: b ⊔ c < a ↔ b < a ∧ c < a
  proof: ⟨fun h => ⟨le_sup_left.trans_lt h, le_sup_right.trans_lt h⟩,
   fun h => sup_ind (p := (· < a)) b c h.1 h.2⟩

中文:
定理 sup_lt_iff
  结论: b ⊔ c < a ↔ b < a ∧ c < a
  证明: ⟨fun h => ⟨le_sup_left.trans_lt h, le_sup_right.trans_lt h⟩,
   fun h => sup_ind (p := (· < a)) b c h.1 h.2⟩

Depends on / 依赖: le_sup_left, le_sup_left.trans_lt, le_sup_right, le_sup_right.trans_lt, sup_ind, trans_lt
-/
theorem sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a :=
  ⟨fun h => ⟨le_sup_left.trans_lt h, le_sup_right.trans_lt h⟩,
   fun h => sup_ind (p := (· < a)) b c h.1 h.2⟩

variable (a b c d)

@[to_dual]
/--
theorem `max_max_max_comm` / 定理 `max_max_max_comm`

English:
theorem max_max_max_comm
  statement: max (max a b) (max c d) = max (max a c) (max b d)
  proof: sup_sup_sup_comm _ _ _ _

中文:
定理 max_max_max_comm
  结论: 最大值 (最大值 a b) (最大值 c d) = 最大值 (最大值 a c) (最大值 b d)
  证明: sup_sup_sup_comm _ _ _ _

Depends on / 依赖: sup_sup_sup_comm
-/
theorem max_max_max_comm : max (max a b) (max c d) = max (max a c) (max b d) :=
  sup_sup_sup_comm _ _ _ _

end LinearOrder

/--
theorem `sup_eq_maxDefault` / 定理 `sup_eq_maxDefault`

English:
theorem sup_eq_maxDefault
  given: [SemilatticeSup α] [DecidableLE α] [@Std.Total α (· <= ·)]
  proof: by
  ext x y
  unfold maxDefault
  split_ifs with h'
  exacts [sup_of_le_right h', sup_of_le_left <| (total_of (· <= ·) x y).resolve_left h']

中文:
定理 sup_eq_maxDefault
  条件: [SemilatticeSup α] [DecidableLE α] [@Std.全 α (· <= ·)]
  证明: by
  ext x y
  unfold maxDefault
  split_ifs with h'
  exacts [sup_of_le_right h', sup_of_le_left <| (total_of (· <= ·) x y).resolve_left h']

Depends on / 依赖: exacts, maxDefault, resolve_left, split_ifs, sup_of_le_left, sup_of_le_right, total_of
-/
theorem sup_eq_maxDefault [SemilatticeSup α] [DecidableLE α] [@Std.Total α (· <= ·)] :
    (· ⊔ ·) = (maxDefault : α -> α -> α) := by
  ext x y
  unfold maxDefault
  split_ifs with h'
  exacts [sup_of_le_right h', sup_of_le_left <| (total_of (· <= ·) x y).resolve_left h']

/--
theorem `inf_eq_minDefault` / 定理 `inf_eq_minDefault`

English:
theorem inf_eq_minDefault
  given: [SemilatticeInf α] [DecidableLE α] [@Std.Total α (· <= ·)]
  proof: by
  ext x y
  unfold minDefault
  split_ifs with h'
  exacts [inf_of_le_left h', inf_of_le_right <| (total_of (· <= ·) x y).resolve_left h']

中文:
定理 inf_eq_minDefault
  条件: [SemilatticeInf α] [DecidableLE α] [@Std.全 α (· <= ·)]
  证明: by
  ext x y
  unfold minDefault
  split_ifs with h'
  exacts [inf_of_le_left h', inf_of_le_right <| (total_of (· <= ·) x y).resolve_left h']

Depends on / 依赖: exacts, inf_of_le_left, inf_of_le_right, minDefault, resolve_left, split_ifs, total_of
-/
theorem inf_eq_minDefault [SemilatticeInf α] [DecidableLE α] [@Std.Total α (· <= ·)] :
    (· ⊓ ·) = (minDefault : α -> α -> α) := by
  ext x y
  unfold minDefault
  split_ifs with h'
  exacts [inf_of_le_left h', inf_of_le_right <| (total_of (· <= ·) x y).resolve_left h']

/--
Definition of `Lattice.toLinearOrder` / `Lattice.toLinearOrder` 的定义

English:
abbreviation Lattice.toLinearOrder
  signature: (α : Type u) [Lattice α] [DecidableEq α]
  body: ‹_›
  toDecidableEq := ‹_›
  toDecidableLT := ‹_›
  le_total := total_of (· <= ·)
  max_def := by exact congr_fun₂ sup_eq_maxDefault
  min_def := by exact congr_fun₂ inf_eq_minDefault

中文:
缩写 格.toLinearOrder
  签名: (α : 类型u) [格 α] [DecidableEq α]
  定义体: ‹_›
  toDecidableEq := ‹_›
  toDecidableLT := ‹_›
  le_total := total_of (· <= ·)
  max_def := by exact congr_fun₂ sup_eq_maxDefault
  min_def := by exact congr_fun₂ inf_eq_minDefault
-/
abbrev Lattice.toLinearOrder (α : Type u) [Lattice α] [DecidableEq α]
    [DecidableLE α] [DecidableLT α] [@Std.Total α (· <= ·)] : LinearOrder α where
  toDecidableLE := ‹_›
  toDecidableEq := ‹_›
  toDecidableLT := ‹_›
  le_total := total_of (· <= ·)
  max_def := by exact congr_fun₂ sup_eq_maxDefault
  min_def := by exact congr_fun₂ inf_eq_minDefault

-- see Note [lower instance priority]
instance (priority := 100) {α : Type u} [LinearOrder α] : DistribLattice α where
  le_sup_inf _ b c :=
    match le_total b c with
| Or.inl h => inf_le_of_left_le sup_le_sup_left (le_inf (le_refl b) h) _
| Or.inr h => inf_le_of_right_le sup_le_sup_left (le_inf h (le_refl c)) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribLattice Nat
  body: inferInstance

中文:
实例 :
  签名: Distrib格 自然数
  定义体: inferInstance
-/
instance : DistribLattice Nat := inferInstance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice Int
  body: inferInstance

中文:
实例 :
  签名: 格 整数
  定义体: inferInstance
-/
instance : Lattice Int := inferInstance

/-! ### Dual order -/


open OrderDual

@[to_dual (attr := simp)]
/--
theorem `ofDual_sup` / 定理 `ofDual_sup`

English:
theorem ofDual_sup
  given: [Min α] (a b : αᵒᵈ)
  statement: ofDual (a ⊔ b) = ofDual a ⊓ ofDual b
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 ofDual_sup
  条件: [最小值 α] (a b : αᵒᵈ)
  结论: ofDual (a ⊔ b) = ofDual a ⊓ ofDual b
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem ofDual_sup [Min α] (a b : αᵒᵈ) : ofDual (a ⊔ b) = ofDual a ⊓ ofDual b :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `toDual_sup` / 定理 `toDual_sup`

English:
theorem toDual_sup
  given: [Max α] (a b : α)
  statement: toDual (a ⊔ b) = toDual a ⊓ toDual b
  proof: rfl

中文:
定理 toDual_sup
  条件: [最大值 α] (a b : α)
  结论: toDual (a ⊔ b) = toDual a ⊓ toDual b
  证明: rfl
-/
theorem toDual_sup [Max α] (a b : α) : toDual (a ⊔ b) = toDual a ⊓ toDual b :=
  rfl

section LinearOrder

variable [LinearOrder α]

/--
theorem `ofDual_max` / 定理 `ofDual_max`

English:
theorem ofDual_max
  given: (a b : αᵒᵈ)
  statement: ofDual (max a b) = min (ofDual a) (ofDual b)
  proof: rfl

中文:
定理 ofDual_max
  条件: (a b : αᵒᵈ)
  结论: ofDual (最大值 a b) = 最小值 (ofDual a) (ofDual b)
  证明: rfl
-/
@[to_dual] theorem ofDual_max (a b : αᵒᵈ) : ofDual (max a b) = min (ofDual a) (ofDual b) :=
  rfl

/--
theorem `toDual_max` / 定理 `toDual_max`

English:
theorem toDual_max
  given: (a b : α)
  statement: toDual (max a b) = min (toDual a) (toDual b)
  proof: rfl

中文:
定理 toDual_max
  条件: (a b : α)
  结论: toDual (最大值 a b) = 最小值 (toDual a) (toDual b)
  证明: rfl
-/
@[to_dual] theorem toDual_max (a b : α) : toDual (max a b) = min (toDual a) (toDual b) :=
  rfl

end LinearOrder

/-! ### Function lattices -/


namespace Pi

variable {ι : Type*} {α' : ι -> Type*}

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Max (α' i)] : Max (forall i, α' i)
  body: ⟨fun f g i => f i ⊔ g i⟩

@[to_dual (attr := simp)]

中文:
实例 [对任意
  签名: i, 最大值 (α' i)] : 最大值 (对任意 i, α' i)
  定义体: ⟨fun f g i => f i ⊔ g i⟩

@[to_dual (attr := simp)]
-/
instance [forall i, Max (α' i)] : Max (forall i, α' i) :=
  ⟨fun f g i => f i ⊔ g i⟩

@[to_dual (attr := simp)]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: [forall i, Max (α' i)] (f g : forall i, α' i) (i : ι)
  statement: (f ⊔ g) i = f i ⊔ g i
  proof: rfl

@[to_dual (attr := push ←)]

中文:
定理 sup_apply
  条件: [对任意 i, 最大值 (α' i)] (f g : 对任意 i, α' i) (i : ι)
  结论: (f ⊔ g) i = f i ⊔ g i
  证明: rfl

@[to_dual (attr := push ←)]
-/
theorem sup_apply [forall i, Max (α' i)] (f g : forall i, α' i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
  rfl

@[to_dual (attr := push ←)]
/--
theorem `sup_def` / 定理 `sup_def`

English:
theorem sup_def
  given: [forall i, Max (α' i)] (f g : forall i, α' i)
  statement: f ⊔ g = fun i => f i ⊔ g i
  proof: rfl

@[to_dual]

中文:
定理 sup_def
  条件: [对任意 i, 最大值 (α' i)] (f g : 对任意 i, α' i)
  结论: f ⊔ g = fun i => f i ⊔ g i
  证明: rfl

@[to_dual]
-/
theorem sup_def [forall i, Max (α' i)] (f g : forall i, α' i) : f ⊔ g = fun i => f i ⊔ g i :=
  rfl

@[to_dual]
/--
Instance `instSemilatticeSup` / 实例 `instSemilatticeSup`

English:
instance instSemilatticeSup
  signature: [forall i, SemilatticeSup (α' i)]
  body: x i ⊔ y i
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ ac bc i := sup_le (ac i) (bc i)

中文:
实例 instSemilatticeSup
  签名: [对任意 i, SemilatticeSup (α' i)]
  定义体: x i ⊔ y i
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ ac bc i := sup_le (ac i) (bc i)
-/
instance instSemilatticeSup [forall i, SemilatticeSup (α' i)] : SemilatticeSup (forall i, α' i) where
  sup x y i := x i ⊔ y i
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ ac bc i := sup_le (ac i) (bc i)

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: [forall i, Lattice (α' i)]

中文:
实例 instLattice
  签名: [对任意 i, 格 (α' i)]
-/
instance instLattice [forall i, Lattice (α' i)] : Lattice (forall i, α' i) where

/--
Instance `instDistribLattice` / 实例 `instDistribLattice`

English:
instance instDistribLattice
  signature: [forall i, DistribLattice (α' i)]
  body: le_sup_inf

中文:
实例 instDistribLattice
  签名: [对任意 i, Distrib格 (α' i)]
  定义体: le_sup_inf

Depends on / 依赖: le_sup_inf
-/
instance instDistribLattice [forall i, DistribLattice (α' i)] : DistribLattice (forall i, α' i) where
  le_sup_inf _ _ _ _ := le_sup_inf

end Pi

namespace Function

variable {ι : Type*} {π : ι -> Type*} [DecidableEq ι]

-- Porting note: Dot notation on `Function.update` broke
@[to_dual]
/--
theorem `update_sup` / 定理 `update_sup`

English:
theorem update_sup
  given: [forall i, SemilatticeSup (π i)] (f : forall i, π i) (i : ι) (a b : π i)
  proof: funext fun j => by obtain rfl | hji := eq_or_ne j i <;> simp [update_of_ne, *]

中文:
定理 update_sup
  条件: [对任意 i, SemilatticeSup (π i)] (f : 对任意 i, π i) (i : ι) (a b : π i)
  证明: funext fun j => by obtain rfl | hji := eq_or_ne j i <;> simp [update_of_ne, *]

Depends on / 依赖: eq_or_ne, update_of_ne
-/
theorem update_sup [forall i, SemilatticeSup (π i)] (f : forall i, π i) (i : ι) (a b : π i) :
    update f i (a ⊔ b) = update f i a ⊔ update f i b :=
  funext fun j => by obtain rfl | hji := eq_or_ne j i <;> simp [update_of_ne, *]

end Function

/-!
### Monotone functions and lattices
-/


namespace Monotone

/-- Pointwise supremum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise infimum of two monotone functions is a monotone function. -/]
/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  statement: [Preorder α] [SemilatticeSup β] {f g : α -> β} (hf : Monotone f)
  proof: fun _ _ h => sup_le_sup (hf h) (hg h)

中文:
定理 上确界
  结论: [预序 α] [SemilatticeSup β] {f g : α -> β} (hf : 递增 f)
  证明: fun _ _ h => sup_le_sup (hf h) (hg h)
-/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α -> β} (hf : Monotone f)
    (hg : Monotone g) :
    Monotone (f ⊔ g) := fun _ _ h => sup_le_sup (hf h) (hg h)

/-- Pointwise maximum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise minimum of two monotone functions is a monotone function. -/]
/--
theorem `max` / 定理 `max`

English:
theorem max
  statement: [Preorder α] [LinearOrder β] {f g : α -> β} (hf : Monotone f)
  proof: hf.sup hg

@[to_dual map_inf_le]

中文:
定理 最大值
  结论: [预序 α] [线性序 β] {f g : α -> β} (hf : 递增 f)
  证明: hf.sup hg

@[to_dual map_inf_le]
-/
protected theorem max [Preorder α] [LinearOrder β] {f g : α -> β} (hf : Monotone f)
    (hg : Monotone g) :
    Monotone fun x => max (f x) (g x) :=
  hf.sup hg

@[to_dual map_inf_le]
/--
theorem `le_map_sup` / 定理 `le_map_sup`

English:
theorem le_map_sup
  given: [SemilatticeSup α] [SemilatticeSup β] {f : α -> β} (h : Monotone f) (x y : α)
  proof: sup_le (h le_sup_left) (h le_sup_right)

@[to_dual of_map_inf_le_left]

中文:
定理 le_map_sup
  条件: [SemilatticeSup α] [SemilatticeSup β] {f : α -> β} (h : 递增 f) (x y : α)
  证明: sup_le (h le_sup_left) (h le_sup_right)

@[to_dual of_map_inf_le_left]

Depends on / 依赖: Classical, Classical.typeDecidableEq, le_sup_left, le_sup_right, sup_le, typeDecidableEq
-/
theorem le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α -> β} (h : Monotone f) (x y : α) :
    f x ⊔ f y <= f (x ⊔ y) :=
  sup_le (h le_sup_left) (h le_sup_right)

@[to_dual of_map_inf_le_left]
/--
theorem `of_left_le_map_sup` / 定理 `of_left_le_map_sup`

English:
theorem of_left_le_map_sup
  statement: [SemilatticeSup α] [Preorder β] {f : α -> β}
  proof: by
  intro x y hxy
  rw [← sup_eq_right.2 hxy]
  apply h

@[to_dual of_map_inf_le]

中文:
定理 of_left_le_map_sup
  结论: [SemilatticeSup α] [预序 β] {f : α -> β}
  证明: by
  intro x y hxy
  rw [← sup_eq_right.2 hxy]
  apply h

@[to_dual of_map_inf_le]

Depends on / 依赖: Classical, Classical.propDecidable, propDecidable, sup_eq_right
-/
theorem of_left_le_map_sup [SemilatticeSup α] [Preorder β] {f : α -> β}
    (h : forall x y, f x <= f (x ⊔ y)) : Monotone f := by
  intro x y hxy
  rw [← sup_eq_right.2 hxy]
  apply h

@[to_dual of_map_inf_le]
/--
theorem `of_le_map_sup` / 定理 `of_le_map_sup`

English:
theorem of_le_map_sup
  statement: [SemilatticeSup α] [SemilatticeSup β] {f : α -> β}
  proof: of_left_le_map_sup fun x y => le_sup_left.trans (h x y)

@[to_dual]

中文:
定理 of_le_map_sup
  结论: [SemilatticeSup α] [SemilatticeSup β] {f : α -> β}
  证明: of_left_le_map_sup fun x y => le_sup_left.trans (h x y)

@[to_dual]

Depends on / 依赖: le_sup_left, le_sup_left.trans, of_left_le_map_sup
-/
theorem of_le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α -> β}
    (h : forall x y, f x ⊔ f y <= f (x ⊔ y)) : Monotone f :=
  of_left_le_map_sup fun x y => le_sup_left.trans (h x y)

@[to_dual]
/--
theorem `of_map_sup` / 定理 `of_map_sup`

English:
theorem of_map_sup
  statement: [SemilatticeSup α] [SemilatticeSup β] {f : α -> β}
  proof: of_le_map_sup fun x y => (h x y).ge

中文:
定理 of_map_sup
  结论: [SemilatticeSup α] [SemilatticeSup β] {f : α -> β}
  证明: of_le_map_sup fun x y => (h x y).ge

Depends on / 依赖: of_le_map_sup
-/
theorem of_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α -> β}
    (h : forall x y, f (x ⊔ y) = f x ⊔ f y) : Monotone f :=
  of_le_map_sup fun x y => (h x y).ge

variable [LinearOrder α]

@[to_dual]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: [SemilatticeSup β] {f : α -> β} (hf : Monotone f) (x y : α)
  proof: (Std.Total.total x y).elim (fun h : x <= y => by simp only [h, hf h, sup_of_le_right]) fun h => by
    simp only [h, hf h, sup_of_le_left]

中文:
定理 map_sup
  条件: [SemilatticeSup β] {f : α -> β} (hf : 递增 f) (x y : α)
  证明: (Std.Total.total x y).elim (fun h : x <= y => by simp only [h, hf h, sup_of_le_right]) fun h => by
    simp only [h, hf h, sup_of_le_left]

Depends on / 依赖: Std.Total.total, sup_of_le_left, sup_of_le_right
-/
theorem map_sup [SemilatticeSup β] {f : α -> β} (hf : Monotone f) (x y : α) :
    f (x ⊔ y) = f x ⊔ f y :=
  (Std.Total.total x y).elim (fun h : x <= y => by simp only [h, hf h, sup_of_le_right]) fun h => by
    simp only [h, hf h, sup_of_le_left]

end Monotone

/--
theorem `exists_ge_and_iff_exists` / 定理 `exists_ge_and_iff_exists`

English:
theorem exists_ge_and_iff_exists
  given: [SemilatticeSup α] {P : α -> Prop} {x₀ : α} (hP : Monotone P)
  proof: ⟨fun h => h.imp fun _ h => h.2, fun ⟨x, hx⟩ => ⟨x ⊔ x₀, le_sup_right, hP le_sup_left hx⟩⟩

中文:
定理 存在_ge_and_iff_存在
  条件: [SemilatticeSup α] {P : α -> 命题} {x₀ : α} (hP : 递增 P)
  证明: ⟨fun h => h.imp fun _ h => h.2, fun ⟨x, hx⟩ => ⟨x ⊔ x₀, le_sup_right, hP le_sup_left hx⟩⟩

Depends on / 依赖: h.imp, le_sup_left, le_sup_right
-/
theorem exists_ge_and_iff_exists [SemilatticeSup α] {P : α -> Prop} {x₀ : α} (hP : Monotone P) :
    (exists x, x₀ <= x ∧ P x) ↔ exists x, P x :=
  ⟨fun h => h.imp fun _ h => h.2, fun ⟨x, hx⟩ => ⟨x ⊔ x₀, le_sup_right, hP le_sup_left hx⟩⟩

/--
theorem `exists_and_iff_of_monotone` / 定理 `exists_and_iff_of_monotone`

English:
theorem exists_and_iff_of_monotone
  statement: [SemilatticeSup α] {P Q : α -> Prop}
  proof: ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ => ⟨x ⊔ y, ⟨hP le_sup_left hPx, hQ le_sup_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ => ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩

中文:
定理 存在_and_iff_of_monotone
  结论: [SemilatticeSup α] {P Q : α -> 命题}
  证明: ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ => ⟨x ⊔ y, ⟨hP le_sup_left hPx, hQ le_sup_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ => ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩

Depends on / 依赖: le_sup_left, le_sup_right
-/
theorem exists_and_iff_of_monotone [SemilatticeSup α] {P Q : α -> Prop}
    (hP : Monotone P) (hQ : Monotone Q) :
    ((exists x, P x) ∧ exists x, Q x) ↔ (exists x, P x ∧ Q x) :=
  ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ => ⟨x ⊔ y, ⟨hP le_sup_left hPx, hQ le_sup_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ => ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩

namespace MonotoneOn
variable {f : α -> β} {s : Set α} {x y : α}

/-- Pointwise supremum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise infimum of two monotone functions is a monotone function. -/]
/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  statement: [Preorder α] [SemilatticeSup β] {f g : α -> β} {s : Set α}
  proof: fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)

中文:
定理 上确界
  结论: [预序 α] [SemilatticeSup β] {f g : α -> β} {s : 集合 α}
  证明: fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)
-/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α -> β} {s : Set α}
    (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (f ⊔ g) s :=
  fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)

/-- Pointwise maximum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise minimum of two monotone functions is a monotone function. -/]
/--
theorem `max` / 定理 `max`

English:
theorem max
  statement: [Preorder α] [LinearOrder β] {f g : α -> β} {s : Set α} (hf : MonotoneOn f s)
  proof: hf.sup hg

@[to_dual]

中文:
定理 最大值
  结论: [预序 α] [线性序 β] {f g : α -> β} {s : 集合 α} (hf : MonotoneOn f s)
  证明: hf.sup hg

@[to_dual]
-/
protected theorem max [Preorder α] [LinearOrder β] {f g : α -> β} {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => max (f x) (g x)) s :=
  hf.sup hg

@[to_dual]
/--
theorem `of_map_sup` / 定理 `of_map_sup`

English:
theorem of_map_sup
  statement: [SemilatticeSup α] [SemilatticeSup β]
  proof: fun x hx y hy hxy =>
sup_eq_right.1 by rw [← h _ hx _ hy, sup_eq_right.2 hxy]

中文:
定理 of_map_sup
  结论: [SemilatticeSup α] [SemilatticeSup β]
  证明: fun x hx y hy hxy =>
sup_eq_right.1 by rw [← h _ hx _ hy, sup_eq_right.2 hxy]
-/
theorem of_map_sup [SemilatticeSup α] [SemilatticeSup β]
    (h : forall x in s, forall y in s, f (x ⊔ y) = f x ⊔ f y) : MonotoneOn f s := fun x hx y hy hxy =>
sup_eq_right.1 by rw [← h _ hx _ hy, sup_eq_right.2 hxy]

variable [LinearOrder α]

@[to_dual]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: [SemilatticeSup β] (hf : MonotoneOn f s) (hx : x in s) (hy : y in s)
  proof: by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right]

中文:
定理 map_sup
  条件: [SemilatticeSup β] (hf : MonotoneOn f s) (hx : x in s) (hy : y in s)
  证明: by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right]

Depends on / 依赖: le_total, sup_of_le_left, sup_of_le_right
-/
theorem map_sup [SemilatticeSup β] (hf : MonotoneOn f s) (hx : x in s) (hy : y in s) :
    f (x ⊔ y) = f x ⊔ f y := by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right]

end MonotoneOn

namespace Antitone

/-- Pointwise supremum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise infimum of two antitone functions is an antitone function. -/]
/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  statement: [Preorder α] [SemilatticeSup β] {f g : α -> β} (hf : Antitone f)
  proof: fun _ _ h => sup_le_sup (hf h) (hg h)

中文:
定理 上确界
  结论: [预序 α] [SemilatticeSup β] {f g : α -> β} (hf : 递减 f)
  证明: fun _ _ h => sup_le_sup (hf h) (hg h)
-/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α -> β} (hf : Antitone f)
    (hg : Antitone g) :
    Antitone (f ⊔ g) := fun _ _ h => sup_le_sup (hf h) (hg h)

/-- Pointwise maximum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise minimum of two antitone functions is an antitone function. -/]
/--
theorem `max` / 定理 `max`

English:
theorem max
  statement: [Preorder α] [LinearOrder β] {f g : α -> β} (hf : Antitone f)
  proof: hf.sup hg

@[to_dual le_map_inf]

中文:
定理 最大值
  结论: [预序 α] [线性序 β] {f g : α -> β} (hf : 递减 f)
  证明: hf.sup hg

@[to_dual le_map_inf]
-/
protected theorem max [Preorder α] [LinearOrder β] {f g : α -> β} (hf : Antitone f)
    (hg : Antitone g) :
    Antitone fun x => max (f x) (g x) :=
  hf.sup hg

@[to_dual le_map_inf]
/--
theorem `map_sup_le` / 定理 `map_sup_le`

English:
theorem map_sup_le
  given: [SemilatticeSup α] [SemilatticeInf β] {f : α -> β} (h : Antitone f) (x y : α)
  proof: h.dual_right.le_map_sup x y

中文:
定理 map_sup_le
  条件: [SemilatticeSup α] [SemilatticeInf β] {f : α -> β} (h : 递减 f) (x y : α)
  证明: h.dual_right.le_map_sup x y

Depends on / 依赖: dual_right, h.dual_right.le_map_sup, le_map_sup
-/
theorem map_sup_le [SemilatticeSup α] [SemilatticeInf β] {f : α -> β} (h : Antitone f) (x y : α) :
    f (x ⊔ y) <= f x ⊓ f y :=
  h.dual_right.le_map_sup x y

variable [LinearOrder α]

@[to_dual]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: [SemilatticeInf β] {f : α -> β} (hf : Antitone f) (x y : α)
  proof: hf.dual_right.map_sup x y

中文:
定理 map_sup
  条件: [SemilatticeInf β] {f : α -> β} (hf : 递减 f) (x y : α)
  证明: hf.dual_right.map_sup x y

Depends on / 依赖: Ideal.mul_mem_left, dual_right, hf.dual_right.map_sup, map_sup, mul_mem_left
-/
theorem map_sup [SemilatticeInf β] {f : α -> β} (hf : Antitone f) (x y : α) :
    f (x ⊔ y) = f x ⊓ f y :=
  hf.dual_right.map_sup x y

end Antitone

/--
theorem `exists_le_and_iff_exists` / 定理 `exists_le_and_iff_exists`

English:
theorem exists_le_and_iff_exists
  given: [SemilatticeInf α] {P : α -> Prop} {x₀ : α} (hP : Antitone P)
  proof: exists_ge_and_iff_exists hP.dual_left

中文:
定理 存在_le_and_iff_存在
  条件: [SemilatticeInf α] {P : α -> 命题} {x₀ : α} (hP : 递减 P)
  证明: exists_ge_and_iff_exists hP.dual_left

Depends on / 依赖: dual_left, exists_ge_and_iff_exists, hP.dual_left
-/
theorem exists_le_and_iff_exists [SemilatticeInf α] {P : α -> Prop} {x₀ : α} (hP : Antitone P) :
    (exists x, x <= x₀ ∧ P x) ↔ exists x, P x :=
exists_ge_and_iff_exists hP.dual_left

/--
theorem `exists_and_iff_of_antitone` / 定理 `exists_and_iff_of_antitone`

English:
theorem exists_and_iff_of_antitone
  statement: [SemilatticeInf α] {P Q : α -> Prop}
  proof: ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ => ⟨x ⊓ y, ⟨hP inf_le_left hPx, hQ inf_le_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ => ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩

中文:
定理 存在_and_iff_of_antitone
  结论: [SemilatticeInf α] {P Q : α -> 命题}
  证明: ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ => ⟨x ⊓ y, ⟨hP inf_le_left hPx, hQ inf_le_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ => ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩

Depends on / 依赖: inf_le_left, inf_le_right
-/
theorem exists_and_iff_of_antitone [SemilatticeInf α] {P Q : α -> Prop}
    (hP : Antitone P) (hQ : Antitone Q) : ((exists x, P x) ∧ exists x, Q x) ↔ (exists x, P x ∧ Q x) :=
  ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ => ⟨x ⊓ y, ⟨hP inf_le_left hPx, hQ inf_le_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ => ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩

namespace AntitoneOn
variable {f : α -> β} {s : Set α} {x y : α}

/-- Pointwise supremum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise infimum of two antitone functions is an antitone function. -/]
/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  statement: [Preorder α] [SemilatticeSup β] {f g : α -> β} {s : Set α}
  proof: fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)

中文:
定理 上确界
  结论: [预序 α] [SemilatticeSup β] {f g : α -> β} {s : 集合 α}
  证明: fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)
-/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α -> β} {s : Set α}
    (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (f ⊔ g) s :=
  fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)

/-- Pointwise maximum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise minimum of two antitone functions is an antitone function. -/]
/--
theorem `max` / 定理 `max`

English:
theorem max
  statement: [Preorder α] [LinearOrder β] {f g : α -> β} {s : Set α} (hf : AntitoneOn f s)
  proof: hf.sup hg

@[to_dual]

中文:
定理 最大值
  结论: [预序 α] [线性序 β] {f g : α -> β} {s : 集合 α} (hf : AntitoneOn f s)
  证明: hf.sup hg

@[to_dual]
-/
protected theorem max [Preorder α] [LinearOrder β] {f g : α -> β} {s : Set α} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => max (f x) (g x)) s :=
  hf.sup hg

@[to_dual]
/--
theorem `of_map_inf` / 定理 `of_map_inf`

English:
theorem of_map_inf
  statement: [SemilatticeInf α] [SemilatticeSup β]
  proof: fun x hx y hy hxy =>
sup_eq_left.1 by rw [← h _ hx _ hy, inf_eq_left.2 hxy]

中文:
定理 of_map_inf
  结论: [SemilatticeInf α] [SemilatticeSup β]
  证明: fun x hx y hy hxy =>
sup_eq_left.1 by rw [← h _ hx _ hy, inf_eq_left.2 hxy]
-/
theorem of_map_inf [SemilatticeInf α] [SemilatticeSup β]
    (h : forall x in s, forall y in s, f (x ⊓ y) = f x ⊔ f y) : AntitoneOn f s := fun x hx y hy hxy =>
sup_eq_left.1 by rw [← h _ hx _ hy, inf_eq_left.2 hxy]

variable [LinearOrder α]

@[to_dual]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: [SemilatticeInf β] (hf : AntitoneOn f s) (hx : x in s) (hy : y in s)
  proof: by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right, inf_of_le_left, inf_of_le_right]

中文:
定理 map_sup
  条件: [SemilatticeInf β] (hf : AntitoneOn f s) (hx : x in s) (hy : y in s)
  证明: by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right, inf_of_le_left, inf_of_le_right]

Depends on / 依赖: inf_of_le_left, inf_of_le_right, le_total, sup_of_le_left, sup_of_le_right
-/
theorem map_sup [SemilatticeInf β] (hf : AntitoneOn f s) (hx : x in s) (hy : y in s) :
    f (x ⊔ y) = f x ⊓ f y := by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right, inf_of_le_left, inf_of_le_right]

end AntitoneOn

/-!
### Products of (semi-)lattices
-/


namespace Prod

variable (α β)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Max
  signature: α] [Max β] : Max (α × β)
  body: ⟨fun p q => ⟨p.1 ⊔ q.1, p.2 ⊔ q.2⟩⟩

@[to_dual (attr := simp)]

中文:
实例 [最大值
  签名: α] [最大值 β] : 最大值 (α × β)
  定义体: ⟨fun p q => ⟨p.1 ⊔ q.1, p.2 ⊔ q.2⟩⟩

@[to_dual (attr := simp)]
-/
instance [Max α] [Max β] : Max (α × β) :=
  ⟨fun p q => ⟨p.1 ⊔ q.1, p.2 ⊔ q.2⟩⟩

@[to_dual (attr := simp)]
/--
theorem `mk_sup_mk` / 定理 `mk_sup_mk`

English:
theorem mk_sup_mk
  given: [Max α] [Max β] (a₁ a₂ : α) (b₁ b₂ : β)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 mk_sup_mk
  条件: [最大值 α] [最大值 β] (a₁ a₂ : α) (b₁ b₂ : β)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem mk_sup_mk [Max α] [Max β] (a₁ a₂ : α) (b₁ b₂ : β) :
    (a₁, b₁) ⊔ (a₂, b₂) = (a₁ ⊔ a₂, b₁ ⊔ b₂) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `fst_sup` / 定理 `fst_sup`

English:
theorem fst_sup
  given: [Max α] [Max β] (p q : α × β)
  statement: (p ⊔ q).fst = p.fst ⊔ q.fst
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 fst_sup
  条件: [最大值 α] [最大值 β] (p q : α × β)
  结论: (p ⊔ q).fst = p.fst ⊔ q.fst
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem fst_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).fst = p.fst ⊔ q.fst :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `snd_sup` / 定理 `snd_sup`

English:
theorem snd_sup
  given: [Max α] [Max β] (p q : α × β)
  statement: (p ⊔ q).snd = p.snd ⊔ q.snd
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 snd_sup
  条件: [最大值 α] [最大值 β] (p q : α × β)
  结论: (p ⊔ q).snd = p.snd ⊔ q.snd
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem snd_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).snd = p.snd ⊔ q.snd :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `swap_sup` / 定理 `swap_sup`

English:
theorem swap_sup
  given: [Max α] [Max β] (p q : α × β)
  statement: (p ⊔ q).swap = p.swap ⊔ q.swap
  proof: rfl

@[to_dual]

中文:
定理 swap_sup
  条件: [最大值 α] [最大值 β] (p q : α × β)
  结论: (p ⊔ q).swap = p.swap ⊔ q.swap
  证明: rfl

@[to_dual]
-/
theorem swap_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).swap = p.swap ⊔ q.swap :=
  rfl

@[to_dual]
/--
theorem `sup_def` / 定理 `sup_def`

English:
theorem sup_def
  given: [Max α] [Max β] (p q : α × β)
  statement: p ⊔ q = (p.fst ⊔ q.fst, p.snd ⊔ q.snd)
  proof: rfl

@[to_dual]

中文:
定理 sup_def
  条件: [最大值 α] [最大值 β] (p q : α × β)
  结论: p ⊔ q = (p.fst ⊔ q.fst, p.snd ⊔ q.snd)
  证明: rfl

@[to_dual]
-/
theorem sup_def [Max α] [Max β] (p q : α × β) : p ⊔ q = (p.fst ⊔ q.fst, p.snd ⊔ q.snd) :=
  rfl

@[to_dual]
/--
Instance `instSemilatticeSup` / 实例 `instSemilatticeSup`

English:
instance instSemilatticeSup
  signature: [SemilatticeSup α] [SemilatticeSup β]
  body: ⟨a.1 ⊔ b.1, a.2 ⊔ b.2⟩
  sup_le _ _ _ h₁ h₂ := ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩

中文:
实例 instSemilatticeSup
  签名: [SemilatticeSup α] [SemilatticeSup β]
  定义体: ⟨a.1 ⊔ b.1, a.2 ⊔ b.2⟩
  sup_le _ _ _ h₁ h₂ := ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩
-/
instance instSemilatticeSup [SemilatticeSup α] [SemilatticeSup β] : SemilatticeSup (α × β) where
  sup a b := ⟨a.1 ⊔ b.1, a.2 ⊔ b.2⟩
  sup_le _ _ _ h₁ h₂ := ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: [Lattice α] [Lattice β]

中文:
实例 instLattice
  签名: [格 α] [格 β]
-/
instance instLattice [Lattice α] [Lattice β] : Lattice (α × β) where

/--
Instance `instDistribLattice` / 实例 `instDistribLattice`

English:
instance instDistribLattice
  signature: [DistribLattice α] [DistribLattice β]
  body: ⟨le_sup_inf, le_sup_inf⟩

中文:
实例 instDistribLattice
  签名: [Distrib格 α] [Distrib格 β]
  定义体: ⟨le_sup_inf, le_sup_inf⟩

Depends on / 依赖: le_sup_inf
-/
instance instDistribLattice [DistribLattice α] [DistribLattice β] : DistribLattice (α × β) where
  le_sup_inf _ _ _ := ⟨le_sup_inf, le_sup_inf⟩

end Prod

/-!
### Subtypes of (semi-)lattices
-/


namespace Subtype

/-- A subtype forms a `⊔`-semilattice if `⊔` preserves the property.
See note [reducible non-instances]. -/
@[to_dual (rename := Psup -> Pinf)
/-- A subtype forms a `⊓`-semilattice if `⊓` preserves the property.
See note [reducible non-instances]. -/]
/--
Definition of `semilatticeSup` / `semilatticeSup` 的定义

English:
abbreviation semilatticeSup
  signature: [SemilatticeSup α] {P : α -> Prop}
  body: ⟨x.1 ⊔ y.1, Psup x.2 y.2⟩
  le_sup_left _ _ := le_sup_left
  le_sup_right _ _ := le_sup_right
  sup_le _ _ _ h1 h2 := sup_le h1 h2

中文:
缩写 semilatticeSup
  签名: [SemilatticeSup α] {P : α -> 命题}
  定义体: ⟨x.1 ⊔ y.1, Psup x.2 y.2⟩
  le_sup_left _ _ := le_sup_left
  le_sup_right _ _ := le_sup_right
  sup_le _ _ _ h1 h2 := sup_le h1 h2
-/
protected abbrev semilatticeSup [SemilatticeSup α] {P : α -> Prop}
    (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)) :
    SemilatticeSup { x : α // P x } where
  sup x y := ⟨x.1 ⊔ y.1, Psup x.2 y.2⟩
  le_sup_left _ _ := le_sup_left
  le_sup_right _ _ := le_sup_right
  sup_le _ _ _ h1 h2 := sup_le h1 h2

/--
Definition of `lattice` / `lattice` 的定义

English:
abbreviation lattice
  signature: [Lattice α] {P : α -> Prop} (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y))
  body: Subtype.semilatticeInf Pinf
  __ := Subtype.semilatticeSup Psup

@[to_dual (attr := simp, norm_cast) (rename := Psup -> Pinf)]

中文:
缩写 lattice
  签名: [格 α] {P : α -> 命题} (Psup : 对任意 ⦃x y⦄, P x -> P y -> P (x ⊔ y))
  定义体: Subtype.semilatticeInf Pinf
  __ := Subtype.semilatticeSup Psup

@[to_dual (attr := simp, norm_cast) (rename := Psup -> Pinf)]
-/
protected abbrev lattice [Lattice α] {P : α -> Prop} (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y))
    (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) : Lattice { x : α // P x } where
  __ := Subtype.semilatticeInf Pinf
  __ := Subtype.semilatticeSup Psup

@[to_dual (attr := simp, norm_cast) (rename := Psup -> Pinf)]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  statement: [SemilatticeSup α] {P : α -> Prop}
  proof: rfl

@[to_dual (attr := simp) (rename := Psup -> Pinf)]

中文:
定理 coe_sup
  结论: [SemilatticeSup α] {P : α -> 命题}
  证明: rfl

@[to_dual (attr := simp) (rename := Psup -> Pinf)]

Depends on / 依赖: Subtype, Subtype.semilatticeSup, semilatticeSup
-/
theorem coe_sup [SemilatticeSup α] {P : α -> Prop}
    (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)) (x y : Subtype P) :
    (haveI := Subtype.semilatticeSup Psup; (x ⊔ y : Subtype P) : α) = (x ⊔ y : α) :=
  rfl

@[to_dual (attr := simp) (rename := Psup -> Pinf)]
/--
theorem `mk_sup_mk` / 定理 `mk_sup_mk`

English:
theorem mk_sup_mk
  statement: [SemilatticeSup α] {P : α -> Prop}
  proof: rfl

中文:
定理 mk_sup_mk
  结论: [SemilatticeSup α] {P : α -> 命题}
  证明: rfl

Depends on / 依赖: Subtype, Subtype.semilatticeSup, semilatticeSup
-/
theorem mk_sup_mk [SemilatticeSup α] {P : α -> Prop}
    (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)) {x y : α} (hx : P x) (hy : P y) :
    (haveI := Subtype.semilatticeSup Psup; (⟨x, hx⟩ ⊔ ⟨y, hy⟩ : Subtype P)) =
      ⟨x ⊔ y, Psup hx hy⟩ :=
  rfl

end Subtype

section lift

/-- A type endowed with `⊔` is a `SemilatticeSup`, if it admits an injective map that
preserves `⊔` to a `SemilatticeSup`.
See note [reducible non-instances]. -/
@[to_dual /-- A type endowed with `⊓` is a `SemilatticeInf`, if it admits an injective map that
preserves `⊓` to a `SemilatticeInf`.
See note [reducible non-instances]. -/]
/--
Definition of `Function.Injective.semilatticeSup` / `Function.Injective.semilatticeSup` 的定义

English:
abbreviation Function.Injective.semilatticeSup
  signature: [Max α] [LE α] [LT α] [SemilatticeSup β]
  body: hf_inj.partialOrder f le lt
  sup a b := max a b
  le_sup_left a b := by
    rw [← le]; rw [map_sup]
    exact le_sup_left
  le_sup_right a b := by
    rw [← le]; rw [map_sup]
    exact le_sup_right
  sup_le a b c ha hb := by
    rw [← le] at *
    rw [map_sup]
    exact sup_le ha hb

中文:
缩写 函数.单射.semilatticeSup
  签名: [最大值 α] [LE α] [LT α] [SemilatticeSup β]
  定义体: hf_inj.partialOrder f le lt
  sup a b := max a b
  le_sup_left a b := by
    rw [← le]; rw [map_sup]
    exact le_sup_left
  le_sup_right a b := by
    rw [← le]; rw [map_sup]
    exact le_sup_right
  sup_le a b c ha hb := by
    rw [← le] at *
    rw [map_sup]
    exact sup_le ha hb
-/
protected abbrev Function.Injective.semilatticeSup [Max α] [LE α] [LT α] [SemilatticeSup β]
    (f : α -> β) (hf_inj : Function.Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) :
    SemilatticeSup α where
  __ := hf_inj.partialOrder f le lt
  sup a b := max a b
  le_sup_left a b := by
    rw [← le]; rw [map_sup]
    exact le_sup_left
  le_sup_right a b := by
    rw [← le]; rw [map_sup]
    exact le_sup_right
  sup_le a b c ha hb := by
    rw [← le] at *
    rw [map_sup]
    exact sup_le ha hb

/-- A type endowed with `⊔` and `⊓` is a `Lattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `Lattice`.
See note [reducible non-instances]. -/
@[to_dual self (reorder := 3 4, le (x y), lt (x y), map_inf map_sup)]
/--
Definition of `Function.Injective.lattice` / `Function.Injective.lattice` 的定义

English:
abbreviation Function.Injective.lattice
  signature: [Max α] [Min α] [LE α] [LT α] [Lattice β]
  body: hf_inj.semilatticeSup f le lt map_sup
  __ := hf_inj.semilatticeInf f le lt map_inf

中文:
缩写 函数.单射.lattice
  签名: [最大值 α] [最小值 α] [LE α] [LT α] [格 β]
  定义体: hf_inj.semilatticeSup f le lt map_sup
  __ := hf_inj.semilatticeInf f le lt map_inf
-/
protected abbrev Function.Injective.lattice [Max α] [Min α] [LE α] [LT α] [Lattice β]
    (f : α -> β) (hf_inj : Function.Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b) :
    Lattice α where
  __ := hf_inj.semilatticeSup f le lt map_sup
  __ := hf_inj.semilatticeInf f le lt map_inf

/-- A type endowed with `⊔` and `⊓` is a `DistribLattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `DistribLattice`.
See note [reducible non-instances]. -/
@[to_dual self (reorder := 3 4, le (x y), lt (x y), map_inf map_sup)]
/--
Definition of `Function.Injective.distribLattice` / `Function.Injective.distribLattice` 的定义

English:
abbreviation Function.Injective.distribLattice
  signature: [Max α] [Min α] [LE α] [LT α] [DistribLattice β]
  body: hf_inj.lattice f le lt map_sup map_inf
  le_sup_inf a b c := by
    rw [← le]; rw [map_inf]; rw [map_sup]; rw [map_sup]; rw [map_sup]; rw [map_inf]
    exact le_sup_inf

中文:
缩写 函数.单射.distribLattice
  签名: [最大值 α] [最小值 α] [LE α] [LT α] [Distrib格 β]
  定义体: hf_inj.lattice f le lt map_sup map_inf
  le_sup_inf a b c := by
    rw [← le]; rw [map_inf]; rw [map_sup]; rw [map_sup]; rw [map_sup]; rw [map_inf]
    exact le_sup_inf
-/
protected abbrev Function.Injective.distribLattice [Max α] [Min α] [LE α] [LT α] [DistribLattice β]
    (f : α -> β) (hf_inj : Function.Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b) :
    DistribLattice α where
  __ := hf_inj.lattice f le lt map_sup map_inf
  le_sup_inf a b c := by
    rw [← le]; rw [map_inf]; rw [map_sup]; rw [map_sup]; rw [map_sup]; rw [map_inf]
    exact le_sup_inf

/--
Definition of `Subtype.distribLattice` / `Subtype.distribLattice` 的定义

English:
abbreviation Subtype.distribLattice
  signature: [DistribLattice α] {P : α -> Prop}
  body: letI := Subtype.lattice Psup Pinf
  Subtype.coe_injective.distribLattice _ coe_le_coe coe_lt_coe (coe_sup Psup) (coe_inf Pinf)

中文:
缩写 子类型.distribLattice
  签名: [Distrib格 α] {P : α -> 命题}
  定义体: letI := Subtype.lattice Psup Pinf
  Subtype.coe_injective.distribLattice _ coe_le_coe coe_lt_coe (coe_sup Psup) (coe_inf Pinf)
-/
protected abbrev Subtype.distribLattice [DistribLattice α] {P : α -> Prop}
    (Psup : forall ⦃s t : α⦄, P s -> P t -> P (s ⊔ t)) (Pinf : forall ⦃s t : α⦄, P s -> P t -> P (s ⊓ t)) :
    DistribLattice (Subtype P) :=
  letI := Subtype.lattice Psup Pinf
  Subtype.coe_injective.distribLattice _ coe_le_coe coe_lt_coe (coe_sup Psup) (coe_inf Pinf)

namespace Equiv

variable (e : α ≃ β)

/--
Definition of `preorder` / `preorder` 的定义

English:
abbreviation preorder
  signature: [Preorder β]
  body: by
  let le := e.le
  let lt := e.lt
  apply Function.Injective.preorder e <;> intros <;> rfl

中文:
缩写 preorder
  签名: [预序 β]
  定义体: by
  let le := e.le
  let lt := e.lt
  apply Function.Injective.preorder e <;> intros <;> rfl
-/
protected abbrev preorder [Preorder β] : Preorder α := by
  let le := e.le
  let lt := e.lt
  apply Function.Injective.preorder e <;> intros <;> rfl

/--
Definition of `partialOrder` / `partialOrder` 的定义

English:
abbreviation partialOrder
  signature: [PartialOrder β]
  body: by
  let preorder := e.preorder
  apply e.injective.partialOrder <;> intros <;> rfl

中文:
缩写 partialOrder
  签名: [偏序 β]
  定义体: by
  let preorder := e.preorder
  apply e.injective.partialOrder <;> intros <;> rfl
-/
protected abbrev partialOrder [PartialOrder β] : PartialOrder α := by
  let preorder := e.preorder
  apply e.injective.partialOrder <;> intros <;> rfl

/--
Definition of `linearOrder` / `linearOrder` 的定义

English:
abbreviation linearOrder
  signature: [LinearOrder β] [DecidableEq α]
  body: by
  let max := e.max
  let min := e.min
  let preorder := e.preorder
  let compare := e.ord
  apply e.injective.linearOrder <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 linearOrder
  签名: [线性序 β] [DecidableEq α]
  定义体: by
  let max := e.max
  let min := e.min
  let preorder := e.preorder
  let compare := e.ord
  apply e.injective.linearOrder <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev linearOrder [LinearOrder β] [DecidableEq α] : LinearOrder α := by
  let max := e.max
  let min := e.min
  let preorder := e.preorder
  let compare := e.ord
  apply e.injective.linearOrder <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `semilatticeSup` / `semilatticeSup` 的定义

English:
abbreviation semilatticeSup
  signature: [SemilatticeSup β]
  body: by
  let max := e.max
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeSup <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 semilatticeSup
  签名: [SemilatticeSup β]
  定义体: by
  let max := e.max
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeSup <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev semilatticeSup [SemilatticeSup β] : SemilatticeSup α := by
  let max := e.max
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeSup <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `semilatticeInf` / `semilatticeInf` 的定义

English:
abbreviation semilatticeInf
  signature: [SemilatticeInf β]
  body: by
  let min := e.min
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeInf <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 semilatticeInf
  签名: [SemilatticeInf β]
  定义体: by
  let min := e.min
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeInf <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev semilatticeInf [SemilatticeInf β] : SemilatticeInf α := by
  let min := e.min
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeInf <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `lattice` / `lattice` 的定义

English:
abbreviation lattice
  signature: [Lattice β]
  body: by
  let semilatticeSup := e.semilatticeSup
  let semilatticeInf := e.semilatticeInf
  apply e.injective.lattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 lattice
  签名: [格 β]
  定义体: by
  let semilatticeSup := e.semilatticeSup
  let semilatticeInf := e.semilatticeInf
  apply e.injective.lattice <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev lattice [Lattice β] : Lattice α := by
  let semilatticeSup := e.semilatticeSup
  let semilatticeInf := e.semilatticeInf
  apply e.injective.lattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `distribLattice` / `distribLattice` 的定义

English:
abbreviation distribLattice
  signature: [DistribLattice β]
  body: by
  let lattice := e.lattice
  apply e.injective.distribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 distribLattice
  签名: [Distrib格 β]
  定义体: by
  let lattice := e.lattice
  apply e.injective.distribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev distribLattice [DistribLattice β] : DistribLattice α := by
  let lattice := e.lattice
  apply e.injective.distribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv

end lift

namespace ULift

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemilatticeSup
  signature: α] : SemilatticeSup (ULift.{v} α)
  body: ULift.down_injective.semilatticeSup _ .rfl .rfl down_sup

中文:
实例 [SemilatticeSup
  签名: α] : SemilatticeSup (类型层提升.{v} α)
  定义体: ULift.down_injective.semilatticeSup _ .rfl .rfl down_sup

Depends on / 依赖: ULift.down_injective.semilatticeSup, down_injective, down_sup, semilatticeSup
-/
instance [SemilatticeSup α] : SemilatticeSup (ULift.{v} α) :=
  ULift.down_injective.semilatticeSup _ .rfl .rfl down_sup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Lattice
  signature: α] : Lattice (ULift.{v} α) where

中文:
实例 [格
  签名: α] : 格 (类型层提升.{v} α) where
-/
instance [Lattice α] : Lattice (ULift.{v} α) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribLattice
  signature: α] : DistribLattice (ULift.{v} α)
  body: ULift.down_injective.distribLattice _ .rfl .rfl down_sup down_inf

中文:
实例 [Distrib格
  签名: α] : Distrib格 (类型层提升.{v} α)
  定义体: ULift.down_injective.distribLattice _ .rfl .rfl down_sup down_inf

Depends on / 依赖: ULift.down_injective.distribLattice, distribLattice, down_inf, down_injective, down_sup
-/
instance [DistribLattice α] : DistribLattice (ULift.{v} α) :=
  ULift.down_injective.distribLattice _ .rfl .rfl down_sup down_inf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: α] : LinearOrder (ULift.{v} α)
  body: ULift.down_injective.linearOrder _ down_le down_lt down_inf down_sup down_compare

中文:
实例 [线性序
  签名: α] : 线性序 (类型层提升.{v} α)
  定义体: ULift.down_injective.linearOrder _ down_le down_lt down_inf down_sup down_compare

Depends on / 依赖: ULift.down_injective.linearOrder, down_compare, down_inf, down_injective, down_le, down_lt, down_sup, linearOrder
-/
instance [LinearOrder α] : LinearOrder (ULift.{v} α) :=
  ULift.down_injective.linearOrder _ down_le down_lt down_inf down_sup down_compare

end ULift

--To avoid noncomputability poisoning from `Bool.completeBooleanAlgebra`
/--
Instance `Bool.instPartialOrder` / 实例 `Bool.instPartialOrder`

English:
instance Bool.instPartialOrder
  signature: : PartialOrder Bool
  body: inferInstance

中文:
实例 布尔值.instPartialOrder
  签名: : 偏序 布尔值
  定义体: inferInstance
-/
instance Bool.instPartialOrder : PartialOrder Bool := inferInstance
/--
Instance `Bool.instDistribLattice` / 实例 `Bool.instDistribLattice`

English:
instance Bool.instDistribLattice
  signature: : DistribLattice Bool
  body: inferInstance

中文:
实例 布尔值.instDistribLattice
  签名: : Distrib格 布尔值
  定义体: inferInstance
-/
instance Bool.instDistribLattice : DistribLattice Bool := inferInstance

variable [LinearOrder α] {p : α -> α -> Prop}

/--
lemma `pairwise_iff_lt` / 引理 `pairwise_iff_lt`

English:
lemma pairwise_iff_lt
  given: [Std.Symm p]
  statement: Pairwise p ↔ forall ⦃a b⦄, a < b -> p a b
  proof: by
simpa [Pairwise, ← lt_or_lt_iff_ne, or_imp, forall_and] using fun h a b hab => symm h _ _ hab

中文:
引理 pairwise_iff_lt
  条件: [Std.Symm p]
  结论: 两两 p ↔ 对任意 ⦃a b⦄, a < b -> p a b
  证明: by
simpa [Pairwise, ← lt_or_lt_iff_ne, or_imp, forall_and] using fun h a b hab => symm h _ _ hab

Depends on / 依赖: Pairwise, forall_and, lt_or_lt_iff_ne, or_imp
-/
lemma pairwise_iff_lt [Std.Symm p] : Pairwise p ↔ forall ⦃a b⦄, a < b -> p a b := by
simpa [Pairwise, ← lt_or_lt_iff_ne, or_imp, forall_and] using fun h a b hab => symm h _ _ hab

/--
lemma `pairwise_iff_gt` / 引理 `pairwise_iff_gt`

English:
lemma pairwise_iff_gt
  given: [Std.Symm p]
  statement: Pairwise p ↔ forall ⦃a b⦄, b < a -> p a b
  proof: by
simpa [Pairwise, ← lt_or_lt_iff_ne, or_imp, forall_and] using fun h a b hab => symm h _ _ hab

alias ⟨_, Pairwise.of_lt⟩ := pairwise_iff_lt
alias ⟨_, Pairwise.of_gt⟩ := pairwise_iff_gt

中文:
引理 pairwise_iff_gt
  条件: [Std.Symm p]
  结论: 两两 p ↔ 对任意 ⦃a b⦄, b < a -> p a b
  证明: by
simpa [Pairwise, ← lt_or_lt_iff_ne, or_imp, forall_and] using fun h a b hab => symm h _ _ hab

alias ⟨_, Pairwise.of_lt⟩ := pairwise_iff_lt
alias ⟨_, Pairwise.of_gt⟩ := pairwise_iff_gt

Depends on / 依赖: Pairwise, forall_and, lt_or_lt_iff_ne, or_imp
-/
lemma pairwise_iff_gt [Std.Symm p] : Pairwise p ↔ forall ⦃a b⦄, b < a -> p a b := by
simpa [Pairwise, ← lt_or_lt_iff_ne, or_imp, forall_and] using fun h a b hab => symm h _ _ hab

alias ⟨_, Pairwise.of_lt⟩ := pairwise_iff_lt
alias ⟨_, Pairwise.of_gt⟩ := pairwise_iff_gt
