/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Tactic.Abel

/-!

# Ideals over a ring

This file defines `Ideal R`, the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

@[expose] public section


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open scoped Pointwise

/--
Definition of `Ideal` / `Ideal` 的定义

English:
abbreviation Ideal
  signature: (R : Type u) [Semiring R]
  body: Submodule R R

中文:
缩写 Ideal
  签名: (R : 类型u) [Semiring R]
  定义体: Submodule R R

Depends on / 依赖: Submodule
-/
abbrev Ideal (R : Type u) [Semiring R] :=
  Submodule R R

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/--
Definition of `IsTwoSided` / `IsTwoSided` 的定义

English:
class IsTwoSided
  parameters: : Prop where
  axioms and operations (1):
    - mul_mem_of_left({a : α} (b : α)) : a in I -> a * b in I

中文:
类 IsTwoSided
  参数: : 命题 where
  公理与运算 (1 个):
    - mul_mem_of_left({a : α} (b : α)) : a in I -> a * b in I
-/
@[mk_iff] class IsTwoSided : Prop where
  mul_mem_of_left {a : α} (b : α) : a in I -> a * b in I

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : α) in I
  proof: Submodule.zero_mem I

中文:
定理 zero_mem
  结论: (0 : α) in I
  证明: Submodule.zero_mem I
-/
protected theorem zero_mem : (0 : α) in I :=
  Submodule.zero_mem I

/--
theorem `add_mem` / 定理 `add_mem`

English:
theorem add_mem
  statement: a in I -> b in I -> a + b in I
  proof: Submodule.add_mem I

中文:
定理 add_mem
  结论: a in I -> b in I -> a + b in I
  证明: Submodule.add_mem I
-/
protected theorem add_mem : a in I -> b in I -> a + b in I :=
  Submodule.add_mem I

variable (a)

/--
theorem `mul_mem_left` / 定理 `mul_mem_left`

English:
theorem mul_mem_left
  statement: b in I -> a * b in I
  proof: Submodule.smul_mem I a

中文:
定理 mul_mem_left
  结论: b in I -> a * b in I
  证明: Submodule.smul_mem I a

Depends on / 依赖: Submodule, Submodule.smul_mem, smul_mem
-/
theorem mul_mem_left : b in I -> a * b in I :=
  Submodule.smul_mem I a

/--
theorem `mul_mem_right` / 定理 `mul_mem_right`

English:
theorem mul_mem_right
  statement: {α} {a : α} (b : α) [Semiring α] (I : Ideal α) [I.IsTwoSided]
  proof: IsTwoSided.mul_mem_of_left b h

中文:
定理 mul_mem_right
  结论: {α} {a : α} (b : α) [Semiring α] (I : Ideal α) [I.IsTwoSided]
  证明: IsTwoSided.mul_mem_of_left b h

Depends on / 依赖: IsTwoSided, IsTwoSided.mul_mem_of_left, mul_mem_of_left
-/
theorem mul_mem_right {α} {a : α} (b : α) [Semiring α] (I : Ideal α) [I.IsTwoSided]
    (h : a in I) : a * b in I :=
  IsTwoSided.mul_mem_of_left b h

variable {a}

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {I J : Ideal α} (h : forall x, x in I ↔ x in J)
  statement: I = J
  proof: Submodule.ext h

@[simp]

中文:
定理 ext
  条件: {I J : Ideal α} (h : 对任意 x, x in I ↔ x in J)
  结论: I = J
  证明: Submodule.ext h

@[simp]

Depends on / 依赖: Submodule, Submodule.ext
-/
theorem ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J :=
  Submodule.ext h

@[simp]
/--
theorem `unit_mul_mem_iff_mem` / 定理 `unit_mul_mem_iff_mem`

English:
theorem unit_mul_mem_iff_mem
  given: {x y : α} (hy : IsUnit y)
  statement: y * x in I ↔ x in I
  proof: by
  refine ⟨fun h => ?_, fun h => I.mul_mem_left y h⟩
  obtain ⟨y', hy'⟩ := hy.exists_left_inv
  have := I.mul_mem_left y' h
  rwa [← mul_assoc, hy', one_mul] at this

中文:
定理 unit_mul_mem_iff_mem
  条件: {x y : α} (hy : IsUnit y)
  结论: y * x in I ↔ x in I
  证明: by
  refine ⟨fun h => ?_, fun h => I.mul_mem_left y h⟩
  obtain ⟨y', hy'⟩ := hy.exists_left_inv
  have := I.mul_mem_left y' h
  rwa [← mul_assoc, hy', one_mul] at this

Depends on / 依赖: I.mul_mem_left, exists_left_inv, hy.exists_left_inv, mul_assoc, mul_mem_left, one_mul
-/
theorem unit_mul_mem_iff_mem {x y : α} (hy : IsUnit y) : y * x in I ↔ x in I := by
  refine ⟨fun h => ?_, fun h => I.mul_mem_left y h⟩
  obtain ⟨y', hy'⟩ := hy.exists_left_inv
  have := I.mul_mem_left y' h
  rwa [← mul_assoc, hy', one_mul] at this

/--
theorem `pow_mem_of_mem` / 定理 `pow_mem_of_mem`

English:
theorem pow_mem_of_mem
  given: (ha : a in I) (n : Nat) (hn : 0 < n)
  statement: a ^ n in I
  proof: Nat.casesOn n (Not.elim (by decide))
    (fun m _hm => (pow_succ a m).symm ▸ I.mul_mem_left (a ^ m) ha) hn

中文:
定理 pow_mem_of_mem
  条件: (ha : a in I) (n : 自然数) (hn : 0 < n)
  结论: a ^ n in I
  证明: Nat.casesOn n (Not.elim (by decide))
    (fun m _hm => (pow_succ a m).symm ▸ I.mul_mem_left (a ^ m) ha) hn

Depends on / 依赖: I.mul_mem_left, Nat.casesOn, Not.elim, casesOn, mul_mem_left, pow_succ
-/
theorem pow_mem_of_mem (ha : a in I) (n : Nat) (hn : 0 < n) : a ^ n in I :=
  Nat.casesOn n (Not.elim (by decide))
    (fun m _hm => (pow_succ a m).symm ▸ I.mul_mem_left (a ^ m) ha) hn

/--
theorem `pow_mem_of_pow_mem` / 定理 `pow_mem_of_pow_mem`

English:
theorem pow_mem_of_pow_mem
  given: {m n : Nat} (ha : a ^ m in I) (h : m <= n)
  statement: a ^ n in I
  proof: by
  rw [← Nat.add_sub_of_le h]; rw [add_comm]; rw [pow_add]
  exact I.mul_mem_left _ ha

中文:
定理 pow_mem_of_pow_mem
  条件: {m n : 自然数} (ha : a ^ m in I) (h : m <= n)
  结论: a ^ n in I
  证明: by
  rw [← Nat.add_sub_of_le h]; rw [add_comm]; rw [pow_add]
  exact I.mul_mem_left _ ha

Depends on / 依赖: I.mul_mem_left, Nat.add_sub_of_le, add_comm, add_sub_of_le, mul_mem_left, pow_add
-/
theorem pow_mem_of_pow_mem {m n : Nat} (ha : a ^ m in I) (h : m <= n) : a ^ n in I := by
  rw [← Nat.add_sub_of_le h]; rw [add_comm]; rw [pow_add]
  exact I.mul_mem_left _ ha

end Ideal

/--
Definition of `Module.eqIdeal` / `Module.eqIdeal` 的定义

English:
definition Module.eqIdeal
  signature: (R) {M} [Semiring R] [AddCommMonoid M] [Module R M] (m m' : M)
  body: {r : R | r • m = r • m'}
  add_mem' h h' := by simpa [add_smul] using congr($h + $h')
  zero_mem' := by simp_rw [Set.mem_ofPred, zero_smul]
  smul_mem' _ _ h := by simpa [mul_smul] using congr(_ • $h)

中文:
定义 Module.eqIdeal
  签名: (R) {M} [Semiring R] [AddCommMonoid M] [Module R M] (m m' : M)
  定义体: {r : R | r • m = r • m'}
  add_mem' h h' := by simpa [add_smul] using congr($h + $h')
  zero_mem' := by simp_rw [Set.mem_ofPred, zero_smul]
  smul_mem' _ _ h := by simpa [mul_smul] using congr(_ • $h)
-/
def Module.eqIdeal (R) {M} [Semiring R] [AddCommMonoid M] [Module R M] (m m' : M) : Ideal R where
  carrier := {r : R | r • m = r • m'}
  add_mem' h h' := by simpa [add_smul] using congr($h + $h')
  zero_mem' := by simp_rw [Set.mem_ofPred, zero_smul]
  smul_mem' _ _ h := by simpa [mul_smul] using congr(_ • $h)

end Semiring

section CommSemiring

variable {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace Ideal

variable [CommSemiring α] (I : Ideal α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: I.IsTwoSided
  body: ⟨fun b ha => mul_comm b _ ▸ I.smul_mem _ ha⟩

中文:
实例 :
  签名: I.IsTwoSided
  定义体: ⟨fun b ha => mul_comm b _ ▸ I.smul_mem _ ha⟩

Depends on / 依赖: I.smul_mem, mul_comm, smul_mem
-/
instance : I.IsTwoSided := ⟨fun b ha => mul_comm b _ ▸ I.smul_mem _ ha⟩
instance {α} [CommRing α] (I : Ideal α) : I.IsTwoSided := inferInstance

@[simp]
/--
theorem `mul_unit_mem_iff_mem` / 定理 `mul_unit_mem_iff_mem`

English:
theorem mul_unit_mem_iff_mem
  given: {x y : α} (hy : IsUnit y)
  statement: x * y in I ↔ x in I
  proof: mul_comm y x ▸ unit_mul_mem_iff_mem I hy

中文:
定理 mul_unit_mem_iff_mem
  条件: {x y : α} (hy : IsUnit y)
  结论: x * y in I ↔ x in I
  证明: mul_comm y x ▸ unit_mul_mem_iff_mem I hy

Depends on / 依赖: mul_comm, unit_mul_mem_iff_mem
-/
theorem mul_unit_mem_iff_mem {x y : α} (hy : IsUnit y) : x * y in I ↔ x in I :=
  mul_comm y x ▸ unit_mul_mem_iff_mem I hy

/--
lemma `mem_of_dvd` / 引理 `mem_of_dvd`

English:
lemma mem_of_dvd
  given: (hab : a ∣ b) (ha : a in I)
  statement: b in I
  proof: by
  obtain ⟨c, rfl⟩ := hab; exact I.mul_mem_right _ ha

中文:
引理 mem_of_dvd
  条件: (hab : a ∣ b) (ha : a in I)
  结论: b in I
  证明: by
  obtain ⟨c, rfl⟩ := hab; exact I.mul_mem_right _ ha

Depends on / 依赖: I.mul_mem_right, mul_mem_right
-/
lemma mem_of_dvd (hab : a ∣ b) (ha : a in I) : b in I := by
  obtain ⟨c, rfl⟩ := hab; exact I.mul_mem_right _ ha

end Ideal

end CommSemiring

section Ring

namespace Ideal

variable [Ring α] (I : Ideal α) {a b c d : α}

/--
theorem `neg_mem_iff` / 定理 `neg_mem_iff`

English:
theorem neg_mem_iff
  statement: -a in I ↔ a in I
  proof: Submodule.neg_mem_iff I

中文:
定理 neg_mem_iff
  结论: -a in I ↔ a in I
  证明: Submodule.neg_mem_iff I
-/
protected theorem neg_mem_iff : -a in I ↔ a in I :=
  Submodule.neg_mem_iff I

/--
theorem `add_mem_iff_left` / 定理 `add_mem_iff_left`

English:
theorem add_mem_iff_left
  statement: b in I -> (a + b in I ↔ a in I)
  proof: Submodule.add_mem_iff_left I

中文:
定理 add_mem_iff_left
  结论: b in I -> (a + b in I ↔ a in I)
  证明: Submodule.add_mem_iff_left I
-/
protected theorem add_mem_iff_left : b in I -> (a + b in I ↔ a in I) :=
  Submodule.add_mem_iff_left I

/--
theorem `add_mem_iff_right` / 定理 `add_mem_iff_right`

English:
theorem add_mem_iff_right
  statement: a in I -> (a + b in I ↔ b in I)
  proof: Submodule.add_mem_iff_right I

中文:
定理 add_mem_iff_right
  结论: a in I -> (a + b in I ↔ b in I)
  证明: Submodule.add_mem_iff_right I
-/
protected theorem add_mem_iff_right : a in I -> (a + b in I ↔ b in I) :=
  Submodule.add_mem_iff_right I

/--
theorem `sub_mem` / 定理 `sub_mem`

English:
theorem sub_mem
  statement: a in I -> b in I -> a - b in I
  proof: Submodule.sub_mem I

中文:
定理 sub_mem
  结论: a in I -> b in I -> a - b in I
  证明: Submodule.sub_mem I
-/
protected theorem sub_mem : a in I -> b in I -> a - b in I :=
  Submodule.sub_mem I

/--
theorem `mul_sub_mul_mem` / 定理 `mul_sub_mul_mem`

English:
theorem mul_sub_mul_mem
  statement: [I.IsTwoSided]
  proof: by
  rw [show a * c - b * d = (a - b) * c + b * (c - d) by rw [sub_mul]; rw [mul_sub]; abel]
  exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)

中文:
定理 mul_sub_mul_mem
  结论: [I.IsTwoSided]
  证明: by
  rw [show a * c - b * d = (a - b) * c + b * (c - d) by rw [sub_mul]; rw [mul_sub]; abel]
  exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)

Depends on / 依赖: I.add_mem, I.mul_mem_left, I.mul_mem_right, add_mem, mul_mem_left, mul_mem_right, mul_sub, sub_mul
-/
theorem mul_sub_mul_mem [I.IsTwoSided]
    (h1 : a - b in I) (h2 : c - d in I) : a * c - b * d in I := by
  rw [show a * c - b * d = (a - b) * c + b * (c - d) by rw [sub_mul]; rw [mul_sub]; abel]
  exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)

section inertia

variable (G : Type*) [Group G] [MulAction G α] (I : Ideal α)

/--
Definition of `inertia` / `inertia` 的定义

English:
abbreviation inertia
  signature: : Subgroup G
  body: I.toAddSubgroup.inertia G

中文:
缩写 inertia
  签名: : Subgroup G
  定义体: I.toAddSubgroup.inertia G

Depends on / 依赖: I.toAddSubgroup.inertia, inertia, toAddSubgroup
-/
abbrev inertia : Subgroup G := I.toAddSubgroup.inertia G

variable {I G} in
/--
theorem `coe_mem_inertia` / 定理 `coe_mem_inertia`

English:
theorem coe_mem_inertia
  given: {H : Subgroup G} {σ : H}
  statement: ↑σ in I.inertia G ↔ σ in I.inertia H
  proof: I.toAddSubgroup.coe_mem_inertia

中文:
定理 coe_mem_inertia
  条件: {H : Subgroup G} {σ : H}
  结论: ↑σ in I.inertia G ↔ σ in I.inertia H
  证明: I.toAddSubgroup.coe_mem_inertia

Depends on / 依赖: I.toAddSubgroup.coe_mem_inertia, coe_mem_inertia, toAddSubgroup
-/
theorem coe_mem_inertia {H : Subgroup G} {σ : H} : ↑σ in I.inertia G ↔ σ in I.inertia H :=
  I.toAddSubgroup.coe_mem_inertia

end inertia

end Ideal

end Ring
