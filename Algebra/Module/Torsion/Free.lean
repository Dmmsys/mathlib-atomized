/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Regular.Opposite
public import Mathlib.Algebra.Regular.SMul

/-!
# Torsion-free modules

This files defines a torsion-free `R`-(semi)module `M` as a (semi)module where scalar multiplication
by a regular element `r : R` is injective as a map `M → M`.

In the case of a module (group over a ring), this is equivalent to saying that `r • m = 0` for
some `r : R`, `m : M` implies that `r` is a zero-divisor.
If furthermore the base ring is a domain, this is equivalent to the naïve
`r • m = 0 ↔ r = 0 ∨ m = 0` definition.
-/

public section

open Module

variable {R S M N : Type*}

section Semiring
variable [Semiring R] [Semiring S]

section AddCommMonoid
variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

variable (R M) in
/--
Definition of `Module.IsTorsionFree` / `Module.IsTorsionFree` 的定义

English:
class Module.IsTorsionFree
  parameters: where
  axioms and operations (1):
    - isSMulRegular(⦃r) : R⦄ : IsRegular r -> IsSMulRegular M r

中文:
类 模.是无挠
  参数: where
  公理与运算 (1 个):
    - isSMulRegular(⦃r) : R⦄ : 是正则 r -> IsSMulRegular M r

Depends on / 依赖: IsTorsionFree, IsTorsionFree.isSMulRegular, isSMulRegular
-/
class Module.IsTorsionFree where
  isSMulRegular ⦃r : R⦄ : IsRegular r -> IsSMulRegular M r

alias IsRegular.isSMulRegular := IsTorsionFree.isSMulRegular

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTorsionFree R R
  body: hr.1

中文:
实例 :
  签名: 是无挠 R R
  定义体: hr.1
-/
instance : IsTorsionFree R R where isSMulRegular _r hr := hr.1
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTorsionFree Rᵐᵒᵖ R
  body: hr.unop.2

中文:
实例 :
  签名: 是无挠 Rᵐᵒᵖ R
  定义体: hr.unop.2

Depends on / 依赖: hr.unop
-/
instance : IsTorsionFree Rᵐᵒᵖ R where isSMulRegular _r hr := hr.unop.2

/--
lemma `Function.Injective.moduleIsTorsionFree` / 引理 `Function.Injective.moduleIsTorsionFree`

English:
lemma Function.Injective.moduleIsTorsionFree
  statement: [IsTorsionFree R N] (f : M -> N) (hf : f.Injective)
  proof: hf hr.isSMulRegular by simpa [smul] using congr(f $hm)

中文:
引理 函数.单射.moduleIsTorsionFree
  结论: [是无挠 R N] (f : M -> N) (hf : f.单射)
  证明: hf hr.isSMulRegular by simpa [smul] using congr(f $hm)

Depends on / 依赖: hr.isSMulRegular, isSMulRegular
-/
lemma Function.Injective.moduleIsTorsionFree [IsTorsionFree R N] (f : M -> N) (hf : f.Injective)
    (smul : forall (r : R) (m : M), f (r • m) = r • f m) : IsTorsionFree R M where
isSMulRegular r hr m₁ m₂ hm := hf hr.isSMulRegular by simpa [smul] using congr(f $hm)

/--
lemma `Module.IsTorsionFree.comap` / 引理 `Module.IsTorsionFree.comap`

English:
lemma Module.IsTorsionFree.comap
  statement: [IsTorsionFree S M] (f : R -> S)
  proof: (isRegular _ hr).isSMulRegular.of_map f (smul r)

中文:
引理 模.是无挠.comap
  结论: [是无挠 S M] (f : R -> S)
  证明: (isRegular _ hr).isSMulRegular.of_map f (smul r)

Depends on / 依赖: isRegular, isSMulRegular, isSMulRegular.of_map, of_map
-/
lemma Module.IsTorsionFree.comap [IsTorsionFree S M] (f : R -> S)
    (isRegular : forall r, IsRegular r -> IsRegular (f r)) (smul : forall (r : R) (m : M), f r • m = r • m) :
    IsTorsionFree R M where
  isSMulRegular r hr := (isRegular _ hr).isSMulRegular.of_map f (smul r)

/--
Instance `IsAddTorsionFree.to_isTorsionFree_nat` / 实例 `IsAddTorsionFree.to_isTorsionFree_nat`

English:
instance IsAddTorsionFree.to_isTorsionFree_nat
  signature: [IsAddTorsionFree M]
  body: nsmul_right_injective (by simpa [isRegular_iff_ne_zero] using hn)

中文:
实例 是加法无挠.to_isTorsionFree_nat
  签名: [是加法无挠 M]
  定义体: nsmul_right_injective (by simpa [isRegular_iff_ne_zero] using hn)

Depends on / 依赖: isRegular_iff_ne_zero, nsmul_right_injective
-/
instance IsAddTorsionFree.to_isTorsionFree_nat [IsAddTorsionFree M] : IsTorsionFree Nat M where
  isSMulRegular n hn := nsmul_right_injective (by simpa [isRegular_iff_ne_zero] using hn)

/--
Instance `Subsingleton.to_moduleIsTorsionFree` / 实例 `Subsingleton.to_moduleIsTorsionFree`

English:
instance Subsingleton.to_moduleIsTorsionFree
  signature: [Subsingleton M]
  body: Function.injective_of_subsingleton _

中文:
实例 子单例.to_moduleIsTorsionFree
  签名: [子单例 M]
  定义体: Function.injective_of_subsingleton _

Depends on / 依赖: Function, Function.injective_of_subsingleton, injective_of_subsingleton
-/
instance Subsingleton.to_moduleIsTorsionFree [Subsingleton M] : IsTorsionFree R M where
  isSMulRegular _ _ := Function.injective_of_subsingleton _

variable [IsTorsionFree R M]

variable (M) in
/--
lemma `IsRegular.smul_right_injective` / 引理 `IsRegular.smul_right_injective`

English:
lemma IsRegular.smul_right_injective
  given: (hr : IsRegular r)
  statement: ((r • ·) : M -> M).Injective
  proof: hr.isSMulRegular

中文:
引理 是正则.smul_right_injective
  条件: (hr : 是正则 r)
  结论: ((r • ·) : M -> M).单射
  证明: hr.isSMulRegular
-/
protected lemma IsRegular.smul_right_injective (hr : IsRegular r) : ((r • ·) : M -> M).Injective :=
  hr.isSMulRegular

/--
lemma `IsRegular.smul_right_inj` / 引理 `IsRegular.smul_right_inj`

English:
lemma IsRegular.smul_right_inj
  given: (hr : IsRegular r)
  statement: r • m₁ = r • m₂ ↔ m₁ = m₂
  proof: (hr.smul_right_injective _).eq_iff

中文:
引理 是正则.smul_right_inj
  条件: (hr : 是正则 r)
  结论: r • m₁ = r • m₂ ↔ m₁ = m₂
  证明: (hr.smul_right_injective _).eq_iff
-/
@[simp] protected lemma IsRegular.smul_right_inj (hr : IsRegular r) : r • m₁ = r • m₂ ↔ m₁ = m₂ :=
  (hr.smul_right_injective _).eq_iff

/--
lemma `IsRegular.smul_eq_zero_iff_right` / 引理 `IsRegular.smul_eq_zero_iff_right`

English:
lemma IsRegular.smul_eq_zero_iff_right
  given: (hr : IsRegular r)
  proof: by rw [← hr.smul_right_inj (m₁ := m), smul_zero]

中文:
引理 是正则.smul_eq_zero_iff_right
  条件: (hr : 是正则 r)
  证明: by rw [← hr.smul_right_inj (m₁ := m), smul_zero]
-/
@[simp] protected lemma IsRegular.smul_eq_zero_iff_right (hr : IsRegular r) :
    r • m = 0 ↔ m = 0 := by rw [← hr.smul_right_inj (m₁ := m), smul_zero]

/--
lemma `IsRegular.smul_ne_zero_iff_right` / 引理 `IsRegular.smul_ne_zero_iff_right`

English:
lemma IsRegular.smul_ne_zero_iff_right
  given: (hr : IsRegular r)
  statement: r • m != 0 ↔ m != 0
  proof: hr.smul_eq_zero_iff_right.ne

中文:
引理 是正则.smul_ne_zero_iff_right
  条件: (hr : 是正则 r)
  结论: r • m != 0 ↔ m != 0
  证明: hr.smul_eq_zero_iff_right.ne
-/
protected lemma IsRegular.smul_ne_zero_iff_right (hr : IsRegular r) : r • m != 0 ↔ m != 0 :=
  hr.smul_eq_zero_iff_right.ne

variable (R) in
/--
lemma `Module.IsTorsionFree.trans` / 引理 `Module.IsTorsionFree.trans`

English:
lemma Module.IsTorsionFree.trans
  statement: [Module S R] [IsTorsionFree S R] [IsScalarTower S R R]
  proof: by
    refine (?_ : IsRegular (s • 1 : R)).isSMulRegular (by simpa using hxy)
exact ⟨fun x y hxy => hs.isSMulRegular by simpa using hxy,
fun x y hxy => hs.isSMulRegular by simpa using hxy⟩

中文:
引理 模.是无挠.trans
  结论: [模 S R] [是无挠 S R] [标量塔 S R R]
  证明: by
    refine (?_ : IsRegular (s • 1 : R)).isSMulRegular (by simpa using hxy)
exact ⟨fun x y hxy => hs.isSMulRegular by simpa using hxy,
fun x y hxy => hs.isSMulRegular by simpa using hxy⟩

Depends on / 依赖: IsRegular, hs.isSMulRegular, isSMulRegular
-/
lemma Module.IsTorsionFree.trans [Module S R] [IsTorsionFree S R] [IsScalarTower S R R]
    [SMulCommClass S R R] [IsScalarTower S R M] : IsTorsionFree S M where
  isSMulRegular s hs x y hxy := by
    refine (?_ : IsRegular (s • 1 : R)).isSMulRegular (by simpa using hxy)
exact ⟨fun x y hxy => hs.isSMulRegular by simpa using hxy,
fun x y hxy => hs.isSMulRegular by simpa using hxy⟩

variable [IsCancelMulZero R]

/--
lemma `IsSMulRegular.of_ne_zero` / 引理 `IsSMulRegular.of_ne_zero`

English:
lemma IsSMulRegular.of_ne_zero
  given: (hr : r != 0)
  statement: IsSMulRegular M r
  proof: (IsRegular.of_ne_zero hr).isSMulRegular

中文:
引理 IsSMulRegular.of_ne_zero
  条件: (hr : r != 0)
  结论: IsSMulRegular M r
  证明: (IsRegular.of_ne_zero hr).isSMulRegular

Depends on / 依赖: IsRegular, IsRegular.of_ne_zero, isSMulRegular, of_ne_zero
-/
lemma IsSMulRegular.of_ne_zero (hr : r != 0) : IsSMulRegular M r :=
  (IsRegular.of_ne_zero hr).isSMulRegular

variable (M) in
/--
lemma `smul_right_injective` / 引理 `smul_right_injective`

English:
lemma smul_right_injective
  given: (hr : r != 0)
  statement: ((r • ·) : M -> M).Injective
  proof: (IsRegular.of_ne_zero hr).smul_right_injective _

中文:
引理 smul_right_injective
  条件: (hr : r != 0)
  结论: ((r • ·) : M -> M).单射
  证明: (IsRegular.of_ne_zero hr).smul_right_injective _

Depends on / 依赖: GroupWithZero, GroupWithZero.toNoZeroSMulDivisors, IsRegular, IsRegular.of_ne_zero, NoZeroSMulDivisors, of_ne_zero, smul_right_injective, toNoZeroSMulDivisors
-/
lemma smul_right_injective (hr : r != 0) : ((r • ·) : M -> M).Injective :=
  (IsRegular.of_ne_zero hr).smul_right_injective _

/--
lemma `smul_right_inj` / 引理 `smul_right_inj`

English:
lemma smul_right_inj
  given: (hr : r != 0)
  statement: r • m₁ = r • m₂ ↔ m₁ = m₂
  proof: (IsRegular.of_ne_zero hr).smul_right_inj

中文:
引理 smul_right_inj
  条件: (hr : r != 0)
  结论: r • m₁ = r • m₂ ↔ m₁ = m₂
  证明: (IsRegular.of_ne_zero hr).smul_right_inj
-/
@[simp] lemma smul_right_inj (hr : r != 0) : r • m₁ = r • m₂ ↔ m₁ = m₂ :=
  (IsRegular.of_ne_zero hr).smul_right_inj

/--
lemma `smul_eq_zero_iff_right` / 引理 `smul_eq_zero_iff_right`

English:
lemma smul_eq_zero_iff_right
  given: (hr : r != 0)
  statement: r • m = 0 ↔ m = 0
  proof: (IsRegular.of_ne_zero hr).smul_eq_zero_iff_right

中文:
引理 smul_eq_zero_iff_right
  条件: (hr : r != 0)
  结论: r • m = 0 ↔ m = 0
  证明: (IsRegular.of_ne_zero hr).smul_eq_zero_iff_right

Depends on / 依赖: IsRegular, IsRegular.of_ne_zero, NoZeroDivisors, NoZeroDivisors.toNoZeroSMulDivisors, of_ne_zero, smul_eq_zero_iff_right, toNoZeroSMulDivisors
-/
lemma smul_eq_zero_iff_right (hr : r != 0) : r • m = 0 ↔ m = 0 :=
  (IsRegular.of_ne_zero hr).smul_eq_zero_iff_right

/--
lemma `smul_ne_zero_iff_right` / 引理 `smul_ne_zero_iff_right`

English:
lemma smul_ne_zero_iff_right
  given: (hr : r != 0)
  statement: r • m != 0 ↔ m != 0
  proof: (smul_eq_zero_iff_right hr).ne

中文:
引理 smul_ne_zero_iff_right
  条件: (hr : r != 0)
  结论: r • m != 0 ↔ m != 0
  证明: (smul_eq_zero_iff_right hr).ne

Depends on / 依赖: smul_eq_zero_iff_right
-/
lemma smul_ne_zero_iff_right (hr : r != 0) : r • m != 0 ↔ m != 0 := (smul_eq_zero_iff_right hr).ne

/--
lemma `smul_eq_zero` / 引理 `smul_eq_zero`

English:
lemma smul_eq_zero
  statement: r • m = 0 ↔ r = 0 ∨ m = 0
  proof: by
  obtain rfl | hr := eq_or_ne r 0 <;> simp [smul_eq_zero_iff_right, *]

中文:
引理 smul_eq_zero
  结论: r • m = 0 ↔ r = 0 ∨ m = 0
  证明: by
  obtain rfl | hr := eq_or_ne r 0 <;> simp [smul_eq_zero_iff_right, *]
-/
@[simp] lemma smul_eq_zero : r • m = 0 ↔ r = 0 ∨ m = 0 := by
  obtain rfl | hr := eq_or_ne r 0 <;> simp [smul_eq_zero_iff_right, *]

/--
lemma `smul_ne_zero_iff` / 引理 `smul_ne_zero_iff`

English:
lemma smul_ne_zero_iff
  statement: r • m != 0 ↔ r != 0 ∧ m != 0
  proof: by simp

中文:
引理 smul_ne_zero_iff
  结论: r • m != 0 ↔ r != 0 ∧ m != 0
  证明: by simp
-/
lemma smul_ne_zero_iff : r • m != 0 ↔ r != 0 ∧ m != 0 := by simp

/--
lemma `smul_ne_zero` / 引理 `smul_ne_zero`

English:
lemma smul_ne_zero
  given: (hr : r != 0) (hm : m != 0)
  statement: r • m != 0
  proof: by simp [*]

中文:
引理 smul_ne_zero
  条件: (hr : r != 0) (hm : m != 0)
  结论: r • m != 0
  证明: by simp [*]
-/
lemma smul_ne_zero (hr : r != 0) (hm : m != 0) : r • m != 0 := by simp [*]

/--
lemma `smul_eq_zero_iff_left` / 引理 `smul_eq_zero_iff_left`

English:
lemma smul_eq_zero_iff_left
  given: (hm : m != 0)
  statement: r • m = 0 ↔ r = 0
  proof: by simp [*]

中文:
引理 smul_eq_zero_iff_left
  条件: (hm : m != 0)
  结论: r • m = 0 ↔ r = 0
  证明: by simp [*]
-/
lemma smul_eq_zero_iff_left (hm : m != 0) : r • m = 0 ↔ r = 0 := by simp [*]
/--
lemma `smul_ne_zero_iff_left` / 引理 `smul_ne_zero_iff_left`

English:
lemma smul_ne_zero_iff_left
  given: (hm : m != 0)
  statement: r • m != 0 ↔ r != 0
  proof: by simp [*]

中文:
引理 smul_ne_zero_iff_left
  条件: (hm : m != 0)
  结论: r • m != 0 ↔ r != 0
  证明: by simp [*]
-/
lemma smul_ne_zero_iff_left (hm : m != 0) : r • m != 0 ↔ r != 0 := by simp [*]

variable [CharZero R]

variable (R M) in
include R in
/--
lemma `IsAddTorsionFree.of_isTorsionFree` / 引理 `IsAddTorsionFree.of_isTorsionFree`

English:
lemma IsAddTorsionFree.of_isTorsionFree
  statement: IsAddTorsionFree M where
  proof: by
    simp_rw [← Nat.cast_smul_eq_nsmul R]; apply smul_right_injective; simpa

中文:
引理 是加法无挠.of_isTorsionFree
  结论: 是加法无挠 M where
  证明: by
    simp_rw [← Nat.cast_smul_eq_nsmul R]; apply smul_right_injective; simpa

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, simp_rw, smul_right_injective
-/
lemma IsAddTorsionFree.of_isTorsionFree : IsAddTorsionFree M where
  nsmul_right_injective n hn := by
    simp_rw [← Nat.cast_smul_eq_nsmul R]; apply smul_right_injective; simpa

/-- A characteristic zero domain is torsion-free. -/
instance (priority := 100) IsAddTorsionFree.of_isDomain_charZero : IsAddTorsionFree R :=
  .of_isTorsionFree R R

@[simp]
/--
lemma `Module.isTorsionFree_nat_iff_isAddTorsionFree` / 引理 `Module.isTorsionFree_nat_iff_isAddTorsionFree`

English:
lemma Module.isTorsionFree_nat_iff_isAddTorsionFree
  statement: IsTorsionFree Nat M ↔ IsAddTorsionFree M where
  proof: .of_isTorsionFree Nat _
  mpr _ := inferInstance

中文:
引理 模.isTorsionFree_nat_iff_isAddTorsionFree
  结论: 是无挠 自然数 M ↔ 是加法无挠 M where
  证明: .of_isTorsionFree Nat _
  mpr _ := inferInstance

Depends on / 依赖: of_isTorsionFree
-/
lemma Module.isTorsionFree_nat_iff_isAddTorsionFree : IsTorsionFree Nat M ↔ IsAddTorsionFree M where
  mp _ := .of_isTorsionFree Nat _
  mpr _ := inferInstance

end AddCommMonoid

section AddCommGroup
variable [CharZero R] [IsDomain R] [AddCommGroup M] [Module R M] {m : M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsAddTorsionFree
  signature: M] : IsTorsionFree Int M where
  body: zsmul_right_injective (by simpa [isRegular_iff_ne_zero] using hn)

@[simp]

中文:
实例 [是加法无挠
  签名: M] : 是无挠 整数 M where
  定义体: zsmul_right_injective (by simpa [isRegular_iff_ne_zero] using hn)

@[simp]

Depends on / 依赖: isRegular_iff_ne_zero, zsmul_right_injective
-/
instance [IsAddTorsionFree M] : IsTorsionFree Int M where
  isSMulRegular n hn := zsmul_right_injective (by simpa [isRegular_iff_ne_zero] using hn)

@[simp]
/--
lemma `Module.isTorsionFree_int_iff_isAddTorsionFree` / 引理 `Module.isTorsionFree_int_iff_isAddTorsionFree`

English:
lemma Module.isTorsionFree_int_iff_isAddTorsionFree
  statement: IsTorsionFree Int M ↔ IsAddTorsionFree M where
  proof: .of_isTorsionFree Int _
  mpr _ := inferInstance

中文:
引理 模.isTorsionFree_int_iff_isAddTorsionFree
  结论: 是无挠 整数 M ↔ 是加法无挠 M where
  证明: .of_isTorsionFree Int _
  mpr _ := inferInstance

Depends on / 依赖: of_isTorsionFree
-/
lemma Module.isTorsionFree_int_iff_isAddTorsionFree : IsTorsionFree Int M ↔ IsAddTorsionFree M where
  mp _ := .of_isTorsionFree Int _
  mpr _ := inferInstance

end AddCommGroup
end Semiring

section Ring
variable [Ring R] [AddCommGroup M] [Module R M] {m : M} {r₁ r₂ : R}

/--
lemma `Module.IsTorsionFree.of_smul_eq_zero` / 引理 `Module.IsTorsionFree.of_smul_eq_zero`

English:
lemma Module.IsTorsionFree.of_smul_eq_zero
  statement: [Nontrivial R]
  proof: by
    simpa [sub_eq_zero, hr.ne_zero] using h r (m₁ - m₂) (by simpa [smul_sub, sub_eq_zero] using hm)

中文:
引理 模.是无挠.of_smul_eq_zero
  结论: [非平凡 R]
  证明: by
    simpa [sub_eq_zero, hr.ne_zero] using h r (m₁ - m₂) (by simpa [smul_sub, sub_eq_zero] using hm)

Depends on / 依赖: hr.ne_zero, ne_zero, smul_sub, sub_eq_zero
-/
lemma Module.IsTorsionFree.of_smul_eq_zero [Nontrivial R]
    (h : forall (r : R) (m : M), r • m = 0 -> r = 0 ∨ m = 0) :
    IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm := by
    simpa [sub_eq_zero, hr.ne_zero] using h r (m₁ - m₂) (by simpa [smul_sub, sub_eq_zero] using hm)

/--
lemma `Module.isTorsionFree_iff_smul_eq_zero` / 引理 `Module.isTorsionFree_iff_smul_eq_zero`

English:
lemma Module.isTorsionFree_iff_smul_eq_zero
  given: [IsDomain R]
  proof: smul_eq_zero.1
  mpr := .of_smul_eq_zero

中文:
引理 模.isTorsionFree_iff_smul_eq_zero
  条件: [是整环 R]
  证明: smul_eq_zero.1
  mpr := .of_smul_eq_zero

Depends on / 依赖: smul_eq_zero
-/
lemma Module.isTorsionFree_iff_smul_eq_zero [IsDomain R] :
    IsTorsionFree R M ↔ forall (r : R) (m : M), r • m = 0 -> r = 0 ∨ m = 0 where
  mp _ _ _ := smul_eq_zero.1
  mpr := .of_smul_eq_zero

variable [IsCancelMulZero R] [IsTorsionFree R M]

variable (R) in
/--
lemma `smul_left_injective` / 引理 `smul_left_injective`

English:
lemma smul_left_injective
  given: (hm : m != 0)
  statement: ((· • m) : R -> M).Injective
  proof: by
  rintro r₁ r₂ hr
  dsimp at hr
  rwa [← sub_eq_zero, ← sub_smul, smul_eq_zero_iff_left hm, sub_eq_zero] at hr

中文:
引理 smul_left_injective
  条件: (hm : m != 0)
  结论: ((· • m) : R -> M).单射
  证明: by
  rintro r₁ r₂ hr
  dsimp at hr
  rwa [← sub_eq_zero, ← sub_smul, smul_eq_zero_iff_left hm, sub_eq_zero] at hr

Depends on / 依赖: smul_eq_zero_iff_left, sub_eq_zero, sub_smul
-/
lemma smul_left_injective (hm : m != 0) : ((· • m) : R -> M).Injective := by
  rintro r₁ r₂ hr
  dsimp at hr
  rwa [← sub_eq_zero, ← sub_smul, smul_eq_zero_iff_left hm, sub_eq_zero] at hr

/--
lemma `smul_left_inj` / 引理 `smul_left_inj`

English:
lemma smul_left_inj
  given: (hm : m != 0)
  statement: r₁ • m = r₂ • m ↔ r₁ = r₂
  proof: (smul_left_injective _ hm).eq_iff

中文:
引理 smul_left_inj
  条件: (hm : m != 0)
  结论: r₁ • m = r₂ • m ↔ r₁ = r₂
  证明: (smul_left_injective _ hm).eq_iff
-/
@[simp] lemma smul_left_inj (hm : m != 0) : r₁ • m = r₂ • m ↔ r₁ = r₂ :=
  (smul_left_injective _ hm).eq_iff

end Ring

section Semiring
variable (R M) [Semiring R] [AddCommGroup M] [Module R M]

-- TODO: Add a `ℤ`-specific version of `smul_left_injective` and move this lemma to an earlier file.
/--
lemma `CharZero.of_isAddTorsionFree` / 引理 `CharZero.of_isAddTorsionFree`

English:
lemma CharZero.of_isAddTorsionFree
  given: [Nontrivial M] [IsAddTorsionFree M]
  statement: CharZero R
  proof: by
  refine ⟨fun {n m h} => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  replace h : (n : Int) • x = (m : Int) • x := by simp [← Nat.cast_smul_eq_nsmul R, h]
  simpa using smul_left_injective Int hx h

中文:
引理 特征零.of_isAddTorsionFree
  条件: [非平凡 M] [是加法无挠 M]
  结论: 特征零 R
  证明: by
  refine ⟨fun {n m h} => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  replace h : (n : Int) • x = (m : Int) • x := by simp [← Nat.cast_smul_eq_nsmul R, h]
  simpa using smul_left_injective Int hx h

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, exists_ne, replace, smul_left_injective
-/
lemma CharZero.of_isAddTorsionFree [Nontrivial M] [IsAddTorsionFree M] : CharZero R := by
  refine ⟨fun {n m h} => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  replace h : (n : Int) • x = (m : Int) • x := by simp [← Nat.cast_smul_eq_nsmul R, h]
  simpa using smul_left_injective Int hx h

end Semiring
