/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma, Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Non-zero divisors and smul-divisors

In this file we define the submonoid `nonZeroDivisors` and `nonZeroSMulDivisors` of a
`MonoidWithZero`. We also define `nonZeroDivisorsLeft` and `nonZeroDivisorsRight` for
non-commutative monoids.

## Notation

This file declares the notations:
- `M₀⁰` for the submonoid of non-zero-divisors of `M₀`, in the scope `nonZeroDivisors`.
- `M₀⁰[M]` for the submonoid of non-zero smul-divisors of `M₀` with respect to `M`, in the locale
  `nonZeroSMulDivisors`

Use the statement `open scoped nonZeroDivisors nonZeroSMulDivisors` to access this notation in
your own code.

-/

@[expose] public section

assert_not_exists Ring

open Function

/--
lemma `Irreducible.coe_ne_zero` / 引理 `Irreducible.coe_ne_zero`

English:
lemma Irreducible.coe_ne_zero
  statement: {M₀ S : Type*} [MonoidWithZero M₀] [SetLike S M₀]
  proof: fun h => hx.1 by simpa using hx.2 (a := x) (b := x) (by ext; simp [h])

中文:
引理 不可约.coe_ne_zero
  结论: {M₀ S : 类型} [带零幺半群 M₀] [集合状 S M₀]
  证明: fun h => hx.1 by simpa using hx.2 (a := x) (b := x) (by ext; simp [h])
-/
lemma Irreducible.coe_ne_zero {M₀ S : Type*} [MonoidWithZero M₀] [SetLike S M₀]
    [SubmonoidClass S M₀] {s : S} {x : s} (hx : Irreducible x) : (x : M₀) != 0 :=
fun h => hx.1 by simpa using hx.2 (a := x) (b := x) (by ext; simp [h])

section
variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

/--
Definition of `nonZeroDivisorsLeft` / `nonZeroDivisorsLeft` 的定义

English:
definition nonZeroDivisorsLeft
  signature: : Submonoid M₀ where
  body: {x | forall y, x * y = 0 -> y = 0}
  one_mem' := by simp
mul_mem' {x y} hx hy := fun z hz => hy _ hx _ (mul_assoc x y z ▸ hz)

@[simp]

中文:
定义 nonZeroDivisorsLeft
  签名: : 子幺半群 M₀ where
  定义体: {x | forall y, x * y = 0 -> y = 0}
  one_mem' := by simp
mul_mem' {x y} hx hy := fun z hz => hy _ hx _ (mul_assoc x y z ▸ hz)

@[simp]
-/
def nonZeroDivisorsLeft : Submonoid M₀ where
  carrier := {x | forall y, x * y = 0 -> y = 0}
  one_mem' := by simp
mul_mem' {x y} hx hy := fun z hz => hy _ hx _ (mul_assoc x y z ▸ hz)

@[simp]
/--
lemma `mem_nonZeroDivisorsLeft_iff` / 引理 `mem_nonZeroDivisorsLeft_iff`

English:
lemma mem_nonZeroDivisorsLeft_iff
  statement: x in nonZeroDivisorsLeft M₀ ↔ forall y, x * y = 0 -> y = 0
  proof: .rfl

中文:
引理 mem_nonZeroDivisorsLeft_iff
  结论: x in nonZeroDivisorsLeft M₀ ↔ 对任意 y, x * y = 0 -> y = 0
  证明: .rfl
-/
lemma mem_nonZeroDivisorsLeft_iff : x in nonZeroDivisorsLeft M₀ ↔ forall y, x * y = 0 -> y = 0 := .rfl

/--
lemma `notMem_nonZeroDivisorsLeft_iff` / 引理 `notMem_nonZeroDivisorsLeft_iff`

English:
lemma notMem_nonZeroDivisorsLeft_iff
  proof: by
  simpa [mem_nonZeroDivisorsLeft_iff] using! Set.nonempty_def.symm

中文:
引理 notMem_nonZeroDivisorsLeft_iff
  证明: by
  simpa [mem_nonZeroDivisorsLeft_iff] using! Set.nonempty_def.symm

Depends on / 依赖: Set.nonempty_def.symm, mem_nonZeroDivisorsLeft_iff, nonempty_def
-/
lemma notMem_nonZeroDivisorsLeft_iff :
    x ∉ nonZeroDivisorsLeft M₀ ↔ {y | x * y = 0 ∧ y != 0}.Nonempty := by
  simpa [mem_nonZeroDivisorsLeft_iff] using! Set.nonempty_def.symm

/--
Definition of `nonZeroDivisorsRight` / `nonZeroDivisorsRight` 的定义

English:
definition nonZeroDivisorsRight
  signature: : Submonoid M₀ where
  body: {x | forall y, y * x = 0 -> y = 0}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy z hz => hx _ (hy _ ((mul_assoc z x y).symm ▸ hz))

@[simp]

中文:
定义 nonZeroDivisorsRight
  签名: : 子幺半群 M₀ where
  定义体: {x | forall y, y * x = 0 -> y = 0}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy z hz => hx _ (hy _ ((mul_assoc z x y).symm ▸ hz))

@[simp]
-/
def nonZeroDivisorsRight : Submonoid M₀ where
  carrier := {x | forall y, y * x = 0 -> y = 0}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy z hz => hx _ (hy _ ((mul_assoc z x y).symm ▸ hz))

@[simp]
/--
lemma `mem_nonZeroDivisorsRight_iff` / 引理 `mem_nonZeroDivisorsRight_iff`

English:
lemma mem_nonZeroDivisorsRight_iff
  statement: x in nonZeroDivisorsRight M₀ ↔ forall y, y * x = 0 -> y = 0
  proof: .rfl

中文:
引理 mem_nonZeroDivisorsRight_iff
  结论: x in nonZeroDivisorsRight M₀ ↔ 对任意 y, y * x = 0 -> y = 0
  证明: .rfl
-/
lemma mem_nonZeroDivisorsRight_iff : x in nonZeroDivisorsRight M₀ ↔ forall y, y * x = 0 -> y = 0 := .rfl

/--
lemma `notMem_nonZeroDivisorsRight_iff` / 引理 `notMem_nonZeroDivisorsRight_iff`

English:
lemma notMem_nonZeroDivisorsRight_iff
  proof: by
  simpa [mem_nonZeroDivisorsRight_iff] using! Set.nonempty_def.symm

中文:
引理 notMem_nonZeroDivisorsRight_iff
  证明: by
  simpa [mem_nonZeroDivisorsRight_iff] using! Set.nonempty_def.symm

Depends on / 依赖: Set.nonempty_def.symm, mem_nonZeroDivisorsRight_iff, nonempty_def
-/
lemma notMem_nonZeroDivisorsRight_iff :
    x ∉ nonZeroDivisorsRight M₀ ↔ {y | y * x = 0 ∧ y != 0}.Nonempty := by
  simpa [mem_nonZeroDivisorsRight_iff] using! Set.nonempty_def.symm

/--
lemma `nonZeroDivisorsLeft_eq_right` / 引理 `nonZeroDivisorsLeft_eq_right`

English:
lemma nonZeroDivisorsLeft_eq_right
  given: (M₀ : Type*) [CommMonoidWithZero M₀]
  proof: by
  ext x; simp [mul_comm x]

中文:
引理 nonZeroDivisorsLeft_eq_right
  条件: (M₀ : 类型) [带零交换幺半群 M₀]
  证明: by
  ext x; simp [mul_comm x]

Depends on / 依赖: mul_comm
-/
lemma nonZeroDivisorsLeft_eq_right (M₀ : Type*) [CommMonoidWithZero M₀] :
    nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀ := by
  ext x; simp [mul_comm x]

/--
lemma `coe_nonZeroDivisorsLeft_eq` / 引理 `coe_nonZeroDivisorsLeft_eq`

English:
lemma coe_nonZeroDivisorsLeft_eq
  given: [NoZeroDivisors M₀] [Nontrivial M₀]
  proof: by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsLeft_iff, mul_eq_zero, Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun hx y hx' => by simp_all⟩
  contrapose! h
  exact ⟨1, Or.inl h, one_ne_zero⟩

中文:
引理 coe_nonZeroDivisorsLeft_eq
  条件: [无零因子 M₀] [非平凡 M₀]
  证明: by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsLeft_iff, mul_eq_zero, Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun hx y hx' => by simp_all⟩
  contrapose! h
  exact ⟨1, Or.inl h, one_ne_zero⟩
-/
@[simp] lemma coe_nonZeroDivisorsLeft_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsLeft M₀ = {x : M₀ | x != 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsLeft_iff, mul_eq_zero, Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun hx y hx' => by simp_all⟩
  contrapose! h
  exact ⟨1, Or.inl h, one_ne_zero⟩

/--
lemma `coe_nonZeroDivisorsRight_eq` / 引理 `coe_nonZeroDivisorsRight_eq`

English:
lemma coe_nonZeroDivisorsRight_eq
  given: [NoZeroDivisors M₀] [Nontrivial M₀]
  proof: by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsRight_iff, mul_eq_zero, forall_eq_or_imp, true_and,
    Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun hx y hx' => by contradiction⟩
  contrapose! h
  exact ⟨1, h, one_ne_zero⟩

中文:
引理 coe_nonZeroDivisorsRight_eq
  条件: [无零因子 M₀] [非平凡 M₀]
  证明: by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsRight_iff, mul_eq_zero, forall_eq_or_imp, true_and,
    Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun hx y hx' => by contradiction⟩
  contrapose! h
  exact ⟨1, h, one_ne_zero⟩
-/
@[simp] lemma coe_nonZeroDivisorsRight_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsRight M₀ = {x : M₀ | x != 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsRight_iff, mul_eq_zero, forall_eq_or_imp, true_and,
    Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun hx y hx' => by contradiction⟩
  contrapose! h
  exact ⟨1, h, one_ne_zero⟩

end

/--
Definition of `nonZeroDivisors` / `nonZeroDivisors` 的定义

English:
definition nonZeroDivisors
  signature: (M₀ : Type*) [MonoidWithZero M₀]
  body: nonZeroDivisorsLeft M₀ ⊓ nonZeroDivisorsRight M₀

中文:
定义 nonZeroDivisors
  签名: (M₀ : 类型) [带零幺半群 M₀]
  定义体: nonZeroDivisorsLeft M₀ ⊓ nonZeroDivisorsRight M₀

Depends on / 依赖: nonZeroDivisorsLeft, nonZeroDivisorsRight
-/
def nonZeroDivisors (M₀ : Type*) [MonoidWithZero M₀] : Submonoid M₀ :=
  nonZeroDivisorsLeft M₀ ⊓ nonZeroDivisorsRight M₀

/-- The notation for the submonoid of non-zero divisors. -/
scoped[nonZeroDivisors] notation:9000 M₀ "⁰" => nonZeroDivisors M₀

/--
Definition of `nonZeroSMulDivisors` / `nonZeroSMulDivisors` 的定义

English:
definition nonZeroSMulDivisors
  signature: (M₀ : Type*) [MonoidWithZero M₀] (M : Type*) [Zero M] [MulAction M₀ M]
  body: { r | forall m : M, r • m = 0 -> m = 0}
  one_mem' m h := (one_smul M₀ m) ▸ h
mul_mem' {r₁ r₂} h₁ h₂ m H := h₂ _ h₁ _ mul_smul r₁ r₂ m ▸ H

中文:
定义 nonZeroSMulDivisors
  签名: (M₀ : 类型) [带零幺半群 M₀] (M : 类型) [零 M] [乘法作用 M₀ M]
  定义体: { r | forall m : M, r • m = 0 -> m = 0}
  one_mem' m h := (one_smul M₀ m) ▸ h
mul_mem' {r₁ r₂} h₁ h₂ m H := h₂ _ h₁ _ mul_smul r₁ r₂ m ▸ H
-/
def nonZeroSMulDivisors (M₀ : Type*) [MonoidWithZero M₀] (M : Type*) [Zero M] [MulAction M₀ M] :
    Submonoid M₀ where
  carrier := { r | forall m : M, r • m = 0 -> m = 0}
  one_mem' m h := (one_smul M₀ m) ▸ h
mul_mem' {r₁ r₂} h₁ h₂ m H := h₂ _ h₁ _ mul_smul r₁ r₂ m ▸ H

/-- The notation for the submonoid of non-zero smul-divisors. -/
scoped[nonZeroSMulDivisors] notation:9000 M₀ "⁰[" M "]" => nonZeroSMulDivisors M₀ M

open nonZeroDivisors

section MonoidWithZero
variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

/--
lemma `nonZeroDivisorsLeft_eq_nonZeroSMulDivisors` / 引理 `nonZeroDivisorsLeft_eq_nonZeroSMulDivisors`

English:
lemma nonZeroDivisorsLeft_eq_nonZeroSMulDivisors
  proof: rfl

中文:
引理 nonZeroDivisorsLeft_eq_nonZeroSMulDivisors
  证明: rfl
-/
lemma nonZeroDivisorsLeft_eq_nonZeroSMulDivisors :
    nonZeroDivisorsLeft M₀ = nonZeroSMulDivisors M₀ M₀ := rfl

/--
theorem `mem_nonZeroDivisors_iff` / 定理 `mem_nonZeroDivisors_iff`

English:
theorem mem_nonZeroDivisors_iff
  proof: Iff.rfl

中文:
定理 mem_nonZeroDivisors_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_nonZeroDivisors_iff :
    r in M₀⁰ ↔ (forall x, r * x = 0 -> x = 0) ∧ forall x, x * r = 0 -> x = 0 := Iff.rfl

/--
theorem `mem_nonZeroDivisors_iff'` / 定理 `mem_nonZeroDivisors_iff'`

English:
theorem mem_nonZeroDivisors_iff'
  proof: Iff.rfl

中文:
定理 mem_nonZeroDivisors_iff'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_nonZeroDivisors_iff' :
    r in M₀⁰ ↔ r in nonZeroDivisorsLeft M₀ ∧ r in nonZeroDivisorsRight M₀ := Iff.rfl

/--
lemma `notMem_nonZeroDivisors_iff` / 引理 `notMem_nonZeroDivisors_iff`

English:
lemma notMem_nonZeroDivisors_iff
  proof: by
  simp [-not_and, not_and_or, mem_nonZeroDivisors_iff, Set.nonempty_def]

中文:
引理 notMem_nonZeroDivisors_iff
  证明: by
  simp [-not_and, not_and_or, mem_nonZeroDivisors_iff, Set.nonempty_def]

Depends on / 依赖: Set.nonempty_def, mem_nonZeroDivisors_iff, nonempty_def, not_and, not_and_or
-/
lemma notMem_nonZeroDivisors_iff :
    r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s != 0}.Nonempty ∨ {s | s * r = 0 ∧ s != 0}.Nonempty := by
  simp [-not_and, not_and_or, mem_nonZeroDivisors_iff, Set.nonempty_def]

/--
theorem `mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff` / 定理 `mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff`

English:
theorem mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff
  given: (hr : r in nonZeroDivisorsLeft M₀)
  proof: ⟨hr _, by simp +contextual⟩

中文:
定理 mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff
  条件: (hr : r in nonZeroDivisorsLeft M₀)
  证明: ⟨hr _, by simp +contextual⟩

Depends on / 依赖: contextual
-/
theorem mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff (hr : r in nonZeroDivisorsLeft M₀) :
    r * x = 0 ↔ x = 0 :=
  ⟨hr _, by simp +contextual⟩

/--
theorem `mul_right_mem_nonZeroDivisorsRight_eq_zero_iff` / 定理 `mul_right_mem_nonZeroDivisorsRight_eq_zero_iff`

English:
theorem mul_right_mem_nonZeroDivisorsRight_eq_zero_iff
  given: (hr : r in nonZeroDivisorsRight M₀)
  proof: ⟨hr _, by simp +contextual⟩

中文:
定理 mul_right_mem_nonZeroDivisorsRight_eq_zero_iff
  条件: (hr : r in nonZeroDivisorsRight M₀)
  证明: ⟨hr _, by simp +contextual⟩

Depends on / 依赖: contextual
-/
theorem mul_right_mem_nonZeroDivisorsRight_eq_zero_iff (hr : r in nonZeroDivisorsRight M₀) :
    x * r = 0 ↔ x = 0 :=
  ⟨hr _, by simp +contextual⟩

/--
theorem `mul_right_mem_nonZeroDivisors_eq_zero_iff` / 定理 `mul_right_mem_nonZeroDivisors_eq_zero_iff`

English:
theorem mul_right_mem_nonZeroDivisors_eq_zero_iff
  given: (hr : r in M₀⁰)
  statement: x * r = 0 ↔ x = 0
  proof: mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hr.2

@[simp]

中文:
定理 mul_right_mem_nonZeroDivisors_eq_zero_iff
  条件: (hr : r in M₀⁰)
  结论: x * r = 0 ↔ x = 0
  证明: mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hr.2

@[simp]

Depends on / 依赖: mul_right_mem_nonZeroDivisorsRight_eq_zero_iff
-/
theorem mul_right_mem_nonZeroDivisors_eq_zero_iff (hr : r in M₀⁰) : x * r = 0 ↔ x = 0 :=
  mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hr.2

@[simp]
/--
theorem `mul_right_coe_nonZeroDivisors_eq_zero_iff` / 定理 `mul_right_coe_nonZeroDivisors_eq_zero_iff`

English:
theorem mul_right_coe_nonZeroDivisors_eq_zero_iff
  given: {c : M₀⁰}
  statement: x * c = 0 ↔ x = 0
  proof: mul_right_mem_nonZeroDivisors_eq_zero_iff c.prop

中文:
定理 mul_right_coe_nonZeroDivisors_eq_zero_iff
  条件: {c : M₀⁰}
  结论: x * c = 0 ↔ x = 0
  证明: mul_right_mem_nonZeroDivisors_eq_zero_iff c.prop

Depends on / 依赖: c.prop, mul_right_mem_nonZeroDivisors_eq_zero_iff
-/
theorem mul_right_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : x * c = 0 ↔ x = 0 :=
  mul_right_mem_nonZeroDivisors_eq_zero_iff c.prop

/--
lemma `IsUnit.mem_nonZeroDivisors` / 引理 `IsUnit.mem_nonZeroDivisors`

English:
lemma IsUnit.mem_nonZeroDivisors
  given: (hx : IsUnit x)
  statement: x in M₀⁰
  proof: ⟨fun _ => hx.mul_right_eq_zero.mp, fun _ => hx.mul_left_eq_zero.mp⟩

中文:
引理 是单位.mem_nonZeroDivisors
  条件: (hx : 是单位 x)
  结论: x in M₀⁰
  证明: ⟨fun _ => hx.mul_right_eq_zero.mp, fun _ => hx.mul_left_eq_zero.mp⟩

Depends on / 依赖: hx.mul_left_eq_zero.mp, hx.mul_right_eq_zero.mp, mul_left_eq_zero, mul_right_eq_zero
-/
lemma IsUnit.mem_nonZeroDivisors (hx : IsUnit x) : x in M₀⁰ :=
  ⟨fun _ => hx.mul_right_eq_zero.mp, fun _ => hx.mul_left_eq_zero.mp⟩

variable (M₀) in
/--
lemma `isUnit_le_nonZeroDivisors` / 引理 `isUnit_le_nonZeroDivisors`

English:
lemma isUnit_le_nonZeroDivisors
  statement: IsUnit.submonoid M₀ <= M₀⁰
  proof: fun _ => (·.mem_nonZeroDivisors)

@[deprecated "Use `Submonoid.mul_mem _ hx hy` instead." (since := "2026-01-07")]

中文:
引理 isUnit_le_nonZeroDivisors
  结论: 是单位.submonoid M₀ <= M₀⁰
  证明: fun _ => (·.mem_nonZeroDivisors)

@[deprecated "Use `Submonoid.mul_mem _ hx hy` instead." (since := "2026-01-07")]

Depends on / 依赖: mem_nonZeroDivisors
-/
lemma isUnit_le_nonZeroDivisors : IsUnit.submonoid M₀ <= M₀⁰ := fun _ => (·.mem_nonZeroDivisors)

@[deprecated "Use `Submonoid.mul_mem _ hx hy` instead." (since := "2026-01-07")]
/--
lemma `mul_mem_nonZeroDivisorsLeft_of_mem_nonZeroDivisorsLeft` / 引理 `mul_mem_nonZeroDivisorsLeft_of_mem_nonZeroDivisorsLeft`

English:
lemma mul_mem_nonZeroDivisorsLeft_of_mem_nonZeroDivisorsLeft
  statement: (hx : x in nonZeroDivisorsLeft M₀)
  proof: Submonoid.mul_mem _ hx hy

@[deprecated "Use `Submonoid.mul_mem _ hx hy` instead." (since := "2026-01-07")]

中文:
引理 mul_mem_nonZeroDivisorsLeft_of_mem_nonZeroDivisorsLeft
  结论: (hx : x in nonZeroDivisorsLeft M₀)
  证明: Submonoid.mul_mem _ hx hy

@[deprecated "Use `Submonoid.mul_mem _ hx hy` instead." (since := "2026-01-07")]

Depends on / 依赖: Submonoid, Submonoid.mul_mem, mul_mem
-/
lemma mul_mem_nonZeroDivisorsLeft_of_mem_nonZeroDivisorsLeft (hx : x in nonZeroDivisorsLeft M₀)
    (hy : y in nonZeroDivisorsLeft M₀) :
    x * y in nonZeroDivisorsLeft M₀ := Submonoid.mul_mem _ hx hy

@[deprecated "Use `Submonoid.mul_mem _ hx hy` instead." (since := "2026-01-07")]
/--
lemma `mul_mem_nonZeroDivisorsRight_of_mem_nonZeroDivisorsRight` / 引理 `mul_mem_nonZeroDivisorsRight_of_mem_nonZeroDivisorsRight`

English:
lemma mul_mem_nonZeroDivisorsRight_of_mem_nonZeroDivisorsRight
  statement: (hx : x in nonZeroDivisorsRight M₀)
  proof: Submonoid.mul_mem _ hx hy

中文:
引理 mul_mem_nonZeroDivisorsRight_of_mem_nonZeroDivisorsRight
  结论: (hx : x in nonZeroDivisorsRight M₀)
  证明: Submonoid.mul_mem _ hx hy

Depends on / 依赖: Submonoid, Submonoid.mul_mem, mul_mem
-/
lemma mul_mem_nonZeroDivisorsRight_of_mem_nonZeroDivisorsRight (hx : x in nonZeroDivisorsRight M₀)
    (hy : y in nonZeroDivisorsRight M₀) :
    x * y in nonZeroDivisorsRight M₀ := Submonoid.mul_mem _ hx hy

/--
lemma `mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors` / 引理 `mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors`

English:
lemma mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors
  given: (hx : x in M₀⁰) (hy : y in M₀⁰)
  proof: mem_nonZeroDivisors_iff'.mpr ⟨Submonoid.mul_mem _ hx.1 hy.1, Submonoid.mul_mem _ hx.2 hy.2⟩

中文:
引理 mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors
  条件: (hx : x in M₀⁰) (hy : y in M₀⁰)
  证明: mem_nonZeroDivisors_iff'.mpr ⟨Submonoid.mul_mem _ hx.1 hy.1, Submonoid.mul_mem _ hx.2 hy.2⟩

Depends on / 依赖: Submonoid, Submonoid.mul_mem, mem_nonZeroDivisors_iff, mul_mem
-/
lemma mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors (hx : x in M₀⁰) (hy : y in M₀⁰) :
    x * y in M₀⁰ :=
  mem_nonZeroDivisors_iff'.mpr ⟨Submonoid.mul_mem _ hx.1 hy.1, Submonoid.mul_mem _ hx.2 hy.2⟩

section Nontrivial
variable [Nontrivial M₀]

/--
theorem `zero_notMem_nonZeroDivisorsLeft` / 定理 `zero_notMem_nonZeroDivisorsLeft`

English:
theorem zero_notMem_nonZeroDivisorsLeft
  statement: 0 ∉ nonZeroDivisorsLeft M₀
  proof: fun h => one_ne_zero h 1 zero_mul _

中文:
定理 zero_notMem_nonZeroDivisorsLeft
  结论: 0 ∉ nonZeroDivisorsLeft M₀
  证明: fun h => one_ne_zero h 1 zero_mul _

Depends on / 依赖: one_ne_zero, zero_mul
-/
theorem zero_notMem_nonZeroDivisorsLeft : 0 ∉ nonZeroDivisorsLeft M₀ :=
fun h => one_ne_zero h 1 zero_mul _

/--
theorem `zero_notMem_nonZeroDivisorsRight` / 定理 `zero_notMem_nonZeroDivisorsRight`

English:
theorem zero_notMem_nonZeroDivisorsRight
  statement: 0 ∉ nonZeroDivisorsRight M₀
  proof: fun h => one_ne_zero h 1 mul_zero _

中文:
定理 zero_notMem_nonZeroDivisorsRight
  结论: 0 ∉ nonZeroDivisorsRight M₀
  证明: fun h => one_ne_zero h 1 mul_zero _

Depends on / 依赖: mul_zero, one_ne_zero
-/
theorem zero_notMem_nonZeroDivisorsRight : 0 ∉ nonZeroDivisorsRight M₀ :=
fun h => one_ne_zero h 1 mul_zero _

/--
theorem `zero_notMem_nonZeroDivisors` / 定理 `zero_notMem_nonZeroDivisors`

English:
theorem zero_notMem_nonZeroDivisors
  statement: 0 ∉ M₀⁰
  proof: fun h => zero_notMem_nonZeroDivisorsLeft h.1

中文:
定理 zero_notMem_nonZeroDivisors
  结论: 0 ∉ M₀⁰
  证明: fun h => zero_notMem_nonZeroDivisorsLeft h.1

Depends on / 依赖: zero_notMem_nonZeroDivisorsLeft
-/
theorem zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰ := fun h => zero_notMem_nonZeroDivisorsLeft h.1

/--
theorem `nonZeroDivisors.ne_zero` / 定理 `nonZeroDivisors.ne_zero`

English:
theorem nonZeroDivisors.ne_zero
  given: (hx : x in M₀⁰)
  statement: x != 0
  proof: ne_of_mem_of_not_mem hx zero_notMem_nonZeroDivisors

@[simp]

中文:
定理 nonZeroDivisors.ne_zero
  条件: (hx : x in M₀⁰)
  结论: x != 0
  证明: ne_of_mem_of_not_mem hx zero_notMem_nonZeroDivisors

@[simp]

Depends on / 依赖: ne_of_mem_of_not_mem, zero_notMem_nonZeroDivisors
-/
theorem nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 0 :=
  ne_of_mem_of_not_mem hx zero_notMem_nonZeroDivisors

@[simp]
/--
theorem `nonZeroDivisors.coe_ne_zero` / 定理 `nonZeroDivisors.coe_ne_zero`

English:
theorem nonZeroDivisors.coe_ne_zero
  given: (x : M₀⁰)
  statement: (x : M₀) != 0
  proof: nonZeroDivisors.ne_zero x.2

中文:
定理 nonZeroDivisors.coe_ne_zero
  条件: (x : M₀⁰)
  结论: (x : M₀) != 0
  证明: nonZeroDivisors.ne_zero x.2

Depends on / 依赖: ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero
-/
theorem nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x : M₀) != 0 := nonZeroDivisors.ne_zero x.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLeftCancelMulZero
  signature: M₀] : LeftCancelMonoid M₀⁰ where
  body: Subtype.ext
    mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero z) (by
      simpa only [Subtype.ext_iff, Submonoid.coe_mul] using h)

中文:
实例 [是左消去MulZero
  签名: M₀] : 左消去幺半群 M₀⁰ where
  定义体: Subtype.ext
    mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero z) (by
      simpa only [Subtype.ext_iff, Submonoid.coe_mul] using h)

Depends on / 依赖: Subtype, Subtype.ext
-/
instance [IsLeftCancelMulZero M₀] : LeftCancelMonoid M₀⁰ where
mul_left_cancel z _ _ h := Subtype.ext
    mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero z) (by
      simpa only [Subtype.ext_iff, Submonoid.coe_mul] using h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsRightCancelMulZero
  signature: M₀] : RightCancelMonoid M₀⁰ where
  body: Subtype.ext
    mul_right_cancel₀ (nonZeroDivisors.coe_ne_zero z) (by
      simpa only [Subtype.ext_iff, Submonoid.coe_mul] using h)

中文:
实例 [是右消去MulZero
  签名: M₀] : 右消去幺半群 M₀⁰ where
  定义体: Subtype.ext
    mul_right_cancel₀ (nonZeroDivisors.coe_ne_zero z) (by
      simpa only [Subtype.ext_iff, Submonoid.coe_mul] using h)

Depends on / 依赖: Subtype, Subtype.ext
-/
instance [IsRightCancelMulZero M₀] : RightCancelMonoid M₀⁰ where
mul_right_cancel z _ _ h := Subtype.ext
    mul_right_cancel₀ (nonZeroDivisors.coe_ne_zero z) (by
      simpa only [Subtype.ext_iff, Submonoid.coe_mul] using h)

end Nontrivial

section NoZeroDivisors
variable [NoZeroDivisors M₀]

/--
theorem `eq_zero_of_ne_zero_of_mul_right_eq_zero` / 定理 `eq_zero_of_ne_zero_of_mul_right_eq_zero`

English:
theorem eq_zero_of_ne_zero_of_mul_right_eq_zero
  given: (hx : x != 0) (hxy : y * x = 0)
  statement: y = 0
  proof: Or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

中文:
定理 eq_zero_of_ne_zero_of_mul_right_eq_zero
  条件: (hx : x != 0) (hxy : y * x = 0)
  结论: y = 0
  证明: Or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

Depends on / 依赖: Or.resolve_right, eq_zero_or_eq_zero_of_mul_eq_zero, resolve_right
-/
theorem eq_zero_of_ne_zero_of_mul_right_eq_zero (hx : x != 0) (hxy : y * x = 0) : y = 0 :=
  Or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

/--
theorem `eq_zero_of_ne_zero_of_mul_left_eq_zero` / 定理 `eq_zero_of_ne_zero_of_mul_left_eq_zero`

English:
theorem eq_zero_of_ne_zero_of_mul_left_eq_zero
  given: (hx : x != 0) (hxy : x * y = 0)
  statement: y = 0
  proof: Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

中文:
定理 eq_zero_of_ne_zero_of_mul_left_eq_zero
  条件: (hx : x != 0) (hxy : x * y = 0)
  结论: y = 0
  证明: Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

Depends on / 依赖: Or.resolve_left, eq_zero_or_eq_zero_of_mul_eq_zero, resolve_left
-/
theorem eq_zero_of_ne_zero_of_mul_left_eq_zero (hx : x != 0) (hxy : x * y = 0) : y = 0 :=
  Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

/--
theorem `mem_nonZeroDivisors_of_ne_zero` / 定理 `mem_nonZeroDivisors_of_ne_zero`

English:
theorem mem_nonZeroDivisors_of_ne_zero
  given: (hx : x != 0)
  statement: x in M₀⁰
  proof: ⟨fun _ => eq_zero_of_ne_zero_of_mul_left_eq_zero hx,
   fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero hx⟩

中文:
定理 mem_nonZeroDivisors_of_ne_zero
  条件: (hx : x != 0)
  结论: x in M₀⁰
  证明: ⟨fun _ => eq_zero_of_ne_zero_of_mul_left_eq_zero hx,
   fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero hx⟩

Depends on / 依赖: eq_zero_of_ne_zero_of_mul_left_eq_zero, eq_zero_of_ne_zero_of_mul_right_eq_zero
-/
theorem mem_nonZeroDivisors_of_ne_zero (hx : x != 0) : x in M₀⁰ :=
  ⟨fun _ => eq_zero_of_ne_zero_of_mul_left_eq_zero hx,
   fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero hx⟩

/--
lemma `mem_nonZeroDivisors_iff_ne_zero` / 引理 `mem_nonZeroDivisors_iff_ne_zero`

English:
lemma mem_nonZeroDivisors_iff_ne_zero
  given: [Nontrivial M₀]
  statement: x in M₀⁰ ↔ x != 0
  proof: ⟨nonZeroDivisors.ne_zero, mem_nonZeroDivisors_of_ne_zero⟩

中文:
引理 mem_nonZeroDivisors_iff_ne_zero
  条件: [非平凡 M₀]
  结论: x in M₀⁰ ↔ x != 0
  证明: ⟨nonZeroDivisors.ne_zero, mem_nonZeroDivisors_of_ne_zero⟩
-/
@[simp] lemma mem_nonZeroDivisors_iff_ne_zero [Nontrivial M₀] : x in M₀⁰ ↔ x != 0 :=
  ⟨nonZeroDivisors.ne_zero, mem_nonZeroDivisors_of_ne_zero⟩

/--
theorem `le_nonZeroDivisors_of_noZeroDivisors` / 定理 `le_nonZeroDivisors_of_noZeroDivisors`

English:
theorem le_nonZeroDivisors_of_noZeroDivisors
  given: {S : Submonoid M₀} (hS : (0 : M₀) ∉ S)
  proof: fun _ hx =>
mem_nonZeroDivisors_of_ne_zero by rintro rfl; exact hS hx

中文:
定理 le_nonZeroDivisors_of_noZeroDivisors
  条件: {S : 子幺半群 M₀} (hS : (0 : M₀) ∉ S)
  证明: fun _ hx =>
mem_nonZeroDivisors_of_ne_zero by rintro rfl; exact hS hx
-/
theorem le_nonZeroDivisors_of_noZeroDivisors {S : Submonoid M₀} (hS : (0 : M₀) ∉ S) :
    S <= M₀⁰ := fun _ hx =>
mem_nonZeroDivisors_of_ne_zero by rintro rfl; exact hS hx

/--
theorem `powers_le_nonZeroDivisors_of_noZeroDivisors` / 定理 `powers_le_nonZeroDivisors_of_noZeroDivisors`

English:
theorem powers_le_nonZeroDivisors_of_noZeroDivisors
  given: (hx : x != 0)
  statement: Submonoid.powers x <= M₀⁰
  proof: le_nonZeroDivisors_of_noZeroDivisors fun h => hx (h.recOn fun _ => eq_zero_of_pow_eq_zero)

中文:
定理 powers_le_nonZeroDivisors_of_noZeroDivisors
  条件: (hx : x != 0)
  结论: 子幺半群.powers x <= M₀⁰
  证明: le_nonZeroDivisors_of_noZeroDivisors fun h => hx (h.recOn fun _ => eq_zero_of_pow_eq_zero)

Depends on / 依赖: eq_zero_of_pow_eq_zero, h.recOn, le_nonZeroDivisors_of_noZeroDivisors
-/
theorem powers_le_nonZeroDivisors_of_noZeroDivisors (hx : x != 0) : Submonoid.powers x <= M₀⁰ :=
  le_nonZeroDivisors_of_noZeroDivisors fun h => hx (h.recOn fun _ => eq_zero_of_pow_eq_zero)

end NoZeroDivisors

/--
lemma `IsLeftRegular.mem_nonZeroDivisorsLeft` / 引理 `IsLeftRegular.mem_nonZeroDivisorsLeft`

English:
lemma IsLeftRegular.mem_nonZeroDivisorsLeft
  given: (h : IsLeftRegular r)
  proof: fun _x hx => h.mul_left_eq_zero_iff.mp hx

中文:
引理 IsLeftRegular.mem_nonZeroDivisorsLeft
  条件: (h : IsLeftRegular r)
  证明: fun _x hx => h.mul_left_eq_zero_iff.mp hx

Depends on / 依赖: h.mul_left_eq_zero_iff.mp, mul_left_eq_zero_iff
-/
lemma IsLeftRegular.mem_nonZeroDivisorsLeft (h : IsLeftRegular r) :
    r in nonZeroDivisorsLeft M₀ := fun _x hx => h.mul_left_eq_zero_iff.mp hx

/--
lemma `IsRightRegular.mem_nonZeroDivisorsRight` / 引理 `IsRightRegular.mem_nonZeroDivisorsRight`

English:
lemma IsRightRegular.mem_nonZeroDivisorsRight
  given: (h : IsRightRegular r)
  proof: fun _x hx => h.mul_right_eq_zero_iff.mp hx

中文:
引理 IsRightRegular.mem_nonZeroDivisorsRight
  条件: (h : IsRightRegular r)
  证明: fun _x hx => h.mul_right_eq_zero_iff.mp hx

Depends on / 依赖: h.mul_right_eq_zero_iff.mp, mul_right_eq_zero_iff
-/
lemma IsRightRegular.mem_nonZeroDivisorsRight (h : IsRightRegular r) :
    r in nonZeroDivisorsRight M₀ := fun _x hx => h.mul_right_eq_zero_iff.mp hx

/--
lemma `IsRegular.mem_nonZeroDivisors` / 引理 `IsRegular.mem_nonZeroDivisors`

English:
lemma IsRegular.mem_nonZeroDivisors
  given: (h : IsRegular r)
  statement: r in M₀⁰
  proof: ⟨h.1.mem_nonZeroDivisorsLeft, h.2.mem_nonZeroDivisorsRight⟩

中文:
引理 是正则.mem_nonZeroDivisors
  条件: (h : 是正则 r)
  结论: r in M₀⁰
  证明: ⟨h.1.mem_nonZeroDivisorsLeft, h.2.mem_nonZeroDivisorsRight⟩

Depends on / 依赖: mem_nonZeroDivisorsLeft, mem_nonZeroDivisorsRight
-/
lemma IsRegular.mem_nonZeroDivisors (h : IsRegular r) : r in M₀⁰ :=
  ⟨h.1.mem_nonZeroDivisorsLeft, h.2.mem_nonZeroDivisorsRight⟩

/--
lemma `noZeroDivisors_iff_forall_mem_nonZeroDivisorsLeft` / 引理 `noZeroDivisors_iff_forall_mem_nonZeroDivisorsLeft`

English:
lemma noZeroDivisors_iff_forall_mem_nonZeroDivisorsLeft
  proof: noZeroDivisors_iff_right_eq_zero_of_mul

中文:
引理 noZeroDivisors_iff_对任意_mem_nonZeroDivisorsLeft
  证明: noZeroDivisors_iff_right_eq_zero_of_mul

Depends on / 依赖: noZeroDivisors_iff_right_eq_zero_of_mul
-/
lemma noZeroDivisors_iff_forall_mem_nonZeroDivisorsLeft :
    NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> x in nonZeroDivisorsLeft M₀ :=
  noZeroDivisors_iff_right_eq_zero_of_mul

/--
lemma `noZeroDivisors_iff_forall_mem_nonZeroDivisorsRight` / 引理 `noZeroDivisors_iff_forall_mem_nonZeroDivisorsRight`

English:
lemma noZeroDivisors_iff_forall_mem_nonZeroDivisorsRight
  proof: noZeroDivisors_iff_left_eq_zero_of_mul

中文:
引理 noZeroDivisors_iff_对任意_mem_nonZeroDivisorsRight
  证明: noZeroDivisors_iff_left_eq_zero_of_mul

Depends on / 依赖: noZeroDivisors_iff_left_eq_zero_of_mul
-/
lemma noZeroDivisors_iff_forall_mem_nonZeroDivisorsRight :
    NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> x in nonZeroDivisorsRight M₀ :=
  noZeroDivisors_iff_left_eq_zero_of_mul

/--
lemma `noZeroDivisors_iff_forall_mem_nonZeroDivisors` / 引理 `noZeroDivisors_iff_forall_mem_nonZeroDivisors`

English:
lemma noZeroDivisors_iff_forall_mem_nonZeroDivisors
  proof: noZeroDivisors_iff_eq_zero_of_mul

中文:
引理 noZeroDivisors_iff_对任意_mem_nonZeroDivisors
  证明: noZeroDivisors_iff_eq_zero_of_mul

Depends on / 依赖: noZeroDivisors_iff_eq_zero_of_mul
-/
lemma noZeroDivisors_iff_forall_mem_nonZeroDivisors :
    NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> x in M₀⁰ :=
  noZeroDivisors_iff_eq_zero_of_mul

/--
lemma `IsSMulRegular.mem_nonZeroSMulDivisors` / 引理 `IsSMulRegular.mem_nonZeroSMulDivisors`

English:
lemma IsSMulRegular.mem_nonZeroSMulDivisors
  statement: {M : Type*} [Zero M] [MulActionWithZero M₀ M] {m₀ : M₀}
  proof: fun _ => h.right_eq_zero_of_smul

中文:
引理 IsSMulRegular.mem_nonZeroSMulDivisors
  结论: {M : 类型} [零 M] [带零乘法作用 M₀ M] {m₀ : M₀}
  证明: fun _ => h.right_eq_zero_of_smul

Depends on / 依赖: h.right_eq_zero_of_smul, right_eq_zero_of_smul
-/
lemma IsSMulRegular.mem_nonZeroSMulDivisors {M : Type*} [Zero M] [MulActionWithZero M₀ M] {m₀ : M₀}
    (h : IsSMulRegular M m₀) : m₀ in nonZeroSMulDivisors M₀ M :=
  fun _ => h.right_eq_zero_of_smul

/--
lemma `isSMulRegular_iff_mem_nonZeroSMulDivisors` / 引理 `isSMulRegular_iff_mem_nonZeroSMulDivisors`

English:
lemma isSMulRegular_iff_mem_nonZeroSMulDivisors
  statement: {M : Type*} [AddGroup M] [DistribMulAction M₀ M]
  proof: isSMulRegular_iff_right_eq_zero_of_smul

中文:
引理 isSMulRegular_iff_mem_nonZeroSMulDivisors
  结论: {M : 类型} [加法群 M] [分配乘法作用 M₀ M]
  证明: isSMulRegular_iff_right_eq_zero_of_smul

Depends on / 依赖: isSMulRegular_iff_right_eq_zero_of_smul
-/
lemma isSMulRegular_iff_mem_nonZeroSMulDivisors {M : Type*} [AddGroup M] [DistribMulAction M₀ M]
    {m₀ : M₀} : IsSMulRegular M m₀ ↔ m₀ in nonZeroSMulDivisors M₀ M :=
  isSMulRegular_iff_right_eq_zero_of_smul

variable [FunLike F M₀ M₀']

-- TODO: nonZeroDivisorsLeft/Right also works
/--
theorem `map_ne_zero_of_mem_nonZeroDivisors` / 定理 `map_ne_zero_of_mem_nonZeroDivisors`

English:
theorem map_ne_zero_of_mem_nonZeroDivisors
  statement: [Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F)
  proof: fun h0 =>
  one_ne_zero (h.2 1 ((one_mul x).symm ▸ hg (h0.trans (map_zero g).symm)))

中文:
定理 map_ne_zero_of_mem_nonZeroDivisors
  结论: [非平凡 M₀] [保零态射类 F M₀ M₀'] (g : F)
  证明: fun h0 =>
  one_ne_zero (h.2 1 ((one_mul x).symm ▸ hg (h0.trans (map_zero g).symm)))
-/
theorem map_ne_zero_of_mem_nonZeroDivisors [Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Injective (g : M₀ -> M₀')) {x : M₀} (h : x in M₀⁰) : g x != 0 := fun h0 =>
  one_ne_zero (h.2 1 ((one_mul x).symm ▸ hg (h0.trans (map_zero g).symm)))

/--
theorem `map_mem_nonZeroDivisors` / 定理 `map_mem_nonZeroDivisors`

English:
theorem map_mem_nonZeroDivisors
  statement: [Nontrivial M₀] [NoZeroDivisors M₀'] [ZeroHomClass F M₀ M₀'] (g : F)
  proof: ⟨fun _ => eq_zero_of_ne_zero_of_mul_left_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h),
    fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h)⟩

中文:
定理 map_mem_nonZeroDivisors
  结论: [非平凡 M₀] [无零因子 M₀'] [保零态射类 F M₀ M₀'] (g : F)
  证明: ⟨fun _ => eq_zero_of_ne_zero_of_mul_left_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h),
    fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h)⟩

Depends on / 依赖: eq_zero_of_ne_zero_of_mul_left_eq_zero, eq_zero_of_ne_zero_of_mul_right_eq_zero, map_ne_zero_of_mem_nonZeroDivisors
-/
theorem map_mem_nonZeroDivisors [Nontrivial M₀] [NoZeroDivisors M₀'] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Injective g) {x : M₀} (h : x in M₀⁰) : g x in M₀'⁰ :=
  ⟨fun _ => eq_zero_of_ne_zero_of_mul_left_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h),
    fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h)⟩

/--
theorem `MulEquivClass.map_nonZeroDivisors` / 定理 `MulEquivClass.map_nonZeroDivisors`

English:
theorem MulEquivClass.map_nonZeroDivisors
  statement: {M₀ S F : Type*} [MonoidWithZero M₀] [MonoidWithZero S]
  proof: by
  let h : M₀ ≃* S := h
  change Submonoid.map h _ = _
  ext
  simp_rw [Submonoid.map_equiv_eq_comap_symm, Submonoid.mem_comap, mem_nonZeroDivisors_iff,
    ← h.symm.forall_congr_right, h.symm.toEquiv_eq_coe, h.symm.coe_toEquiv, ← map_mul,
    map_eq_zero_iff _ h.symm.injective]

中文:
定理 乘法等价类.map_nonZeroDivisors
  结论: {M₀ S F : 类型} [带零幺半群 M₀] [带零幺半群 S]
  证明: by
  let h : M₀ ≃* S := h
  change Submonoid.map h _ = _
  ext
  simp_rw [Submonoid.map_equiv_eq_comap_symm, Submonoid.mem_comap, mem_nonZeroDivisors_iff,
    ← h.symm.forall_congr_right, h.symm.toEquiv_eq_coe, h.symm.coe_toEquiv, ← map_mul,
    map_eq_zero_iff _ h.symm.injective]

Depends on / 依赖: Submonoid, Submonoid.map, Submonoid.map_equiv_eq_comap_symm, Submonoid.mem_comap, coe_toEquiv, forall_congr_right, h.symm.coe_toEquiv, h.symm.forall_congr_right, h.symm.injective, h.symm.toEquiv_eq_coe, injective, map_eq_zero_iff, map_equiv_eq_comap_symm, map_mul, mem_comap, mem_nonZeroDivisors_iff, simp_rw, toEquiv_eq_coe
-/
theorem MulEquivClass.map_nonZeroDivisors {M₀ S F : Type*} [MonoidWithZero M₀] [MonoidWithZero S]
    [EquivLike F M₀ S] [MulEquivClass F M₀ S] (h : F) :
    Submonoid.map h (nonZeroDivisors M₀) = nonZeroDivisors S := by
  let h : M₀ ≃* S := h
  change Submonoid.map h _ = _
  ext
  simp_rw [Submonoid.map_equiv_eq_comap_symm, Submonoid.mem_comap, mem_nonZeroDivisors_iff,
    ← h.symm.forall_congr_right, h.symm.toEquiv_eq_coe, h.symm.coe_toEquiv, ← map_mul,
    map_eq_zero_iff _ h.symm.injective]

/--
theorem `map_le_nonZeroDivisors_of_injective` / 定理 `map_le_nonZeroDivisors_of_injective`

English:
theorem map_le_nonZeroDivisors_of_injective
  statement: [NoZeroDivisors M₀'] [MonoidWithZeroHomClass F M₀ M₀']
  proof: by
  cases subsingleton_or_nontrivial M₀
  · simp [Subsingleton.elim S ⊥]
  · refine le_nonZeroDivisors_of_noZeroDivisors ?_
    rintro ⟨x, hx, hx0⟩
exact zero_notMem_nonZeroDivisors hS .mp hx0 ▸ hx map_eq_zero_iff f hf

中文:
定理 map_le_nonZeroDivisors_of_injective
  结论: [无零因子 M₀'] [带零幺半群态射类 F M₀ M₀']
  证明: by
  cases subsingleton_or_nontrivial M₀
  · simp [Subsingleton.elim S ⊥]
  · refine le_nonZeroDivisors_of_noZeroDivisors ?_
    rintro ⟨x, hx, hx0⟩
exact zero_notMem_nonZeroDivisors hS .mp hx0 ▸ hx map_eq_zero_iff f hf

Depends on / 依赖: Subsingleton, Subsingleton.elim, le_nonZeroDivisors_of_noZeroDivisors, map_eq_zero_iff, subsingleton_or_nontrivial, zero_notMem_nonZeroDivisors
-/
theorem map_le_nonZeroDivisors_of_injective [NoZeroDivisors M₀'] [MonoidWithZeroHomClass F M₀ M₀']
    (f : F) (hf : Injective f) {S : Submonoid M₀} (hS : S <= M₀⁰) : S.map f <= M₀'⁰ := by
  cases subsingleton_or_nontrivial M₀
  · simp [Subsingleton.elim S ⊥]
  · refine le_nonZeroDivisors_of_noZeroDivisors ?_
    rintro ⟨x, hx, hx0⟩
exact zero_notMem_nonZeroDivisors hS .mp hx0 ▸ hx map_eq_zero_iff f hf

/--
theorem `nonZeroDivisors_le_comap_nonZeroDivisors_of_injective` / 定理 `nonZeroDivisors_le_comap_nonZeroDivisors_of_injective`

English:
theorem nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
  statement: [NoZeroDivisors M₀']
  proof: Submonoid.le_comap_of_map_le _ (map_le_nonZeroDivisors_of_injective _ hf le_rfl)

中文:
定理 nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
  结论: [无零因子 M₀']
  证明: Submonoid.le_comap_of_map_le _ (map_le_nonZeroDivisors_of_injective _ hf le_rfl)

Depends on / 依赖: Submonoid, Submonoid.le_comap_of_map_le, le_comap_of_map_le, le_rfl, map_le_nonZeroDivisors_of_injective
-/
theorem nonZeroDivisors_le_comap_nonZeroDivisors_of_injective [NoZeroDivisors M₀']
    [MonoidWithZeroHomClass F M₀ M₀'] (f : F) (hf : Injective f) : M₀⁰ <= M₀'⁰.comap f :=
  Submonoid.le_comap_of_map_le _ (map_le_nonZeroDivisors_of_injective _ hf le_rfl)

/--
theorem `mem_nonZeroDivisors_of_injective` / 定理 `mem_nonZeroDivisors_of_injective`

English:
theorem mem_nonZeroDivisors_of_injective
  statement: [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
  proof: ⟨fun y hy => hf map_zero f ▸ hx.1 (f y) (map_mul f x y ▸ map_zero f ▸ congrArg f hy),
fun y hy => hf map_zero f ▸ hx.2 (f y) (map_mul f y x ▸ map_zero f ▸ congrArg f hy)⟩

中文:
定理 mem_nonZeroDivisors_of_injective
  结论: [带零幺半群态射类 F M₀ M₀'] {f : F}
  证明: ⟨fun y hy => hf map_zero f ▸ hx.1 (f y) (map_mul f x y ▸ map_zero f ▸ congrArg f hy),
fun y hy => hf map_zero f ▸ hx.2 (f y) (map_mul f y x ▸ map_zero f ▸ congrArg f hy)⟩

Depends on / 依赖: map_mul, map_zero
-/
theorem mem_nonZeroDivisors_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Injective f) (hx : f x in M₀'⁰) : x in M₀⁰ :=
⟨fun y hy => hf map_zero f ▸ hx.1 (f y) (map_mul f x y ▸ map_zero f ▸ congrArg f hy),
fun y hy => hf map_zero f ▸ hx.2 (f y) (map_mul f y x ▸ map_zero f ▸ congrArg f hy)⟩

/--
theorem `comap_nonZeroDivisors_le_of_injective` / 定理 `comap_nonZeroDivisors_le_of_injective`

English:
theorem comap_nonZeroDivisors_le_of_injective
  statement: [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
  proof: fun _ ha => mem_nonZeroDivisors_of_injective hf (Submonoid.mem_comap.mp ha)

中文:
定理 comap_nonZeroDivisors_le_of_injective
  结论: [带零幺半群态射类 F M₀ M₀'] {f : F}
  证明: fun _ ha => mem_nonZeroDivisors_of_injective hf (Submonoid.mem_comap.mp ha)

Depends on / 依赖: Submonoid, Submonoid.mem_comap.mp, mem_comap, mem_nonZeroDivisors_of_injective
-/
theorem comap_nonZeroDivisors_le_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Injective f) : M₀'⁰.comap f <= M₀⁰ :=
  fun _ ha => mem_nonZeroDivisors_of_injective hf (Submonoid.mem_comap.mp ha)

end MonoidWithZero

section CommMonoidWithZero
variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

/--
lemma `nonZeroDivisorsLeft_eq_nonZeroDivisors` / 引理 `nonZeroDivisorsLeft_eq_nonZeroDivisors`

English:
lemma nonZeroDivisorsLeft_eq_nonZeroDivisors
  statement: nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀
  proof: by
  rw [nonZeroDivisors]; rw [nonZeroDivisorsLeft_eq_right]; rw [inf_idem]

中文:
引理 nonZeroDivisorsLeft_eq_nonZeroDivisors
  结论: nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀
  证明: by
  rw [nonZeroDivisors]; rw [nonZeroDivisorsLeft_eq_right]; rw [inf_idem]

Depends on / 依赖: inf_idem, nonZeroDivisors, nonZeroDivisorsLeft_eq_right
-/
lemma nonZeroDivisorsLeft_eq_nonZeroDivisors : nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀ := by
  rw [nonZeroDivisors]; rw [nonZeroDivisorsLeft_eq_right]; rw [inf_idem]

/--
lemma `nonZeroDivisorsRight_eq_nonZeroDivisors` / 引理 `nonZeroDivisorsRight_eq_nonZeroDivisors`

English:
lemma nonZeroDivisorsRight_eq_nonZeroDivisors
  statement: nonZeroDivisorsRight M₀ = nonZeroDivisors M₀
  proof: by
  rw [← nonZeroDivisorsLeft_eq_right]; rw [nonZeroDivisorsLeft_eq_nonZeroDivisors]

中文:
引理 nonZeroDivisorsRight_eq_nonZeroDivisors
  结论: nonZeroDivisorsRight M₀ = nonZeroDivisors M₀
  证明: by
  rw [← nonZeroDivisorsLeft_eq_right]; rw [nonZeroDivisorsLeft_eq_nonZeroDivisors]

Depends on / 依赖: nonZeroDivisorsLeft_eq_nonZeroDivisors, nonZeroDivisorsLeft_eq_right
-/
lemma nonZeroDivisorsRight_eq_nonZeroDivisors : nonZeroDivisorsRight M₀ = nonZeroDivisors M₀ := by
  rw [← nonZeroDivisorsLeft_eq_right]; rw [nonZeroDivisorsLeft_eq_nonZeroDivisors]

/--
lemma `nonZeroDivisorsRight_eq_left` / 引理 `nonZeroDivisorsRight_eq_left`

English:
lemma nonZeroDivisorsRight_eq_left
  statement: nonZeroDivisorsRight M₀ = nonZeroDivisorsLeft M₀
  proof: by
  rw [nonZeroDivisorsLeft_eq_right]

中文:
引理 nonZeroDivisorsRight_eq_left
  结论: nonZeroDivisorsRight M₀ = nonZeroDivisorsLeft M₀
  证明: by
  rw [nonZeroDivisorsLeft_eq_right]

Depends on / 依赖: nonZeroDivisorsLeft_eq_right
-/
lemma nonZeroDivisorsRight_eq_left : nonZeroDivisorsRight M₀ = nonZeroDivisorsLeft M₀ := by
  rw [nonZeroDivisorsLeft_eq_right]

/--
theorem `mem_nonZeroDivisors_iff_left` / 定理 `mem_nonZeroDivisors_iff_left`

English:
theorem mem_nonZeroDivisors_iff_left
  statement: r in M₀⁰ ↔ forall x, r * x = 0 -> x = 0
  proof: by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]; rfl

中文:
定理 mem_nonZeroDivisors_iff_left
  结论: r in M₀⁰ ↔ 对任意 x, r * x = 0 -> x = 0
  证明: by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]; rfl

Depends on / 依赖: nonZeroDivisorsLeft_eq_nonZeroDivisors
-/
theorem mem_nonZeroDivisors_iff_left : r in M₀⁰ ↔ forall x, r * x = 0 -> x = 0 := by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]; rfl

/--
theorem `mem_nonZeroDivisors_iff_right` / 定理 `mem_nonZeroDivisors_iff_right`

English:
theorem mem_nonZeroDivisors_iff_right
  statement: r in M₀⁰ ↔ forall x, x * r = 0 -> x = 0
  proof: by
  rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]; rfl

中文:
定理 mem_nonZeroDivisors_iff_right
  结论: r in M₀⁰ ↔ 对任意 x, x * r = 0 -> x = 0
  证明: by
  rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]; rfl

Depends on / 依赖: nonZeroDivisorsRight_eq_nonZeroDivisors
-/
theorem mem_nonZeroDivisors_iff_right : r in M₀⁰ ↔ forall x, x * r = 0 -> x = 0 := by
  rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]; rfl

/--
lemma `notMem_nonZeroDivisors_iff_left` / 引理 `notMem_nonZeroDivisors_iff_left`

English:
lemma notMem_nonZeroDivisors_iff_left
  statement: r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s != 0}.Nonempty
  proof: by
  simp [mem_nonZeroDivisors_iff_left, Set.nonempty_def]

中文:
引理 notMem_nonZeroDivisors_iff_left
  结论: r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s != 0}.非空
  证明: by
  simp [mem_nonZeroDivisors_iff_left, Set.nonempty_def]

Depends on / 依赖: Set.nonempty_def, mem_nonZeroDivisors_iff_left, nonempty_def
-/
lemma notMem_nonZeroDivisors_iff_left : r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s != 0}.Nonempty := by
  simp [mem_nonZeroDivisors_iff_left, Set.nonempty_def]

/--
lemma `notMem_nonZeroDivisors_iff_right` / 引理 `notMem_nonZeroDivisors_iff_right`

English:
lemma notMem_nonZeroDivisors_iff_right
  statement: r ∉ M₀⁰ ↔ {s | s * r = 0 ∧ s != 0}.Nonempty
  proof: by
  simp [mem_nonZeroDivisors_iff_right, Set.nonempty_def]

中文:
引理 notMem_nonZeroDivisors_iff_right
  结论: r ∉ M₀⁰ ↔ {s | s * r = 0 ∧ s != 0}.非空
  证明: by
  simp [mem_nonZeroDivisors_iff_right, Set.nonempty_def]

Depends on / 依赖: Set.nonempty_def, mem_nonZeroDivisors_iff_right, nonempty_def
-/
lemma notMem_nonZeroDivisors_iff_right : r ∉ M₀⁰ ↔ {s | s * r = 0 ∧ s != 0}.Nonempty := by
  simp [mem_nonZeroDivisors_iff_right, Set.nonempty_def]

/--
lemma `mul_left_mem_nonZeroDivisors_eq_zero_iff` / 引理 `mul_left_mem_nonZeroDivisors_eq_zero_iff`

English:
lemma mul_left_mem_nonZeroDivisors_eq_zero_iff
  given: (hr : r in M₀⁰)
  statement: r * x = 0 ↔ x = 0
  proof: by
  rw [mul_comm]; rw [mul_right_mem_nonZeroDivisors_eq_zero_iff hr]

@[simp]

中文:
引理 mul_left_mem_nonZeroDivisors_eq_zero_iff
  条件: (hr : r in M₀⁰)
  结论: r * x = 0 ↔ x = 0
  证明: by
  rw [mul_comm]; rw [mul_right_mem_nonZeroDivisors_eq_zero_iff hr]

@[simp]

Depends on / 依赖: mul_comm, mul_right_mem_nonZeroDivisors_eq_zero_iff
-/
lemma mul_left_mem_nonZeroDivisors_eq_zero_iff (hr : r in M₀⁰) : r * x = 0 ↔ x = 0 := by
  rw [mul_comm]; rw [mul_right_mem_nonZeroDivisors_eq_zero_iff hr]

@[simp]
/--
lemma `mul_left_coe_nonZeroDivisors_eq_zero_iff` / 引理 `mul_left_coe_nonZeroDivisors_eq_zero_iff`

English:
lemma mul_left_coe_nonZeroDivisors_eq_zero_iff
  given: {c : M₀⁰}
  statement: (c : M₀) * x = 0 ↔ x = 0
  proof: mul_left_mem_nonZeroDivisors_eq_zero_iff c.prop

中文:
引理 mul_left_coe_nonZeroDivisors_eq_zero_iff
  条件: {c : M₀⁰}
  结论: (c : M₀) * x = 0 ↔ x = 0
  证明: mul_left_mem_nonZeroDivisors_eq_zero_iff c.prop

Depends on / 依赖: c.prop, mul_left_mem_nonZeroDivisors_eq_zero_iff
-/
lemma mul_left_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : (c : M₀) * x = 0 ↔ x = 0 :=
  mul_left_mem_nonZeroDivisors_eq_zero_iff c.prop

/--
lemma `mul_mem_nonZeroDivisors` / 引理 `mul_mem_nonZeroDivisors`

English:
lemma mul_mem_nonZeroDivisors
  statement: a * b in M₀⁰ ↔ a in M₀⁰ ∧ b in M₀⁰ where
  proof: by
    rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    constructor <;> intro x h' <;> apply h.2
    · rw [← mul_assoc, h', zero_mul]
    · rw [mul_comm a b, ← mul_assoc, h', zero_mul]
  mpr := fun h => mul_mem h.1 h.2

中文:
引理 mul_mem_nonZeroDivisors
  结论: a * b in M₀⁰ ↔ a in M₀⁰ ∧ b in M₀⁰ where
  证明: by
    rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    constructor <;> intro x h' <;> apply h.2
    · rw [← mul_assoc, h', zero_mul]
    · rw [mul_comm a b, ← mul_assoc, h', zero_mul]
  mpr := fun h => mul_mem h.1 h.2

Depends on / 依赖: mul_assoc, mul_comm, mul_mem, nonZeroDivisorsRight_eq_nonZeroDivisors, zero_mul
-/
lemma mul_mem_nonZeroDivisors : a * b in M₀⁰ ↔ a in M₀⁰ ∧ b in M₀⁰ where
  mp h := by
    rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    constructor <;> intro x h' <;> apply h.2
    · rw [← mul_assoc, h', zero_mul]
    · rw [mul_comm a b, ← mul_assoc, h', zero_mul]
  mpr := fun h => mul_mem h.1 h.2

/--
theorem `nonZeroDivisors_dvd_iff_dvd_coe` / 定理 `nonZeroDivisors_dvd_iff_dvd_coe`

English:
theorem nonZeroDivisors_dvd_iff_dvd_coe
  given: {a b : M₀⁰}
  proof: ⟨fun ⟨c, hc⟩ => by simp_rw [hc, Submonoid.coe_mul, dvd_mul_right],
  fun ⟨c, hc⟩ => ⟨⟨c, (mul_mem_nonZeroDivisors.mp (hc ▸ b.prop)).2⟩,
    by simp_rw [Subtype.ext_iff, Submonoid.coe_mul, hc]⟩⟩

中文:
定理 nonZeroDivisors_dvd_iff_dvd_coe
  条件: {a b : M₀⁰}
  证明: ⟨fun ⟨c, hc⟩ => by simp_rw [hc, Submonoid.coe_mul, dvd_mul_right],
  fun ⟨c, hc⟩ => ⟨⟨c, (mul_mem_nonZeroDivisors.mp (hc ▸ b.prop)).2⟩,
    by simp_rw [Subtype.ext_iff, Submonoid.coe_mul, hc]⟩⟩

Depends on / 依赖: Submonoid, Submonoid.coe_mul, Subtype, Subtype.ext_iff, b.prop, coe_mul, dvd_mul_right, ext_iff, mul_mem_nonZeroDivisors, mul_mem_nonZeroDivisors.mp, simp_rw
-/
theorem nonZeroDivisors_dvd_iff_dvd_coe {a b : M₀⁰} :
    a ∣ b ↔ (a : M₀) ∣ (b : M₀) :=
  ⟨fun ⟨c, hc⟩ => by simp_rw [hc, Submonoid.coe_mul, dvd_mul_right],
  fun ⟨c, hc⟩ => ⟨⟨c, (mul_mem_nonZeroDivisors.mp (hc ▸ b.prop)).2⟩,
    by simp_rw [Subtype.ext_iff, Submonoid.coe_mul, hc]⟩⟩

/--
lemma `prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors` / 引理 `prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors`

English:
lemma prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors
  proof: s.prod_induction _ _ (fun _ _ => and_imp.mp mul_mem_nonZeroDivisors.mpr) (one_mem _) h

中文:
引理 prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors
  证明: s.prod_induction _ _ (fun _ _ => and_imp.mp mul_mem_nonZeroDivisors.mpr) (one_mem _) h

Depends on / 依赖: and_imp, and_imp.mp, mul_mem_nonZeroDivisors, mul_mem_nonZeroDivisors.mpr, one_mem, prod_induction, s.prod_induction
-/
lemma prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors
    {ι : Type*} {s : Finset ι} {f : ι -> M₀} (h : forall i in s, f i in M₀⁰) :
    ∏ i in s, f i in M₀⁰ :=
  s.prod_induction _ _ (fun _ _ => and_imp.mp mul_mem_nonZeroDivisors.mpr) (one_mem _) h

end CommMonoidWithZero

section GroupWithZero
variable {G₀ : Type*} [GroupWithZero G₀] {x : G₀}

/-- Canonical isomorphism between the non-zero-divisors and units of a group with zero. -/
@[simps]
/--
Definition of `nonZeroDivisorsEquivUnits` / `nonZeroDivisorsEquivUnits` 的定义

English:
definition nonZeroDivisorsEquivUnits
  signature: : G₀⁰ ≃* G₀ˣ where
  body: .mk0 _ mem_nonZeroDivisors_iff_ne_zero.1 u.2
  invFun u := ⟨u, u.isUnit.mem_nonZeroDivisors⟩
  right_inv u := by simp
  map_mul' u v := by simp

中文:
定义 nonZeroDivisorsEquivUnits
  签名: : G₀⁰ ≃* G₀ˣ where
  定义体: .mk0 _ mem_nonZeroDivisors_iff_ne_zero.1 u.2
  invFun u := ⟨u, u.isUnit.mem_nonZeroDivisors⟩
  right_inv u := by simp
  map_mul' u v := by simp

Depends on / 依赖: mem_nonZeroDivisors_iff_ne_zero
-/
noncomputable def nonZeroDivisorsEquivUnits : G₀⁰ ≃* G₀ˣ where
toFun u := .mk0 _ mem_nonZeroDivisors_iff_ne_zero.1 u.2
  invFun u := ⟨u, u.isUnit.mem_nonZeroDivisors⟩
  right_inv u := by simp
  map_mul' u v := by simp

/--
lemma `isUnit_of_mem_nonZeroDivisors` / 引理 `isUnit_of_mem_nonZeroDivisors`

English:
lemma isUnit_of_mem_nonZeroDivisors
  given: (hx : x in nonZeroDivisors G₀)
  statement: IsUnit x
  proof: (nonZeroDivisorsEquivUnits ⟨x, hx⟩).isUnit

中文:
引理 isUnit_of_mem_nonZeroDivisors
  条件: (hx : x in nonZeroDivisors G₀)
  结论: 是单位 x
  证明: (nonZeroDivisorsEquivUnits ⟨x, hx⟩).isUnit

Depends on / 依赖: isUnit, nonZeroDivisorsEquivUnits
-/
lemma isUnit_of_mem_nonZeroDivisors (hx : x in nonZeroDivisors G₀) : IsUnit x :=
  (nonZeroDivisorsEquivUnits ⟨x, hx⟩).isUnit

end GroupWithZero

section nonZeroSMulDivisors

open nonZeroSMulDivisors

variable {M₀ M : Type*} [MonoidWithZero M₀] [Zero M] [MulAction M₀ M] {x : M₀}

/--
lemma `mem_nonZeroSMulDivisors_iff` / 引理 `mem_nonZeroSMulDivisors_iff`

English:
lemma mem_nonZeroSMulDivisors_iff
  statement: x in M₀⁰[M] ↔ forall (m : M), x • m = 0 -> m = 0
  proof: Iff.rfl

中文:
引理 mem_nonZeroSMulDivisors_iff
  结论: x in M₀⁰[M] ↔ 对任意 (m : M), x • m = 0 -> m = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_nonZeroSMulDivisors_iff : x in M₀⁰[M] ↔ forall (m : M), x • m = 0 -> m = 0 := Iff.rfl

end nonZeroSMulDivisors

open scoped nonZeroDivisors

variable {M₀}

section MonoidWithZero
variable [MonoidWithZero M₀] {a b : M₀⁰}

/-- The units of the monoid of non-zero divisors of `M₀` are equivalent to the units of `M₀`. -/
@[simps]
/--
Definition of `unitsNonZeroDivisorsEquiv` / `unitsNonZeroDivisorsEquiv` 的定义

English:
definition unitsNonZeroDivisorsEquiv
  signature: : M₀⁰ˣ ≃* M₀ˣ where
  body: Units.map M₀⁰.subtype
  invFun u := ⟨⟨u, u.isUnit.mem_nonZeroDivisors⟩, ⟨(u⁻¹ : M₀ˣ), u⁻¹.isUnit.mem_nonZeroDivisors⟩,
    by simp, by simp⟩

中文:
定义 unitsNonZeroDivisorsEquiv
  签名: : M₀⁰ˣ ≃* M₀ˣ where
  定义体: Units.map M₀⁰.subtype
  invFun u := ⟨⟨u, u.isUnit.mem_nonZeroDivisors⟩, ⟨(u⁻¹ : M₀ˣ), u⁻¹.isUnit.mem_nonZeroDivisors⟩,
    by simp, by simp⟩

Depends on / 依赖: Units.map, subtype
-/
def unitsNonZeroDivisorsEquiv : M₀⁰ˣ ≃* M₀ˣ where
  __ := Units.map M₀⁰.subtype
  invFun u := ⟨⟨u, u.isUnit.mem_nonZeroDivisors⟩, ⟨(u⁻¹ : M₀ˣ), u⁻¹.isUnit.mem_nonZeroDivisors⟩,
    by simp, by simp⟩

/--
lemma `nonZeroDivisors.associated_coe` / 引理 `nonZeroDivisors.associated_coe`

English:
lemma nonZeroDivisors.associated_coe
  statement: Associated (a : M₀) b ↔ Associated a b
  proof: unitsNonZeroDivisorsEquiv.symm.exists_congr_left.trans by simp [Associated]; norm_cast

中文:
引理 nonZeroDivisors.associated_coe
  结论: Associated (a : M₀) b ↔ Associated a b
  证明: unitsNonZeroDivisorsEquiv.symm.exists_congr_left.trans by simp [Associated]; norm_cast
-/
@[simp, norm_cast] lemma nonZeroDivisors.associated_coe : Associated (a : M₀) b ↔ Associated a b :=
unitsNonZeroDivisorsEquiv.symm.exists_congr_left.trans by simp [Associated]; norm_cast

end MonoidWithZero

section CommMonoidWithZero
variable {M₀ : Type*} [CommMonoidWithZero M₀] {a : M₀}

/--
theorem `mk_mem_nonZeroDivisors_associates` / 定理 `mk_mem_nonZeroDivisors_associates`

English:
theorem mk_mem_nonZeroDivisors_associates
  statement: Associates.mk a in (Associates M₀)⁰ ↔ a in M₀⁰
  proof: by
  rw [mem_nonZeroDivisors_iff_right]; rw [mem_nonZeroDivisors_iff_right]
  contrapose!
  constructor
  · rintro ⟨⟨x⟩, hx₁, hx₂⟩
    refine ⟨x, ?_, ?_⟩
    · rwa [← Associates.mk_eq_zero, ← Associates.mk_mul_mk, ← Associates.quot_mk_eq_mk]
    · rwa [← Associates.mk_ne_zero, ← Associates.quot_mk_e

中文:
定理 mk_mem_nonZeroDivisors_associates
  结论: Associates.mk a in (Associates M₀)⁰ ↔ a in M₀⁰
  证明: by
  rw [mem_nonZeroDivisors_iff_right]; rw [mem_nonZeroDivisors_iff_right]
  contrapose!
  constructor
  · rintro ⟨⟨x⟩, hx₁, hx₂⟩
    refine ⟨x, ?_, ?_⟩
    · rwa [← Associates.mk_eq_zero, ← Associates.mk_mul_mk, ← Associates.quot_mk_eq_mk]
    · rwa [← Associates.mk_ne_zero, ← Associates.quot_mk_e

Depends on / 依赖: Associates, Associates.mk, Associates.mk_eq_zero, Associates.mk_mul_mk, Associates.mk_ne_zero, Associates.mk_zero, Associates.quot_mk_eq_mk, contrapose, mem_nonZeroDivisors_iff_right, mk_eq_zero, mk_mul_mk, mk_ne_zero, mk_zero, quot_mk_eq_mk
-/
theorem mk_mem_nonZeroDivisors_associates : Associates.mk a in (Associates M₀)⁰ ↔ a in M₀⁰ := by
  rw [mem_nonZeroDivisors_iff_right]; rw [mem_nonZeroDivisors_iff_right]
  contrapose!
  constructor
  · rintro ⟨⟨x⟩, hx₁, hx₂⟩
    refine ⟨x, ?_, ?_⟩
    · rwa [← Associates.mk_eq_zero, ← Associates.mk_mul_mk, ← Associates.quot_mk_eq_mk]
    · rwa [← Associates.mk_ne_zero, ← Associates.quot_mk_eq_mk]
  · refine fun ⟨b, hb₁, hb₂⟩ => ⟨Associates.mk b, ?_, by rwa [Associates.mk_ne_zero]⟩
    rw [Associates.mk_mul_mk]; rw [hb₁]; rw [Associates.mk_zero]

/--
Definition of `associatesNonZeroDivisorsEquiv` / `associatesNonZeroDivisorsEquiv` 的定义

English:
definition associatesNonZeroDivisorsEquiv
  signature: : (Associates M₀)⁰ ≃* Associates M₀⁰ where
  body: .subtypeQuotientEquivQuotientSubtype _ (s₂ := Associated.setoid _)
    (· in nonZeroDivisors _)
    (by simp [mem_nonZeroDivisors_iff, Quotient.forall, Associates.mk_mul_mk])
    (by simp +instances [Associated.setoid])
  map_mul' := by simp [Quotient.forall, Associates.mk_mul_mk]

@[simp]

中文:
定义 associatesNonZeroDivisorsEquiv
  签名: : (Associates M₀)⁰ ≃* Associates M₀⁰ where
  定义体: .subtypeQuotientEquivQuotientSubtype _ (s₂ := Associated.setoid _)
    (· in nonZeroDivisors _)
    (by simp [mem_nonZeroDivisors_iff, Quotient.forall, Associates.mk_mul_mk])
    (by simp +instances [Associated.setoid])
  map_mul' := by simp [Quotient.forall, Associates.mk_mul_mk]

@[simp]

Depends on / 依赖: Associated, Associated.setoid, setoid, subtypeQuotientEquivQuotientSubtype
-/
def associatesNonZeroDivisorsEquiv : (Associates M₀)⁰ ≃* Associates M₀⁰ where
  toEquiv := .subtypeQuotientEquivQuotientSubtype _ (s₂ := Associated.setoid _)
    (· in nonZeroDivisors _)
    (by simp [mem_nonZeroDivisors_iff, Quotient.forall, Associates.mk_mul_mk])
    (by simp +instances [Associated.setoid])
  map_mul' := by simp [Quotient.forall, Associates.mk_mul_mk]

@[simp]
/--
lemma `associatesNonZeroDivisorsEquiv_mk_mk` / 引理 `associatesNonZeroDivisorsEquiv_mk_mk`

English:
lemma associatesNonZeroDivisorsEquiv_mk_mk
  given: (a : M₀) (ha)
  proof: rfl

@[simp]

中文:
引理 associatesNonZeroDivisorsEquiv_mk_mk
  条件: (a : M₀) (ha)
  证明: rfl

@[simp]
-/
lemma associatesNonZeroDivisorsEquiv_mk_mk (a : M₀) (ha) :
    associatesNonZeroDivisorsEquiv ⟨⟦a⟧, ha⟩ = ⟦⟨a, mk_mem_nonZeroDivisors_associates.1 ha⟩⟧ := rfl

@[simp]
/--
lemma `associatesNonZeroDivisorsEquiv_symm_mk_mk` / 引理 `associatesNonZeroDivisorsEquiv_symm_mk_mk`

English:
lemma associatesNonZeroDivisorsEquiv_symm_mk_mk
  given: (a : M₀) (ha)
  proof: rfl

中文:
引理 associatesNonZeroDivisorsEquiv_symm_mk_mk
  条件: (a : M₀) (ha)
  证明: rfl
-/
lemma associatesNonZeroDivisorsEquiv_symm_mk_mk (a : M₀) (ha) :
    associatesNonZeroDivisorsEquiv.symm ⟦⟨a, ha⟩⟧ = ⟨⟦a⟧, mk_mem_nonZeroDivisors_associates.2 ha⟩ :=
  rfl

end CommMonoidWithZero
