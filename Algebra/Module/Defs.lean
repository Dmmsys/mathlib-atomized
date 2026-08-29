/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Ring.Defs

/-!
# Modules over a ring

In this file we define

* `Module R M` : an additive commutative monoid `M` is a `Module` over a
  `Semiring R` if for `r : R` and `x : M` their "scalar multiplication" `r • x : M` is defined, and
  the operation `•` satisfies some natural associativity and distributivity axioms similar to those
  on a ring.

## Implementation notes

In typical mathematical usage, our definition of `Module` corresponds to "semimodule", and the
word "module" is reserved for `Module R M` where `R` is a `Ring` and `M` an `AddCommGroup`.
If `R` is a `Field` and `M` an `AddCommGroup`, `M` would be called an `R`-vector space.
Since those assumptions can be made by changing the typeclasses applied to `R` and `M`,
without changing the axioms in `Module`, mathlib calls everything a `Module`.

In older versions of mathlib3, we had separate abbreviations for semimodules and vector spaces.
This caused inference issues in some cases, while not providing any real advantages, so we decided
to use a canonical `Module` typeclass throughout.

## Tags

semimodule, module, vector space
-/

public section

assert_not_exists Field Invertible Pi.single_smul₀ RingHom Set.indicator Multiset Units

open Function Set

universe u v

variable {R S M M₂ : Type*}

/-- A module is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
@[ext]
/--
Definition of `Module` / `Module` 的定义

English:
class Module
  parameters: (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M]
  axioms and operations (2):
    - add_smul : forall (r s : R) (x : M), (r + s) • x = r • x + s • x
    - zero_smul : forall x : M, (0 : R) • x = 0

中文:
类 Module
  参数: (R : 类型u) (M : 类型v) [Semiring R] [AddCommMonoid M]
  公理与运算 (2 个):
    - add_smul : 对任意 (r s : R) (x : M), (r + s) • x = r • x + s • x
    - zero_smul : 对任意 x : M, (0 : R) • x = 0
-/
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : forall (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : forall x : M, (0 : R) • x = 0

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

-- see Note [lower instance priority]
/-- A module over a semiring automatically inherits a `MulActionWithZero` structure. -/
instance (priority := 100) Module.toMulActionWithZero
    {R M} {_ : Semiring R} {_ : AddCommMonoid M} [Module R M] : MulActionWithZero R M :=
  { (inferInstance : MulAction R M) with
    smul_zero := smul_zero
    zero_smul := Module.zero_smul }

/--
theorem `add_smul` / 定理 `add_smul`

English:
theorem add_smul
  statement: (r + s) • x = r • x + s • x
  proof: Module.add_smul r s x

中文:
定理 add_smul
  结论: (r + s) • x = r • x + s • x
  证明: Module.add_smul r s x

Depends on / 依赖: Module, Module.add_smul, add_smul
-/
theorem add_smul : (r + s) • x = r • x + s • x :=
  Module.add_smul r s x

/--
theorem `Convex.combo_self` / 定理 `Convex.combo_self`

English:
theorem Convex.combo_self
  given: {a b : R} (h : a + b = 1) (x : M)
  statement: a • x + b • x = x
  proof: by
  rw [← add_smul]; rw [h]; rw [one_smul]

中文:
定理 Convex.combo_self
  条件: {a b : R} (h : a + b = 1) (x : M)
  结论: a • x + b • x = x
  证明: by
  rw [← add_smul]; rw [h]; rw [one_smul]

Depends on / 依赖: add_smul, one_smul
-/
theorem Convex.combo_self {a b : R} (h : a + b = 1) (x : M) : a • x + b • x = x := by
  rw [← add_smul]; rw [h]; rw [one_smul]

variable (R)

/--
theorem `two_smul` / 定理 `two_smul`

English:
theorem two_smul
  statement: (2 : R) • x = x + x
  proof: by rw [← one_add_one_eq_two, add_smul, one_smul]

中文:
定理 two_smul
  结论: (2 : R) • x = x + x
  证明: by rw [← one_add_one_eq_two, add_smul, one_smul]

Depends on / 依赖: add_smul, one_add_one_eq_two, one_smul
-/
theorem two_smul : (2 : R) • x = x + x := by rw [← one_add_one_eq_two, add_smul, one_smul]

/--
Definition of `Function.Injective.module` / `Function.Injective.module` 的定义

English:
abbreviation Function.Injective.module
  signature: [AddCommMonoid M₂] [SMul R M₂] (f : M₂ ->+ M)
  body: { hf.distribMulAction f smul with
add_smul := fun c₁ c₂ x => hf by simp only [smul, f.map_add, add_smul]
zero_smul := fun x => hf by simp only [smul, zero_smul, f.map_zero] }

中文:
缩写 Function.Injective.module
  签名: [AddCommMonoid M₂] [SMul R M₂] (f : M₂ ->+ M)
  定义体: { hf.distribMulAction f smul with
add_smul := fun c₁ c₂ x => hf by simp only [smul, f.map_add, add_smul]
zero_smul := fun x => hf by simp only [smul, zero_smul, f.map_zero] }
-/
protected abbrev Function.Injective.module [AddCommMonoid M₂] [SMul R M₂] (f : M₂ ->+ M)
    (hf : Injective f) (smul : forall (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { hf.distribMulAction f smul with
add_smul := fun c₁ c₂ x => hf by simp only [smul, f.map_add, add_smul]
zero_smul := fun x => hf by simp only [smul, zero_smul, f.map_zero] }

/--
Definition of `Function.Surjective.module` / `Function.Surjective.module` 的定义

English:
abbreviation Function.Surjective.module
  signature: [AddCommMonoid M₂] [SMul R M₂] (f : M ->+ M₂)
  body: { toDistribMulAction := hf.distribMulAction f smul
    add_smul := fun c₁ c₂ x => by
      rcases hf x with ⟨x, rfl⟩
      simp only [add_smul, ← smul, ← f.map_add]
    zero_smul := fun x => by
      rcases hf x with ⟨x, rfl⟩
      rw [← f.map_zero]; rw [← smul]; rw [zero_smul] }

中文:
缩写 Function.Surjective.module
  签名: [AddCommMonoid M₂] [SMul R M₂] (f : M ->+ M₂)
  定义体: { toDistribMulAction := hf.distribMulAction f smul
    add_smul := fun c₁ c₂ x => by
      rcases hf x with ⟨x, rfl⟩
      simp only [add_smul, ← smul, ← f.map_add]
    zero_smul := fun x => by
      rcases hf x with ⟨x, rfl⟩
      rw [← f.map_zero]; rw [← smul]; rw [zero_smul] }
-/
protected abbrev Function.Surjective.module [AddCommMonoid M₂] [SMul R M₂] (f : M ->+ M₂)
    (hf : Surjective f) (smul : forall (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { toDistribMulAction := hf.distribMulAction f smul
    add_smul := fun c₁ c₂ x => by
      rcases hf x with ⟨x, rfl⟩
      simp only [add_smul, ← smul, ← f.map_add]
    zero_smul := fun x => by
      rcases hf x with ⟨x, rfl⟩
      rw [← f.map_zero]; rw [← smul]; rw [zero_smul] }

variable {R}

/--
theorem `Module.eq_zero_of_zero_eq_one` / 定理 `Module.eq_zero_of_zero_eq_one`

English:
theorem Module.eq_zero_of_zero_eq_one
  given: (zero_eq_one : (0 : R) = 1)
  statement: x = 0
  proof: by
  rw [← one_smul R x]; rw [← zero_eq_one]; rw [zero_smul]

@[simp]

中文:
定理 Module.eq_zero_of_zero_eq_one
  条件: (zero_eq_one : (0 : R) = 1)
  结论: x = 0
  证明: by
  rw [← one_smul R x]; rw [← zero_eq_one]; rw [zero_smul]

@[simp]

Depends on / 依赖: one_smul, zero_eq_one, zero_smul
-/
theorem Module.eq_zero_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : x = 0 := by
  rw [← one_smul R x]; rw [← zero_eq_one]; rw [zero_smul]

@[simp]
/--
theorem `smul_add_one_sub_smul` / 定理 `smul_add_one_sub_smul`

English:
theorem smul_add_one_sub_smul
  given: {R : Type*} [Ring R] [Module R M] {r : R} {m : M}
  proof: by rw [← add_smul, add_sub_cancel, one_smul]

中文:
定理 smul_add_one_sub_smul
  条件: {R : 类型} [Ring R] [Module R M] {r : R} {m : M}
  证明: by rw [← add_smul, add_sub_cancel, one_smul]

Depends on / 依赖: add_smul, add_sub_cancel, one_smul
-/
theorem smul_add_one_sub_smul {R : Type*} [Ring R] [Module R M] {r : R} {m : M} :
    r • m + (1 - r) • m = m := by rw [← add_smul, add_sub_cancel, one_smul]

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [AddCommGroup M]

/--
theorem `Convex.combo_eq_smul_sub_add` / 定理 `Convex.combo_eq_smul_sub_add`

English:
theorem Convex.combo_eq_smul_sub_add
  given: [Module R M] {x y : M} {a b : R} (h : a + b = 1)
  proof: calc
    a • x + b • y = b • y - b • x + (a • x + b • x) := by rw [sub_add_add_cancel, add_comm]
    _ = b • (y - x) + x := by rw [smul_sub, Convex.combo_self h]

中文:
定理 Convex.combo_eq_smul_sub_add
  条件: [Module R M] {x y : M} {a b : R} (h : a + b = 1)
  证明: calc
    a • x + b • y = b • y - b • x + (a • x + b • x) := by rw [sub_add_add_cancel, add_comm]
    _ = b • (y - x) + x := by rw [smul_sub, Convex.combo_self h]

Depends on / 依赖: Convex, Convex.combo_self, add_comm, combo_self, smul_sub, sub_add_add_cancel
-/
theorem Convex.combo_eq_smul_sub_add [Module R M] {x y : M} {a b : R} (h : a + b = 1) :
    a • x + b • y = b • (y - x) + x :=
  calc
    a • x + b • y = b • y - b • x + (a • x + b • x) := by rw [sub_add_add_cancel, add_comm]
    _ = b • (y - x) + x := by rw [smul_sub, Convex.combo_self h]

end AddCommGroup

-- We'll later use this to show `Module ℕ M` and `Module ℤ M` are subsingletons.
/--
theorem `Module.ext'` / 定理 `Module.ext'`

English:
theorem Module.ext'
  statement: {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] (P Q : Module R M)
  proof: by
  ext
  exact w _ _

中文:
定理 Module.ext'
  结论: {R : 类型} [Semiring R] {M : 类型} [AddCommMonoid M] (P Q : Module R M)
  证明: by
  ext
  exact w _ _
-/
theorem Module.ext' {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] (P Q : Module R M)
    (w : forall (r : R) (m : M), (haveI := P; r • m) = (haveI := Q; r • m)) :
    P = Q := by
  ext
  exact w _ _

section Module

variable [Ring R] [AddCommGroup M] [Module R M] (r : R) (x : M)

@[simp]
/--
theorem `neg_smul` / 定理 `neg_smul`

English:
theorem neg_smul
  statement: -r • x = -(r • x)
  proof: eq_neg_of_add_eq_zero_left by rw [← add_smul, neg_add_cancel, zero_smul]

中文:
定理 neg_smul
  结论: -r • x = -(r • x)
  证明: eq_neg_of_add_eq_zero_left by rw [← add_smul, neg_add_cancel, zero_smul]

Depends on / 依赖: add_smul, eq_neg_of_add_eq_zero_left, neg_add_cancel, zero_smul
-/
theorem neg_smul : -r • x = -(r • x) :=
eq_neg_of_add_eq_zero_left by rw [← add_smul, neg_add_cancel, zero_smul]

/--
theorem `neg_smul_neg` / 定理 `neg_smul_neg`

English:
theorem neg_smul_neg
  statement: -r • -x = r • x
  proof: by rw [neg_smul, smul_neg, neg_neg]

中文:
定理 neg_smul_neg
  结论: -r • -x = r • x
  证明: by rw [neg_smul, smul_neg, neg_neg]

Depends on / 依赖: neg_neg, neg_smul, smul_neg
-/
theorem neg_smul_neg : -r • -x = r • x := by rw [neg_smul, smul_neg, neg_neg]

variable (R)

/--
theorem `neg_one_smul` / 定理 `neg_one_smul`

English:
theorem neg_one_smul
  given: (x : M)
  statement: (-1 : R) • x = -x
  proof: by simp

中文:
定理 neg_one_smul
  条件: (x : M)
  结论: (-1 : R) • x = -x
  证明: by simp
-/
theorem neg_one_smul (x : M) : (-1 : R) • x = -x := by simp

variable {R}

/--
theorem `sub_smul` / 定理 `sub_smul`

English:
theorem sub_smul
  given: (r s : R) (y : M)
  statement: (r - s) • y = r • y - s • y
  proof: by
  simp [add_smul, sub_eq_add_neg]

中文:
定理 sub_smul
  条件: (r s : R) (y : M)
  结论: (r - s) • y = r • y - s • y
  证明: by
  simp [add_smul, sub_eq_add_neg]

Depends on / 依赖: add_smul, sub_eq_add_neg
-/
theorem sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y := by
  simp [add_smul, sub_eq_add_neg]

end Module

/--
theorem `Module.subsingleton` / 定理 `Module.subsingleton`

English:
theorem Module.subsingleton
  statement: (R M : Type*) [MonoidWithZero R] [Subsingleton R] [Zero M]
  proof: MulActionWithZero.subsingleton R M

中文:
定理 Module.subsingleton
  结论: (R M : 类型) [MonoidWithZero R] [Subsingleton R] [Zero M]
  证明: MulActionWithZero.subsingleton R M
-/
protected theorem Module.subsingleton (R M : Type*) [MonoidWithZero R] [Subsingleton R] [Zero M]
    [MulActionWithZero R M] : Subsingleton M :=
  MulActionWithZero.subsingleton R M

/--
theorem `Module.nontrivial` / 定理 `Module.nontrivial`

English:
theorem Module.nontrivial
  statement: (R M : Type*) [MonoidWithZero R] [Nontrivial M] [Zero M]
  proof: MulActionWithZero.nontrivial R M

中文:
定理 Module.nontrivial
  结论: (R M : 类型) [MonoidWithZero R] [Nontrivial M] [Zero M]
  证明: MulActionWithZero.nontrivial R M
-/
protected theorem Module.nontrivial (R M : Type*) [MonoidWithZero R] [Nontrivial M] [Zero M]
    [MulActionWithZero R M] : Nontrivial R :=
  MulActionWithZero.nontrivial R M

-- see Note [higher instance priority]
instance (priority := 1100) Semiring.toModule [Semiring R] : Module R R where
  smul_add := mul_add
  add_smul := add_mul
  zero_smul := zero_mul
  smul_zero := mul_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] : DistribSMul R R where
  body: left_distrib

中文:
实例 [NonUnitalNonAssocSemiring
  签名: R] : DistribSMul R R where
  定义体: left_distrib

Depends on / 依赖: left_distrib
-/
instance [NonUnitalNonAssocSemiring R] : DistribSMul R R where
  smul_add := left_distrib
