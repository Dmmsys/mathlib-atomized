/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Algebra.Unitization

/-!
# Quasiregularity and quasispectrum

For a non-unital ring `R`, an element `r : R` is *quasiregular* if it is invertible in the monoid
`(R, ∘)` where `x ∘ y := y + x + x * y` with identity `0 : R`. We implement this both as a type
synonym `PreQuasiregular` which has an associated `Monoid` instance (note: *not* an `AddMonoid`
instance despite the fact that `0 : R` is the identity in this monoid) so that one may access
the quasiregular elements of `R` as `(PreQuasiregular R)ˣ`, but also as a predicate
`IsQuasiregular`.

Quasiregularity is closely tied to invertibility. Indeed, `(PreQuasiregular A)ˣ` is isomorphic to
the subgroup of `Unitization R A` whose scalar part is `1`, whenever `A` is a non-unital
`R`-algebra, and moreover this isomorphism is implemented by the map
`(x : A) ↦ (1 + x : Unitization R A)`. It is because of this isomorphism, and the associated ties
with multiplicative invertibility, that we choose a `Monoid` (as opposed to an `AddMonoid`)
structure on `PreQuasiregular`. In addition, in unital rings, we even have
`IsQuasiregular x ↔ IsUnit (1 + x)`.

The *quasispectrum* of `a : A` (with respect to `R`) is defined in terms of quasiregularity, and
this is the natural analogue of the `spectrum` for non-unital rings. Indeed, it is true that
`quasispectrum R a = spectrum R a ∪ {0}` when `A` is unital.

In Mathlib, the quasispectrum is the domain of the continuous functions associated to the
*non-unital* continuous functional calculus.

## Main definitions

+ `PreQuasiregular R`: a structure wrapping `R` that inherits a distinct `Monoid` instance when `R`
  is a non-unital semiring.
+ `Unitization.unitsFstOne`: the subgroup with carrier `{ x : (Unitization R A)ˣ | x.fst = 1 }`.
+ `unitsFstOne_mulEquiv_quasiregular`: the group isomorphism between
  `Unitization.unitsFstOne` and the units of `PreQuasiregular` (i.e., the quasiregular elements)
  which sends `(1, x) ↦ x`.
+ `IsQuasiregular x`: the proposition that `x : R` is a unit with respect to the monoid structure on
  `PreQuasiregular R`, i.e., there is some `u : (PreQuasiregular R)ˣ` such that `u.val` is
  identified with `x` (via the natural equivalence between `R` and `PreQuasiregular R`).
+ `quasispectrum R a`: in an algebra over the semifield `R`, this is the set
  `{r : R | (hr : IsUnit r) → ¬ IsQuasiregular (-(hr.unit⁻¹ • a))}`, which should be thought of
  as a version of the `spectrum` which is applicable in non-unital algebras.

## Main theorems

+ `isQuasiregular_iff_isUnit`: in a unital ring, `x` is quasiregular if and only if `1 + x` is
  a unit.
+ `quasispectrum_eq_spectrum_union_zero`: in a unital algebra `A` over a semifield `R`, the
  quasispectrum of `a : A` is the `spectrum` with zero added.
+ `Unitization.isQuasiregular_inr_iff`: `a : A` is quasiregular if and only if it is quasiregular
  in `Unitization R A` (via the coercion `Unitization.inr`).
+ `Unitization.quasispectrum_eq_spectrum_inr`: the quasispectrum of `a` in a non-unital `R`-algebra
  `A` is precisely the spectrum of `a` in `Unitization R A` (via the coercion `Unitization.inr`).
-/

@[expose] public section

/--
Definition of `PreQuasiregular` / `PreQuasiregular` 的定义

English:
structure PreQuasiregular
  parameters: (R : Type*)
  axioms and operations (1):
    - val : R

中文:
结构 PreQuasiregular
  参数: (R : 类型)
  公理与运算 (1 个):
    - val : R

Depends on / 依赖: lift_comp_comm_eq
-/
structure PreQuasiregular (R : Type*) where
  /-- The value wrapped into a term of `PreQuasiregular`. -/
  val : R

namespace PreQuasiregular

variable {R : Type*} [NonUnitalSemiring R]

/-- The identity map between `R` and `PreQuasiregular R`. -/
@[simps]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : R ≃ PreQuasiregular R where
  body: .mk
  invFun := PreQuasiregular.val

中文:
定义 equiv
  签名: : R ≃ PreQuasiregular R where
  定义体: .mk
  invFun := PreQuasiregular.val

Depends on / 依赖: _comp_comm
-/
def equiv : R ≃ PreQuasiregular R where
  toFun := .mk
  invFun := PreQuasiregular.val

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (PreQuasiregular R) where
  body: equiv 0

@[simp]

中文:
实例 instOne
  签名: : 幺 (PreQuasiregular R) where
  定义体: equiv 0

@[simp]
-/
instance instOne : One (PreQuasiregular R) where
  one := equiv 0

@[simp]
/--
lemma `val_one` / 引理 `val_one`

English:
lemma val_one
  statement: (1 : PreQuasiregular R).val = 0
  proof: rfl

中文:
引理 val_one
  结论: (1 : PreQuasiregular R).val = 0
  证明: rfl
-/
lemma val_one : (1 : PreQuasiregular R).val = 0 := rfl

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (PreQuasiregular R) where
  body: .mk (y.val + x.val + x.val * y.val)

@[simp]

中文:
实例 instMul
  签名: : 乘法 (PreQuasiregular R) where
  定义体: .mk (y.val + x.val + x.val * y.val)

@[simp]

Depends on / 依赖: Algebra, Algebra.ofModule, mul_smul_comm, ofModule, smul_mul_assoc, x.val, y.val
-/
instance instMul : Mul (PreQuasiregular R) where
  mul x y := .mk (y.val + x.val + x.val * y.val)

@[simp]
/--
lemma `val_mul` / 引理 `val_mul`

English:
lemma val_mul
  given: (x y : PreQuasiregular R)
  statement: (x * y).val = y.val + x.val + x.val * y.val
  proof: rfl

中文:
引理 val_mul
  条件: (x y : PreQuasiregular R)
  结论: (x * y).val = y.val + x.val + x.val * y.val
  证明: rfl
-/
lemma val_mul (x y : PreQuasiregular R) : (x * y).val = y.val + x.val + x.val * y.val := rfl

/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (PreQuasiregular R) where
  body: equiv 0
  mul x y := .mk (y.val + x.val + x.val * y.val)
mul_one _ := equiv.symm.injective by simp [-EmbeddingLike.apply_eq_iff_eq]
one_mul _ := equiv.symm.injective by simp [-EmbeddingLike.apply_eq_iff_eq]
mul_assoc x y z := equiv.symm.injective by simp [mul_add, add_mul, mul_assoc]; abel

@[simp]

中文:
实例 instMonoid
  签名: : 幺半群 (PreQuasiregular R) where
  定义体: equiv 0
  mul x y := .mk (y.val + x.val + x.val * y.val)
mul_one _ := equiv.symm.injective by simp [-EmbeddingLike.apply_eq_iff_eq]
one_mul _ := equiv.symm.injective by simp [-EmbeddingLike.apply_eq_iff_eq]
mul_assoc x y z := equiv.symm.injective by simp [mul_add, add_mul, mul_assoc]; abel

@[simp]
-/
instance instMonoid : Monoid (PreQuasiregular R) where
  one := equiv 0
  mul x y := .mk (y.val + x.val + x.val * y.val)
mul_one _ := equiv.symm.injective by simp [-EmbeddingLike.apply_eq_iff_eq]
one_mul _ := equiv.symm.injective by simp [-EmbeddingLike.apply_eq_iff_eq]
mul_assoc x y z := equiv.symm.injective by simp [mul_add, add_mul, mul_assoc]; abel

@[simp]
/--
lemma `inv_add_add_mul_eq_zero` / 引理 `inv_add_add_mul_eq_zero`

English:
lemma inv_add_add_mul_eq_zero
  given: (u : (PreQuasiregular R)ˣ)
  proof: by
  simpa [-Units.mul_inv] using congr($(u.mul_inv).val)

@[simp]

中文:
引理 inv_add_add_mul_eq_zero
  条件: (u : (PreQuasiregular R)ˣ)
  证明: by
  simpa [-Units.mul_inv] using congr($(u.mul_inv).val)

@[simp]

Depends on / 依赖: Units.mul_inv, mul_inv, u.mul_inv
-/
lemma inv_add_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u⁻¹.val.val + u.val.val + u.val.val * u⁻¹.val.val = 0 := by
  simpa [-Units.mul_inv] using congr($(u.mul_inv).val)

@[simp]
/--
lemma `add_inv_add_mul_eq_zero` / 引理 `add_inv_add_mul_eq_zero`

English:
lemma add_inv_add_mul_eq_zero
  given: (u : (PreQuasiregular R)ˣ)
  proof: by
  simpa [-Units.inv_mul] using congr($(u.inv_mul).val)

中文:
引理 add_inv_add_mul_eq_zero
  条件: (u : (PreQuasiregular R)ˣ)
  证明: by
  simpa [-Units.inv_mul] using congr($(u.inv_mul).val)

Depends on / 依赖: Units.inv_mul, inv_mul, u.inv_mul
-/
lemma add_inv_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u.val.val + u⁻¹.val.val + u⁻¹.val.val * u.val.val = 0 := by
  simpa [-Units.inv_mul] using congr($(u.inv_mul).val)

end PreQuasiregular

namespace Unitization
open PreQuasiregular

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

variable (R A) in
/--
Definition of `unitsFstOne` / `unitsFstOne` 的定义

English:
definition unitsFstOne
  signature: : Subgroup (Unitization R A)ˣ where
  body: {x | x.val.fst = 1}
  one_mem' := rfl
  mul_mem' {x} {y} (hx : x.val.fst = 1) (hy : y.val.fst = 1) := by simp [hx, hy]
  inv_mem' {x} (hx : x.val.fst = 1) := by
    simpa [-Units.mul_inv, hx] using congr(fstHom R A $(x.mul_inv))

@[simp]

中文:
定义 unitsFstOne
  签名: : 子群 (Unitization R A)ˣ where
  定义体: {x | x.val.fst = 1}
  one_mem' := rfl
  mul_mem' {x} {y} (hx : x.val.fst = 1) (hy : y.val.fst = 1) := by simp [hx, hy]
  inv_mem' {x} (hx : x.val.fst = 1) := by
    simpa [-Units.mul_inv, hx] using congr(fstHom R A $(x.mul_inv))

@[simp]

Depends on / 依赖: x.val.fst
-/
def unitsFstOne : Subgroup (Unitization R A)ˣ where
  carrier := {x | x.val.fst = 1}
  one_mem' := rfl
  mul_mem' {x} {y} (hx : x.val.fst = 1) (hy : y.val.fst = 1) := by simp [hx, hy]
  inv_mem' {x} (hx : x.val.fst = 1) := by
    simpa [-Units.mul_inv, hx] using congr(fstHom R A $(x.mul_inv))

@[simp]
/--
lemma `mem_unitsFstOne` / 引理 `mem_unitsFstOne`

English:
lemma mem_unitsFstOne
  given: {x : (Unitization R A)ˣ}
  statement: x in unitsFstOne R A ↔ x.val.fst = 1
  proof: Iff.rfl

@[simp]

中文:
引理 mem_unitsFstOne
  条件: {x : (Unitization R A)ˣ}
  结论: x in unitsFstOne R A ↔ x.val.fst = 1
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_unitsFstOne {x : (Unitization R A)ˣ} : x in unitsFstOne R A ↔ x.val.fst = 1 := Iff.rfl

@[simp]
/--
lemma `unitsFstOne_val_val_fst` / 引理 `unitsFstOne_val_val_fst`

English:
lemma unitsFstOne_val_val_fst
  given: (x : (unitsFstOne R A))
  statement: x.val.val.fst = 1
  proof: mem_unitsFstOne.mp x.property

@[simp]

中文:
引理 unitsFstOne_val_val_fst
  条件: (x : (unitsFstOne R A))
  结论: x.val.val.fst = 1
  证明: mem_unitsFstOne.mp x.property

@[simp]

Depends on / 依赖: mem_unitsFstOne, mem_unitsFstOne.mp, property, x.property
-/
lemma unitsFstOne_val_val_fst (x : (unitsFstOne R A)) : x.val.val.fst = 1 :=
  mem_unitsFstOne.mp x.property

@[simp]
/--
lemma `unitsFstOne_val_inv_val_fst` / 引理 `unitsFstOne_val_inv_val_fst`

English:
lemma unitsFstOne_val_inv_val_fst
  given: (x : (unitsFstOne R A))
  statement: x.val⁻¹.val.fst = 1
  proof: mem_unitsFstOne.mp x⁻¹.property

中文:
引理 unitsFstOne_val_inv_val_fst
  条件: (x : (unitsFstOne R A))
  结论: x.val⁻¹.val.fst = 1
  证明: mem_unitsFstOne.mp x⁻¹.property

Depends on / 依赖: mem_unitsFstOne, mem_unitsFstOne.mp, property
-/
lemma unitsFstOne_val_inv_val_fst (x : (unitsFstOne R A)) : x.val⁻¹.val.fst = 1 :=
  mem_unitsFstOne.mp x⁻¹.property

variable (R) in
/-- If `A` is a non-unital `R`-algebra, then the subgroup of units of `Unitization R A` whose
scalar part is `1 : R` (i.e., `Unitization.unitsFstOne`) is isomorphic to the group of units of
`PreQuasiregular A`. -/
@[simps]
/--
Definition of `unitsFstOne_mulEquiv_quasiregular` / `unitsFstOne_mulEquiv_quasiregular` 的定义

English:
definition unitsFstOne_mulEquiv_quasiregular
  signature: : unitsFstOne R A ≃* (PreQuasiregular A)ˣ where
  body: { val := PreQuasiregular.equiv x.val.val.snd
      inv := PreQuasiregular.equiv x⁻¹.val.val.snd
val_inv := PreQuasiregular.equiv.symm.injective by
        simpa [-Units.mul_inv] using congr($(x.val.mul_inv).snd)
inv_val := PreQuasiregular.equiv.symm.injective by
        simpa [-Units.inv_mul] using congr($(x.val.inv_mul).snd) }
  invFun x :=
    { val :=
      { val := 1 + PreQuasiregular.equiv.symm x.val
        inv := 1 + PreQuasiregular.equiv.symm x⁻¹.val
        val_inv := by
          convert congr((1 + $(inv_add_add_mul_eq_zero x) : Unitization R A))
          · simp only [mul_one, PreQuasiregular.equiv_symm_apply, one_mul, mul_add,
              add_mul, inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero]
        inv_val := by
          convert congr((1 + $(add_inv_add_mul_eq_zero x) : Unitization R A))
          · simp only [mul_one, PreQuasiregular.equiv_symm_apply, one_mul, mul_add,
              add_mul, inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero] }
      property := by simp }
left_inv x := Subtype.ext Units.ext by simpa using x.val.val.inl_fst_add_inr_snd_eq
right_inv x := Units.ext by simp [-PreQuasiregular.equiv_symm_apply]
map_mul' x y := Units.ext PreQuasiregular.equiv.symm.injective by simp

中文:
定义 unitsFstOne_mulEquiv_quasiregular
  签名: : unitsFstOne R A ≃* (PreQuasiregular A)ˣ where
  定义体: { val := PreQuasiregular.equiv x.val.val.snd
      inv := PreQuasiregular.equiv x⁻¹.val.val.snd
val_inv := PreQuasiregular.equiv.symm.injective by
        simpa [-Units.mul_inv] using congr($(x.val.mul_inv).snd)
inv_val := PreQuasiregular.equiv.symm.injective by
        simpa [-Units.inv_mul] using congr($(x.val.inv_mul).snd) }
  invFun x :=
    { val :=
      { val := 1 + PreQuasiregular.equiv.symm x.val
        inv := 1 + PreQuasiregular.equiv.symm x⁻¹.val
        val_inv := by
          convert congr((1 + $(inv_add_add_mul_eq_zero x) : Unitization R A))
          · simp only [mul_one, PreQuasiregular.equiv_symm_apply, one_mul, mul_add,
              add_mul, inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero]
        inv_val := by
          convert congr((1 + $(add_inv_add_mul_eq_zero x) : Unitization R A))
          · simp only [mul_one, PreQuasiregular.equiv_symm_apply, one_mul, mul_add,
              add_mul, inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero] }
      property := by simp }
left_inv x := Subtype.ext Units.ext by simpa using x.val.val.inl_fst_add_inr_snd_eq
right_inv x := Units.ext by simp [-PreQuasiregular.equiv_symm_apply]
map_mul' x y := Units.ext PreQuasiregular.equiv.symm.injective by simp

Depends on / 依赖: PreQuasiregular, PreQuasiregular.equiv, PreQuasiregular.equiv.symm, PreQuasiregular.equiv.symm.injective, Unitization, Units.inv_mul, Units.mul_inv, convert, injective, invFun, inv_add_add_mul_eq_zero, inv_mul, inv_val, mul_inv, val.val.snd, val_inv, x.val, x.val.inv_mul, x.val.mul_inv, x.val.val.snd
-/
def unitsFstOne_mulEquiv_quasiregular : unitsFstOne R A ≃* (PreQuasiregular A)ˣ where
  toFun x :=
    { val := PreQuasiregular.equiv x.val.val.snd
      inv := PreQuasiregular.equiv x⁻¹.val.val.snd
val_inv := PreQuasiregular.equiv.symm.injective by
        simpa [-Units.mul_inv] using congr($(x.val.mul_inv).snd)
inv_val := PreQuasiregular.equiv.symm.injective by
        simpa [-Units.inv_mul] using congr($(x.val.inv_mul).snd) }
  invFun x :=
    { val :=
      { val := 1 + PreQuasiregular.equiv.symm x.val
        inv := 1 + PreQuasiregular.equiv.symm x⁻¹.val
        val_inv := by
          convert congr((1 + $(inv_add_add_mul_eq_zero x) : Unitization R A))
          · simp only [mul_one, PreQuasiregular.equiv_symm_apply, one_mul, mul_add,
              add_mul, inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero]
        inv_val := by
          convert congr((1 + $(add_inv_add_mul_eq_zero x) : Unitization R A))
          · simp only [mul_one, PreQuasiregular.equiv_symm_apply, one_mul, mul_add,
              add_mul, inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero] }
      property := by simp }
left_inv x := Subtype.ext Units.ext by simpa using x.val.val.inl_fst_add_inr_snd_eq
right_inv x := Units.ext by simp [-PreQuasiregular.equiv_symm_apply]
map_mul' x y := Units.ext PreQuasiregular.equiv.symm.injective by simp

end Unitization

section PreQuasiregular

open PreQuasiregular

variable {R : Type*} [NonUnitalSemiring R]

/--
Definition of `IsQuasiregular` / `IsQuasiregular` 的定义

English:
definition IsQuasiregular
  signature: (x : R)
  body: exists u : (PreQuasiregular R)ˣ, equiv.symm u.val = x

@[simp]

中文:
定义 IsQuasiregular
  签名: (x : R)
  定义体: exists u : (PreQuasiregular R)ˣ, equiv.symm u.val = x

@[simp]

Depends on / 依赖: PreQuasiregular, equiv.symm, u.val
-/
def IsQuasiregular (x : R) : Prop :=
  exists u : (PreQuasiregular R)ˣ, equiv.symm u.val = x

@[simp]
/--
lemma `isQuasiregular_zero` / 引理 `isQuasiregular_zero`

English:
lemma isQuasiregular_zero
  statement: IsQuasiregular 0
  proof: ⟨1, rfl⟩

中文:
引理 isQuasiregular_zero
  结论: IsQuasiregular 0
  证明: ⟨1, rfl⟩
-/
lemma isQuasiregular_zero : IsQuasiregular 0 := ⟨1, rfl⟩

/--
lemma `isQuasiregular_iff` / 引理 `isQuasiregular_iff`

English:
lemma isQuasiregular_iff
  given: {x : R}
  proof: by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨equiv.symm u⁻¹.val, by simp⟩
  · rintro ⟨y, hy₁, hy₂⟩
    refine ⟨⟨equiv x, equiv y, ?_, ?_⟩, rfl⟩
    all_goals
      apply equiv.symm.injective
      assumption

中文:
引理 isQuasiregular_iff
  条件: {x : R}
  证明: by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨equiv.symm u⁻¹.val, by simp⟩
  · rintro ⟨y, hy₁, hy₂⟩
    refine ⟨⟨equiv x, equiv y, ?_, ?_⟩, rfl⟩
    all_goals
      apply equiv.symm.injective
      assumption

Depends on / 依赖: all_goals, equiv.symm, equiv.symm.injective, injective
-/
lemma isQuasiregular_iff {x : R} :
    IsQuasiregular x ↔ exists y, y + x + x * y = 0 ∧ x + y + y * x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨equiv.symm u⁻¹.val, by simp⟩
  · rintro ⟨y, hy₁, hy₂⟩
    refine ⟨⟨equiv x, equiv y, ?_, ?_⟩, rfl⟩
    all_goals
      apply equiv.symm.injective
      assumption

/--
lemma `isQuasiregular_iff'` / 引理 `isQuasiregular_iff'`

English:
lemma isQuasiregular_iff'
  given: {x : R}
  statement: IsQuasiregular x ↔ IsUnit (PreQuasiregular.equiv x)
  proof: by
  simp only [IsQuasiregular, IsUnit, Equiv.apply_symm_apply,
    ← PreQuasiregular.equiv (R := R).injective.eq_iff]

中文:
引理 isQuasiregular_iff'
  条件: {x : R}
  结论: IsQuasiregular x ↔ 是单位 (PreQuasiregular.equiv x)
  证明: by
  simp only [IsQuasiregular, IsUnit, Equiv.apply_symm_apply,
    ← PreQuasiregular.equiv (R := R).injective.eq_iff]

Depends on / 依赖: Equiv.apply_symm_apply, IsQuasiregular, IsUnit, PreQuasiregular, PreQuasiregular.equiv, apply_symm_apply, eq_iff, injective, injective.eq_iff
-/
lemma isQuasiregular_iff' {x : R} : IsQuasiregular x ↔ IsUnit (PreQuasiregular.equiv x) := by
  simp only [IsQuasiregular, IsUnit, Equiv.apply_symm_apply,
    ← PreQuasiregular.equiv (R := R).injective.eq_iff]

end PreQuasiregular

/--
lemma `IsQuasiregular.map` / 引理 `IsQuasiregular.map`

English:
lemma IsQuasiregular.map
  statement: {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemiring S]
  proof: by
  rw [isQuasiregular_iff] at hx ⊢
  obtain ⟨y, hy₁, hy₂⟩ := hx
  exact ⟨f y, by simpa using And.intro congr(f $(hy₁)) congr(f $(hy₂))⟩

中文:
引理 IsQuasiregular.map
  结论: {F R S : 类型} [非幺半环 R] [非幺半环 S]
  证明: by
  rw [isQuasiregular_iff] at hx ⊢
  obtain ⟨y, hy₁, hy₂⟩ := hx
  exact ⟨f y, by simpa using And.intro congr(f $(hy₁)) congr(f $(hy₂))⟩

Depends on / 依赖: And.intro, isQuasiregular_iff
-/
lemma IsQuasiregular.map {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemiring S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) {x : R} (hx : IsQuasiregular x) :
    IsQuasiregular (f x) := by
  rw [isQuasiregular_iff] at hx ⊢
  obtain ⟨y, hy₁, hy₂⟩ := hx
  exact ⟨f y, by simpa using And.intro congr(f $(hy₁)) congr(f $(hy₂))⟩

/--
lemma `IsQuasiregular.isUnit_one_add` / 引理 `IsQuasiregular.isUnit_one_add`

English:
lemma IsQuasiregular.isUnit_one_add
  given: {R : Type*} [Semiring R] {x : R} (hx : IsQuasiregular x)
  proof: by
  obtain ⟨y, hy₁, hy₂⟩ := isQuasiregular_iff.mp hx
  refine ⟨⟨1 + x, 1 + y, ?_, ?_⟩, rfl⟩
  · convert congr(1 + $(hy₁)) <;> [noncomm_ring; simp]
  · convert congr(1 + $(hy₂)) <;> [noncomm_ring; simp]

中文:
引理 IsQuasiregular.isUnit_one_add
  条件: {R : 类型} [半环 R] {x : R} (hx : IsQuasiregular x)
  证明: by
  obtain ⟨y, hy₁, hy₂⟩ := isQuasiregular_iff.mp hx
  refine ⟨⟨1 + x, 1 + y, ?_, ?_⟩, rfl⟩
  · convert congr(1 + $(hy₁)) <;> [noncomm_ring; simp]
  · convert congr(1 + $(hy₂)) <;> [noncomm_ring; simp]

Depends on / 依赖: convert, isQuasiregular_iff, isQuasiregular_iff.mp, noncomm_ring
-/
lemma IsQuasiregular.isUnit_one_add {R : Type*} [Semiring R] {x : R} (hx : IsQuasiregular x) :
    IsUnit (1 + x) := by
  obtain ⟨y, hy₁, hy₂⟩ := isQuasiregular_iff.mp hx
  refine ⟨⟨1 + x, 1 + y, ?_, ?_⟩, rfl⟩
  · convert congr(1 + $(hy₁)) <;> [noncomm_ring; simp]
  · convert congr(1 + $(hy₂)) <;> [noncomm_ring; simp]

/--
lemma `isQuasiregular_iff_isUnit` / 引理 `isQuasiregular_iff_isUnit`

English:
lemma isQuasiregular_iff_isUnit
  given: {R : Type*} [Ring R] {x : R}
  proof: by
  refine ⟨IsQuasiregular.isUnit_one_add, fun hx => ?_⟩
  rw [isQuasiregular_iff]
  use hx.unit⁻¹ - 1
  constructor
  case' h.left => have := congr($(hx.mul_val_inv) - 1)
  case' h.right => have := congr($(hx.val_inv_mul) - 1)
  all_goals
    rw [← sub_add_cancel (↑hx.unit⁻¹ : R) 1]; rw [sub_self] at this
    convert this
    noncomm_ring

中文:
引理 isQuasiregular_iff_isUnit
  条件: {R : 类型} [环 R] {x : R}
  证明: by
  refine ⟨IsQuasiregular.isUnit_one_add, fun hx => ?_⟩
  rw [isQuasiregular_iff]
  use hx.unit⁻¹ - 1
  constructor
  case' h.left => have := congr($(hx.mul_val_inv) - 1)
  case' h.right => have := congr($(hx.val_inv_mul) - 1)
  all_goals
    rw [← sub_add_cancel (↑hx.unit⁻¹ : R) 1]; rw [sub_self] at this
    convert this
    noncomm_ring

Depends on / 依赖: IsQuasiregular, IsQuasiregular.isUnit_one_add, all_goals, convert, h.left, h.right, hx.mul_val_inv, hx.unit, hx.val_inv_mul, isQuasiregular_iff, isUnit_one_add, mul_val_inv, noncomm_ring, sub_add_cancel, sub_self, val_inv_mul
-/
lemma isQuasiregular_iff_isUnit {R : Type*} [Ring R] {x : R} :
    IsQuasiregular x ↔ IsUnit (1 + x) := by
  refine ⟨IsQuasiregular.isUnit_one_add, fun hx => ?_⟩
  rw [isQuasiregular_iff]
  use hx.unit⁻¹ - 1
  constructor
  case' h.left => have := congr($(hx.mul_val_inv) - 1)
  case' h.right => have := congr($(hx.val_inv_mul) - 1)
  all_goals
    rw [← sub_add_cancel (↑hx.unit⁻¹ : R) 1]; rw [sub_self] at this
    convert this
    noncomm_ring

-- interestingly, this holds even in the semiring case.
/--
lemma `isQuasiregular_iff_isUnit'` / 引理 `isQuasiregular_iff_isUnit'`

English:
lemma isQuasiregular_iff_isUnit'
  statement: (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalSemiring A]
  proof: by
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨u, rfl⟩
.val.isUnit exact (Unitization.unitsFstOne_mulEquiv_quasiregular R).symm u
  · exact ⟨(Unitization.unitsFstOne_mulEquiv_quasiregular R) ⟨hx.unit, by simp⟩, by simp⟩

中文:
引理 isQuasiregular_iff_isUnit'
  结论: (R : 类型) {A : 类型} [交换半环 R] [非幺半环 A]
  证明: by
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨u, rfl⟩
.val.isUnit exact (Unitization.unitsFstOne_mulEquiv_quasiregular R).symm u
  · exact ⟨(Unitization.unitsFstOne_mulEquiv_quasiregular R) ⟨hx.unit, by simp⟩, by simp⟩

Depends on / 依赖: Unitization, Unitization.unitsFstOne_mulEquiv_quasiregular, hx.unit, isUnit, unitsFstOne_mulEquiv_quasiregular, val.isUnit
-/
lemma isQuasiregular_iff_isUnit' (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalSemiring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {x : A} :
    IsQuasiregular x ↔ IsUnit (1 + x : Unitization R A) := by
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨u, rfl⟩
.val.isUnit exact (Unitization.unitsFstOne_mulEquiv_quasiregular R).symm u
  · exact ⟨(Unitization.unitsFstOne_mulEquiv_quasiregular R) ⟨hx.unit, by simp⟩, by simp⟩

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

/--
Definition of `quasispectrum` / `quasispectrum` 的定义

English:
definition quasispectrum
  signature: (a : A)
  body: {r : R | (hr : IsUnit r) -> ¬ IsQuasiregular (-(hr.unit⁻¹ • a))}

中文:
定义 quasispectrum
  签名: (a : A)
  定义体: {r : R | (hr : IsUnit r) -> ¬ IsQuasiregular (-(hr.unit⁻¹ • a))}

Depends on / 依赖: IsQuasiregular, IsUnit, hr.unit
-/
def quasispectrum (a : A) : Set R :=
  {r : R | (hr : IsUnit r) -> ¬ IsQuasiregular (-(hr.unit⁻¹ • a))}

variable {R} in
/--
lemma `quasispectrum.not_isUnit_mem` / 引理 `quasispectrum.not_isUnit_mem`

English:
lemma quasispectrum.not_isUnit_mem
  given: (a : A) {r : R} (hr : ¬ IsUnit r)
  statement: r in quasispectrum R a
  proof: fun hr' => (hr hr').elim

@[simp]

中文:
引理 quasispectrum.not_isUnit_mem
  条件: (a : A) {r : R} (hr : ¬ 是单位 r)
  结论: r in quasispectrum R a
  证明: fun hr' => (hr hr').elim

@[simp]
-/
lemma quasispectrum.not_isUnit_mem (a : A) {r : R} (hr : ¬ IsUnit r) : r in quasispectrum R a :=
  fun hr' => (hr hr').elim

@[simp]
/--
lemma `quasispectrum.zero_mem` / 引理 `quasispectrum.zero_mem`

English:
lemma quasispectrum.zero_mem
  given: [Nontrivial R] (a : A)
  statement: 0 in quasispectrum R a
  proof: quasispectrum.not_isUnit_mem a by simp

中文:
引理 quasispectrum.zero_mem
  条件: [非平凡 R] (a : A)
  结论: 0 in quasispectrum R a
  证明: quasispectrum.not_isUnit_mem a by simp

Depends on / 依赖: not_isUnit_mem, quasispectrum, quasispectrum.not_isUnit_mem
-/
lemma quasispectrum.zero_mem [Nontrivial R] (a : A) : 0 in quasispectrum R a :=
quasispectrum.not_isUnit_mem a by simp

/--
theorem `quasispectrum.nonempty` / 定理 `quasispectrum.nonempty`

English:
theorem quasispectrum.nonempty
  given: [Nontrivial R] (a : A)
  statement: (quasispectrum R a).Nonempty
  proof: Set.nonempty_of_mem quasispectrum.zero_mem R a

中文:
定理 quasispectrum.nonempty
  条件: [非平凡 R] (a : A)
  结论: (quasispectrum R a).非空
  证明: Set.nonempty_of_mem quasispectrum.zero_mem R a

Depends on / 依赖: Algebra, CommSemiring, Semiring, Set.nonempty_of_mem, nonempty_of_mem, quasispectrum, quasispectrum.zero_mem, toModule, zero_mem
-/
theorem quasispectrum.nonempty [Nontrivial R] (a : A) : (quasispectrum R a).Nonempty :=
Set.nonempty_of_mem quasispectrum.zero_mem R a

/--
Instance `quasispectrum.instZero` / 实例 `quasispectrum.instZero`

English:
instance quasispectrum.instZero
  signature: [Nontrivial R] (a : A)
  body: ⟨0, quasispectrum.zero_mem R a⟩

中文:
实例 quasispectrum.instZero
  签名: [非平凡 R] (a : A)
  定义体: ⟨0, quasispectrum.zero_mem R a⟩

Depends on / 依赖: quasispectrum, quasispectrum.zero_mem, zero_mem
-/
instance quasispectrum.instZero [Nontrivial R] (a : A) : Zero (quasispectrum R a) where
  zero := ⟨0, quasispectrum.zero_mem R a⟩

variable {R}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `NonUnitalAlgHom.quasispectrum_apply_subset'` / 引理 `NonUnitalAlgHom.quasispectrum_apply_subset'`

English:
lemma NonUnitalAlgHom.quasispectrum_apply_subset'
  statement: {F R : Type*} (S : Type*) {A B : Type*}
  proof: by
  refine Set.compl_subset_compl.mp fun x => ?_
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not,
    forall_exists_index]
  refine fun hx this => ⟨hx, ?_⟩
  rw [Units.smul_def]; rw [← smul_one_smul S] at this ⊢
  simpa [-smul_assoc] using this.map φ

中文:
引理 非幺Alg态射.quasispectrum_apply_subset'
  结论: {F R : 类型} (S : 类型) {A B : 类型}
  证明: by
  refine Set.compl_subset_compl.mp fun x => ?_
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not,
    forall_exists_index]
  refine fun hx this => ⟨hx, ?_⟩
  rw [Units.smul_def]; rw [← smul_one_smul S] at this ⊢
  simpa [-smul_assoc] using this.map φ

Depends on / 依赖: Set.compl_subset_compl.mp, Set.mem_compl_iff, Set.mem_ofPred_eq, Units.smul_def, compl_subset_compl, forall_exists_index, mem_compl_iff, mem_ofPred_eq, not_forall, not_not, quasispectrum, smul_assoc, smul_def, smul_one_smul, this.map
-/
lemma NonUnitalAlgHom.quasispectrum_apply_subset' {F R : Type*} (S : Type*) {A B : Type*}
    [CommSemiring R] [Semiring S] [NonUnitalRing A] [NonUnitalRing B] [Module R S]
    [Module S A] [Module R A] [Module S B] [Module R B] [IsScalarTower R S A] [IsScalarTower R S B]
    [FunLike F A B] [NonUnitalAlgHomClass F S A B] (φ : F) (a : A) :
    quasispectrum R (φ a) subseteq quasispectrum R a := by
  refine Set.compl_subset_compl.mp fun x => ?_
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not,
    forall_exists_index]
  refine fun hx this => ⟨hx, ?_⟩
  rw [Units.smul_def]; rw [← smul_one_smul S] at this ⊢
  simpa [-smul_assoc] using this.map φ

/--
lemma `NonUnitalAlgHom.quasispectrum_apply_subset` / 引理 `NonUnitalAlgHom.quasispectrum_apply_subset`

English:
lemma NonUnitalAlgHom.quasispectrum_apply_subset
  statement: {F R A B : Type*}
  proof: NonUnitalAlgHom.quasispectrum_apply_subset' R φ a

@[simp]

中文:
引理 非幺Alg态射.quasispectrum_apply_subset
  结论: {F R A B : 类型}
  证明: NonUnitalAlgHom.quasispectrum_apply_subset' R φ a

@[simp]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.quasispectrum_apply_subset, quasispectrum_apply_subset
-/
lemma NonUnitalAlgHom.quasispectrum_apply_subset {F R A B : Type*}
    [CommRing R] [NonUnitalRing A] [NonUnitalRing B] [Module R A] [Module R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (φ : F) (a : A) :
    quasispectrum R (φ a) subseteq quasispectrum R a :=
  NonUnitalAlgHom.quasispectrum_apply_subset' R φ a

@[simp]
/--
lemma `quasispectrum.coe_zero` / 引理 `quasispectrum.coe_zero`

English:
lemma quasispectrum.coe_zero
  given: [Nontrivial R] (a : A)
  statement: (0 : quasispectrum R a) = (0 : R)
  proof: rfl

中文:
引理 quasispectrum.coe_zero
  条件: [非平凡 R] (a : A)
  结论: (0 : quasispectrum R a) = (0 : R)
  证明: rfl
-/
lemma quasispectrum.coe_zero [Nontrivial R] (a : A) : (0 : quasispectrum R a) = (0 : R) := rfl

/--
lemma `quasispectrum.mem_of_not_quasiregular` / 引理 `quasispectrum.mem_of_not_quasiregular`

English:
lemma quasispectrum.mem_of_not_quasiregular
  statement: (a : A) {r : Rˣ}
  proof: fun _ => by simpa using hr

中文:
引理 quasispectrum.mem_of_not_quasiregular
  结论: (a : A) {r : Rˣ}
  证明: fun _ => by simpa using hr
-/
lemma quasispectrum.mem_of_not_quasiregular (a : A) {r : Rˣ}
    (hr : ¬ IsQuasiregular (-(r⁻¹ • a))) : (r : R) in quasispectrum R a :=
  fun _ => by simpa using hr

/--
lemma `quasispectrum_eq_spectrum_union` / 引理 `quasispectrum_eq_spectrum_union`

English:
lemma quasispectrum_eq_spectrum_union
  statement: (R : Type*) {A : Type*} [CommSemiring R]
  proof: by
  ext r
  rw [quasispectrum]
  simp only [Set.mem_ofPred_eq, Set.mem_union, ← imp_iff_or_not, spectrum.mem_iff]
  congr! 1 with hr
  rw [not_iff_not]; rw [isQuasiregular_iff_isUnit]; rw [← sub_eq_add_neg]; rw [Algebra.algebraMap_eq_smul_one]
  exact (IsUnit.smul_sub_iff_sub_inv_smul hr.unit a).symm

中文:
引理 quasispectrum_eq_spectrum_union
  结论: (R : 类型) {A : 类型} [交换半环 R]
  证明: by
  ext r
  rw [quasispectrum]
  simp only [Set.mem_ofPred_eq, Set.mem_union, ← imp_iff_or_not, spectrum.mem_iff]
  congr! 1 with hr
  rw [not_iff_not]; rw [isQuasiregular_iff_isUnit]; rw [← sub_eq_add_neg]; rw [Algebra.algebraMap_eq_smul_one]
  exact (IsUnit.smul_sub_iff_sub_inv_smul hr.unit a).symm

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, IsUnit, IsUnit.smul_sub_iff_sub_inv_smul, Set.mem_ofPred_eq, Set.mem_union, algebraMap_eq_smul_one, hr.unit, imp_iff_or_not, isQuasiregular_iff_isUnit, mem_iff, mem_ofPred_eq, mem_union, not_iff_not, quasispectrum, smul_sub_iff_sub_inv_smul, spectrum, spectrum.mem_iff, sub_eq_add_neg
-/
lemma quasispectrum_eq_spectrum_union (R : Type*) {A : Type*} [CommSemiring R]
    [Ring A] [Algebra R A] (a : A) : quasispectrum R a = spectrum R a union {r : R | ¬ IsUnit r} := by
  ext r
  rw [quasispectrum]
  simp only [Set.mem_ofPred_eq, Set.mem_union, ← imp_iff_or_not, spectrum.mem_iff]
  congr! 1 with hr
  rw [not_iff_not]; rw [isQuasiregular_iff_isUnit]; rw [← sub_eq_add_neg]; rw [Algebra.algebraMap_eq_smul_one]
  exact (IsUnit.smul_sub_iff_sub_inv_smul hr.unit a).symm

/--
lemma `spectrum_subset_quasispectrum` / 引理 `spectrum_subset_quasispectrum`

English:
lemma spectrum_subset_quasispectrum
  statement: (R : Type*) {A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  proof: quasispectrum_eq_spectrum_union R a ▸ Set.subset_union_left

中文:
引理 spectrum_subset_quasispectrum
  结论: (R : 类型) {A : 类型} [交换半环 R] [环 A] [代数 R A]
  证明: quasispectrum_eq_spectrum_union R a ▸ Set.subset_union_left

Depends on / 依赖: Set.subset_union_left, quasispectrum_eq_spectrum_union, subset_union_left
-/
lemma spectrum_subset_quasispectrum (R : Type*) {A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    (a : A) : spectrum R a subseteq quasispectrum R a :=
  quasispectrum_eq_spectrum_union R a ▸ Set.subset_union_left

/--
lemma `quasispectrum_eq_spectrum_union_zero` / 引理 `quasispectrum_eq_spectrum_union_zero`

English:
lemma quasispectrum_eq_spectrum_union_zero
  statement: (R : Type*) {A : Type*} [Semifield R] [Ring A]
  proof: by
  convert! quasispectrum_eq_spectrum_union R a
  simp

中文:
引理 quasispectrum_eq_spectrum_union_zero
  结论: (R : 类型) {A : 类型} [半域 R] [环 A]
  证明: by
  convert! quasispectrum_eq_spectrum_union R a
  simp

Depends on / 依赖: convert, quasispectrum_eq_spectrum_union
-/
lemma quasispectrum_eq_spectrum_union_zero (R : Type*) {A : Type*} [Semifield R] [Ring A]
    [Algebra R A] (a : A) : quasispectrum R a = spectrum R a union {0} := by
  convert! quasispectrum_eq_spectrum_union R a
  simp

/--
lemma `mem_quasispectrum_iff` / 引理 `mem_quasispectrum_iff`

English:
lemma mem_quasispectrum_iff
  statement: {R A : Type*} [Semifield R] [Ring A]
  proof: by
  simp [quasispectrum_eq_spectrum_union_zero]

中文:
引理 mem_quasispectrum_iff
  结论: {R A : 类型} [半域 R] [环 A]
  证明: by
  simp [quasispectrum_eq_spectrum_union_zero]

Depends on / 依赖: IsScalarTower, _root_, _root_.IsScalarTower.right, quasispectrum_eq_spectrum_union_zero
-/
lemma mem_quasispectrum_iff {R A : Type*} [Semifield R] [Ring A]
    [Algebra R A] {a : A} {x : R} :
    x in quasispectrum R a ↔ x = 0 ∨ x in spectrum R a := by
  simp [quasispectrum_eq_spectrum_union_zero]

namespace Unitization
variable [IsScalarTower R A A] [SMulCommClass R A A]

/--
lemma `isQuasiregular_inr_iff` / 引理 `isQuasiregular_inr_iff`

English:
lemma isQuasiregular_inr_iff
  given: (a : A)
  proof: by
  refine ⟨fun ha => ?_, IsQuasiregular.map (inrNonUnitalAlgHom R A)⟩
  rw [isQuasiregular_iff] at ha ⊢
  obtain ⟨y, hy₁, hy₂⟩ := ha
  lift y to A using by simpa using congr(fstHom R A $(hy₁))
refine ⟨y, ?_, ?_⟩ <;> exact inr_injective (R := R) by simpa

中文:
引理 isQuasiregular_inr_iff
  条件: (a : A)
  证明: by
  refine ⟨fun ha => ?_, IsQuasiregular.map (inrNonUnitalAlgHom R A)⟩
  rw [isQuasiregular_iff] at ha ⊢
  obtain ⟨y, hy₁, hy₂⟩ := ha
  lift y to A using by simpa using congr(fstHom R A $(hy₁))
refine ⟨y, ?_, ?_⟩ <;> exact inr_injective (R := R) by simpa

Depends on / 依赖: IsQuasiregular, IsQuasiregular.map, fstHom, inrNonUnitalAlgHom, inr_injective, isQuasiregular_iff
-/
lemma isQuasiregular_inr_iff (a : A) :
    IsQuasiregular (a : Unitization R A) ↔ IsQuasiregular a := by
  refine ⟨fun ha => ?_, IsQuasiregular.map (inrNonUnitalAlgHom R A)⟩
  rw [isQuasiregular_iff] at ha ⊢
  obtain ⟨y, hy₁, hy₂⟩ := ha
  lift y to A using by simpa using congr(fstHom R A $(hy₁))
refine ⟨y, ?_, ?_⟩ <;> exact inr_injective (R := R) by simpa

/--
lemma `zero_mem_spectrum_inr` / 引理 `zero_mem_spectrum_inr`

English:
lemma zero_mem_spectrum_inr
  statement: (R S : Type*) {A : Type*} [CommSemiring R]
  proof: by
  rw [spectrum.zero_mem_iff]
  rintro ⟨u, hu⟩
  simpa [-Units.mul_inv, hu] using congr($(u.mul_inv).fst)

中文:
引理 zero_mem_spectrum_inr
  结论: (R S : 类型) {A : 类型} [交换半环 R]
  证明: by
  rw [spectrum.zero_mem_iff]
  rintro ⟨u, hu⟩
  simpa [-Units.mul_inv, hu] using congr($(u.mul_inv).fst)

Depends on / 依赖: Units.mul_inv, mul_inv, spectrum, spectrum.zero_mem_iff, u.mul_inv, zero_mem_iff
-/
lemma zero_mem_spectrum_inr (R S : Type*) {A : Type*} [CommSemiring R]
    [CommRing S] [Nontrivial S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    0 in spectrum R (a : Unitization S A) := by
  rw [spectrum.zero_mem_iff]
  rintro ⟨u, hu⟩
  simpa [-Units.mul_inv, hu] using congr($(u.mul_inv).fst)

/--
lemma `mem_spectrum_inr_of_not_isUnit` / 引理 `mem_spectrum_inr_of_not_isUnit`

English:
lemma mem_spectrum_inr_of_not_isUnit
  statement: {R A : Type*} [CommRing R]
  proof: fun h => hr by simpa [map_sub] using h.map (fstHom R A)

中文:
引理 mem_spectrum_inr_of_not_isUnit
  结论: {R A : 类型} [交换环 R]
  证明: fun h => hr by simpa [map_sub] using h.map (fstHom R A)

Depends on / 依赖: fstHom, h.map, map_sub
-/
lemma mem_spectrum_inr_of_not_isUnit {R A : Type*} [CommRing R]
    [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (a : A) (r : R) (hr : ¬ IsUnit r) : r in spectrum R (a : Unitization R A) :=
fun h => hr by simpa [map_sub] using h.map (fstHom R A)

/--
lemma `quasispectrum_eq_spectrum_inr` / 引理 `quasispectrum_eq_spectrum_inr`

English:
lemma quasispectrum_eq_spectrum_inr
  statement: (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
  proof: by
  ext r
  have : { r | ¬ IsUnit r} subseteq spectrum R _ := mem_spectrum_inr_of_not_isUnit a
  rw [← Set.union_eq_left.mpr this]; rw [← quasispectrum_eq_spectrum_union]
  apply forall_congr' fun hr => ?_
  rw [not_iff_not]; rw [Units.smul_def]; rw [Units.smul_def]; rw [← inr_smul]; rw [← inr_neg]; rw [isQuasiregular_inr_iff]

中文:
引理 quasispectrum_eq_spectrum_inr
  结论: (R : 类型) {A : 类型} [交换环 R] [非幺环 A]
  证明: by
  ext r
  have : { r | ¬ IsUnit r} subseteq spectrum R _ := mem_spectrum_inr_of_not_isUnit a
  rw [← Set.union_eq_left.mpr this]; rw [← quasispectrum_eq_spectrum_union]
  apply forall_congr' fun hr => ?_
  rw [not_iff_not]; rw [Units.smul_def]; rw [Units.smul_def]; rw [← inr_smul]; rw [← inr_neg]; rw [isQuasiregular_inr_iff]

Depends on / 依赖: IsUnit, Set.union_eq_left.mpr, Units.smul_def, forall_congr, inr_neg, inr_smul, isQuasiregular_inr_iff, mem_spectrum_inr_of_not_isUnit, not_iff_not, quasispectrum_eq_spectrum_union, smul_def, spectrum, subseteq, union_eq_left
-/
lemma quasispectrum_eq_spectrum_inr (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (a : A) :
    quasispectrum R a = spectrum R (a : Unitization R A) := by
  ext r
  have : { r | ¬ IsUnit r} subseteq spectrum R _ := mem_spectrum_inr_of_not_isUnit a
  rw [← Set.union_eq_left.mpr this]; rw [← quasispectrum_eq_spectrum_union]
  apply forall_congr' fun hr => ?_
  rw [not_iff_not]; rw [Units.smul_def]; rw [Units.smul_def]; rw [← inr_smul]; rw [← inr_neg]; rw [isQuasiregular_inr_iff]

/--
lemma `quasispectrum_eq_spectrum_inr'` / 引理 `quasispectrum_eq_spectrum_inr'`

English:
lemma quasispectrum_eq_spectrum_inr'
  statement: (R S : Type*) {A : Type*} [Semifield R]
  proof: by
  ext r
  have := Set.singleton_subset_iff.mpr (zero_mem_spectrum_inr R S a)
  rw [← Set.union_eq_self_of_subset_right this]; rw [← quasispectrum_eq_spectrum_union_zero]
  apply forall_congr' fun x => ?_
  rw [not_iff_not]; rw [Units.smul_def]; rw [Units.smul_def]; rw [← inr_smul]; rw [← inr_neg]; rw [isQuasiregular_inr_iff]

中文:
引理 quasispectrum_eq_spectrum_inr'
  结论: (R S : 类型) {A : 类型} [半域 R]
  证明: by
  ext r
  have := Set.singleton_subset_iff.mpr (zero_mem_spectrum_inr R S a)
  rw [← Set.union_eq_self_of_subset_right this]; rw [← quasispectrum_eq_spectrum_union_zero]
  apply forall_congr' fun x => ?_
  rw [not_iff_not]; rw [Units.smul_def]; rw [Units.smul_def]; rw [← inr_smul]; rw [← inr_neg]; rw [isQuasiregular_inr_iff]

Depends on / 依赖: Set.singleton_subset_iff.mpr, Set.union_eq_self_of_subset_right, Units.smul_def, forall_congr, inr_neg, inr_smul, isQuasiregular_inr_iff, not_iff_not, quasispectrum_eq_spectrum_union_zero, singleton_subset_iff, smul_def, union_eq_self_of_subset_right, zero_mem_spectrum_inr
-/
lemma quasispectrum_eq_spectrum_inr' (R S : Type*) {A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    quasispectrum R a = spectrum R (a : Unitization S A) := by
  ext r
  have := Set.singleton_subset_iff.mpr (zero_mem_spectrum_inr R S a)
  rw [← Set.union_eq_self_of_subset_right this]; rw [← quasispectrum_eq_spectrum_union_zero]
  apply forall_congr' fun x => ?_
  rw [not_iff_not]; rw [Units.smul_def]; rw [Units.smul_def]; rw [← inr_smul]; rw [← inr_neg]; rw [isQuasiregular_inr_iff]

/--
lemma `quasispectrum_inr_eq` / 引理 `quasispectrum_inr_eq`

English:
lemma quasispectrum_inr_eq
  statement: (R S : Type*) {A : Type*} [Semifield R]
  proof: by
  rw [quasispectrum_eq_spectrum_union_zero]; rw [quasispectrum_eq_spectrum_inr' R S]
  simpa using zero_mem_spectrum_inr _ _ _

中文:
引理 quasispectrum_inr_eq
  结论: (R S : 类型) {A : 类型} [半域 R]
  证明: by
  rw [quasispectrum_eq_spectrum_union_zero]; rw [quasispectrum_eq_spectrum_inr' R S]
  simpa using zero_mem_spectrum_inr _ _ _

Depends on / 依赖: quasispectrum_eq_spectrum_inr, quasispectrum_eq_spectrum_union_zero, zero_mem_spectrum_inr
-/
lemma quasispectrum_inr_eq (R S : Type*) {A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    quasispectrum R (a : Unitization S A) = quasispectrum R a := by
  rw [quasispectrum_eq_spectrum_union_zero]; rw [quasispectrum_eq_spectrum_inr' R S]
  simpa using zero_mem_spectrum_inr _ _ _

end Unitization

/--
lemma `quasispectrum.mul_comm` / 引理 `quasispectrum.mul_comm`

English:
lemma quasispectrum.mul_comm
  statement: {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
  proof: by
  rw [← Set.inter_union_compl (quasispectrum R (a * b)) {r | IsUnit r}]; rw [← Set.inter_union_compl (quasispectrum R (b * a)) {r | IsUnit r}]
  congr! 1
  · simpa [Set.inter_comm _ {r | IsUnit r}, Unitization.quasispectrum_eq_spectrum_inr,
      Unitization.inr_mul] using spectrum.setOfPred_isUnit_inter_mul_comm _ _
  · rw [Set.inter_eq_right.mpr, Set.inter_eq_right.mpr]
    all_goals exact fun _ => quasispectrum.not_isUnit_mem _

中文:
引理 quasispectrum.mul_comm
  结论: {R A : 类型} [交换环 R] [非幺环 A] [模 R A]
  证明: by
  rw [← Set.inter_union_compl (quasispectrum R (a * b)) {r | IsUnit r}]; rw [← Set.inter_union_compl (quasispectrum R (b * a)) {r | IsUnit r}]
  congr! 1
  · simpa [Set.inter_comm _ {r | IsUnit r}, Unitization.quasispectrum_eq_spectrum_inr,
      Unitization.inr_mul] using spectrum.setOfPred_isUnit_inter_mul_comm _ _
  · rw [Set.inter_eq_right.mpr, Set.inter_eq_right.mpr]
    all_goals exact fun _ => quasispectrum.not_isUnit_mem _

Depends on / 依赖: IsUnit, Set.inter_comm, Set.inter_eq_right.mpr, Set.inter_union_compl, Unitization, Unitization.inr_mul, Unitization.quasispectrum_eq_spectrum_inr, all_goals, inr_mul, inter_comm, inter_eq_right, inter_union_compl, not_isUnit_mem, quasispectrum, quasispectrum.not_isUnit_mem, quasispectrum_eq_spectrum_inr, setOfPred_isUnit_inter_mul_comm, spectrum, spectrum.setOfPred_isUnit_inter_mul_comm
-/
lemma quasispectrum.mul_comm {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (a b : A) :
    quasispectrum R (a * b) = quasispectrum R (b * a) := by
  rw [← Set.inter_union_compl (quasispectrum R (a * b)) {r | IsUnit r}]; rw [← Set.inter_union_compl (quasispectrum R (b * a)) {r | IsUnit r}]
  congr! 1
  · simpa [Set.inter_comm _ {r | IsUnit r}, Unitization.quasispectrum_eq_spectrum_inr,
      Unitization.inr_mul] using spectrum.setOfPred_isUnit_inter_mul_comm _ _
  · rw [Set.inter_eq_right.mpr, Set.inter_eq_right.mpr]
    all_goals exact fun _ => quasispectrum.not_isUnit_mem _

/--
Definition of `NonnegSpectrumClass` / `NonnegSpectrumClass` 的定义

English:
class NonnegSpectrumClass
  parameters: (𝕜 A : Type*) [CommSemiring 𝕜] [PartialOrder 𝕜]
  axioms and operations (1):
    - quasispectrum_nonneg_of_nonneg : forall a : A, 0 <= a -> forall x in quasispectrum 𝕜 a, 0 <= x

中文:
类 NonnegSpectrum类
  参数: (𝕜 A : 类型) [交换半环 𝕜] [偏序 𝕜]
  公理与运算 (1 个):
    - quasispectrum_nonneg_of_nonneg : 对任意 a : A, 0 <= a -> 对任意 x in quasispectrum 𝕜 a, 0 <= x
-/
class NonnegSpectrumClass (𝕜 A : Type*) [CommSemiring 𝕜] [PartialOrder 𝕜]
    [NonUnitalRing A] [PartialOrder A]
    [Module 𝕜 A] : Prop where
  quasispectrum_nonneg_of_nonneg : forall a : A, 0 <= a -> forall x in quasispectrum 𝕜 a, 0 <= x

export NonnegSpectrumClass (quasispectrum_nonneg_of_nonneg)

namespace NonnegSpectrumClass

/--
lemma `iff_spectrum_nonneg` / 引理 `iff_spectrum_nonneg`

English:
lemma iff_spectrum_nonneg
  statement: {𝕜 A : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [Ring A] [PartialOrder A]
  proof: by
  simp [show NonnegSpectrumClass 𝕜 A ↔ _ from ⟨fun ⟨h⟩ => h, (⟨·⟩)⟩,
    quasispectrum_eq_spectrum_union_zero]

alias ⟨_, of_spectrum_nonneg⟩ := iff_spectrum_nonneg

中文:
引理 iff_spectrum_nonneg
  结论: {𝕜 A : 类型} [半域 𝕜] [线性序 𝕜] [环 A] [偏序 A]
  证明: by
  simp [show NonnegSpectrumClass 𝕜 A ↔ _ from ⟨fun ⟨h⟩ => h, (⟨·⟩)⟩,
    quasispectrum_eq_spectrum_union_zero]

alias ⟨_, of_spectrum_nonneg⟩ := iff_spectrum_nonneg

Depends on / 依赖: Algebra, NonnegSpectrumClass, quasispectrum_eq_spectrum_union_zero
-/
lemma iff_spectrum_nonneg {𝕜 A : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [Ring A] [PartialOrder A]
    [Algebra 𝕜 A] : NonnegSpectrumClass 𝕜 A ↔ forall a : A, 0 <= a -> forall x in spectrum 𝕜 a, 0 <= x := by
  simp [show NonnegSpectrumClass 𝕜 A ↔ _ from ⟨fun ⟨h⟩ => h, (⟨·⟩)⟩,
    quasispectrum_eq_spectrum_union_zero]

alias ⟨_, of_spectrum_nonneg⟩ := iff_spectrum_nonneg

/--
lemma `nonneg_of_mem_quasispectrum` / 引理 `nonneg_of_mem_quasispectrum`

English:
lemma nonneg_of_mem_quasispectrum
  statement: {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [PartialOrder A]
  proof: quasispectrum_nonneg_of_nonneg a ha x hx

grind_pattern nonneg_of_mem_quasispectrum => x in quasispectrum 𝕜 a

中文:
引理 nonneg_of_mem_quasispectrum
  结论: {𝕜 : 类型} [交换半环 𝕜] [偏序 𝕜] [偏序 A]
  证明: quasispectrum_nonneg_of_nonneg a ha x hx

grind_pattern nonneg_of_mem_quasispectrum => x in quasispectrum 𝕜 a

Depends on / 依赖: quasispectrum_nonneg_of_nonneg
-/
lemma nonneg_of_mem_quasispectrum {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [PartialOrder A]
    [Module 𝕜 A] [NonnegSpectrumClass 𝕜 A] {a : A} (ha : 0 <= a) {x : 𝕜}
    (hx : x in quasispectrum 𝕜 a) : 0 <= x := quasispectrum_nonneg_of_nonneg a ha x hx

grind_pattern nonneg_of_mem_quasispectrum => x in quasispectrum 𝕜 a

end NonnegSpectrumClass

/--
lemma `spectrum_nonneg_of_nonneg` / 引理 `spectrum_nonneg_of_nonneg`

English:
lemma spectrum_nonneg_of_nonneg
  statement: {𝕜 A : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
  proof: NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg a ha x (spectrum_subset_quasispectrum 𝕜 a hx)

grind_pattern spectrum_nonneg_of_nonneg => x in spectrum 𝕜 a

中文:
引理 spectrum_nonneg_of_nonneg
  结论: {𝕜 A : 类型} [交换半环 𝕜] [偏序 𝕜]
  证明: NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg a ha x (spectrum_subset_quasispectrum 𝕜 a hx)

grind_pattern spectrum_nonneg_of_nonneg => x in spectrum 𝕜 a

Depends on / 依赖: NonnegSpectrumClass, NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg, quasispectrum_nonneg_of_nonneg, spectrum_subset_quasispectrum
-/
lemma spectrum_nonneg_of_nonneg {𝕜 A : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
    [Ring A] [PartialOrder A]
    [Algebra 𝕜 A] [NonnegSpectrumClass 𝕜 A] ⦃a : A⦄ (ha : 0 <= a) ⦃x : 𝕜⦄ (hx : x in spectrum 𝕜 a) :
    0 <= x :=
  NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg a ha x (spectrum_subset_quasispectrum 𝕜 a hx)

grind_pattern spectrum_nonneg_of_nonneg => x in spectrum 𝕜 a

/-! ### Restriction of the spectrum -/

/--
Definition of `QuasispectrumRestricts` / `QuasispectrumRestricts` 的定义

English:
structure QuasispectrumRestricts
  axioms and operations (2):
    - rightInvOn : (quasispectrum S a).RightInvOn f (algebraMap R S)
    - left_inv : Function.LeftInverse f (algebraMap R S)

中文:
结构 QuasispectrumRestricts
  公理与运算 (2 个):
    - rightInvOn : (quasispectrum S a).RightInvOn f (algebraMap R S)
    - left_inv : 函数.左逆 f (algebraMap R S)
-/
structure QuasispectrumRestricts
    {R S A : Type*} [CommSemiring R] [CommSemiring S] [NonUnitalRing A]
    [Module R A] [Module S A] [Algebra R S] (a : A) (f : S -> R) : Prop where
  /-- `f` is a right inverse of `algebraMap R S` when restricted to `quasispectrum S a`. -/
  rightInvOn : (quasispectrum S a).RightInvOn f (algebraMap R S)
  /-- `f` is a left inverse of `algebraMap R S`. -/
  left_inv : Function.LeftInverse f (algebraMap R S)

/--
lemma `quasispectrumRestricts_iff` / 引理 `quasispectrumRestricts_iff`

English:
lemma quasispectrumRestricts_iff
  proof: ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

@[simp]

中文:
引理 quasispectrumRestricts_iff
  证明: ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

@[simp]
-/
lemma quasispectrumRestricts_iff
    {R S A : Type*} [CommSemiring R] [CommSemiring S] [NonUnitalRing A]
    [Module R A] [Module S A] [Algebra R S] (a : A) (f : S -> R) :
    QuasispectrumRestricts a f ↔ (quasispectrum S a).RightInvOn f (algebraMap R S) ∧
      Function.LeftInverse f (algebraMap R S) :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

@[simp]
/--
theorem `quasispectrum.algebraMap_mem_iff` / 定理 `quasispectrum.algebraMap_mem_iff`

English:
theorem quasispectrum.algebraMap_mem_iff
  statement: (S : Type*) {R A : Type*} [Semifield R] [Field S]
  proof: by
  simp_rw [Unitization.quasispectrum_eq_spectrum_inr' _ S a, spectrum.algebraMap_mem_iff]

protected alias ⟨quasispectrum.of_algebraMap_mem, quasispectrum.algebraMap_mem⟩ :=
  quasispectrum.algebraMap_mem_iff

@[simp]

中文:
定理 quasispectrum.algebraMap_mem_iff
  结论: (S : 类型) {R A : 类型} [半域 R] [域 S]
  证明: by
  simp_rw [Unitization.quasispectrum_eq_spectrum_inr' _ S a, spectrum.algebraMap_mem_iff]

protected alias ⟨quasispectrum.of_algebraMap_mem, quasispectrum.algebraMap_mem⟩ :=
  quasispectrum.algebraMap_mem_iff

@[simp]

Depends on / 依赖: Unitization, Unitization.quasispectrum_eq_spectrum_inr, algebraMap_mem_iff, quasispectrum_eq_spectrum_inr, simp_rw, spectrum, spectrum.algebraMap_mem_iff
-/
theorem quasispectrum.algebraMap_mem_iff (S : Type*) {R A : Type*} [Semifield R] [Field S]
    [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r in quasispectrum S a ↔ r in quasispectrum R a := by
  simp_rw [Unitization.quasispectrum_eq_spectrum_inr' _ S a, spectrum.algebraMap_mem_iff]

protected alias ⟨quasispectrum.of_algebraMap_mem, quasispectrum.algebraMap_mem⟩ :=
  quasispectrum.algebraMap_mem_iff

@[simp]
/--
theorem `quasispectrum.preimage_algebraMap` / 定理 `quasispectrum.preimage_algebraMap`

English:
theorem quasispectrum.preimage_algebraMap
  statement: (S : Type*) {R A : Type*} [Semifield R] [Field S]
  proof: Set.ext fun _ => quasispectrum.algebraMap_mem_iff _

中文:
定理 quasispectrum.preimage_algebraMap
  结论: (S : 类型) {R A : 类型} [半域 R] [域 S]
  证明: Set.ext fun _ => quasispectrum.algebraMap_mem_iff _

Depends on / 依赖: Set.ext, algebraMap_mem_iff, quasispectrum, quasispectrum.algebraMap_mem_iff
-/
theorem quasispectrum.preimage_algebraMap (S : Type*) {R A : Type*} [Semifield R] [Field S]
    [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' quasispectrum S a = quasispectrum R a :=
  Set.ext fun _ => quasispectrum.algebraMap_mem_iff _

namespace QuasispectrumRestricts

section NonUnital

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]
variable [Algebra R S] {a : A} {f : S -> R}

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (h : QuasispectrumRestricts a f)
  statement: f 0 = 0
  proof: by
  rw [← h.left_inv 0]; rw [map_zero (algebraMap R S)]

中文:
定理 map_zero
  条件: (h : QuasispectrumRestricts a f)
  结论: f 0 = 0
  证明: by
  rw [← h.left_inv 0]; rw [map_zero (algebraMap R S)]
-/
protected theorem map_zero (h : QuasispectrumRestricts a f) : f 0 = 0 := by
  rw [← h.left_inv 0]; rw [map_zero (algebraMap R S)]

/--
theorem `of_subset_range_algebraMap` / 定理 `of_subset_range_algebraMap`

English:
theorem of_subset_range_algebraMap
  statement: (hf : f.LeftInverse (algebraMap R S))
  proof: fun s hs => by obtain ⟨r, rfl⟩ := h hs; rw [hf r]
  left_inv := hf

中文:
定理 of_subset_range_algebraMap
  结论: (hf : f.左逆 (algebraMap R S))
  证明: fun s hs => by obtain ⟨r, rfl⟩ := h hs; rw [hf r]
  left_inv := hf

Depends on / 依赖: IsFractionRing, IsFractionRing.div_surjective, algebraMap, algebraMap_eq_smul_one, div_surjective, isEpi_iff_forall_one_tmul_eq, replace, smul_def, smul_div_assoc, smul_tmul
-/
theorem of_subset_range_algebraMap (hf : f.LeftInverse (algebraMap R S))
    (h : quasispectrum S a subseteq Set.range (algebraMap R S)) : QuasispectrumRestricts a f where
  rightInvOn := fun s hs => by obtain ⟨r, rfl⟩ := h hs; rw [hf r]
  left_inv := hf

/--
lemma `of_quasispectrum_eq` / 引理 `of_quasispectrum_eq`

English:
lemma of_quasispectrum_eq
  statement: {a b : A} {f : S -> R} (ha : QuasispectrumRestricts a f)
  proof: h ▸ ha.rightInvOn
  left_inv := ha.left_inv

中文:
引理 of_quasispectrum_eq
  结论: {a b : A} {f : S -> R} (ha : QuasispectrumRestricts a f)
  证明: h ▸ ha.rightInvOn
  left_inv := ha.left_inv

Depends on / 依赖: ha.rightInvOn, rightInvOn
-/
lemma of_quasispectrum_eq {a b : A} {f : S -> R} (ha : QuasispectrumRestricts a f)
    (h : quasispectrum S a = quasispectrum S b) : QuasispectrumRestricts b f where
  rightInvOn := h ▸ ha.rightInvOn
  left_inv := ha.left_inv

variable [IsScalarTower S A A] [SMulCommClass S A A]

/--
lemma `mul_comm_iff` / 引理 `mul_comm_iff`

English:
lemma mul_comm_iff
  given: {f : S -> R} {a b : A}
  proof: by
  simp only [quasispectrumRestricts_iff, quasispectrum.mul_comm]

alias ⟨mul_comm, _⟩ := mul_comm_iff

中文:
引理 mul_comm_iff
  条件: {f : S -> R} {a b : A}
  证明: by
  simp only [quasispectrumRestricts_iff, quasispectrum.mul_comm]

alias ⟨mul_comm, _⟩ := mul_comm_iff

Depends on / 依赖: mul_comm, quasispectrum, quasispectrum.mul_comm, quasispectrumRestricts_iff
-/
lemma mul_comm_iff {f : S -> R} {a b : A} :
    QuasispectrumRestricts (a * b) f ↔ QuasispectrumRestricts (b * a) f := by
  simp only [quasispectrumRestricts_iff, quasispectrum.mul_comm]

alias ⟨mul_comm, _⟩ := mul_comm_iff

variable [IsScalarTower R S A]

/--
theorem `algebraMap_image` / 定理 `algebraMap_image`

English:
theorem algebraMap_image
  given: (h : QuasispectrumRestricts a f)
  proof: by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [quasispectrum.preimage_algebraMap] using
      (quasispectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨quasispectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

中文:
定理 algebraMap_image
  条件: (h : QuasispectrumRestricts a f)
  证明: by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [quasispectrum.preimage_algebraMap] using
      (quasispectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨quasispectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

Depends on / 依赖: Set.eq_of_subset_of_subset, algebraMap, eq_of_subset_of_subset, h.rightInvOn, image_preimage_subset, of_algebraMap_mem, preimage_algebraMap, quasispectrum, quasispectrum.of_algebraMap_mem, quasispectrum.preimage_algebraMap, rightInvOn
-/
theorem algebraMap_image (h : QuasispectrumRestricts a f) :
    algebraMap R S '' quasispectrum R a = quasispectrum S a := by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [quasispectrum.preimage_algebraMap] using
      (quasispectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨quasispectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

/--
theorem `image` / 定理 `image`

English:
theorem image
  given: (h : QuasispectrumRestricts a f)
  statement: f '' quasispectrum S a = quasispectrum R a
  proof: by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']

中文:
定理 像
  条件: (h : QuasispectrumRestricts a f)
  结论: f '' quasispectrum S a = quasispectrum R a
  证明: by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']

Depends on / 依赖: Set.image_id, Set.image_image, algebraMap_image, h.algebraMap_image, h.left_inv, image_id, image_image, left_inv
-/
theorem image (h : QuasispectrumRestricts a f) : f '' quasispectrum S a = quasispectrum R a := by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']

/--
theorem `apply_mem` / 定理 `apply_mem`

English:
theorem apply_mem
  given: (h : QuasispectrumRestricts a f) {s : S} (hs : s in quasispectrum S a)
  proof: h.image ▸ ⟨s, hs, rfl⟩

中文:
定理 apply_mem
  条件: (h : QuasispectrumRestricts a f) {s : S} (hs : s in quasispectrum S a)
  证明: h.image ▸ ⟨s, hs, rfl⟩

Depends on / 依赖: CommSemiring, Semiring, h.image, toAlgHomClass
-/
theorem apply_mem (h : QuasispectrumRestricts a f) {s : S} (hs : s in quasispectrum S a) :
    f s in quasispectrum R a :=
  h.image ▸ ⟨s, hs, rfl⟩

/--
theorem `subset_preimage` / 定理 `subset_preimage`

English:
theorem subset_preimage
  given: (h : QuasispectrumRestricts a f)
  proof: h.image ▸ (quasispectrum S a).subset_preimage_image f

中文:
定理 subset_preimage
  条件: (h : QuasispectrumRestricts a f)
  证明: h.image ▸ (quasispectrum S a).subset_preimage_image f

Depends on / 依赖: CommSemiring, h.image, quasispectrum, subset_preimage_image, toLinearEquivClass
-/
theorem subset_preimage (h : QuasispectrumRestricts a f) :
    quasispectrum S a subseteq f ⁻¹' quasispectrum R a :=
  h.image ▸ (quasispectrum S a).subset_preimage_image f

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  statement: {R₁ R₂ R₃ A : Type*} [Semifield R₁] [Field R₂] [Field R₃]
  proof: by
    convert! hfge ▸ hf.left_inv.comp hg.left_inv
    congrm (⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))
  rightInvOn := by
    convert! hfge ▸ hg.rightInvOn.comp hf.rightInvOn fun _ => hf.apply_mem
    congrm (⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))

中文:
引理 comp
  结论: {R₁ R₂ R₃ A : 类型} [半域 R₁] [域 R₂] [域 R₃]
  证明: by
    convert! hfge ▸ hf.left_inv.comp hg.left_inv
    congrm (⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))
  rightInvOn := by
    convert! hfge ▸ hg.rightInvOn.comp hf.rightInvOn fun _ => hf.apply_mem
    congrm (⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))
-/
protected lemma comp {R₁ R₂ R₃ A : Type*} [Semifield R₁] [Field R₂] [Field R₃]
    [NonUnitalRing A] [Module R₁ A] [Module R₂ A] [Module R₃ A] [Algebra R₁ R₂] [Algebra R₂ R₃]
    [Algebra R₁ R₃] [IsScalarTower R₁ R₂ R₃] [IsScalarTower R₂ R₃ A] [IsScalarTower R₃ A A]
    [SMulCommClass R₃ A A] {a : A} {f : R₃ -> R₂} {g : R₂ -> R₁} {e : R₃ -> R₁} (hfge : g ∘ f = e)
    (hf : QuasispectrumRestricts a f) (hg : QuasispectrumRestricts a g) :
    QuasispectrumRestricts a e where
  left_inv := by
    convert! hfge ▸ hf.left_inv.comp hg.left_inv
    congrm (⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))
  rightInvOn := by
    convert! hfge ▸ hg.rightInvOn.comp hf.rightInvOn fun _ => hf.apply_mem
    congrm (⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))

end NonUnital

end QuasispectrumRestricts

/-- A (reducible) alias of `QuasispectrumRestricts` which enforces stronger type class assumptions
on the types involved, as it's really intended for the `spectrum`. The separate definition also
allows for dot notation. -/
@[reducible]
/--
Definition of `SpectrumRestricts` / `SpectrumRestricts` 的定义

English:
definition SpectrumRestricts
  body: QuasispectrumRestricts a f

中文:
定义 SpectrumRestricts
  定义体: QuasispectrumRestricts a f

Depends on / 依赖: QuasispectrumRestricts
-/
def SpectrumRestricts
    {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R A] [Algebra S A] [Algebra R S] (a : A) (f : S -> R) : Prop :=
  QuasispectrumRestricts a f

namespace SpectrumRestricts

section Unital

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S -> R}

/--
theorem `rightInvOn` / 定理 `rightInvOn`

English:
theorem rightInvOn
  given: (h : SpectrumRestricts a f)
  statement: (spectrum S a).RightInvOn f (algebraMap R S)
  proof: (QuasispectrumRestricts.rightInvOn h).mono spectrum_subset_quasispectrum _ _

中文:
定理 rightInvOn
  条件: (h : SpectrumRestricts a f)
  结论: (spectrum S a).RightInvOn f (algebraMap R S)
  证明: (QuasispectrumRestricts.rightInvOn h).mono spectrum_subset_quasispectrum _ _

Depends on / 依赖: QuasispectrumRestricts, QuasispectrumRestricts.rightInvOn, rightInvOn, spectrum_subset_quasispectrum
-/
theorem rightInvOn (h : SpectrumRestricts a f) : (spectrum S a).RightInvOn f (algebraMap R S) :=
(QuasispectrumRestricts.rightInvOn h).mono spectrum_subset_quasispectrum _ _

/--
theorem `of_rightInvOn` / 定理 `of_rightInvOn`

English:
theorem of_rightInvOn
  statement: (h₁ : Function.LeftInverse f (algebraMap R S))
  proof: by
    obtain (rfl | hx) := mem_quasispectrum_iff.mp hx
    · simpa using h₁ 0
    · exact h₂ hx
  left_inv := h₁

中文:
定理 of_rightInvOn
  结论: (h₁ : 函数.左逆 f (algebraMap R S))
  证明: by
    obtain (rfl | hx) := mem_quasispectrum_iff.mp hx
    · simpa using h₁ 0
    · exact h₂ hx
  left_inv := h₁

Depends on / 依赖: left_inv, mem_quasispectrum_iff, mem_quasispectrum_iff.mp
-/
theorem of_rightInvOn (h₁ : Function.LeftInverse f (algebraMap R S))
    (h₂ : (spectrum S a).RightInvOn f (algebraMap R S)) : SpectrumRestricts a f where
  rightInvOn x hx := by
    obtain (rfl | hx) := mem_quasispectrum_iff.mp hx
    · simpa using h₁ 0
    · exact h₂ hx
  left_inv := h₁

/--
lemma `_root_.spectrumRestricts_iff` / 引理 `_root_.spectrumRestricts_iff`

English:
lemma _root_.spectrumRestricts_iff
  proof: ⟨fun h => ⟨h.rightInvOn, h.left_inv⟩, fun h => .of_rightInvOn h.2 h.1⟩

中文:
引理 _root_.spectrumRestricts_iff
  证明: ⟨fun h => ⟨h.rightInvOn, h.left_inv⟩, fun h => .of_rightInvOn h.2 h.1⟩

Depends on / 依赖: h.left_inv, h.rightInvOn, left_inv, of_rightInvOn, rightInvOn
-/
lemma _root_.spectrumRestricts_iff :
    SpectrumRestricts a f ↔ (spectrum S a).RightInvOn f (algebraMap R S) ∧
      Function.LeftInverse f (algebraMap R S) :=
  ⟨fun h => ⟨h.rightInvOn, h.left_inv⟩, fun h => .of_rightInvOn h.2 h.1⟩

/--
theorem `of_subset_range_algebraMap` / 定理 `of_subset_range_algebraMap`

English:
theorem of_subset_range_algebraMap
  statement: (hf : f.LeftInverse (algebraMap R S))
  proof: fun s hs => by
    rw [mem_quasispectrum_iff] at hs
    obtain (rfl | hs) := hs
    · simpa using hf 0
    · obtain ⟨r, rfl⟩ := h hs
      rw [hf r]
  left_inv := hf

中文:
定理 of_subset_range_algebraMap
  结论: (hf : f.左逆 (algebraMap R S))
  证明: fun s hs => by
    rw [mem_quasispectrum_iff] at hs
    obtain (rfl | hs) := hs
    · simpa using hf 0
    · obtain ⟨r, rfl⟩ := h hs
      rw [hf r]
  left_inv := hf

Depends on / 依赖: left_inv, mem_quasispectrum_iff
-/
theorem of_subset_range_algebraMap (hf : f.LeftInverse (algebraMap R S))
    (h : spectrum S a subseteq Set.range (algebraMap R S)) : SpectrumRestricts a f where
  rightInvOn := fun s hs => by
    rw [mem_quasispectrum_iff] at hs
    obtain (rfl | hs) := hs
    · simpa using hf 0
    · obtain ⟨r, rfl⟩ := h hs
      rw [hf r]
  left_inv := hf

/--
lemma `of_spectrum_eq` / 引理 `of_spectrum_eq`

English:
lemma of_spectrum_eq
  statement: {a b : A} {f : S -> R} (ha : SpectrumRestricts a f)
  proof: by
    rw [quasispectrum_eq_spectrum_union_zero]; rw [← h]; rw [← quasispectrum_eq_spectrum_union_zero]
    exact QuasispectrumRestricts.rightInvOn ha
  left_inv := ha.left_inv

中文:
引理 of_spectrum_eq
  结论: {a b : A} {f : S -> R} (ha : SpectrumRestricts a f)
  证明: by
    rw [quasispectrum_eq_spectrum_union_zero]; rw [← h]; rw [← quasispectrum_eq_spectrum_union_zero]
    exact QuasispectrumRestricts.rightInvOn ha
  left_inv := ha.left_inv

Depends on / 依赖: QuasispectrumRestricts, QuasispectrumRestricts.rightInvOn, ha.left_inv, left_inv, quasispectrum_eq_spectrum_union_zero, rightInvOn
-/
lemma of_spectrum_eq {a b : A} {f : S -> R} (ha : SpectrumRestricts a f)
    (h : spectrum S a = spectrum S b) : SpectrumRestricts b f where
  rightInvOn := by
    rw [quasispectrum_eq_spectrum_union_zero]; rw [← h]; rw [← quasispectrum_eq_spectrum_union_zero]
    exact QuasispectrumRestricts.rightInvOn ha
  left_inv := ha.left_inv

/--
lemma `mul_comm_iff` / 引理 `mul_comm_iff`

English:
lemma mul_comm_iff
  statement: {R S A : Type*} [Semifield R] [Field S] [Ring A]
  proof: QuasispectrumRestricts.mul_comm_iff

alias ⟨mul_comm, _⟩ := mul_comm_iff

中文:
引理 mul_comm_iff
  结论: {R S A : 类型} [半域 R] [域 S] [环 A]
  证明: QuasispectrumRestricts.mul_comm_iff

alias ⟨mul_comm, _⟩ := mul_comm_iff

Depends on / 依赖: QuasispectrumRestricts, QuasispectrumRestricts.mul_comm_iff, mul_comm_iff
-/
lemma mul_comm_iff {R S A : Type*} [Semifield R] [Field S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] {a b : A} {f : S -> R} :
    SpectrumRestricts (a * b) f ↔ SpectrumRestricts (b * a) f :=
  QuasispectrumRestricts.mul_comm_iff

alias ⟨mul_comm, _⟩ := mul_comm_iff

variable [IsScalarTower R S A]

/--
theorem `algebraMap_image` / 定理 `algebraMap_image`

English:
theorem algebraMap_image
  given: (h : SpectrumRestricts a f)
  proof: by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [spectrum.preimage_algebraMap] using
      (spectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨spectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

中文:
定理 algebraMap_image
  条件: (h : SpectrumRestricts a f)
  证明: by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [spectrum.preimage_algebraMap] using
      (spectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨spectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

Depends on / 依赖: Set.eq_of_subset_of_subset, algebraMap, eq_of_subset_of_subset, h.rightInvOn, image_preimage_subset, of_algebraMap_mem, preimage_algebraMap, rightInvOn, spectrum, spectrum.of_algebraMap_mem, spectrum.preimage_algebraMap
-/
theorem algebraMap_image (h : SpectrumRestricts a f) :
    algebraMap R S '' spectrum R a = spectrum S a := by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [spectrum.preimage_algebraMap] using
      (spectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨spectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

/--
theorem `image` / 定理 `image`

English:
theorem image
  given: (h : SpectrumRestricts a f)
  statement: f '' spectrum S a = spectrum R a
  proof: by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']

中文:
定理 像
  条件: (h : SpectrumRestricts a f)
  结论: f '' spectrum S a = spectrum R a
  证明: by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']

Depends on / 依赖: Set.image_id, Set.image_image, algebraMap_image, h.algebraMap_image, h.left_inv, image_id, image_image, left_inv
-/
theorem image (h : SpectrumRestricts a f) : f '' spectrum S a = spectrum R a := by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']

/--
theorem `apply_mem` / 定理 `apply_mem`

English:
theorem apply_mem
  given: (h : SpectrumRestricts a f) {s : S} (hs : s in spectrum S a)
  proof: h.image ▸ ⟨s, hs, rfl⟩

中文:
定理 apply_mem
  条件: (h : SpectrumRestricts a f) {s : S} (hs : s in spectrum S a)
  证明: h.image ▸ ⟨s, hs, rfl⟩

Depends on / 依赖: h.image
-/
theorem apply_mem (h : SpectrumRestricts a f) {s : S} (hs : s in spectrum S a) :
    f s in spectrum R a :=
  h.image ▸ ⟨s, hs, rfl⟩

/--
theorem `subset_preimage` / 定理 `subset_preimage`

English:
theorem subset_preimage
  given: (h : SpectrumRestricts a f)
  statement: spectrum S a subseteq f ⁻¹' spectrum R a
  proof: h.image ▸ (spectrum S a).subset_preimage_image f

中文:
定理 subset_preimage
  条件: (h : SpectrumRestricts a f)
  结论: spectrum S a subseteq f ⁻¹' spectrum R a
  证明: h.image ▸ (spectrum S a).subset_preimage_image f

Depends on / 依赖: h.image, spectrum, subset_preimage_image
-/
theorem subset_preimage (h : SpectrumRestricts a f) : spectrum S a subseteq f ⁻¹' spectrum R a :=
  h.image ▸ (spectrum S a).subset_preimage_image f

end Unital

end SpectrumRestricts

/--
theorem `quasispectrumRestricts_iff_spectrumRestricts_inr` / 定理 `quasispectrumRestricts_iff_spectrumRestricts_inr`

English:
theorem quasispectrumRestricts_iff_spectrumRestricts_inr
  statement: (S : Type*) {R A : Type*} [Semifield R]
  proof: by
  rw [quasispectrumRestricts_iff]; rw [spectrumRestricts_iff]; rw [← Unitization.quasispectrum_eq_spectrum_inr']

中文:
定理 quasispectrumRestricts_iff_spectrumRestricts_inr
  结论: (S : 类型) {R A : 类型} [半域 R]
  证明: by
  rw [quasispectrumRestricts_iff]; rw [spectrumRestricts_iff]; rw [← Unitization.quasispectrum_eq_spectrum_inr']

Depends on / 依赖: Unitization, Unitization.quasispectrum_eq_spectrum_inr, quasispectrumRestricts_iff, quasispectrum_eq_spectrum_inr, spectrumRestricts_iff
-/
theorem quasispectrumRestricts_iff_spectrumRestricts_inr (S : Type*) {R A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [IsScalarTower R S A] {a : A} {f : S -> R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts (a : Unitization S A) f := by
  rw [quasispectrumRestricts_iff]; rw [spectrumRestricts_iff]; rw [← Unitization.quasispectrum_eq_spectrum_inr']

/--
lemma `quasispectrumRestricts_iff_spectrumRestricts_inr'` / 引理 `quasispectrumRestricts_iff_spectrumRestricts_inr'`

English:
lemma quasispectrumRestricts_iff_spectrumRestricts_inr'
  proof: by
  simp only [quasispectrumRestricts_iff, SpectrumRestricts, Unitization.quasispectrum_inr_eq]

中文:
引理 quasispectrumRestricts_iff_spectrumRestricts_inr'
  证明: by
  simp only [quasispectrumRestricts_iff, SpectrumRestricts, Unitization.quasispectrum_inr_eq]

Depends on / 依赖: SpectrumRestricts, Unitization, Unitization.quasispectrum_inr_eq, quasispectrumRestricts_iff, quasispectrum_inr_eq
-/
lemma quasispectrumRestricts_iff_spectrumRestricts_inr'
    {R S' A : Type*} (S : Type*) [Semifield R] [Semifield S'] [Field S] [NonUnitalRing A]
    [Module R A] [Module S' A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [Algebra R S'] [Algebra S' S] [Algebra R S] [IsScalarTower S' S A] [IsScalarTower R S A]
    {a : A} {f : S' -> R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts (a : Unitization S A) f := by
  simp only [quasispectrumRestricts_iff, SpectrumRestricts, Unitization.quasispectrum_inr_eq]

/--
theorem `quasispectrumRestricts_iff_spectrumRestricts` / 定理 `quasispectrumRestricts_iff_spectrumRestricts`

English:
theorem quasispectrumRestricts_iff_spectrumRestricts
  statement: {R S A : Type*} [Semifield R] [Semifield S]
  proof: by rfl

中文:
定理 quasispectrumRestricts_iff_spectrumRestricts
  结论: {R S A : 类型} [半域 R] [半域 S]
  证明: by rfl
-/
theorem quasispectrumRestricts_iff_spectrumRestricts {R S A : Type*} [Semifield R] [Semifield S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S -> R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts a f := by rfl
