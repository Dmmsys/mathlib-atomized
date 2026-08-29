/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Algebra.Star.MonoidHom
public import Mathlib.Algebra.Star.StarProjection

/-!
# Unitary elements of a star monoid

This file defines `unitary R`, where `R` is a star monoid, as the submonoid made of the elements
that satisfy `star U * U = 1` and `U * star U = 1`, and these form a group.
This includes, for instance, unitary operators on Hilbert spaces.

See also `Matrix.UnitaryGroup` for specializations to `unitary (Matrix n n R)`.

## Tags

unitary
-/

@[expose] public section


/--
Definition of `unitary` / `unitary` 的定义

English:
definition unitary
  signature: (R : Type*) [Monoid R] [StarMul R]
  body: { U | star U * U = 1 ∧ U * star U = 1 }
  one_mem' := by simp only [mul_one, and_self_iff, Set.mem_ofPred_eq, star_one]
  mul_mem' := @fun U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩ => by
    refine ⟨?_, ?_⟩
    · calc
        star (U * B) * (U * B) = star B * star U * U * B := by simp only [mul_assoc, star_mul]
   

中文:
定义 unitary
  签名: (R : 类型) [幺半群 R] [StarMul R]
  定义体: { U | star U * U = 1 ∧ U * star U = 1 }
  one_mem' := by simp only [mul_one, and_self_iff, Set.mem_ofPred_eq, star_one]
  mul_mem' := @fun U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩ => by
    refine ⟨?_, ?_⟩
    · calc
        star (U * B) * (U * B) = star B * star U * U * B := by simp only [mul_assoc, star_mul]
   
-/
def unitary (R : Type*) [Monoid R] [StarMul R] : Submonoid R where
  carrier := { U | star U * U = 1 ∧ U * star U = 1 }
  one_mem' := by simp only [mul_one, and_self_iff, Set.mem_ofPred_eq, star_one]
  mul_mem' := @fun U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩ => by
    refine ⟨?_, ?_⟩
    · calc
        star (U * B) * (U * B) = star B * star U * U * B := by simp only [mul_assoc, star_mul]
        _ = star B * (star U * U) * B := by rw [← mul_assoc]
        _ = 1 := by rw [hA₁, mul_one, hB₁]
    · calc
        U * B * star (U * B) = U * B * (star B * star U) := by rw [star_mul]
        _ = U * (B * star B) * star U := by simp_rw [← mul_assoc]
        _ = 1 := by rw [hB₂, mul_one, hA₂]

variable {R : Type*}

namespace Unitary

section Monoid

variable [Monoid R] [StarMul R]

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {U : R}
  statement: U in unitary R ↔ star U * U = 1 ∧ U * star U = 1
  proof: Iff.rfl

@[simp]

中文:
定理 mem_iff
  条件: {U : R}
  结论: U in unitary R ↔ star U * U = 1 ∧ U * star U = 1
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_iff {U : R} : U in unitary R ↔ star U * U = 1 ∧ U * star U = 1 :=
  Iff.rfl

@[simp]
/--
theorem `star_mul_self_of_mem` / 定理 `star_mul_self_of_mem`

English:
theorem star_mul_self_of_mem
  given: {U : R} (hU : U in unitary R)
  statement: star U * U = 1
  proof: hU.1

@[simp]

中文:
定理 star_mul_self_of_mem
  条件: {U : R} (hU : U in unitary R)
  结论: star U * U = 1
  证明: hU.1

@[simp]
-/
theorem star_mul_self_of_mem {U : R} (hU : U in unitary R) : star U * U = 1 :=
  hU.1

@[simp]
/--
theorem `mul_star_self_of_mem` / 定理 `mul_star_self_of_mem`

English:
theorem mul_star_self_of_mem
  given: {U : R} (hU : U in unitary R)
  statement: U * star U = 1
  proof: hU.2

中文:
定理 mul_star_self_of_mem
  条件: {U : R} (hU : U in unitary R)
  结论: U * star U = 1
  证明: hU.2
-/
theorem mul_star_self_of_mem {U : R} (hU : U in unitary R) : U * star U = 1 :=
  hU.2

/--
theorem `star_mem` / 定理 `star_mem`

English:
theorem star_mem
  given: {U : R} (hU : U in unitary R)
  statement: star U in unitary R
  proof: ⟨by rw [star_star, mul_star_self_of_mem hU], by rw [star_star, star_mul_self_of_mem hU]⟩

@[simp]

中文:
定理 star_mem
  条件: {U : R} (hU : U in unitary R)
  结论: star U in unitary R
  证明: ⟨by rw [star_star, mul_star_self_of_mem hU], by rw [star_star, star_mul_self_of_mem hU]⟩

@[simp]

Depends on / 依赖: mul_star_self_of_mem, star_mul_self_of_mem, star_star
-/
theorem star_mem {U : R} (hU : U in unitary R) : star U in unitary R :=
  ⟨by rw [star_star, mul_star_self_of_mem hU], by rw [star_star, star_mul_self_of_mem hU]⟩

@[simp]
/--
theorem `star_mem_iff` / 定理 `star_mem_iff`

English:
theorem star_mem_iff
  given: {U : R}
  statement: star U in unitary R ↔ U in unitary R
  proof: ⟨fun h => star_star U ▸ star_mem h, star_mem⟩

中文:
定理 star_mem_iff
  条件: {U : R}
  结论: star U in unitary R ↔ U in unitary R
  证明: ⟨fun h => star_star U ▸ star_mem h, star_mem⟩

Depends on / 依赖: star_mem, star_star
-/
theorem star_mem_iff {U : R} : star U in unitary R ↔ U in unitary R :=
  ⟨fun h => star_star U ▸ star_mem h, star_mem⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (unitary R)
  body: ⟨fun U => ⟨star U, star_mem U.prop⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 对合 (unitary R)
  定义体: ⟨fun U => ⟨star U, star_mem U.prop⟩⟩

@[simp, norm_cast]

Depends on / 依赖: U.prop, star_mem
-/
instance : Star (unitary R) :=
  ⟨fun U => ⟨star U, star_mem U.prop⟩⟩

@[simp, norm_cast]
/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: {U : unitary R}
  statement: ↑(star U) = (star U : R)
  proof: rfl

中文:
定理 coe_star
  条件: {U : unitary R}
  结论: ↑(star U) = (star U : R)
  证明: rfl
-/
theorem coe_star {U : unitary R} : ↑(star U) = (star U : R) :=
  rfl

/--
theorem `coe_star_mul_self` / 定理 `coe_star_mul_self`

English:
theorem coe_star_mul_self
  given: (U : unitary R)
  statement: (star U : R) * U = 1
  proof: star_mul_self_of_mem U.prop

中文:
定理 coe_star_mul_self
  条件: (U : unitary R)
  结论: (star U : R) * U = 1
  证明: star_mul_self_of_mem U.prop

Depends on / 依赖: U.prop, star_mul_self_of_mem
-/
theorem coe_star_mul_self (U : unitary R) : (star U : R) * U = 1 :=
  star_mul_self_of_mem U.prop

/--
theorem `coe_mul_star_self` / 定理 `coe_mul_star_self`

English:
theorem coe_mul_star_self
  given: (U : unitary R)
  statement: (U : R) * star U = 1
  proof: mul_star_self_of_mem U.prop

@[simp]

中文:
定理 coe_mul_star_self
  条件: (U : unitary R)
  结论: (U : R) * star U = 1
  证明: mul_star_self_of_mem U.prop

@[simp]

Depends on / 依赖: U.prop, mul_star_self_of_mem
-/
theorem coe_mul_star_self (U : unitary R) : (U : R) * star U = 1 :=
  mul_star_self_of_mem U.prop

@[simp]
/--
theorem `star_mul_self` / 定理 `star_mul_self`

English:
theorem star_mul_self
  given: (U : unitary R)
  statement: star U * U = 1
  proof: Subtype.ext coe_star_mul_self U

@[simp]

中文:
定理 star_mul_self
  条件: (U : unitary R)
  结论: star U * U = 1
  证明: Subtype.ext coe_star_mul_self U

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, coe_star_mul_self
-/
theorem star_mul_self (U : unitary R) : star U * U = 1 :=
Subtype.ext coe_star_mul_self U

@[simp]
/--
theorem `mul_star_self` / 定理 `mul_star_self`

English:
theorem mul_star_self
  given: (U : unitary R)
  statement: U * star U = 1
  proof: Subtype.ext coe_mul_star_self U

中文:
定理 mul_star_self
  条件: (U : unitary R)
  结论: U * star U = 1
  证明: Subtype.ext coe_mul_star_self U

Depends on / 依赖: Subtype, Subtype.ext, coe_mul_star_self
-/
theorem mul_star_self (U : unitary R) : U * star U = 1 :=
Subtype.ext coe_mul_star_self U

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (unitary R)
  body: { Submonoid.toMonoid _ with
    inv := star
    inv_mul_cancel := star_mul_self }

中文:
实例 :
  签名: 群 (unitary R)
  定义体: { Submonoid.toMonoid _ with
    inv := star
    inv_mul_cancel := star_mul_self }

Depends on / 依赖: Submonoid, Submonoid.toMonoid, inv_mul_cancel, star_mul_self, toMonoid
-/
instance : Group (unitary R) :=
  { Submonoid.toMonoid _ with
    inv := star
    inv_mul_cancel := star_mul_self }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveStar (unitary R)
  body: ⟨by
    intro x
    ext
    rw [coe_star]; rw [coe_star]; rw [star_star]⟩

中文:
实例 :
  签名: InvolutiveStar (unitary R)
  定义体: ⟨by
    intro x
    ext
    rw [coe_star]; rw [coe_star]; rw [star_star]⟩

Depends on / 依赖: coe_star, star_star
-/
instance : InvolutiveStar (unitary R) :=
  ⟨by
    intro x
    ext
    rw [coe_star]; rw [coe_star]; rw [star_star]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul (unitary R)
  body: ⟨by
    intro x y
    ext
    rw [coe_star]; rw [Submonoid.coe_mul]; rw [Submonoid.coe_mul]; rw [coe_star]; rw [coe_star]; rw [star_mul]⟩

中文:
实例 :
  签名: StarMul (unitary R)
  定义体: ⟨by
    intro x y
    ext
    rw [coe_star]; rw [Submonoid.coe_mul]; rw [Submonoid.coe_mul]; rw [coe_star]; rw [coe_star]; rw [star_mul]⟩

Depends on / 依赖: Submonoid, Submonoid.coe_mul, coe_mul, coe_star, star_mul
-/
instance : StarMul (unitary R) :=
  ⟨by
    intro x y
    ext
    rw [coe_star]; rw [Submonoid.coe_mul]; rw [Submonoid.coe_mul]; rw [coe_star]; rw [coe_star]; rw [star_mul]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (unitary R)
  body: ⟨1⟩

中文:
实例 :
  签名: 可居 (unitary R)
  定义体: ⟨1⟩
-/
instance : Inhabited (unitary R) :=
  ⟨1⟩

/--
theorem `star_eq_inv` / 定理 `star_eq_inv`

English:
theorem star_eq_inv
  given: (U : unitary R)
  statement: star U = U⁻¹
  proof: rfl

中文:
定理 star_eq_inv
  条件: (U : unitary R)
  结论: star U = U⁻¹
  证明: rfl
-/
theorem star_eq_inv (U : unitary R) : star U = U⁻¹ :=
  rfl

/--
theorem `star_eq_inv'` / 定理 `star_eq_inv'`

English:
theorem star_eq_inv'
  statement: (star : unitary R -> unitary R) = Inv.inv
  proof: rfl

中文:
定理 star_eq_inv'
  结论: (star : unitary R -> unitary R) = 取逆.inv
  证明: rfl
-/
theorem star_eq_inv' : (star : unitary R -> unitary R) = Inv.inv :=
  rfl

/-- The unitary elements embed into the units. -/
@[simps]
/--
Definition of `toUnits` / `toUnits` 的定义

English:
definition toUnits
  signature: : unitary R ->* Rˣ where
  body: ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

中文:
定义 toUnits
  签名: : unitary R ->* Rˣ where
  定义体: ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

Depends on / 依赖: coe_mul_star_self, coe_star_mul_self
-/
def toUnits : unitary R ->* Rˣ where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

/--
theorem `toUnits_injective` / 定理 `toUnits_injective`

English:
theorem toUnits_injective
  statement: Function.Injective (toUnits : unitary R -> Rˣ)
  proof: fun _ _ h =>
Subtype.ext Units.ext_iff.mp h

中文:
定理 toUnits_injective
  结论: 函数.单射 (toUnits : unitary R -> Rˣ)
  证明: fun _ _ h =>
Subtype.ext Units.ext_iff.mp h
-/
theorem toUnits_injective : Function.Injective (toUnits : unitary R -> Rˣ) := fun _ _ h =>
Subtype.ext Units.ext_iff.mp h

/--
theorem `_root_.IsUnit.mem_unitary_iff_star_mul_self` / 定理 `_root_.IsUnit.mem_unitary_iff_star_mul_self`

English:
theorem _root_.IsUnit.mem_unitary_iff_star_mul_self
  given: {u : R} (hu : IsUnit u)
  proof: by
  rw [mem_iff]; rw [and_iff_left_of_imp fun h_mul => ?_]
  lift u to Rˣ using hu
  exact left_inv_eq_right_inv h_mul u.mul_inv ▸ u.mul_inv

中文:
定理 _root_.是单位.mem_unitary_iff_star_mul_self
  条件: {u : R} (hu : 是单位 u)
  证明: by
  rw [mem_iff]; rw [and_iff_left_of_imp fun h_mul => ?_]
  lift u to Rˣ using hu
  exact left_inv_eq_right_inv h_mul u.mul_inv ▸ u.mul_inv

Depends on / 依赖: and_iff_left_of_imp, h_mul, left_inv_eq_right_inv, mem_iff, mul_inv, u.mul_inv
-/
theorem _root_.IsUnit.mem_unitary_iff_star_mul_self {u : R} (hu : IsUnit u) :
    u in unitary R ↔ star u * u = 1 := by
  rw [mem_iff]; rw [and_iff_left_of_imp fun h_mul => ?_]
  lift u to Rˣ using hu
  exact left_inv_eq_right_inv h_mul u.mul_inv ▸ u.mul_inv

/--
theorem `_root_.IsUnit.mem_unitary_iff_mul_star_self` / 定理 `_root_.IsUnit.mem_unitary_iff_mul_star_self`

English:
theorem _root_.IsUnit.mem_unitary_iff_mul_star_self
  given: {u : R} (hu : IsUnit u)
  proof: by
  rw [← star_mem_iff]; rw [hu.star.mem_unitary_iff_star_mul_self]; rw [star_star]

alias ⟨_, _root_.IsUnit.mem_unitary_of_star_mul_self⟩ := IsUnit.mem_unitary_iff_star_mul_self
alias ⟨_, _root_.IsUnit.mem_unitary_of_mul_star_self⟩ := IsUnit.mem_unitary_iff_mul_star_self

中文:
定理 _root_.是单位.mem_unitary_iff_mul_star_self
  条件: {u : R} (hu : 是单位 u)
  证明: by
  rw [← star_mem_iff]; rw [hu.star.mem_unitary_iff_star_mul_self]; rw [star_star]

alias ⟨_, _root_.IsUnit.mem_unitary_of_star_mul_self⟩ := IsUnit.mem_unitary_iff_star_mul_self
alias ⟨_, _root_.IsUnit.mem_unitary_of_mul_star_self⟩ := IsUnit.mem_unitary_iff_mul_star_self

Depends on / 依赖: hu.star.mem_unitary_iff_star_mul_self, mem_unitary_iff_star_mul_self, star_mem_iff, star_star
-/
theorem _root_.IsUnit.mem_unitary_iff_mul_star_self {u : R} (hu : IsUnit u) :
    u in unitary R ↔ u * star u = 1 := by
  rw [← star_mem_iff]; rw [hu.star.mem_unitary_iff_star_mul_self]; rw [star_star]

alias ⟨_, _root_.IsUnit.mem_unitary_of_star_mul_self⟩ := IsUnit.mem_unitary_iff_star_mul_self
alias ⟨_, _root_.IsUnit.mem_unitary_of_mul_star_self⟩ := IsUnit.mem_unitary_iff_mul_star_self

/--
theorem `isUnit_coe` / 定理 `isUnit_coe`

English:
theorem isUnit_coe
  given: {U : unitary R}
  statement: IsUnit (U : R)
  proof: (Unitary.toUnits _).isUnit

中文:
定理 isUnit_coe
  条件: {U : unitary R}
  结论: 是单位 (U : R)
  证明: (Unitary.toUnits _).isUnit

Depends on / 依赖: Unitary, Unitary.toUnits, isUnit, toUnits
-/
theorem isUnit_coe {U : unitary R} : IsUnit (U : R) := (Unitary.toUnits _).isUnit

/--
theorem `mul_left_inj` / 定理 `mul_left_inj`

English:
theorem mul_left_inj
  given: {x y : R} (U : unitary R)
  proof: val_toUnits_apply U ▸ Units.mul_left_inj _

中文:
定理 mul_left_inj
  条件: {x y : R} (U : unitary R)
  证明: val_toUnits_apply U ▸ Units.mul_left_inj _
-/
protected theorem mul_left_inj {x y : R} (U : unitary R) :
    x * U = y * U ↔ x = y :=
  val_toUnits_apply U ▸ Units.mul_left_inj _

/--
theorem `mul_right_inj` / 定理 `mul_right_inj`

English:
theorem mul_right_inj
  given: {x y : R} (U : unitary R)
  proof: val_toUnits_apply U ▸ Units.mul_right_inj _

中文:
定理 mul_right_inj
  条件: {x y : R} (U : unitary R)
  证明: val_toUnits_apply U ▸ Units.mul_right_inj _
-/
protected theorem mul_right_inj {x y : R} (U : unitary R) :
    U * x = U * y ↔ x = y :=
  val_toUnits_apply U ▸ Units.mul_right_inj _

/--
lemma `mul_inv_mem_iff` / 引理 `mul_inv_mem_iff`

English:
lemma mul_inv_mem_iff
  given: {G : Type*} [Group G] [StarMul G] (a b : G)
  proof: by
  rw [(Group.isUnit _).mem_unitary_iff_star_mul_self]; rw [star_mul]; rw [star_inv]; rw [mul_assoc]; rw [inv_mul_eq_iff_eq_mul]; rw [mul_one]; rw [← mul_assoc]; rw [mul_inv_eq_iff_eq_mul]

中文:
引理 mul_inv_mem_iff
  条件: {G : 类型} [群 G] [StarMul G] (a b : G)
  证明: by
  rw [(Group.isUnit _).mem_unitary_iff_star_mul_self]; rw [star_mul]; rw [star_inv]; rw [mul_assoc]; rw [inv_mul_eq_iff_eq_mul]; rw [mul_one]; rw [← mul_assoc]; rw [mul_inv_eq_iff_eq_mul]

Depends on / 依赖: Group.isUnit, inv_mul_eq_iff_eq_mul, isUnit, mem_unitary_iff_star_mul_self, mul_assoc, mul_inv_eq_iff_eq_mul, mul_one, star_inv, star_mul
-/
lemma mul_inv_mem_iff {G : Type*} [Group G] [StarMul G] (a b : G) :
    a * b⁻¹ in unitary G ↔ star a * a = star b * b := by
  rw [(Group.isUnit _).mem_unitary_iff_star_mul_self]; rw [star_mul]; rw [star_inv]; rw [mul_assoc]; rw [inv_mul_eq_iff_eq_mul]; rw [mul_one]; rw [← mul_assoc]; rw [mul_inv_eq_iff_eq_mul]

/--
lemma `inv_mul_mem_iff` / 引理 `inv_mul_mem_iff`

English:
lemma inv_mul_mem_iff
  given: {G : Type*} [Group G] [StarMul G] (a b : G)
  proof: by
  simpa [← mul_inv_rev] using mul_inv_mem_iff a⁻¹ b⁻¹

中文:
引理 inv_mul_mem_iff
  条件: {G : 类型} [群 G] [StarMul G] (a b : G)
  证明: by
  simpa [← mul_inv_rev] using mul_inv_mem_iff a⁻¹ b⁻¹

Depends on / 依赖: mul_inv_mem_iff, mul_inv_rev
-/
lemma inv_mul_mem_iff {G : Type*} [Group G] [StarMul G] (a b : G) :
    a⁻¹ * b in unitary G ↔ a * star a = b * star b := by
  simpa [← mul_inv_rev] using mul_inv_mem_iff a⁻¹ b⁻¹

/--
theorem `_root_.Units.unitary_eq` / 定理 `_root_.Units.unitary_eq`

English:
theorem _root_.Units.unitary_eq
  statement: unitary Rˣ = (unitary R).comap (Units.coeHom R)
  proof: by
  ext
  simp [mem_iff, Units.ext_iff]

中文:
定理 _root_.单位群.unitary_eq
  结论: unitary Rˣ = (unitary R).comap (单位群.coeHom R)
  证明: by
  ext
  simp [mem_iff, Units.ext_iff]

Depends on / 依赖: Units.ext_iff, ext_iff, mem_iff
-/
theorem _root_.Units.unitary_eq : unitary Rˣ = (unitary R).comap (Units.coeHom R) := by
  ext
  simp [mem_iff, Units.ext_iff]

/--
lemma `_root_.Units.mul_inv_mem_unitary` / 引理 `_root_.Units.mul_inv_mem_unitary`

English:
lemma _root_.Units.mul_inv_mem_unitary
  given: (a b : Rˣ)
  proof: by
  simp [← mul_inv_mem_iff, Units.unitary_eq]

中文:
引理 _root_.单位群.mul_inv_mem_unitary
  条件: (a b : Rˣ)
  证明: by
  simp [← mul_inv_mem_iff, Units.unitary_eq]
-/
protected lemma _root_.Units.mul_inv_mem_unitary (a b : Rˣ) :
    (a * b⁻¹ : R) in unitary R ↔ star a * a = star b * b := by
  simp [← mul_inv_mem_iff, Units.unitary_eq]

/--
lemma `_root_.Units.inv_mul_mem_unitary` / 引理 `_root_.Units.inv_mul_mem_unitary`

English:
lemma _root_.Units.inv_mul_mem_unitary
  given: (a b : Rˣ)
  proof: by
  simp [← inv_mul_mem_iff, Units.unitary_eq]

中文:
引理 _root_.单位群.inv_mul_mem_unitary
  条件: (a b : Rˣ)
  证明: by
  simp [← inv_mul_mem_iff, Units.unitary_eq]
-/
protected lemma _root_.Units.inv_mul_mem_unitary (a b : Rˣ) :
    (a⁻¹ * b : R) in unitary R ↔ a * star a = b * star b := by
  simp [← inv_mul_mem_iff, Units.unitary_eq]

/--
Instance `instIsStarNormal` / 实例 `instIsStarNormal`

English:
instance instIsStarNormal
  signature: (u : unitary R)
  body: star_mul_self u

中文:
实例 instIsStarNormal
  签名: (u : unitary R)
  定义体: star_mul_self u

Depends on / 依赖: star_mul_self
-/
instance instIsStarNormal (u : unitary R) : IsStarNormal u where
.trans (mul_star_self u).symm star_comm_self := star_mul_self u

/--
Instance `coe_isStarNormal` / 实例 `coe_isStarNormal`

English:
instance coe_isStarNormal
  signature: (u : unitary R)
  body: congr(Subtype.val $(star_comm_self' u))

@[aesop 10% apply (rule_sets := [CStarAlgebra])]

中文:
实例 coe_isStarNormal
  签名: (u : unitary R)
  定义体: congr(Subtype.val $(star_comm_self' u))

@[aesop 10% apply (rule_sets := [CStarAlgebra])]

Depends on / 依赖: Subtype, Subtype.val, star_comm_self
-/
instance coe_isStarNormal (u : unitary R) : IsStarNormal (u : R) where
  star_comm_self := congr(Subtype.val $(star_comm_self' u))

@[aesop 10% apply (rule_sets := [CStarAlgebra])]
/--
lemma `_root_.isStarNormal_of_mem_unitary` / 引理 `_root_.isStarNormal_of_mem_unitary`

English:
lemma _root_.isStarNormal_of_mem_unitary
  given: {u : R} (hu : u in unitary R)
  statement: IsStarNormal u
  proof: coe_isStarNormal ⟨u, hu⟩

中文:
引理 _root_.isStarNormal_of_mem_unitary
  条件: {u : R} (hu : u in unitary R)
  结论: 是StarNormal u
  证明: coe_isStarNormal ⟨u, hu⟩

Depends on / 依赖: coe_isStarNormal
-/
lemma _root_.isStarNormal_of_mem_unitary {u : R} (hu : u in unitary R) : IsStarNormal u :=
  coe_isStarNormal ⟨u, hu⟩

/--
lemma `commute_self_star` / 引理 `commute_self_star`

English:
lemma commute_self_star
  given: (u : unitary R)
  statement: Commute u (star u)
  proof: by simp [commute_iff_eq]

中文:
引理 commute_self_star
  条件: (u : unitary R)
  结论: Commute u (star u)
  证明: by simp [commute_iff_eq]

Depends on / 依赖: commute_iff_eq
-/
lemma commute_self_star (u : unitary R) : Commute u (star u) := by simp [commute_iff_eq]
/--
lemma `commute_star_self` / 引理 `commute_star_self`

English:
lemma commute_star_self
  given: (u : unitary R)
  statement: Commute (star u) u
  proof: by simp [commute_iff_eq]

中文:
引理 commute_star_self
  条件: (u : unitary R)
  结论: Commute (star u) u
  证明: by simp [commute_iff_eq]

Depends on / 依赖: commute_iff_eq
-/
lemma commute_star_self (u : unitary R) : Commute (star u) u := by simp [commute_iff_eq]

/--
lemma `_root_.commute_unitary_star_self` / 引理 `_root_.commute_unitary_star_self`

English:
lemma _root_.commute_unitary_star_self
  given: {u : R} (hu : u in unitary R)
  statement: Commute (star u) u
  proof: .star_comm_self isStarNormal_of_mem_unitary hu

中文:
引理 _root_.commute_unitary_star_self
  条件: {u : R} (hu : u in unitary R)
  结论: Commute (star u) u
  证明: .star_comm_self isStarNormal_of_mem_unitary hu

Depends on / 依赖: isStarNormal_of_mem_unitary, star_comm_self
-/
lemma _root_.commute_unitary_star_self {u : R} (hu : u in unitary R) : Commute (star u) u :=
.star_comm_self isStarNormal_of_mem_unitary hu

/--
lemma `_root_.commute_unitary_self_star` / 引理 `_root_.commute_unitary_self_star`

English:
lemma _root_.commute_unitary_self_star
  given: {u : R} (hu : u in unitary R)
  statement: Commute u (star u)
  proof: .symm commute_unitary_star_self hu

中文:
引理 _root_.commute_unitary_self_star
  条件: {u : R} (hu : u in unitary R)
  结论: Commute u (star u)
  证明: .symm commute_unitary_star_self hu

Depends on / 依赖: commute_unitary_star_self
-/
lemma _root_.commute_unitary_self_star {u : R} (hu : u in unitary R) : Commute u (star u) :=
.symm commute_unitary_star_self hu

/--
lemma `_root_.commute_unitary_iff_star_left_conjugate` / 引理 `_root_.commute_unitary_iff_star_left_conjugate`

English:
lemma _root_.commute_unitary_iff_star_left_conjugate
  given: {x u : R} (hu : u in unitary R)
  proof: by
  simpa using! (Unitary.toUnits ⟨u, hu⟩).commute_iff_inv_mul_cancel

中文:
引理 _root_.commute_unitary_iff_star_left_conjugate
  条件: {x u : R} (hu : u in unitary R)
  证明: by
  simpa using! (Unitary.toUnits ⟨u, hu⟩).commute_iff_inv_mul_cancel

Depends on / 依赖: Unitary, Unitary.toUnits, commute_iff_inv_mul_cancel, toUnits
-/
lemma _root_.commute_unitary_iff_star_left_conjugate {x u : R} (hu : u in unitary R) :
    Commute u x ↔ star u * x * u = x := by
  simpa using! (Unitary.toUnits ⟨u, hu⟩).commute_iff_inv_mul_cancel

/--
lemma `_root_.commute_unitary_iff_star_right_conjugate` / 引理 `_root_.commute_unitary_iff_star_right_conjugate`

English:
lemma _root_.commute_unitary_iff_star_right_conjugate
  given: {x u : R} (hu : u in unitary R)
  proof: by
  simpa using! (Unitary.toUnits ⟨u, hu⟩).commute_iff_mul_inv_cancel

中文:
引理 _root_.commute_unitary_iff_star_right_conjugate
  条件: {x u : R} (hu : u in unitary R)
  证明: by
  simpa using! (Unitary.toUnits ⟨u, hu⟩).commute_iff_mul_inv_cancel

Depends on / 依赖: Unitary, Unitary.toUnits, commute_iff_mul_inv_cancel, toUnits
-/
lemma _root_.commute_unitary_iff_star_right_conjugate {x u : R} (hu : u in unitary R) :
    Commute u x ↔ u * x * star u = x := by
  simpa using! (Unitary.toUnits ⟨u, hu⟩).commute_iff_mul_inv_cancel

end Monoid

end Unitary

section Group

variable {G : Type*} [Group G] [StarMul G]

/--
theorem `Unitary.inv_mem` / 定理 `Unitary.inv_mem`

English:
theorem Unitary.inv_mem
  given: {g : G} (hg : g in unitary G)
  statement: g⁻¹ in unitary G
  proof: by
  simp_rw [mem_iff, star_inv, ← mul_inv_rev, inv_eq_one] at *
  exact hg.symm

中文:
定理 酉.inv_mem
  条件: {g : G} (hg : g in unitary G)
  结论: g⁻¹ in unitary G
  证明: by
  simp_rw [mem_iff, star_inv, ← mul_inv_rev, inv_eq_one] at *
  exact hg.symm

Depends on / 依赖: hg.symm, inv_eq_one, mem_iff, mul_inv_rev, simp_rw, star_inv
-/
theorem Unitary.inv_mem {g : G} (hg : g in unitary G) : g⁻¹ in unitary G := by
  simp_rw [mem_iff, star_inv, ← mul_inv_rev, inv_eq_one] at *
  exact hg.symm

variable (G) in
/--
Definition of `unitarySubgroup` / `unitarySubgroup` 的定义

English:
definition unitarySubgroup
  signature: : Subgroup G where
  body: unitary G
  inv_mem' := Unitary.inv_mem

@[simp]

中文:
定义 unitarySubgroup
  签名: : 子群 G where
  定义体: unitary G
  inv_mem' := Unitary.inv_mem

@[simp]

Depends on / 依赖: unitary
-/
def unitarySubgroup : Subgroup G where
  toSubmonoid := unitary G
  inv_mem' := Unitary.inv_mem

@[simp]
/--
theorem `unitarySubgroup_toSubmonoid` / 定理 `unitarySubgroup_toSubmonoid`

English:
theorem unitarySubgroup_toSubmonoid
  statement: (unitarySubgroup G).toSubmonoid = unitary G
  proof: rfl

@[simp]

中文:
定理 unitarySubgroup_toSubmonoid
  结论: (unitarySubgroup G).toSubmonoid = unitary G
  证明: rfl

@[simp]

Depends on / 依赖: StructureSheaf, StructureSheaf.toOpen, basicOpen, modulesSpecToSheafIso, of_linearEquiv, powers, toLinearEquiv, toLinearEquiv.symm
-/
theorem unitarySubgroup_toSubmonoid : (unitarySubgroup G).toSubmonoid = unitary G := rfl

@[simp]
/--
theorem `mem_unitarySubgroup_iff` / 定理 `mem_unitarySubgroup_iff`

English:
theorem mem_unitarySubgroup_iff
  given: {g : G}
  statement: g in unitarySubgroup G ↔ g in unitary G
  proof: Iff.rfl

nonrec theorem Unitary.inv_mem_iff {g : G} : g⁻¹ in unitary G ↔ g in unitary G :=
  inv_mem_iff (H := unitarySubgroup G)

中文:
定理 mem_unitarySubgroup_iff
  条件: {g : G}
  结论: g in unitarySubgroup G ↔ g in unitary G
  证明: Iff.rfl

nonrec theorem Unitary.inv_mem_iff {g : G} : g⁻¹ in unitary G ↔ g in unitary G :=
  inv_mem_iff (H := unitarySubgroup G)

Depends on / 依赖: Iff.rfl, Module, Presheaf, TopCat, TopCat.Presheaf.stalk, moduleStructurePresheaf, presheaf
-/
theorem mem_unitarySubgroup_iff {g : G} : g in unitarySubgroup G ↔ g in unitary G :=
  Iff.rfl

nonrec theorem Unitary.inv_mem_iff {g : G} : g⁻¹ in unitary G ↔ g in unitary G :=
  inv_mem_iff (H := unitarySubgroup G)

end Group

namespace Unitary

section SMul

section

variable {A : Type*}
  [Monoid R] [Monoid A] [MulAction R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [StarMul R] [StarMul A] [StarModule R A]

/--
lemma `smul_mem_of_mem` / 引理 `smul_mem_of_mem`

English:
lemma smul_mem_of_mem
  given: {r : R} {a : A} (hr : r in unitary R) (ha : a in unitary A)
  proof: by
  simp [mem_iff, smul_smul, mul_smul_comm, smul_mul_assoc, hr, ha]

中文:
引理 smul_mem_of_mem
  条件: {r : R} {a : A} (hr : r in unitary R) (ha : a in unitary A)
  证明: by
  simp [mem_iff, smul_smul, mul_smul_comm, smul_mul_assoc, hr, ha]

Depends on / 依赖: mem_iff, mul_smul_comm, smul_mul_assoc, smul_smul
-/
lemma smul_mem_of_mem {r : R} {a : A} (hr : r in unitary R) (ha : a in unitary A) :
    r • a in unitary A := by
  simp [mem_iff, smul_smul, mul_smul_comm, smul_mul_assoc, hr, ha]

/--
lemma `smul_mem` / 引理 `smul_mem`

English:
lemma smul_mem
  given: (r : unitary R) {a : A} (ha : a in unitary A)
  proof: smul_mem_of_mem (R := R) r.prop ha

中文:
引理 smul_mem
  条件: (r : unitary R) {a : A} (ha : a in unitary A)
  证明: smul_mem_of_mem (R := R) r.prop ha

Depends on / 依赖: IsLocalizedModule, StructureSheaf, StructureSheaf.toStalk, asIdeal, primeCompl, r.prop, smul_mem_of_mem, x.asIdeal.primeCompl
-/
lemma smul_mem (r : unitary R) {a : A} (ha : a in unitary A) :
    r • a in unitary A :=
  smul_mem_of_mem (R := R) r.prop ha

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (unitary R) (unitary A)
  body: ⟨r • a, smul_mem r a.prop⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 标量乘法 (unitary R) (unitary A)
  定义体: ⟨r • a, smul_mem r a.prop⟩

@[simp, norm_cast]

Depends on / 依赖: a.prop, smul_mem
-/
instance : SMul (unitary R) (unitary A) where
  smul r a := ⟨r • a, smul_mem r a.prop⟩

@[simp, norm_cast]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (r : unitary R) (a : unitary A)
  statement: ↑(r • a) = r • (a : A)
  proof: rfl

中文:
引理 coe_smul
  条件: (r : unitary R) (a : unitary A)
  结论: ↑(r • a) = r • (a : A)
  证明: rfl
-/
lemma coe_smul (r : unitary R) (a : unitary A) : ↑(r • a) = r • (a : A) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction (unitary R) (unitary A)
  body: Subtype.ext one_smul ..
mul_smul _ _ _ := Subtype.ext mul_smul ..

中文:
实例 :
  签名: 乘法作用 (unitary R) (unitary A)
  定义体: Subtype.ext one_smul ..
mul_smul _ _ _ := Subtype.ext mul_smul ..

Depends on / 依赖: Subtype, Subtype.ext, one_smul
-/
instance : MulAction (unitary R) (unitary A) where
one_smul _ := Subtype.ext one_smul ..
mul_smul _ _ _ := Subtype.ext mul_smul ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarModule (unitary R) (unitary A)
  body: Subtype.ext star_smul (_ : R) _

中文:
实例 :
  签名: 对合模 (unitary R) (unitary A)
  定义体: Subtype.ext star_smul (_ : R) _

Depends on / 依赖: Subtype, Subtype.ext, star_smul
-/
instance : StarModule (unitary R) (unitary A) where
star_smul _ _ := Subtype.ext star_smul (_ : R) _

end

section

variable {S A : Type*}
  [Monoid R] [Monoid S] [Monoid A] [StarMul R] [StarMul S] [StarMul A]
  [MulAction R S] [MulAction R A] [MulAction S A]
  [StarModule R S] [StarModule R A] [StarModule S A]
  [IsScalarTower R A A] [IsScalarTower S A A]
  [SMulCommClass R A A] [SMulCommClass S A A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: R S A] : SMulCommClass (unitary R) (unitary S) (unitary A) where
  body: Subtype.ext smul_comm _ (_ : S) (_ : A)

中文:
实例 [标量交换类
  签名: R S A] : 标量交换类 (unitary R) (unitary S) (unitary A) where
  定义体: Subtype.ext smul_comm _ (_ : S) (_ : A)

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance [SMulCommClass R S A] : SMulCommClass (unitary R) (unitary S) (unitary A) where
smul_comm _ _ _ := Subtype.ext smul_comm _ (_ : S) (_ : A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsScalarTower
  signature: R S S] [SMulCommClass R S S] [IsScalarTower R S A] :
  body: Subtype.ext smul_assoc _ (_ : S) (_ : A)

中文:
实例 [标量塔
  签名: R S S] [标量交换类 R S S] [标量塔 R S A] :
  定义体: Subtype.ext smul_assoc _ (_ : S) (_ : A)

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance [IsScalarTower R S S] [SMulCommClass R S S] [IsScalarTower R S A] :
    IsScalarTower (unitary R) (unitary S) (unitary A) where
smul_assoc _ _ _ := Subtype.ext smul_assoc _ (_ : S) (_ : A)

end

end SMul

section Map

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

/--
lemma `map_mem` / 引理 `map_mem`

English:
lemma map_mem
  statement: {F : Type*} [FunLike F R S] [StarHomClass F R S] [MonoidHomClass F R S]
  proof: by
  rw [mem_iff] at hr
  simpa [map_star, map_mul] using! And.intro congr(f $(hr.1)) congr(f $(hr.2))

中文:
引理 map_mem
  结论: {F : 类型} [函数状 F R S] [对合态射类 F R S] [幺半群态射类 F R S]
  证明: by
  rw [mem_iff] at hr
  simpa [map_star, map_mul] using! And.intro congr(f $(hr.1)) congr(f $(hr.2))

Depends on / 依赖: And.intro, map_mul, map_star, mem_iff
-/
lemma map_mem {F : Type*} [FunLike F R S] [StarHomClass F R S] [MonoidHomClass F R S]
    (f : F) {r : R} (hr : r in unitary R) : f r in unitary S := by
  rw [mem_iff] at hr
  simpa [map_star, map_mul] using! And.intro congr(f $(hr.1)) congr(f $(hr.2))

/-- The star monoid homomorphism between unitary subgroups induced by a star monoid homomorphism of
the underlying star monoids. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->⋆* S)
  body: Subtype.map f (fun _ => map_mem f)
map_one' := Subtype.ext map_one f
map_mul' _ _ := Subtype.ext map_mul f _ _
map_star' _ := Subtype.ext map_star f _

@[simp]

中文:
定义 map
  签名: (f : R ->⋆* S)
  定义体: Subtype.map f (fun _ => map_mem f)
map_one' := Subtype.ext map_one f
map_mul' _ _ := Subtype.ext map_mul f _ _
map_star' _ := Subtype.ext map_star f _

@[simp]

Depends on / 依赖: Subtype, Subtype.map, map_mem
-/
def map (f : R ->⋆* S) : unitary R ->⋆* unitary S where
  toFun := Subtype.map f (fun _ => map_mem f)
map_one' := Subtype.ext map_one f
map_mul' _ _ := Subtype.ext map_mul f _ _
map_star' _ := Subtype.ext map_star f _

@[simp]
/--
lemma `coe_map` / 引理 `coe_map`

English:
lemma coe_map
  given: (f : R ->⋆* S) (x : unitary R)
  statement: map f x = f x
  proof: rfl

@[simp]

中文:
引理 coe_map
  条件: (f : R ->⋆* S) (x : unitary R)
  结论: map f x = f x
  证明: rfl

@[simp]
-/
lemma coe_map (f : R ->⋆* S) (x : unitary R) : map f x = f x := rfl

@[simp]
/--
lemma `coe_map_star` / 引理 `coe_map_star`

English:
lemma coe_map_star
  given: (f : R ->⋆* S) (x : unitary R)
  statement: map f (star x) = f (star x)
  proof: rfl

@[simp]

中文:
引理 coe_map_star
  条件: (f : R ->⋆* S) (x : unitary R)
  结论: map f (star x) = f (star x)
  证明: rfl

@[simp]
-/
lemma coe_map_star (f : R ->⋆* S) (x : unitary R) : map f (star x) = f (star x) := rfl

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map (.id R) = .id (unitary R)
  proof: rfl

中文:
引理 map_id
  结论: map (.id R) = .id (unitary R)
  证明: rfl
-/
lemma map_id : map (.id R) = .id (unitary R) := rfl

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (g : S ->⋆* T) (f : R ->⋆* S)
  statement: map (g.comp f) = (map g).comp (map f)
  proof: rfl

@[simp]

中文:
引理 map_comp
  条件: (g : S ->⋆* T) (f : R ->⋆* S)
  结论: map (g.comp f) = (map g).comp (map f)
  证明: rfl

@[simp]
-/
lemma map_comp (g : S ->⋆* T) (f : R ->⋆* S) : map (g.comp f) = (map g).comp (map f) := rfl

@[simp]
/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  given: {f : R ->⋆* S} (hf : Function.Injective f)
  proof: Subtype.map_injective (fun _ => map_mem f) hf

中文:
引理 map_injective
  条件: {f : R ->⋆* S} (hf : 函数.单射 f)
  证明: Subtype.map_injective (fun _ => map_mem f) hf

Depends on / 依赖: Subtype, Subtype.map_injective, map_injective, map_mem
-/
lemma map_injective {f : R ->⋆* S} (hf : Function.Injective f) :
    Function.Injective (map f : unitary R -> unitary S) :=
  Subtype.map_injective (fun _ => map_mem f) hf

/--
lemma `toUnits_comp_map` / 引理 `toUnits_comp_map`

English:
lemma toUnits_comp_map
  given: (f : R ->⋆* S)
  proof: by
  ext; rfl

中文:
引理 toUnits_comp_map
  条件: (f : R ->⋆* S)
  证明: by
  ext; rfl
-/
lemma toUnits_comp_map (f : R ->⋆* S) :
    toUnits.comp (map f).toMonoidHom = (Units.map f.toMonoidHom).comp toUnits := by
  ext; rfl

/-- The star monoid isomorphism between unitary subgroups induced by a star monoid isomorphism of
the underlying star monoids. -/
@[simps]
/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (f : R ≃⋆* S)
  body: { map f.toStarMonoidHom with
    toFun := map f.toStarMonoidHom
    invFun := map f.symm.toStarMonoidHom
left_inv := fun _ => Subtype.ext f.left_inv _
right_inv := fun _ => Subtype.ext f.right_inv _ }

@[simp]

中文:
定义 mapEquiv
  签名: (f : R ≃⋆* S)
  定义体: { map f.toStarMonoidHom with
    toFun := map f.toStarMonoidHom
    invFun := map f.symm.toStarMonoidHom
left_inv := fun _ => Subtype.ext f.left_inv _
right_inv := fun _ => Subtype.ext f.right_inv _ }

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, f.left_inv, f.right_inv, f.symm.toStarMonoidHom, f.toStarMonoidHom, invFun, left_inv, right_inv, toStarMonoidHom
-/
def mapEquiv (f : R ≃⋆* S) : unitary R ≃⋆* unitary S :=
  { map f.toStarMonoidHom with
    toFun := map f.toStarMonoidHom
    invFun := map f.symm.toStarMonoidHom
left_inv := fun _ => Subtype.ext f.left_inv _
right_inv := fun _ => Subtype.ext f.right_inv _ }

@[simp]
/--
lemma `mapEquiv_refl` / 引理 `mapEquiv_refl`

English:
lemma mapEquiv_refl
  statement: mapEquiv (.refl R) = .refl (unitary R)
  proof: rfl

@[simp]

中文:
引理 mapEquiv_refl
  结论: mapEquiv (.refl R) = .refl (unitary R)
  证明: rfl

@[simp]
-/
lemma mapEquiv_refl : mapEquiv (.refl R) = .refl (unitary R) := rfl

@[simp]
/--
lemma `mapEquiv_symm` / 引理 `mapEquiv_symm`

English:
lemma mapEquiv_symm
  given: (f : R ≃⋆* S)
  statement: mapEquiv f.symm = (mapEquiv f).symm
  proof: rfl

@[simp]

中文:
引理 mapEquiv_symm
  条件: (f : R ≃⋆* S)
  结论: mapEquiv f.symm = (mapEquiv f).symm
  证明: rfl

@[simp]
-/
lemma mapEquiv_symm (f : R ≃⋆* S) : mapEquiv f.symm = (mapEquiv f).symm := rfl

@[simp]
/--
lemma `mapEquiv_trans` / 引理 `mapEquiv_trans`

English:
lemma mapEquiv_trans
  given: (f : R ≃⋆* S) (g : S ≃⋆* T)
  proof: rfl

@[simp]

中文:
引理 mapEquiv_trans
  条件: (f : R ≃⋆* S) (g : S ≃⋆* T)
  证明: rfl

@[simp]
-/
lemma mapEquiv_trans (f : R ≃⋆* S) (g : S ≃⋆* T) :
    mapEquiv (f.trans g) = (mapEquiv f).trans (mapEquiv g) :=
  rfl

@[simp]
/--
lemma `toMonoidHom_mapEquiv` / 引理 `toMonoidHom_mapEquiv`

English:
lemma toMonoidHom_mapEquiv
  given: (f : R ≃⋆* S)
  proof: rfl

中文:
引理 toMonoidHom_mapEquiv
  条件: (f : R ≃⋆* S)
  证明: rfl

Depends on / 依赖: SheafOfModules, SheafOfModules.free
-/
lemma toMonoidHom_mapEquiv (f : R ≃⋆* S) :
    (mapEquiv f).toStarMonoidHom = map f.toStarMonoidHom :=
  rfl

/-- The unitary subgroup of the units is equivalent to the unitary elements of the monoid. -/
@[simps!]
/--
Definition of `_root_.unitarySubgroupUnitsEquiv` / `_root_.unitarySubgroupUnitsEquiv` 的定义

English:
definition _root_.unitarySubgroupUnitsEquiv
  signature: {M : Type*} [Monoid M] [StarMul M]
  body: ⟨x.val, congr_arg Units.val x.prop.1, congr_arg Units.val x.prop.2⟩
  invFun x := ⟨⟨x, star x, x.prop.2, x.prop.1⟩, Units.ext x.prop.1, Units.ext x.prop.2⟩
  map_mul' _ _ := rfl
left_inv _ := Subtype.ext Units.ext rfl
  right_inv _ := rfl

中文:
定义 _root_.unitarySubgroupUnitsEquiv
  签名: {M : 类型} [幺半群 M] [StarMul M]
  定义体: ⟨x.val, congr_arg Units.val x.prop.1, congr_arg Units.val x.prop.2⟩
  invFun x := ⟨⟨x, star x, x.prop.2, x.prop.1⟩, Units.ext x.prop.1, Units.ext x.prop.2⟩
  map_mul' _ _ := rfl
left_inv _ := Subtype.ext Units.ext rfl
  right_inv _ := rfl

Depends on / 依赖: Units.val, congr_arg, x.prop, x.val
-/
def _root_.unitarySubgroupUnitsEquiv {M : Type*} [Monoid M] [StarMul M] :
    unitarySubgroup Mˣ ≃* unitary M where
  toFun x := ⟨x.val, congr_arg Units.val x.prop.1, congr_arg Units.val x.prop.2⟩
  invFun x := ⟨⟨x, star x, x.prop.2, x.prop.1⟩, Units.ext x.prop.1, Units.ext x.prop.2⟩
  map_mul' _ _ := rfl
left_inv _ := Subtype.ext Units.ext rfl
  right_inv _ := rfl

end Map

section CommMonoid

variable [CommMonoid R] [StarMul R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommGroup (unitary R)
  body: { (inferInstance : Group (unitary R)), Submonoid.toCommMonoid _ with }

中文:
实例 :
  签名: 交换群 (unitary R)
  定义体: { (inferInstance : Group (unitary R)), Submonoid.toCommMonoid _ with }

Depends on / 依赖: Submonoid, Submonoid.toCommMonoid, toCommMonoid, unitary
-/
instance : CommGroup (unitary R) :=
  { (inferInstance : Group (unitary R)), Submonoid.toCommMonoid _ with }

/--
theorem `mem_iff_star_mul_self` / 定理 `mem_iff_star_mul_self`

English:
theorem mem_iff_star_mul_self
  given: {U : R}
  statement: U in unitary R ↔ star U * U = 1
  proof: mem_iff.trans and_iff_left_of_imp fun h => mul_comm (star U) U ▸ h

中文:
定理 mem_iff_star_mul_self
  条件: {U : R}
  结论: U in unitary R ↔ star U * U = 1
  证明: mem_iff.trans and_iff_left_of_imp fun h => mul_comm (star U) U ▸ h

Depends on / 依赖: and_iff_left_of_imp, mem_iff, mem_iff.trans, mul_comm
-/
theorem mem_iff_star_mul_self {U : R} : U in unitary R ↔ star U * U = 1 :=
mem_iff.trans and_iff_left_of_imp fun h => mul_comm (star U) U ▸ h

/--
theorem `mem_iff_self_mul_star` / 定理 `mem_iff_self_mul_star`

English:
theorem mem_iff_self_mul_star
  given: {U : R}
  statement: U in unitary R ↔ U * star U = 1
  proof: mem_iff.trans and_iff_right_of_imp fun h => mul_comm U (star U) ▸ h

中文:
定理 mem_iff_self_mul_star
  条件: {U : R}
  结论: U in unitary R ↔ U * star U = 1
  证明: mem_iff.trans and_iff_right_of_imp fun h => mul_comm U (star U) ▸ h

Depends on / 依赖: and_iff_right_of_imp, mem_iff, mem_iff.trans, mul_comm
-/
theorem mem_iff_self_mul_star {U : R} : U in unitary R ↔ U * star U = 1 :=
mem_iff.trans and_iff_right_of_imp fun h => mul_comm U (star U) ▸ h

end CommMonoid

section GroupWithZero

variable [GroupWithZero R] [StarMul R]

@[norm_cast]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (U : unitary R)
  statement: ↑U⁻¹ = (U⁻¹ : R)
  proof: eq_inv_of_mul_eq_one_right coe_mul_star_self _

@[norm_cast]

中文:
定理 coe_inv
  条件: (U : unitary R)
  结论: ↑U⁻¹ = (U⁻¹ : R)
  证明: eq_inv_of_mul_eq_one_right coe_mul_star_self _

@[norm_cast]

Depends on / 依赖: coe_mul_star_self, eq_inv_of_mul_eq_one_right
-/
theorem coe_inv (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R) :=
eq_inv_of_mul_eq_one_right coe_mul_star_self _

@[norm_cast]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (U₁ U₂ : unitary R)
  statement: ↑(U₁ / U₂) = (U₁ / U₂ : R)
  proof: by
  simp only [div_eq_mul_inv, coe_inv, Submonoid.coe_mul]

@[norm_cast]

中文:
定理 coe_div
  条件: (U₁ U₂ : unitary R)
  结论: ↑(U₁ / U₂) = (U₁ / U₂ : R)
  证明: by
  simp only [div_eq_mul_inv, coe_inv, Submonoid.coe_mul]

@[norm_cast]

Depends on / 依赖: Submonoid, Submonoid.coe_mul, coe_inv, coe_mul, div_eq_mul_inv
-/
theorem coe_div (U₁ U₂ : unitary R) : ↑(U₁ / U₂) = (U₁ / U₂ : R) := by
  simp only [div_eq_mul_inv, coe_inv, Submonoid.coe_mul]

@[norm_cast]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (U : unitary R) (z : Int)
  statement: ↑(U ^ z) = (U : R) ^ z
  proof: by
  cases z
  · simp [SubmonoidClass.coe_pow]
  · simp [coe_inv]

中文:
定理 coe_zpow
  条件: (U : unitary R) (z : 整数)
  结论: ↑(U ^ z) = (U : R) ^ z
  证明: by
  cases z
  · simp [SubmonoidClass.coe_pow]
  · simp [coe_inv]

Depends on / 依赖: SubmonoidClass, SubmonoidClass.coe_pow, coe_inv, coe_pow
-/
theorem coe_zpow (U : unitary R) (z : Int) : ↑(U ^ z) = (U : R) ^ z := by
  cases z
  · simp [SubmonoidClass.coe_pow]
  · simp [coe_inv]

end GroupWithZero

section Ring

variable [Ring R] [StarRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (unitary R)
  body: ⟨-U, by simp [mem_iff, star_neg]⟩

@[norm_cast]

中文:
实例 :
  签名: 取负 (unitary R)
  定义体: ⟨-U, by simp [mem_iff, star_neg]⟩

@[norm_cast]

Depends on / 依赖: mem_iff, star_neg
-/
instance : Neg (unitary R) where
  neg U :=
    ⟨-U, by simp [mem_iff, star_neg]⟩

@[norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (U : unitary R)
  statement: ↑(-U) = (-U : R)
  proof: rfl

中文:
定理 coe_neg
  条件: (U : unitary R)
  结论: ↑(-U) = (-U : R)
  证明: rfl
-/
theorem coe_neg (U : unitary R) : ↑(-U) = (-U : R) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasDistribNeg (unitary R)
  body: Subtype.coe_injective.hasDistribNeg _ coe_neg (unitary R).coe_mul

中文:
实例 :
  签名: 有DistribNeg (unitary R)
  定义体: Subtype.coe_injective.hasDistribNeg _ coe_neg (unitary R).coe_mul

Depends on / 依赖: Subtype, Subtype.coe_injective.hasDistribNeg, coe_injective, coe_mul, coe_neg, hasDistribNeg, unitary
-/
instance : HasDistribNeg (unitary R) :=
  Subtype.coe_injective.hasDistribNeg _ coe_neg (unitary R).coe_mul

end Ring

section UnitaryConjugate

universe u

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] [StarMul A]

/-- Unitary conjugation preserves the spectrum, star on right. -/
@[simp]
/--
lemma `spectrum_star_right_conjugate` / 引理 `spectrum_star_right_conjugate`

English:
lemma spectrum_star_right_conjugate
  given: {a : A} {U : unitary A}
  proof: spectrum.units_conjugate (u := toUnits U)

中文:
引理 spectrum_star_right_conjugate
  条件: {a : A} {U : unitary A}
  证明: spectrum.units_conjugate (u := toUnits U)

Depends on / 依赖: spectrum, spectrum.units_conjugate, toUnits, units_conjugate
-/
lemma spectrum_star_right_conjugate {a : A} {U : unitary A} :
    spectrum R (U * a * (star U : A)) = spectrum R a :=
  spectrum.units_conjugate (u := toUnits U)

/-- Unitary conjugation preserves the spectrum, star on left. -/
@[simp]
/--
lemma `spectrum_star_left_conjugate` / 引理 `spectrum_star_left_conjugate`

English:
lemma spectrum_star_left_conjugate
  given: {a : A} {U : unitary A}
  proof: by
  simpa using spectrum_star_right_conjugate (U := star U)

中文:
引理 spectrum_star_left_conjugate
  条件: {a : A} {U : unitary A}
  证明: by
  simpa using spectrum_star_right_conjugate (U := star U)

Depends on / 依赖: spectrum_star_right_conjugate
-/
lemma spectrum_star_left_conjugate {a : A} {U : unitary A} :
    spectrum R ((star U : A) * a * U) = spectrum R a := by
  simpa using spectrum_star_right_conjugate (U := star U)

end UnitaryConjugate

/--
theorem `mem_iff_eq_one_or_eq_neg_one` / 定理 `mem_iff_eq_one_or_eq_neg_one`

English:
theorem mem_iff_eq_one_or_eq_neg_one
  statement: [Ring R] [StarRing R] [TrivialStar R] [NoZeroDivisors R]
  proof: by
  simp [mem_iff, mul_self_eq_one_iff]

中文:
定理 mem_iff_eq_one_or_eq_neg_one
  结论: [环 R] [对合环 R] [TrivialStar R] [无零因子 R]
  证明: by
  simp [mem_iff, mul_self_eq_one_iff]

Depends on / 依赖: mem_iff, mul_self_eq_one_iff
-/
theorem mem_iff_eq_one_or_eq_neg_one [Ring R] [StarRing R] [TrivialStar R] [NoZeroDivisors R]
    {a : R} : a in unitary R ↔ a = 1 ∨ a = -1 := by
  simp [mem_iff, mul_self_eq_one_iff]

end Unitary

/--
theorem `IsStarProjection.two_mul_sub_one_mem_unitary` / 定理 `IsStarProjection.two_mul_sub_one_mem_unitary`

English:
theorem IsStarProjection.two_mul_sub_one_mem_unitary
  statement: {R : Type*} [Ring R] [StarRing R] {p : R}
  proof: by
  simp only [two_mul, Unitary.mem_iff, star_sub, star_add,
    hp.isSelfAdjoint.star_eq, star_one, mul_sub, mul_add,
    sub_mul, add_mul, hp.isIdempotentElem.eq, one_mul, add_sub_cancel_right,
    mul_one, sub_sub_cancel, and_self]

中文:
定理 是StarProjection.two_mul_sub_one_mem_unitary
  结论: {R : 类型} [环 R] [对合环 R] {p : R}
  证明: by
  simp only [two_mul, Unitary.mem_iff, star_sub, star_add,
    hp.isSelfAdjoint.star_eq, star_one, mul_sub, mul_add,
    sub_mul, add_mul, hp.isIdempotentElem.eq, one_mul, add_sub_cancel_right,
    mul_one, sub_sub_cancel, and_self]

Depends on / 依赖: Unitary, Unitary.mem_iff, add_mul, add_sub_cancel_right, and_self, hp.isIdempotentElem.eq, hp.isSelfAdjoint.star_eq, isIdempotentElem, isSelfAdjoint, mem_iff, mul_add, mul_one, mul_sub, one_mul, star_add, star_eq, star_one, star_sub, sub_mul, sub_sub_cancel
-/
theorem IsStarProjection.two_mul_sub_one_mem_unitary {R : Type*} [Ring R] [StarRing R] {p : R}
    (hp : IsStarProjection p) : 2 * p - 1 in unitary R := by
  simp only [two_mul, Unitary.mem_iff, star_sub, star_add,
    hp.isSelfAdjoint.star_eq, star_one, mul_sub, mul_add,
    sub_mul, add_mul, hp.isIdempotentElem.eq, one_mul, add_sub_cancel_right,
    mul_one, sub_sub_cancel, and_self]
