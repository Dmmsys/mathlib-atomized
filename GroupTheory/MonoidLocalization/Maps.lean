/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Mapping properties of monoid localizations

Given an `S`-localization map `f : M →* N`, we can define `Submonoid.LocalizationMap.lift`, the
homomorphism from `N` induced by a homomorphism from `M` which maps elements of `S` to invertible
elements of the codomain. Similarly, given commutative monoids `P, Q`, a submonoid `T` of `P` and a
localization map for `T` from `P` to `Q`, then a homomorphism `g : M →* P` such that `g(S) ⊆ T`
induces a homomorphism of localizations, `LocalizationMap.map`, from `N` to `Q`.

## Tags

localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid, grothendieck group
-/

@[expose] public section

assert_not_exists MonoidWithZero Ring

open Function

section CommMonoid

variable {M : Type*} [CommMonoid M] (S : Submonoid M) (N : Type*) [CommMonoid N] {P : Type*}
  [CommMonoid P]

variable {S N}

namespace Submonoid

namespace LocalizationMap

variable (f : LocalizationMap S N)

variable {g : M ->* P}

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g(S) ⊆ Units P`, `f x = f y → g x = g y` for all `x y : M`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g(S) ⊆ AddUnits P`, `f x = f y → g x = g y`
for all `x y : M`. -/]
/--
theorem `eq_of_eq` / 定理 `eq_of_eq`

English:
theorem eq_of_eq
  given: (hg : forall y : S, IsUnit (g y)) {x y} (h : f x = f y)
  statement: g x = g y
  proof: by
  obtain ⟨c, hc⟩ := f.eq_iff_exists.1 h
  rw [← one_mul (g x)]; rw [← IsUnit.liftRight_inv_mul (g.domRestrict S) hg c]
  change _ * g c * _ = _
  rw [mul_assoc]; rw [← g.map_mul]; rw [hc]; rw [mul_comm]; rw [mul_inv_left hg]; rw [g.map_mul]

中文:
定理 eq_of_eq
  条件: (hg : 对任意 y : S, 是单位 (g y)) {x y} (h : f x = f y)
  结论: g x = g y
  证明: by
  obtain ⟨c, hc⟩ := f.eq_iff_exists.1 h
  rw [← one_mul (g x)]; rw [← IsUnit.liftRight_inv_mul (g.domRestrict S) hg c]
  change _ * g c * _ = _
  rw [mul_assoc]; rw [← g.map_mul]; rw [hc]; rw [mul_comm]; rw [mul_inv_left hg]; rw [g.map_mul]

Depends on / 依赖: IsUnit, IsUnit.liftRight_inv_mul, domRestrict, eq_iff_exists, f.eq_iff_exists, g.domRestrict, g.map_mul, liftRight_inv_mul, map_mul, mul_assoc, mul_comm, mul_inv_left, one_mul
-/
theorem eq_of_eq (hg : forall y : S, IsUnit (g y)) {x y} (h : f x = f y) : g x = g y := by
  obtain ⟨c, hc⟩ := f.eq_iff_exists.1 h
  rw [← one_mul (g x)]; rw [← IsUnit.liftRight_inv_mul (g.domRestrict S) hg c]
  change _ * g c * _ = _
  rw [mul_assoc]; rw [← g.map_mul]; rw [hc]; rw [mul_comm]; rw [mul_inv_left hg]; rw [g.map_mul]

/-- Given `CommMonoid`s `M, P`, Localization maps `f : M →* N, k : P →* Q` for Submonoids
`S, T` respectively, and `g : M →* P` such that `g(S) ⊆ T`, `f x = f y` implies
`k (g x) = k (g y)`. -/
@[to_additive
/-- Given `AddCommMonoid`s `M, P`, Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids
`S, T` respectively, and `g : M →+ P` such that `g(S) ⊆ T`, `f x = f y`
implies `k (g x) = k (g y)`. -/]
/--
theorem `comp_eq_of_eq` / 定理 `comp_eq_of_eq`

English:
theorem comp_eq_of_eq
  statement: {T : Submonoid P} {Q : Type*} [CommMonoid Q] (hg : forall y : S, g y in T)
  proof: f.eq_of_eq (fun y : S => show IsUnit (k.toMonoidHom.comp g y) from k.map_units ⟨g y, hg y⟩) h

中文:
定理 comp_eq_of_eq
  结论: {T : 子幺半群 P} {Q : 类型} [交换幺半群 Q] (hg : 对任意 y : S, g y in T)
  证明: f.eq_of_eq (fun y : S => show IsUnit (k.toMonoidHom.comp g y) from k.map_units ⟨g y, hg y⟩) h

Depends on / 依赖: IsUnit, eq_of_eq, f.eq_of_eq, k.map_units, k.toMonoidHom.comp, map_units, toMonoidHom
-/
theorem comp_eq_of_eq {T : Submonoid P} {Q : Type*} [CommMonoid Q] (hg : forall y : S, g y in T)
    (k : LocalizationMap T Q) {x y} (h : f x = f y) : k (g x) = k (g y) :=
  f.eq_of_eq (fun y : S => show IsUnit (k.toMonoidHom.comp g y) from k.map_units ⟨g y, hg y⟩) h

variable (hg : forall y : S, IsUnit (g y))

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S` are such that
`z = f x * (f y)⁻¹`. -/
@[to_additive
/-- Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism
induced from `N` to `P` sending `z : N` to `g x - g y`, where `(x, y) : M × S` are such that
`z = f x - f y`. -/]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : N ->* P where
  body: g (f.sec z).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec z).2)⁻¹
  map_one' := by rw [mul_inv_left, mul_one]; exact f.eq_of_eq hg (by rw [← sec_spec, one_mul])
  map_mul' x y := by
    rw [mul_inv_left hg]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_inv_right hg]; rw [mul_comm _ (g (f.sec y).1)]; rw [←
      mul_assoc]; rw [← mul_assoc]; rw [mul_inv_right hg]
    repeat rw [← g.map_mul]
    refine f.eq_of_eq hg ?_
    simp_rw [map_mul, sec_spec', ← toMonoidHom_apply]
    ac_rfl

@[to_additive]

中文:
定义 lift
  签名: : N ->* P where
  定义体: g (f.sec z).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec z).2)⁻¹
  map_one' := by rw [mul_inv_left, mul_one]; exact f.eq_of_eq hg (by rw [← sec_spec, one_mul])
  map_mul' x y := by
    rw [mul_inv_left hg]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_inv_right hg]; rw [mul_comm _ (g (f.sec y).1)]; rw [←
      mul_assoc]; rw [← mul_assoc]; rw [mul_inv_right hg]
    repeat rw [← g.map_mul]
    refine f.eq_of_eq hg ?_
    simp_rw [map_mul, sec_spec', ← toMonoidHom_apply]
    ac_rfl

@[to_additive]

Depends on / 依赖: IsUnit, IsUnit.liftRight, domRestrict, f.sec, g.domRestrict, liftRight
-/
noncomputable def lift : N ->* P where
  toFun z := g (f.sec z).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec z).2)⁻¹
  map_one' := by rw [mul_inv_left, mul_one]; exact f.eq_of_eq hg (by rw [← sec_spec, one_mul])
  map_mul' x y := by
    rw [mul_inv_left hg]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_inv_right hg]; rw [mul_comm _ (g (f.sec y).1)]; rw [←
      mul_assoc]; rw [← mul_assoc]; rw [mul_inv_right hg]
    repeat rw [← g.map_mul]
    refine f.eq_of_eq hg ?_
    simp_rw [map_mul, sec_spec', ← toMonoidHom_apply]
    ac_rfl

@[to_additive]
/--
lemma `lift_apply` / 引理 `lift_apply`

English:
lemma lift_apply
  given: (z)
  proof: rfl

中文:
引理 lift_apply
  条件: (z)
  证明: rfl
-/
lemma lift_apply (z) :
    f.lift hg z = g (f.sec z).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec z).2)⁻¹ :=
  rfl

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism
induced from `N` to `P` maps `f x - f y` to `g x - g y` for all `x : M, y ∈ S`. -/]
/--
theorem `lift_mk'` / 定理 `lift_mk'`

English:
theorem lift_mk'
  given: (x y)
  proof: (mul_inv hg).2
f.eq_of_eq hg by
      simp_rw [map_mul, sec_spec', mul_assoc, f.mk'_spec, mul_comm]

中文:
定理 lift_mk'
  条件: (x y)
  证明: (mul_inv hg).2
f.eq_of_eq hg by
      simp_rw [map_mul, sec_spec', mul_assoc, f.mk'_spec, mul_comm]

Depends on / 依赖: _spec, eq_of_eq, f.eq_of_eq, f.mk, map_mul, mul_assoc, mul_comm, mul_inv, sec_spec, simp_rw
-/
theorem lift_mk' (x y) :
    f.lift hg (f.mk' x y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹ :=
(mul_inv hg).2
f.eq_of_eq hg by
      simp_rw [map_mul, sec_spec', mul_assoc, f.mk'_spec, mul_comm]

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a localization map
`g : M →* P` for the same submonoid, the homomorphism induced from
`N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
@[to_additive (attr := simp)
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M` and a localization map
`g : M →+ P` for the same submonoid, the homomorphism
induced from `N` to `P` maps `f x - f y` to `g x - g y` for all `x : M, y ∈ S`. -/]
/--
theorem `lift_localizationMap_mk'` / 定理 `lift_localizationMap_mk'`

English:
theorem lift_localizationMap_mk'
  given: (g : S.LocalizationMap P) (x y)
  proof: f.lift_mk' _ _ _

中文:
定理 lift_localizationMap_mk'
  条件: (g : S.Localization映射 P) (x y)
  证明: f.lift_mk' _ _ _

Depends on / 依赖: f.lift_mk, lift_mk
-/
theorem lift_localizationMap_mk' (g : S.LocalizationMap P) (x y) :
    f.lift g.map_units (f.mk' x y) = g.mk' x y :=
  f.lift_mk' _ _ _

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v : P`, we have
`f.lift hg z = v ↔ g x = g y * v`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an
`AddCommMonoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all
`z : N, v : P`, we have `f.lift hg z = v ↔ g x = g y + v`, where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
/--
theorem `lift_spec` / 定理 `lift_spec`

English:
theorem lift_spec
  given: (z v)
  statement: f.lift hg z = v ↔ g (f.sec z).1 = g (f.sec z).2 * v
  proof: mul_inv_left hg _ _ v

中文:
定理 lift_spec
  条件: (z v)
  结论: f.lift hg z = v ↔ g (f.sec z).1 = g (f.sec z).2 * v
  证明: mul_inv_left hg _ _ v

Depends on / 依赖: mul_inv_left
-/
theorem lift_spec (z v) : f.lift hg z = v ↔ g (f.sec z).1 = g (f.sec z).2 * v :=
  mul_inv_left hg _ _ v

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v w : P`, we have
`f.lift hg z * w = v ↔ g x * w = g y * v`, where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an `AddCommMonoid` map
`g : M →+ P` induces a map `f.lift hg : N →+ P` then for all
`z : N, v w : P`, we have `f.lift hg z + w = v ↔ g x + w = g y + v`, where `x : M, y ∈ S` are such
that `z + f y = f x`. -/]
/--
theorem `lift_spec_mul` / 定理 `lift_spec_mul`

English:
theorem lift_spec_mul
  given: (z w v)
  statement: f.lift hg z * w = v ↔ g (f.sec z).1 * w = g (f.sec z).2 * v
  proof: by
  rw [mul_comm]; rw [lift_apply]; rw [← mul_assoc]; rw [mul_inv_left hg]; rw [mul_comm]

@[to_additive]

中文:
定理 lift_spec_mul
  条件: (z w v)
  结论: f.lift hg z * w = v ↔ g (f.sec z).1 * w = g (f.sec z).2 * v
  证明: by
  rw [mul_comm]; rw [lift_apply]; rw [← mul_assoc]; rw [mul_inv_left hg]; rw [mul_comm]

@[to_additive]

Depends on / 依赖: lift_apply, mul_assoc, mul_comm, mul_inv_left
-/
theorem lift_spec_mul (z w v) : f.lift hg z * w = v ↔ g (f.sec z).1 * w = g (f.sec z).2 * v := by
  rw [mul_comm]; rw [lift_apply]; rw [← mul_assoc]; rw [mul_inv_left hg]; rw [mul_comm]

@[to_additive]
/--
theorem `lift_mk'_spec` / 定理 `lift_mk'_spec`

English:
theorem lift_mk'_spec
  given: (x v) (y : S)
  statement: f.lift hg (f.mk' x y) = v ↔ g x = g y * v
  proof: by
  rw [f.lift_mk' hg]; exact mul_inv_left hg _ _ _

中文:
定理 lift_mk'_spec
  条件: (x v) (y : S)
  结论: f.lift hg (f.mk' x y) = v ↔ g x = g y * v
  证明: by
  rw [f.lift_mk' hg]; exact mul_inv_left hg _ _ _
-/
theorem lift_mk'_spec (x v) (y : S) : f.lift hg (f.mk' x y) = v ↔ g x = g y * v := by
  rw [f.lift_mk' hg]; exact mul_inv_left hg _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`f.lift hg z * g y = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an `AddCommMonoid`
map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we have
`f.lift hg z + g y = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`. -/]
/--
theorem `lift_mul_right` / 定理 `lift_mul_right`

English:
theorem lift_mul_right
  given: (z)
  statement: f.lift hg z * g (f.sec z).2 = g (f.sec z).1
  proof: by
  rw [lift_apply]; rw [mul_assoc]; rw [← g.domRestrict_apply]; rw [IsUnit.liftRight_inv_mul]; rw [mul_one]

中文:
定理 lift_mul_right
  条件: (z)
  结论: f.lift hg z * g (f.sec z).2 = g (f.sec z).1
  证明: by
  rw [lift_apply]; rw [mul_assoc]; rw [← g.domRestrict_apply]; rw [IsUnit.liftRight_inv_mul]; rw [mul_one]

Depends on / 依赖: IsUnit, IsUnit.liftRight_inv_mul, domRestrict_apply, g.domRestrict_apply, liftRight_inv_mul, lift_apply, mul_assoc, mul_one
-/
theorem lift_mul_right (z) : f.lift hg z * g (f.sec z).2 = g (f.sec z).1 := by
  rw [lift_apply]; rw [mul_assoc]; rw [← g.domRestrict_apply]; rw [IsUnit.liftRight_inv_mul]; rw [mul_one]

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`g y * f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an `AddCommMonoid` map
`g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we have
`g y + f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`. -/]
/--
theorem `lift_mul_left` / 定理 `lift_mul_left`

English:
theorem lift_mul_left
  given: (z)
  statement: g (f.sec z).2 * f.lift hg z = g (f.sec z).1
  proof: by
  rw [mul_comm]; rw [lift_mul_right]

@[to_additive (attr := simp)]

中文:
定理 lift_mul_left
  条件: (z)
  结论: g (f.sec z).2 * f.lift hg z = g (f.sec z).1
  证明: by
  rw [mul_comm]; rw [lift_mul_right]

@[to_additive (attr := simp)]

Depends on / 依赖: lift_mul_right, mul_comm
-/
theorem lift_mul_left (z) : g (f.sec z).2 * f.lift hg z = g (f.sec z).1 := by
  rw [mul_comm]; rw [lift_mul_right]

@[to_additive (attr := simp)]
/--
theorem `lift_eq` / 定理 `lift_eq`

English:
theorem lift_eq
  given: (x : M)
  statement: f.lift hg (f x) = g x
  proof: by
  rw [lift_spec]; rw [← g.map_mul]; exact f.eq_of_eq hg (by rw [sec_spec', map_mul])

@[to_additive]

中文:
定理 lift_eq
  条件: (x : M)
  结论: f.lift hg (f x) = g x
  证明: by
  rw [lift_spec]; rw [← g.map_mul]; exact f.eq_of_eq hg (by rw [sec_spec', map_mul])

@[to_additive]

Depends on / 依赖: eq_of_eq, f.eq_of_eq, g.map_mul, lift_spec, map_mul, sec_spec
-/
theorem lift_eq (x : M) : f.lift hg (f x) = g x := by
  rw [lift_spec]; rw [← g.map_mul]; exact f.eq_of_eq hg (by rw [sec_spec', map_mul])

@[to_additive]
/--
theorem `lift_eq_iff` / 定理 `lift_eq_iff`

English:
theorem lift_eq_iff
  given: {x y : M × S}
  proof: by
  rw [lift_mk']; rw [lift_mk']; rw [mul_inv hg]

@[to_additive (attr := simp)]

中文:
定理 lift_eq_iff
  条件: {x y : M × S}
  证明: by
  rw [lift_mk']; rw [lift_mk']; rw [mul_inv hg]

@[to_additive (attr := simp)]

Depends on / 依赖: lift_mk, mul_inv
-/
theorem lift_eq_iff {x y : M × S} :
    f.lift hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) := by
  rw [lift_mk']; rw [lift_mk']; rw [mul_inv hg]

@[to_additive (attr := simp)]
/--
theorem `lift_comp` / 定理 `lift_comp`

English:
theorem lift_comp
  statement: (f.lift hg).comp f.toMonoidHom = g
  proof: by ext; exact f.lift_eq hg _

@[to_additive (attr := simp)]

中文:
定理 lift_comp
  结论: (f.lift hg).comp f.toMonoidHom = g
  证明: by ext; exact f.lift_eq hg _

@[to_additive (attr := simp)]

Depends on / 依赖: f.lift_eq, lift_eq
-/
theorem lift_comp : (f.lift hg).comp f.toMonoidHom = g := by ext; exact f.lift_eq hg _

@[to_additive (attr := simp)]
/--
theorem `lift_of_comp` / 定理 `lift_of_comp`

English:
theorem lift_of_comp
  given: (j : N ->* P)
  statement: f.lift (f.isUnit_comp j) = j
  proof: by
  ext; simp_rw [lift_spec, j.comp_apply, ← map_mul, toMonoidHom_apply, sec_spec']

@[to_additive]

中文:
定理 lift_of_comp
  条件: (j : N ->* P)
  结论: f.lift (f.isUnit_comp j) = j
  证明: by
  ext; simp_rw [lift_spec, j.comp_apply, ← map_mul, toMonoidHom_apply, sec_spec']

@[to_additive]

Depends on / 依赖: comp_apply, j.comp_apply, lift_spec, map_mul, sec_spec, simp_rw, toMonoidHom_apply
-/
theorem lift_of_comp (j : N ->* P) : f.lift (f.isUnit_comp j) = j := by
  ext; simp_rw [lift_spec, j.comp_apply, ← map_mul, toMonoidHom_apply, sec_spec']

@[to_additive]
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: {j : N ->* P} (hj : forall x, j (f x) = g x)
  statement: f.lift hg = j
  proof: by
  ext
  rw [lift_spec]; rw [← hj]; rw [← hj]; rw [← j.map_mul]
  apply congr_arg
  rw [← sec_spec']

@[to_additive (attr := simp)]

中文:
定理 lift_unique
  条件: {j : N ->* P} (hj : 对任意 x, j (f x) = g x)
  结论: f.lift hg = j
  证明: by
  ext
  rw [lift_spec]; rw [← hj]; rw [← hj]; rw [← j.map_mul]
  apply congr_arg
  rw [← sec_spec']

@[to_additive (attr := simp)]

Depends on / 依赖: congr_arg, j.map_mul, lift_spec, map_mul, sec_spec
-/
theorem lift_unique {j : N ->* P} (hj : forall x, j (f x) = g x) : f.lift hg = j := by
  ext
  rw [lift_spec]; rw [← hj]; rw [← hj]; rw [← j.map_mul]
  apply congr_arg
  rw [← sec_spec']

@[to_additive (attr := simp)]
/--
theorem `lift_id` / 定理 `lift_id`

English:
theorem lift_id
  given: (x)
  statement: f.lift f.map_units x = x
  proof: DFunLike.ext_iff.1 (f.lift_of_comp <| MonoidHom.id N) x

中文:
定理 lift_id
  条件: (x)
  结论: f.lift f.map_units x = x
  证明: DFunLike.ext_iff.1 (f.lift_of_comp <| MonoidHom.id N) x

Depends on / 依赖: DFunLike, DFunLike.ext_iff, MonoidHom, MonoidHom.id, ext_iff, f.lift_of_comp, lift_of_comp
-/
theorem lift_id (x) : f.lift f.map_units x = x :=
  DFunLike.ext_iff.1 (f.lift_of_comp <| MonoidHom.id N) x

/-- Given Localization maps `f : M →* N` for a Submonoid `S ⊆ M` and
`k : M →* Q` for a Submonoid `T ⊆ M`, such that `S ≤ T`, and we have
`l : M →* A`, the composition of the induced map `f.lift` for `k` with
the induced map `k.lift` for `l` is equal to the induced map `f.lift` for `l`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N` for a Submonoid `S ⊆ M` and
`k : M →+ Q` for a Submonoid `T ⊆ M`, such that `S ≤ T`, and we have
`l : M →+ A`, the composition of the induced map `f.lift` for `k` with
the induced map `k.lift` for `l` is equal to the induced map `f.lift` for `l` -/]
/--
theorem `lift_comp_lift` / 定理 `lift_comp_lift`

English:
theorem lift_comp_lift
  statement: {T : Submonoid M} (hST : S <= T) {Q : Type*} [CommMonoid Q]
  proof: .symm
  lift_unique _ _ fun x => by rw [← toMonoidHom_apply, ← MonoidHom.comp_apply,
    MonoidHom.comp_assoc, lift_comp, lift_comp]

@[to_additive]

中文:
定理 lift_comp_lift
  结论: {T : 子幺半群 M} (hST : S <= T) {Q : 类型} [交换幺半群 Q]
  证明: .symm
  lift_unique _ _ fun x => by rw [← toMonoidHom_apply, ← MonoidHom.comp_apply,
    MonoidHom.comp_assoc, lift_comp, lift_comp]

@[to_additive]
-/
theorem lift_comp_lift {T : Submonoid M} (hST : S <= T) {Q : Type*} [CommMonoid Q]
    (k : LocalizationMap T Q) {A : Type*} [CommMonoid A] {l : M ->* A}
    (hl : forall w : T, IsUnit (l w)) :
    (k.lift hl).comp (f.lift (map_units k ⟨_, hST ·.2⟩)) =
f.lift (hl ⟨_, hST ·.2⟩) := .symm
  lift_unique _ _ fun x => by rw [← toMonoidHom_apply, ← MonoidHom.comp_apply,
    MonoidHom.comp_assoc, lift_comp, lift_comp]

@[to_additive]
/--
theorem `lift_comp_lift_eq` / 定理 `lift_comp_lift_eq`

English:
theorem lift_comp_lift_eq
  statement: {Q : Type*} [CommMonoid Q] (k : LocalizationMap S Q)
  proof: lift_comp_lift f le_rfl k hl

中文:
定理 lift_comp_lift_eq
  结论: {Q : 类型} [交换幺半群 Q] (k : Localization映射 S Q)
  证明: lift_comp_lift f le_rfl k hl

Depends on / 依赖: le_rfl, lift_comp_lift
-/
theorem lift_comp_lift_eq {Q : Type*} [CommMonoid Q] (k : LocalizationMap S Q)
    {A : Type*} [CommMonoid A] {l : M ->* A} (hl : forall w : S, IsUnit (l w)) :
    (k.lift hl).comp (f.lift k.map_units) = f.lift hl :=
  lift_comp_lift f le_rfl k hl

/-- Given two Localization maps `f : M →* N, k : M →* P` for a Submonoid `S ⊆ M`, the hom
from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P` induced by `k`. -/
@[to_additive (attr := simp)
/-- Given two Localization maps `f : M →+ N, k : M →+ P` for a Submonoid `S ⊆ M`, the hom
from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P` induced by `k`. -/]
/--
theorem `lift_left_inverse` / 定理 `lift_left_inverse`

English:
theorem lift_left_inverse
  given: {k : LocalizationMap S P} (z : N)
  proof: (DFunLike.congr_fun (lift_comp_lift_eq f k f.map_units) z).trans (lift_id f z)

@[to_additive]

中文:
定理 lift_left_inverse
  条件: {k : Localization映射 S P} (z : N)
  证明: (DFunLike.congr_fun (lift_comp_lift_eq f k f.map_units) z).trans (lift_id f z)

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, f.map_units, lift_comp_lift_eq, lift_id, map_units
-/
theorem lift_left_inverse {k : LocalizationMap S P} (z : N) :
    k.lift f.map_units (f.lift k.map_units z) = z :=
  (DFunLike.congr_fun (lift_comp_lift_eq f k f.map_units) z).trans (lift_id f z)

@[to_additive]
/--
theorem `lift_surjective_iff` / 定理 `lift_surjective_iff`

English:
theorem lift_surjective_iff
  proof: by
  constructor
  · intro H v
    obtain ⟨z, hz⟩ := H v
    obtain ⟨x, hx⟩ := f.surj z
    use x
    rw [← hz]; rw [f.eq_mk'_iff_mul_eq.2 hx]; rw [lift_mk']; rw [mul_assoc]; rw [mul_comm _ (g ↑x.2)]; rw [← MonoidHom.domRestrict_apply]; rw [IsUnit.mul_liftRight_inv (g.domRestrict S) hg]; rw [mul_one]
  · intro H v
    obtain ⟨x, hx⟩ := H v
    use f.mk' x.1 x.2
    rw [lift_mk']; rw [mul_inv_left hg]; rw [mul_comm]; rw [← hx]

@[to_additive]

中文:
定理 lift_surjective_iff
  证明: by
  constructor
  · intro H v
    obtain ⟨z, hz⟩ := H v
    obtain ⟨x, hx⟩ := f.surj z
    use x
    rw [← hz]; rw [f.eq_mk'_iff_mul_eq.2 hx]; rw [lift_mk']; rw [mul_assoc]; rw [mul_comm _ (g ↑x.2)]; rw [← MonoidHom.domRestrict_apply]; rw [IsUnit.mul_liftRight_inv (g.domRestrict S) hg]; rw [mul_one]
  · intro H v
    obtain ⟨x, hx⟩ := H v
    use f.mk' x.1 x.2
    rw [lift_mk']; rw [mul_inv_left hg]; rw [mul_comm]; rw [← hx]

@[to_additive]

Depends on / 依赖: IsUnit, IsUnit.mul_liftRight_inv, MonoidHom, MonoidHom.domRestrict_apply, _iff_mul_eq, domRestrict, domRestrict_apply, eq_mk, f.eq_mk, f.mk, f.surj, g.domRestrict, lift_mk, mul_assoc, mul_comm, mul_inv_left, mul_liftRight_inv, mul_one
-/
theorem lift_surjective_iff :
    Function.Surjective (f.lift hg) ↔ forall v : P, exists x : M × S, v * g x.2 = g x.1 := by
  constructor
  · intro H v
    obtain ⟨z, hz⟩ := H v
    obtain ⟨x, hx⟩ := f.surj z
    use x
    rw [← hz]; rw [f.eq_mk'_iff_mul_eq.2 hx]; rw [lift_mk']; rw [mul_assoc]; rw [mul_comm _ (g ↑x.2)]; rw [← MonoidHom.domRestrict_apply]; rw [IsUnit.mul_liftRight_inv (g.domRestrict S) hg]; rw [mul_one]
  · intro H v
    obtain ⟨x, hx⟩ := H v
    use f.mk' x.1 x.2
    rw [lift_mk']; rw [mul_inv_left hg]; rw [mul_comm]; rw [← hx]

@[to_additive]
/--
theorem `lift_injective_iff` / 定理 `lift_injective_iff`

English:
theorem lift_injective_iff
  proof: by
  constructor
  · intro H x y
    constructor
    · exact f.eq_of_eq hg
    · intro h
      rw [← f.lift_eq hg]; rw [← f.lift_eq hg] at h
      exact H h
  · intro H z w h
    obtain ⟨_, _⟩ := f.surj z
    obtain ⟨_, _⟩ := f.surj w
    rw [← f.mk'_sec z]; rw [← f.mk'_sec w]
    exact (mul_inv f.map_units).2 ((H _ _).2 <| (mul_inv hg).1 h)

中文:
定理 lift_injective_iff
  证明: by
  constructor
  · intro H x y
    constructor
    · exact f.eq_of_eq hg
    · intro h
      rw [← f.lift_eq hg]; rw [← f.lift_eq hg] at h
      exact H h
  · intro H z w h
    obtain ⟨_, _⟩ := f.surj z
    obtain ⟨_, _⟩ := f.surj w
    rw [← f.mk'_sec z]; rw [← f.mk'_sec w]
    exact (mul_inv f.map_units).2 ((H _ _).2 <| (mul_inv hg).1 h)

Depends on / 依赖: _sec, eq_of_eq, f.eq_of_eq, f.lift_eq, f.map_units, f.mk, f.surj, lift_eq, map_units, mul_inv
-/
theorem lift_injective_iff :
    Function.Injective (f.lift hg) ↔ forall x y, f x = f y ↔ g x = g y := by
  constructor
  · intro H x y
    constructor
    · exact f.eq_of_eq hg
    · intro h
      rw [← f.lift_eq hg]; rw [← f.lift_eq hg] at h
      exact H h
  · intro H z w h
    obtain ⟨_, _⟩ := f.surj z
    obtain ⟨_, _⟩ := f.surj w
    rw [← f.mk'_sec z]; rw [← f.mk'_sec w]
    exact (mul_inv f.map_units).2 ((H _ _).2 <| (mul_inv hg).1 h)

variable {T : Submonoid P} (hy : forall y : S, g y in T) {Q : Type*} [CommMonoid Q]
  (k : LocalizationMap T Q)

/-- Given a `CommMonoid` homomorphism `g : M →* P` where for Submonoids `S ⊆ M, T ⊆ P` we have
`g(S) ⊆ T`, the induced Monoid homomorphism from the Localization of `M` at `S` to the
Localization of `P` at `T`: if `f : M →* N` and `k : P →* Q` are Localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : M × S` are such
that `z = f x * (f y)⁻¹`. -/
@[to_additive
/-- Given an `AddCommMonoid` homomorphism `g : M →+ P` where for AddSubmonoids `S ⊆ M, T ⊆ P` we
have `g(S) ⊆ T`, the induced AddMonoid homomorphism from the Localization of `M` at `S` to the
Localization of `P` at `T`: if `f : M →+ N` and `k : P →+ Q` are Localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) - k (g y)`, where `(x, y) : M × S` are such
that `z = f x - f y`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : N ->* Q
  body: @lift _ _ _ _ _ _ _ f (k.toMonoidHom.comp g) fun y => k.map_units ⟨g y, hy y⟩

中文:
定义 map
  签名: : N ->* Q
  定义体: @lift _ _ _ _ _ _ _ f (k.toMonoidHom.comp g) fun y => k.map_units ⟨g y, hy y⟩

Depends on / 依赖: k.map_units, k.toMonoidHom.comp, map_units, toMonoidHom
-/
noncomputable def map : N ->* Q :=
  @lift _ _ _ _ _ _ _ f (k.toMonoidHom.comp g) fun y => k.map_units ⟨g y, hy y⟩

variable {k}

@[to_additive (attr := simp)]
/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  given: (x)
  statement: f.map hy k (f x) = k (g x)
  proof: f.lift_eq (fun y => k.map_units ⟨g y, hy y⟩) x

@[to_additive (attr := simp)]

中文:
定理 map_eq
  条件: (x)
  结论: f.map hy k (f x) = k (g x)
  证明: f.lift_eq (fun y => k.map_units ⟨g y, hy y⟩) x

@[to_additive (attr := simp)]

Depends on / 依赖: f.lift_eq, k.map_units, lift_eq, map_units
-/
theorem map_eq (x) : f.map hy k (f x) = k (g x) :=
  f.lift_eq (fun y => k.map_units ⟨g y, hy y⟩) x

@[to_additive (attr := simp)]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: (f.map hy k).comp f.toMonoidHom = k.toMonoidHom.comp g
  proof: f.lift_comp fun y => k.map_units ⟨g y, hy y⟩

中文:
定理 map_comp
  结论: (f.map hy k).comp f.toMonoidHom = k.toMonoidHom.comp g
  证明: f.lift_comp fun y => k.map_units ⟨g y, hy y⟩

Depends on / 依赖: f.lift_comp, k.map_units, lift_comp, map_units
-/
theorem map_comp : (f.map hy k).comp f.toMonoidHom = k.toMonoidHom.comp g :=
  f.lift_comp fun y => k.map_units ⟨g y, hy y⟩

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
theorem `map_mk'` / 定理 `map_mk'`

English:
theorem map_mk'
  given: (x) (y : S)
  statement: f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩
  proof: by
  rw [map]; rw [lift_mk']; rw [mul_inv_left]
  change k (g x) = k (g y) * _
  rw [mul_mk'_eq_mk'_of_mul]
  exact (k.mk'_mul_cancel_left (g x) ⟨g y, hy y⟩).symm

中文:
定理 map_mk'
  条件: (x) (y : S)
  结论: f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩
  证明: by
  rw [map]; rw [lift_mk']; rw [mul_inv_left]
  change k (g x) = k (g y) * _
  rw [mul_mk'_eq_mk'_of_mul]
  exact (k.mk'_mul_cancel_left (g x) ⟨g y, hy y⟩).symm

Depends on / 依赖: _eq_mk, _mul_cancel_left, _of_mul, k.mk, lift_mk, mul_inv_left, mul_mk
-/
theorem map_mk' (x) (y : S) : f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩ := by
  rw [map]; rw [lift_mk']; rw [mul_inv_left]
  change k (g x) = k (g y) * _
  rw [mul_mk'_eq_mk'_of_mul]
  exact (k.mk'_mul_cancel_left (g x) ⟨g y, hy y⟩).symm

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) * u` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids `S, T` respectively, if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) + u` where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
/--
theorem `map_spec` / 定理 `map_spec`

English:
theorem map_spec
  given: (z u)
  statement: f.map hy k z = u ↔ k (g (f.sec z).1) = k (g (f.sec z).2) * u
  proof: f.lift_spec (fun y => k.map_units ⟨g y, hy y⟩) _ _

中文:
定理 map_spec
  条件: (z u)
  结论: f.map hy k z = u ↔ k (g (f.sec z).1) = k (g (f.sec z).2) * u
  证明: f.lift_spec (fun y => k.map_units ⟨g y, hy y⟩) _ _

Depends on / 依赖: f.lift_spec, k.map_units, lift_spec, map_units
-/
theorem map_spec (z u) : f.map hy k z = u ↔ k (g (f.sec z).1) = k (g (f.sec z).2) * u :=
  f.lift_spec (fun y => k.map_units ⟨g y, hy y⟩) _ _

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `f.map hy k z * k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids `S, T` respectively, if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
we have `f.map hy k z + k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
/--
theorem `map_mul_right` / 定理 `map_mul_right`

English:
theorem map_mul_right
  given: (z)
  statement: f.map hy k z * k (g (f.sec z).2) = k (g (f.sec z).1)
  proof: f.lift_mul_right (fun y => k.map_units ⟨g y, hy y⟩) _

中文:
定理 map_mul_right
  条件: (z)
  结论: f.map hy k z * k (g (f.sec z).2) = k (g (f.sec z).1)
  证明: f.lift_mul_right (fun y => k.map_units ⟨g y, hy y⟩) _

Depends on / 依赖: f.lift_mul_right, k.map_units, lift_mul_right, map_units
-/
theorem map_mul_right (z) : f.map hy k z * k (g (f.sec z).2) = k (g (f.sec z).1) :=
  f.lift_mul_right (fun y => k.map_units ⟨g y, hy y⟩) _

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `k (g y) * f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids `S, T` respectively if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
we have `k (g y) + f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
/--
theorem `map_mul_left` / 定理 `map_mul_left`

English:
theorem map_mul_left
  given: (z)
  statement: k (g (f.sec z).2) * f.map hy k z = k (g (f.sec z).1)
  proof: by
  rw [mul_comm]; rw [f.map_mul_right]

@[to_additive (attr := simp)]

中文:
定理 map_mul_left
  条件: (z)
  结论: k (g (f.sec z).2) * f.map hy k z = k (g (f.sec z).1)
  证明: by
  rw [mul_comm]; rw [f.map_mul_right]

@[to_additive (attr := simp)]

Depends on / 依赖: f.map_mul_right, map_mul_right, mul_comm
-/
theorem map_mul_left (z) : k (g (f.sec z).2) * f.map hy k z = k (g (f.sec z).1) := by
  rw [mul_comm]; rw [f.map_mul_right]

@[to_additive (attr := simp)]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (z : N)
  statement: f.map (fun y => show MonoidHom.id M y in S from y.2) f z = z
  proof: f.lift_id z

中文:
定理 map_id
  条件: (z : N)
  结论: f.map (fun y => show 幺半群态射.id M y in S from y.2) f z = z
  证明: f.lift_id z

Depends on / 依赖: f.lift_id, lift_id
-/
theorem map_id (z : N) : f.map (fun y => show MonoidHom.id M y in S from y.2) f z = z :=
  f.lift_id z

set_option backward.isDefEq.respectTransparency false in
/-- If `CommMonoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive
/-- If `AddCommMonoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/]
/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  statement: {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R]
  proof: by
  ext z
  change j _ * _ = j (l _) * _
  rw [mul_inv_left]; rw [← mul_assoc]; rw [mul_inv_right]
  change j _ * j (l (g _)) = j (l _) * _
  rw [← map_mul j]; rw [← map_mul j]; rw [← l.map_mul]; rw [← l.map_mul]
  refine k.comp_eq_of_eq hl j ?_
  rw [map_mul k]; rw [map_mul k]; rw [sec_spec']; rw [mul_assoc]; rw [map_mul_right]

中文:
定理 map_comp_map
  结论: {A : 类型} [交换幺半群 A] {U : 子幺半群 A} {R} [交换幺半群 R]
  证明: by
  ext z
  change j _ * _ = j (l _) * _
  rw [mul_inv_left]; rw [← mul_assoc]; rw [mul_inv_right]
  change j _ * j (l (g _)) = j (l _) * _
  rw [← map_mul j]; rw [← map_mul j]; rw [← l.map_mul]; rw [← l.map_mul]
  refine k.comp_eq_of_eq hl j ?_
  rw [map_mul k]; rw [map_mul k]; rw [sec_spec']; rw [mul_assoc]; rw [map_mul_right]

Depends on / 依赖: comp_eq_of_eq, k.comp_eq_of_eq, l.map_mul, map_mul, map_mul_right, mul_assoc, mul_inv_left, mul_inv_right, sec_spec
-/
theorem map_comp_map {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R]
    (j : LocalizationMap U R) {l : P ->* A} (hl : forall w : T, l w in U) :
    (k.map hl j).comp (f.map hy k) =
    f.map (fun x => show l.comp g x in U from hl ⟨g x, hy x⟩) j := by
  ext z
  change j _ * _ = j (l _) * _
  rw [mul_inv_left]; rw [← mul_assoc]; rw [mul_inv_right]
  change j _ * j (l (g _)) = j (l _) * _
  rw [← map_mul j]; rw [← map_mul j]; rw [← l.map_mul]; rw [← l.map_mul]
  refine k.comp_eq_of_eq hl j ?_
  rw [map_mul k]; rw [map_mul k]; rw [sec_spec']; rw [mul_assoc]; rw [map_mul_right]

/-- If `CommMonoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive
/-- If `AddCommMonoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R]
  proof: by
  -- Porting note: need to specify `k` explicitly
  rw [← f.map_comp_map (k := k) hy j hl]
  simp only [MonoidHom.coe_comp, comp_apply]

中文:
定理 map_map
  结论: {A : 类型} [交换幺半群 A] {U : 子幺半群 A} {R} [交换幺半群 R]
  证明: by
  -- Porting note: need to specify `k` explicitly
  rw [← f.map_comp_map (k := k) hy j hl]
  simp only [MonoidHom.coe_comp, comp_apply]
-/
theorem map_map {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R]
    (j : LocalizationMap U R) {l : P ->* A} (hl : forall w : T, l w in U) (x) :
    k.map hl j (f.map hy k x) = f.map (fun x => show l.comp g x in U from hl ⟨g x, hy x⟩) j x := by
  -- Porting note: need to specify `k` explicitly
  rw [← f.map_comp_map (k := k) hy j hl]
  simp only [MonoidHom.coe_comp, comp_apply]

/--
theorem `map_injective_of_surjOn_or_injective` / 定理 `map_injective_of_surjOn_or_injective`

English:
theorem map_injective_of_surjOn_or_injective
  proof: fun z w hizw => by
  set i := f.map hy k
  have ifkg (a : M) : i (f a) = k (g a) := f.map_eq hy a
  have ⟨z', w', x, hxz, hxw⟩ := surj₂ f z w
  have : k (g z') = k (g w') := by rw [← ifkg, ← ifkg, ← hxz, ← hxw, map_mul, map_mul, hizw]
  obtain surj | inj := or
  · have ⟨⟨c, hc'⟩, eq⟩ := k.exists_of_eq this
    obtain ⟨c, hc, rfl⟩ := surj hc'
    simp_rw [← map_mul, hg.eq_iff] at eq
    rw [← (f.map_units x).mul_left_inj]; rw [hxz]; rw [hxw]; rw [f.eq_iff_exists]
    exact ⟨⟨c, hc⟩, eq⟩
  · apply (f.map_units x).mul_right_cancel
    rw [hxz]; rw [hxw]; rw [hg (inj this)]

中文:
定理 map_injective_of_surjOn_or_injective
  证明: fun z w hizw => by
  set i := f.map hy k
  have ifkg (a : M) : i (f a) = k (g a) := f.map_eq hy a
  have ⟨z', w', x, hxz, hxw⟩ := surj₂ f z w
  have : k (g z') = k (g w') := by rw [← ifkg, ← ifkg, ← hxz, ← hxw, map_mul, map_mul, hizw]
  obtain surj | inj := or
  · have ⟨⟨c, hc'⟩, eq⟩ := k.exists_of_eq this
    obtain ⟨c, hc, rfl⟩ := surj hc'
    simp_rw [← map_mul, hg.eq_iff] at eq
    rw [← (f.map_units x).mul_left_inj]; rw [hxz]; rw [hxw]; rw [f.eq_iff_exists]
    exact ⟨⟨c, hc⟩, eq⟩
  · apply (f.map_units x).mul_right_cancel
    rw [hxz]; rw [hxw]; rw [hg (inj this)]
-/
@[to_additive] theorem map_injective_of_surjOn_or_injective
    (or : (S : Set M).SurjOn g T ∨ Injective k) (hg : Injective g) :
    Injective (f.map hy k) := fun z w hizw => by
  set i := f.map hy k
  have ifkg (a : M) : i (f a) = k (g a) := f.map_eq hy a
  have ⟨z', w', x, hxz, hxw⟩ := surj₂ f z w
  have : k (g z') = k (g w') := by rw [← ifkg, ← ifkg, ← hxz, ← hxw, map_mul, map_mul, hizw]
  obtain surj | inj := or
  · have ⟨⟨c, hc'⟩, eq⟩ := k.exists_of_eq this
    obtain ⟨c, hc, rfl⟩ := surj hc'
    simp_rw [← map_mul, hg.eq_iff] at eq
    rw [← (f.map_units x).mul_left_inj]; rw [hxz]; rw [hxw]; rw [f.eq_iff_exists]
    exact ⟨⟨c, hc⟩, eq⟩
  · apply (f.map_units x).mul_right_cancel
    rw [hxz]; rw [hxw]; rw [hg (inj this)]

/--
theorem `map_surjective_of_surjOn` / 定理 `map_surjective_of_surjOn`

English:
theorem map_surjective_of_surjOn
  statement: (surj : (S : Set M).SurjOn g T)
  proof: fun z => by
  obtain ⟨y, ⟨t, ht⟩, rfl⟩ := k.mk'_surjective z
  obtain ⟨s, hs, rfl⟩ := surj ht
  obtain ⟨x, rfl⟩ := hg y
  use f.mk' x ⟨s, hs⟩
  rw [map_mk']

中文:
定理 map_surjective_of_surjOn
  结论: (surj : (S : 集合 M).满射限制 g T)
  证明: fun z => by
  obtain ⟨y, ⟨t, ht⟩, rfl⟩ := k.mk'_surjective z
  obtain ⟨s, hs, rfl⟩ := surj ht
  obtain ⟨x, rfl⟩ := hg y
  use f.mk' x ⟨s, hs⟩
  rw [map_mk']
-/
@[to_additive] theorem map_surjective_of_surjOn (surj : (S : Set M).SurjOn g T)
    (hg : Surjective g) : Surjective (f.map hy k) := fun z => by
  obtain ⟨y, ⟨t, ht⟩, rfl⟩ := k.mk'_surjective z
  obtain ⟨s, hs, rfl⟩ := surj ht
  obtain ⟨x, rfl⟩ := hg y
  use f.mk' x ⟨s, hs⟩
  rw [map_mk']

/-- Given an injective `CommMonoid` homomorphism `g : M →* P`, and a submonoid `S ⊆ M`,
the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `g S`, is injective.
-/
@[to_additive /-- Given an injective `AddCommMonoid` homomorphism `g : M →+ P`, and a
submonoid `S ⊆ M`, the induced monoid homomorphism from the localization of `M` at `S`
to the localization of `P` at `g S`, is injective. -/]
/--
theorem `map_injective_of_injective` / 定理 `map_injective_of_injective`

English:
theorem map_injective_of_injective
  given: (hg : Injective g) (k : LocalizationMap (S.map g) Q)
  proof: f.map_injective_of_surjOn_or_injective _ (.inl <| Set.surjOn_image ..) hg

中文:
定理 map_injective_of_injective
  条件: (hg : 单射 g) (k : Localization映射 (S.map g) Q)
  证明: f.map_injective_of_surjOn_or_injective _ (.inl <| Set.surjOn_image ..) hg

Depends on / 依赖: Set.surjOn_image, f.map_injective_of_surjOn_or_injective, map_injective_of_surjOn_or_injective, surjOn_image
-/
theorem map_injective_of_injective (hg : Injective g) (k : LocalizationMap (S.map g) Q) :
    Injective (map f (apply_coe_mem_map g S) k) :=
  f.map_injective_of_surjOn_or_injective _ (.inl <| Set.surjOn_image ..) hg

/-- Given a surjective `CommMonoid` homomorphism `g : M →* P`, and a submonoid `S ⊆ M`,
the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `g S`, is surjective.
-/
@[to_additive /-- Given a surjective `AddCommMonoid` homomorphism `g : M →+ P`, and a
submonoid `S ⊆ M`, the induced monoid homomorphism from the localization of `M` at `S`
to the localization of `P` at `g S`, is surjective. -/]
/--
theorem `map_surjective_of_surjective` / 定理 `map_surjective_of_surjective`

English:
theorem map_surjective_of_surjective
  given: (hg : Surjective g) (k : LocalizationMap (S.map g) Q)
  proof: f.map_surjective_of_surjOn _ (Set.surjOn_image ..) hg

中文:
定理 map_surjective_of_surjective
  条件: (hg : 满射 g) (k : Localization映射 (S.map g) Q)
  证明: f.map_surjective_of_surjOn _ (Set.surjOn_image ..) hg

Depends on / 依赖: Set.surjOn_image, f.map_surjective_of_surjOn, map_surjective_of_surjOn, surjOn_image
-/
theorem map_surjective_of_surjective (hg : Surjective g) (k : LocalizationMap (S.map g) Q) :
    Surjective (map f (apply_coe_mem_map g S) k) :=
  f.map_surjective_of_surjOn _ (Set.surjOn_image ..) hg

end LocalizationMap

end Submonoid

namespace Submonoid

namespace LocalizationMap

variable (f : S.LocalizationMap N) {g : M ->* P} (hg : forall y : S, IsUnit (g y)) {T : Submonoid P}
  {Q : Type*} [CommMonoid Q]

/-- If `f : M →* N` and `k : M →* P` are Localization maps for a Submonoid `S`, we get an
isomorphism of `N` and `P`. -/
@[to_additive
/-- If `f : M →+ N` and `k : M →+ R` are Localization maps for an AddSubmonoid `S`, we get an
isomorphism of `N` and `R`. -/]
/--
Definition of `mulEquivOfLocalizations` / `mulEquivOfLocalizations` 的定义

English:
definition mulEquivOfLocalizations
  signature: (k : LocalizationMap S P)
  body: { toFun := f.lift k.map_units
  invFun := k.lift f.map_units
  left_inv := f.lift_left_inverse
  right_inv := k.lift_left_inverse
  map_mul' := map_mul _ }

@[to_additive (attr := simp)]

中文:
定义 mulEquivOfLocalizations
  签名: (k : Localization映射 S P)
  定义体: { toFun := f.lift k.map_units
  invFun := k.lift f.map_units
  left_inv := f.lift_left_inverse
  right_inv := k.lift_left_inverse
  map_mul' := map_mul _ }

@[to_additive (attr := simp)]

Depends on / 依赖: f.lift, f.lift_left_inverse, f.map_units, invFun, k.lift, k.lift_left_inverse, k.map_units, left_inv, lift_left_inverse, map_mul, map_units, right_inv
-/
noncomputable def mulEquivOfLocalizations (k : LocalizationMap S P) : N ≃* P :=
{ toFun := f.lift k.map_units
  invFun := k.lift f.map_units
  left_inv := f.lift_left_inverse
  right_inv := k.lift_left_inverse
  map_mul' := map_mul _ }

@[to_additive (attr := simp)]
/--
theorem `mulEquivOfLocalizations_apply` / 定理 `mulEquivOfLocalizations_apply`

English:
theorem mulEquivOfLocalizations_apply
  given: {k : LocalizationMap S P} {x}
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mulEquivOfLocalizations_apply
  条件: {k : Localization映射 S P} {x}
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mulEquivOfLocalizations_apply {k : LocalizationMap S P} {x} :
    f.mulEquivOfLocalizations k x = f.lift k.map_units x := rfl

@[to_additive (attr := simp)]
/--
theorem `mulEquivOfLocalizations_symm_apply` / 定理 `mulEquivOfLocalizations_symm_apply`

English:
theorem mulEquivOfLocalizations_symm_apply
  given: {k : LocalizationMap S P} {x}
  proof: rfl

@[to_additive]

中文:
定理 mulEquivOfLocalizations_symm_apply
  条件: {k : Localization映射 S P} {x}
  证明: rfl

@[to_additive]
-/
theorem mulEquivOfLocalizations_symm_apply {k : LocalizationMap S P} {x} :
    (f.mulEquivOfLocalizations k).symm x = k.lift f.map_units x := rfl

@[to_additive]
/--
theorem `mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizations` / 定理 `mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizations`

English:
theorem mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizations
  given: {k : LocalizationMap S P}
  proof: rfl

中文:
定理 mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizations
  条件: {k : Localization映射 S P}
  证明: rfl
-/
theorem mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizations {k : LocalizationMap S P} :
    (k.mulEquivOfLocalizations f).symm = f.mulEquivOfLocalizations k := rfl

/-- If `f : M →* N` is a Localization map for a Submonoid `S` and `k : N ≃* P` is an isomorphism
of `CommMonoid`s, `k ∘ f` is a Localization map for `M` at `S`. -/
@[to_additive
/-- If `f : M →+ N` is a Localization map for a Submonoid `S` and `k : N ≃+ P` is an isomorphism
of `AddCommMonoid`s, `k ∘ f` is a Localization map for `M` at `S`. -/]
/--
Definition of `ofMulEquivOfLocalizations` / `ofMulEquivOfLocalizations` 的定义

English:
definition ofMulEquivOfLocalizations
  signature: (k : N ≃* P)
  body: (k.toMonoidHom.comp f.toMonoidHom).toLocalizationMap (fun y => isUnit_comp f k.toMonoidHom y)
    (fun v =>
      let ⟨z, hz⟩ := k.surjective v
      let ⟨x, hx⟩ := f.surj z
      ⟨x, show v * k (f _) = k (f _) by rw [← hx, map_mul, ← hz]⟩)
    fun x y => (k.apply_eq_iff_eq.trans f.eq_iff_exists).1

@[to_additive (attr := simp)]

中文:
定义 ofMulEquivOfLocalizations
  签名: (k : N ≃* P)
  定义体: (k.toMonoidHom.comp f.toMonoidHom).toLocalizationMap (fun y => isUnit_comp f k.toMonoidHom y)
    (fun v =>
      let ⟨z, hz⟩ := k.surjective v
      let ⟨x, hx⟩ := f.surj z
      ⟨x, show v * k (f _) = k (f _) by rw [← hx, map_mul, ← hz]⟩)
    fun x y => (k.apply_eq_iff_eq.trans f.eq_iff_exists).1

@[to_additive (attr := simp)]

Depends on / 依赖: apply_eq_iff_eq, eq_iff_exists, f.eq_iff_exists, f.surj, f.toMonoidHom, isUnit_comp, k.apply_eq_iff_eq.trans, k.surjective, k.toMonoidHom, k.toMonoidHom.comp, map_mul, surjective, toLocalizationMap, toMonoidHom
-/
def ofMulEquivOfLocalizations (k : N ≃* P) : LocalizationMap S P :=
  (k.toMonoidHom.comp f.toMonoidHom).toLocalizationMap (fun y => isUnit_comp f k.toMonoidHom y)
    (fun v =>
      let ⟨z, hz⟩ := k.surjective v
      let ⟨x, hx⟩ := f.surj z
      ⟨x, show v * k (f _) = k (f _) by rw [← hx, map_mul, ← hz]⟩)
    fun x y => (k.apply_eq_iff_eq.trans f.eq_iff_exists).1

@[to_additive (attr := simp)]
/--
theorem `ofMulEquivOfLocalizations_apply` / 定理 `ofMulEquivOfLocalizations_apply`

English:
theorem ofMulEquivOfLocalizations_apply
  given: {k : N ≃* P} (x)
  proof: rfl

@[to_additive]

中文:
定理 ofMulEquivOfLocalizations_apply
  条件: {k : N ≃* P} (x)
  证明: rfl

@[to_additive]
-/
theorem ofMulEquivOfLocalizations_apply {k : N ≃* P} (x) :
    f.ofMulEquivOfLocalizations k x = k (f x) := rfl

@[to_additive]
/--
theorem `ofMulEquivOfLocalizations_eq` / 定理 `ofMulEquivOfLocalizations_eq`

English:
theorem ofMulEquivOfLocalizations_eq
  given: {k : N ≃* P}
  proof: rfl

@[to_additive]

中文:
定理 ofMulEquivOfLocalizations_eq
  条件: {k : N ≃* P}
  证明: rfl

@[to_additive]
-/
theorem ofMulEquivOfLocalizations_eq {k : N ≃* P} :
    (f.ofMulEquivOfLocalizations k).toMonoidHom = k.toMonoidHom.comp f.toMonoidHom := rfl

@[to_additive]
/--
theorem `symm_comp_ofMulEquivOfLocalizations_apply` / 定理 `symm_comp_ofMulEquivOfLocalizations_apply`

English:
theorem symm_comp_ofMulEquivOfLocalizations_apply
  given: {k : N ≃* P} (x)
  proof: k.symm_apply_apply (f x)

@[to_additive]

中文:
定理 symm_comp_ofMulEquivOfLocalizations_apply
  条件: {k : N ≃* P} (x)
  证明: k.symm_apply_apply (f x)

@[to_additive]

Depends on / 依赖: k.symm_apply_apply, symm_apply_apply
-/
theorem symm_comp_ofMulEquivOfLocalizations_apply {k : N ≃* P} (x) :
    k.symm (f.ofMulEquivOfLocalizations k x) = f x := k.symm_apply_apply (f x)

@[to_additive]
/--
theorem `symm_comp_ofMulEquivOfLocalizations_apply'` / 定理 `symm_comp_ofMulEquivOfLocalizations_apply'`

English:
theorem symm_comp_ofMulEquivOfLocalizations_apply'
  given: {k : P ≃* N} (x)
  proof: k.apply_symm_apply (f x)

@[to_additive]

中文:
定理 symm_comp_ofMulEquivOfLocalizations_apply'
  条件: {k : P ≃* N} (x)
  证明: k.apply_symm_apply (f x)

@[to_additive]

Depends on / 依赖: apply_symm_apply, k.apply_symm_apply
-/
theorem symm_comp_ofMulEquivOfLocalizations_apply' {k : P ≃* N} (x) :
    k (f.ofMulEquivOfLocalizations k.symm x) = f x := k.apply_symm_apply (f x)

@[to_additive]
/--
theorem `ofMulEquivOfLocalizations_eq_iff_eq` / 定理 `ofMulEquivOfLocalizations_eq_iff_eq`

English:
theorem ofMulEquivOfLocalizations_eq_iff_eq
  given: {k : N ≃* P} {x y}
  proof: k.toEquiv.eq_symm_apply.symm

@[to_additive addEquivOfLocalizations_right_inv]

中文:
定理 ofMulEquivOfLocalizations_eq_iff_eq
  条件: {k : N ≃* P} {x y}
  证明: k.toEquiv.eq_symm_apply.symm

@[to_additive addEquivOfLocalizations_right_inv]

Depends on / 依赖: eq_symm_apply, k.toEquiv.eq_symm_apply.symm, toEquiv
-/
theorem ofMulEquivOfLocalizations_eq_iff_eq {k : N ≃* P} {x y} :
    f.ofMulEquivOfLocalizations k x = y ↔ f x = k.symm y :=
  k.toEquiv.eq_symm_apply.symm

@[to_additive addEquivOfLocalizations_right_inv]
/--
theorem `mulEquivOfLocalizations_right_inv` / 定理 `mulEquivOfLocalizations_right_inv`

English:
theorem mulEquivOfLocalizations_right_inv
  given: (k : LocalizationMap S P)
  proof: toMonoidHom_injective f.lift_comp k.map_units

@[to_additive addEquivOfLocalizations_right_inv_apply]

中文:
定理 mulEquivOfLocalizations_right_inv
  条件: (k : Localization映射 S P)
  证明: toMonoidHom_injective f.lift_comp k.map_units

@[to_additive addEquivOfLocalizations_right_inv_apply]

Depends on / 依赖: f.lift_comp, k.map_units, lift_comp, map_units, toMonoidHom_injective
-/
theorem mulEquivOfLocalizations_right_inv (k : LocalizationMap S P) :
    f.ofMulEquivOfLocalizations (f.mulEquivOfLocalizations k) = k :=
toMonoidHom_injective f.lift_comp k.map_units

@[to_additive addEquivOfLocalizations_right_inv_apply]
/--
theorem `mulEquivOfLocalizations_right_inv_apply` / 定理 `mulEquivOfLocalizations_right_inv_apply`

English:
theorem mulEquivOfLocalizations_right_inv_apply
  given: {k : LocalizationMap S P} {x}
  proof: by simp

@[to_additive (attr := simp)]

中文:
定理 mulEquivOfLocalizations_right_inv_apply
  条件: {k : Localization映射 S P} {x}
  证明: by simp

@[to_additive (attr := simp)]
-/
theorem mulEquivOfLocalizations_right_inv_apply {k : LocalizationMap S P} {x} :
    f.ofMulEquivOfLocalizations (f.mulEquivOfLocalizations k) x = k x := by simp

@[to_additive (attr := simp)]
/--
theorem `mulEquivOfLocalizations_left_inv` / 定理 `mulEquivOfLocalizations_left_inv`

English:
theorem mulEquivOfLocalizations_left_inv
  given: (k : N ≃* P)
  proof: DFunLike.ext _ _ fun x => DFunLike.ext_iff.1 (f.lift_of_comp k.toMonoidHom) x

@[to_additive]

中文:
定理 mulEquivOfLocalizations_left_inv
  条件: (k : N ≃* P)
  证明: DFunLike.ext _ _ fun x => DFunLike.ext_iff.1 (f.lift_of_comp k.toMonoidHom) x

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext, DFunLike.ext_iff, ext_iff, f.lift_of_comp, k.toMonoidHom, lift_of_comp, toMonoidHom
-/
theorem mulEquivOfLocalizations_left_inv (k : N ≃* P) :
    f.mulEquivOfLocalizations (f.ofMulEquivOfLocalizations k) = k :=
  DFunLike.ext _ _ fun x => DFunLike.ext_iff.1 (f.lift_of_comp k.toMonoidHom) x

@[to_additive]
/--
theorem `mulEquivOfLocalizations_left_inv_apply` / 定理 `mulEquivOfLocalizations_left_inv_apply`

English:
theorem mulEquivOfLocalizations_left_inv_apply
  given: {k : N ≃* P} (x)
  proof: by simp

@[to_additive (attr := simp)]

中文:
定理 mulEquivOfLocalizations_left_inv_apply
  条件: {k : N ≃* P} (x)
  证明: by simp

@[to_additive (attr := simp)]
-/
theorem mulEquivOfLocalizations_left_inv_apply {k : N ≃* P} (x) :
    f.mulEquivOfLocalizations (f.ofMulEquivOfLocalizations k) x = k x := by simp

@[to_additive (attr := simp)]
/--
theorem `ofMulEquivOfLocalizations_id` / 定理 `ofMulEquivOfLocalizations_id`

English:
theorem ofMulEquivOfLocalizations_id
  statement: f.ofMulEquivOfLocalizations (MulEquiv.refl N) = f
  proof: by
  ext; rfl

@[to_additive]

中文:
定理 ofMulEquivOfLocalizations_id
  结论: f.ofMulEquivOfLocalizations (乘法等价.refl N) = f
  证明: by
  ext; rfl

@[to_additive]
-/
theorem ofMulEquivOfLocalizations_id : f.ofMulEquivOfLocalizations (MulEquiv.refl N) = f := by
  ext; rfl

@[to_additive]
/--
theorem `ofMulEquivOfLocalizations_comp` / 定理 `ofMulEquivOfLocalizations_comp`

English:
theorem ofMulEquivOfLocalizations_comp
  given: {k : N ≃* P} {j : P ≃* Q}
  proof: by
  ext; rfl

中文:
定理 ofMulEquivOfLocalizations_comp
  条件: {k : N ≃* P} {j : P ≃* Q}
  证明: by
  ext; rfl
-/
theorem ofMulEquivOfLocalizations_comp {k : N ≃* P} {j : P ≃* Q} :
    (f.ofMulEquivOfLocalizations (k.trans j)).toMonoidHom =
      j.toMonoidHom.comp (f.ofMulEquivOfLocalizations k).toMonoidHom := by
  ext; rfl

/-- Given `CommMonoid`s `M, P` and Submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is a Localization
map for `S` and `k : P ≃* M` is an isomorphism of `CommMonoid`s such that `k(T) = S`, `f ∘ k`
is a Localization map for `T`. -/
@[to_additive
/-- Given `AddCommMonoid`s `M, P` and `AddSubmonoid`s `S ⊆ M, T ⊆ P`, if `f : M →* N` is a
Localization map for `S` and `k : P ≃+ M` is an isomorphism of `AddCommMonoid`s such that
`k(T) = S`, `f ∘ k` is a Localization map for `T`. -/]
/--
Definition of `ofMulEquivOfDom` / `ofMulEquivOfDom` 的定义

English:
definition ofMulEquivOfDom
  signature: {k : P ≃* M} (H : T.map k.toMonoidHom = S)
  body: have H' : S.comap k.toMonoidHom = T :=
    H ▸ (SetLike.coe_injective <| T.1.1.preimage_image_eq k.toEquiv.injective)
  (f.toMonoidHom.comp k.toMonoidHom).toLocalizationMap
    (fun y =>
      let ⟨z, hz⟩ := f.map_units ⟨k y, H ▸ Set.mem_image_of_mem k y.2⟩
      ⟨z, hz⟩)
    (fun z =>
      let ⟨x, hx⟩ := f.surj z
      let ⟨v, hv⟩ := k.surjective x.1
      let ⟨w, hw⟩ := k.surjective x.2
      ⟨(v, ⟨w, H' ▸ show k w in S from hw.symm ▸ x.2.2⟩), by
        simp_rw [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hv, hw]
        dsimp
        rw [hx]⟩)
    fun x y => by
      rw [MonoidHom.comp_apply]; rw [MonoidHom.comp_apply]; rw [MulEquiv.toMonoidHom_eq_coe]; rw [MonoidHom.coe_coe]; rw [toMonoidHom_apply]; rw [toMonoidHom_apply]; rw [f.eq_iff_exists]
      rintro ⟨c, hc⟩
      let ⟨d, hd⟩ := k.surjective c
      refine ⟨⟨d, H' ▸ show k d in S from hd.symm ▸ c.2⟩, ?_⟩
      rw [← hd]; rw [← map_mul k]; rw [← map_mul k] at hc; exact k.injective hc

@[to_additive (attr := simp)]

中文:
定义 ofMulEquivOfDom
  签名: {k : P ≃* M} (H : T.map k.toMonoidHom = S)
  定义体: have H' : S.comap k.toMonoidHom = T :=
    H ▸ (SetLike.coe_injective <| T.1.1.preimage_image_eq k.toEquiv.injective)
  (f.toMonoidHom.comp k.toMonoidHom).toLocalizationMap
    (fun y =>
      let ⟨z, hz⟩ := f.map_units ⟨k y, H ▸ Set.mem_image_of_mem k y.2⟩
      ⟨z, hz⟩)
    (fun z =>
      let ⟨x, hx⟩ := f.surj z
      let ⟨v, hv⟩ := k.surjective x.1
      let ⟨w, hw⟩ := k.surjective x.2
      ⟨(v, ⟨w, H' ▸ show k w in S from hw.symm ▸ x.2.2⟩), by
        simp_rw [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hv, hw]
        dsimp
        rw [hx]⟩)
    fun x y => by
      rw [MonoidHom.comp_apply]; rw [MonoidHom.comp_apply]; rw [MulEquiv.toMonoidHom_eq_coe]; rw [MonoidHom.coe_coe]; rw [toMonoidHom_apply]; rw [toMonoidHom_apply]; rw [f.eq_iff_exists]
      rintro ⟨c, hc⟩
      let ⟨d, hd⟩ := k.surjective c
      refine ⟨⟨d, H' ▸ show k d in S from hd.symm ▸ c.2⟩, ?_⟩
      rw [← hd]; rw [← map_mul k]; rw [← map_mul k] at hc; exact k.injective hc

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHom, MonoidHom.coe_coe, MonoidHom.comp_apply, MulEquiv, MulEquiv.toMonoidHom_eq_coe, S.comap, Set.mem_image_of_mem, SetLike, SetLike.coe_injective, coe_coe, coe_injective, comp_apply, f.map_units, f.surj, f.toMonoidHom.comp, hw.symm, injective, k.surjective, k.toEquiv.injective, k.toMonoidHom
-/
def ofMulEquivOfDom {k : P ≃* M} (H : T.map k.toMonoidHom = S) : LocalizationMap T N :=
  have H' : S.comap k.toMonoidHom = T :=
    H ▸ (SetLike.coe_injective <| T.1.1.preimage_image_eq k.toEquiv.injective)
  (f.toMonoidHom.comp k.toMonoidHom).toLocalizationMap
    (fun y =>
      let ⟨z, hz⟩ := f.map_units ⟨k y, H ▸ Set.mem_image_of_mem k y.2⟩
      ⟨z, hz⟩)
    (fun z =>
      let ⟨x, hx⟩ := f.surj z
      let ⟨v, hv⟩ := k.surjective x.1
      let ⟨w, hw⟩ := k.surjective x.2
      ⟨(v, ⟨w, H' ▸ show k w in S from hw.symm ▸ x.2.2⟩), by
        simp_rw [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hv, hw]
        dsimp
        rw [hx]⟩)
    fun x y => by
      rw [MonoidHom.comp_apply]; rw [MonoidHom.comp_apply]; rw [MulEquiv.toMonoidHom_eq_coe]; rw [MonoidHom.coe_coe]; rw [toMonoidHom_apply]; rw [toMonoidHom_apply]; rw [f.eq_iff_exists]
      rintro ⟨c, hc⟩
      let ⟨d, hd⟩ := k.surjective c
      refine ⟨⟨d, H' ▸ show k d in S from hd.symm ▸ c.2⟩, ?_⟩
      rw [← hd]; rw [← map_mul k]; rw [← map_mul k] at hc; exact k.injective hc

@[to_additive (attr := simp)]
/--
theorem `ofMulEquivOfDom_apply` / 定理 `ofMulEquivOfDom_apply`

English:
theorem ofMulEquivOfDom_apply
  given: {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x)
  proof: rfl

@[to_additive]

中文:
定理 ofMulEquivOfDom_apply
  条件: {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x)
  证明: rfl

@[to_additive]
-/
theorem ofMulEquivOfDom_apply {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x) :
    f.ofMulEquivOfDom H x = f (k x) := rfl

@[to_additive]
/--
theorem `ofMulEquivOfDom_eq` / 定理 `ofMulEquivOfDom_eq`

English:
theorem ofMulEquivOfDom_eq
  given: {k : P ≃* M} (H : T.map k.toMonoidHom = S)
  proof: rfl

@[to_additive]

中文:
定理 ofMulEquivOfDom_eq
  条件: {k : P ≃* M} (H : T.map k.toMonoidHom = S)
  证明: rfl

@[to_additive]
-/
theorem ofMulEquivOfDom_eq {k : P ≃* M} (H : T.map k.toMonoidHom = S) :
    (f.ofMulEquivOfDom H).toMonoidHom = f.toMonoidHom.comp k.toMonoidHom := rfl

@[to_additive]
/--
theorem `ofMulEquivOfDom_comp_symm` / 定理 `ofMulEquivOfDom_comp_symm`

English:
theorem ofMulEquivOfDom_comp_symm
  given: {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x)
  proof: congr_arg f k.apply_symm_apply x

@[to_additive]

中文:
定理 ofMulEquivOfDom_comp_symm
  条件: {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x)
  证明: congr_arg f k.apply_symm_apply x

@[to_additive]

Depends on / 依赖: apply_symm_apply, congr_arg, k.apply_symm_apply
-/
theorem ofMulEquivOfDom_comp_symm {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x) :
    f.ofMulEquivOfDom H (k.symm x) = f x :=
congr_arg f k.apply_symm_apply x

@[to_additive]
/--
theorem `ofMulEquivOfDom_comp` / 定理 `ofMulEquivOfDom_comp`

English:
theorem ofMulEquivOfDom_comp
  given: {k : M ≃* P} (H : T.map k.symm.toMonoidHom = S) (x)
  proof: congr_arg f k.symm_apply_apply x

中文:
定理 ofMulEquivOfDom_comp
  条件: {k : M ≃* P} (H : T.map k.symm.toMonoidHom = S) (x)
  证明: congr_arg f k.symm_apply_apply x

Depends on / 依赖: congr_arg, k.symm_apply_apply, symm_apply_apply
-/
theorem ofMulEquivOfDom_comp {k : M ≃* P} (H : T.map k.symm.toMonoidHom = S) (x) :
f.ofMulEquivOfDom H (k x) = f x := congr_arg f k.symm_apply_apply x

/-- A special case of `f ∘ id = f`, `f` a Localization map. -/
@[to_additive (attr := simp) /-- A special case of `f ∘ id = f`, `f` a Localization map. -/]
/--
theorem `ofMulEquivOfDom_id` / 定理 `ofMulEquivOfDom_id`

English:
theorem ofMulEquivOfDom_id
  proof: by
  ext; rfl

中文:
定理 ofMulEquivOfDom_id
  证明: by
  ext; rfl
-/
theorem ofMulEquivOfDom_id :
    f.ofMulEquivOfDom
        (show S.map (MulEquiv.refl M).toMonoidHom = S from
          Submonoid.ext fun x => ⟨fun ⟨_, hy, h⟩ => h ▸ hy, fun h => ⟨x, h, rfl⟩⟩) = f := by
  ext; rfl

/-- Given Localization maps `f : M →* N, k : P →* U` for Submonoids `S, T` respectively, an
isomorphism `j : M ≃* P` such that `j(S) = T` induces an isomorphism of localizations `N ≃* U`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ U` for Submonoids `S, T` respectively, an
isomorphism `j : M ≃+ P` such that `j(S) = T` induces an isomorphism of localizations `N ≃+ U`. -/]
/--
Definition of `mulEquivOfMulEquiv` / `mulEquivOfMulEquiv` 的定义

English:
definition mulEquivOfMulEquiv
  signature: (k : LocalizationMap T Q) {j : M ≃* P}
  body: f.mulEquivOfLocalizations k.ofMulEquivOfDom H

@[to_additive (attr := simp)]

中文:
定义 mulEquivOfMulEquiv
  签名: (k : Localization映射 T Q) {j : M ≃* P}
  定义体: f.mulEquivOfLocalizations k.ofMulEquivOfDom H

@[to_additive (attr := simp)]

Depends on / 依赖: f.mulEquivOfLocalizations, k.ofMulEquivOfDom, mulEquivOfLocalizations, ofMulEquivOfDom
-/
noncomputable def mulEquivOfMulEquiv (k : LocalizationMap T Q) {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) : N ≃* Q :=
f.mulEquivOfLocalizations k.ofMulEquivOfDom H

@[to_additive (attr := simp)]
/--
theorem `mulEquivOfMulEquiv_eq_map_apply` / 定理 `mulEquivOfMulEquiv_eq_map_apply`

English:
theorem mulEquivOfMulEquiv_eq_map_apply
  statement: {k : LocalizationMap T Q} {j : M ≃* P}
  proof: rfl

@[to_additive]

中文:
定理 mulEquivOfMulEquiv_eq_map_apply
  结论: {k : Localization映射 T Q} {j : M ≃* P}
  证明: rfl

@[to_additive]
-/
theorem mulEquivOfMulEquiv_eq_map_apply {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) (x) :
    f.mulEquivOfMulEquiv k H x =
      f.map (fun y : S => show j.toMonoidHom y in T from H ▸ Set.mem_image_of_mem j y.2) k x := rfl

@[to_additive]
/--
theorem `mulEquivOfMulEquiv_eq_map` / 定理 `mulEquivOfMulEquiv_eq_map`

English:
theorem mulEquivOfMulEquiv_eq_map
  statement: {k : LocalizationMap T Q} {j : M ≃* P}
  proof: rfl

@[to_additive]

中文:
定理 mulEquivOfMulEquiv_eq_map
  结论: {k : Localization映射 T Q} {j : M ≃* P}
  证明: rfl

@[to_additive]
-/
theorem mulEquivOfMulEquiv_eq_map {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) :
    (f.mulEquivOfMulEquiv k H).toMonoidHom =
      f.map (fun y : S => show j.toMonoidHom y in T from H ▸ Set.mem_image_of_mem j y.2) k := rfl

@[to_additive]
/--
theorem `mulEquivOfMulEquiv_eq` / 定理 `mulEquivOfMulEquiv_eq`

English:
theorem mulEquivOfMulEquiv_eq
  statement: {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
  proof: f.map_eq (fun y : S => H ▸ Set.mem_image_of_mem j y.2) _

@[to_additive]

中文:
定理 mulEquivOfMulEquiv_eq
  结论: {k : Localization映射 T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
  证明: f.map_eq (fun y : S => H ▸ Set.mem_image_of_mem j y.2) _

@[to_additive]

Depends on / 依赖: Set.mem_image_of_mem, f.map_eq, map_eq, mem_image_of_mem
-/
theorem mulEquivOfMulEquiv_eq {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
    (x) :
    f.mulEquivOfMulEquiv k H (f x) = k (j x) :=
  f.map_eq (fun y : S => H ▸ Set.mem_image_of_mem j y.2) _

@[to_additive]
/--
theorem `mulEquivOfMulEquiv_mk'` / 定理 `mulEquivOfMulEquiv_mk'`

English:
theorem mulEquivOfMulEquiv_mk'
  statement: {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
  proof: f.map_mk' (fun y : S => H ▸ Set.mem_image_of_mem j y.2) _ _

@[to_additive]

中文:
定理 mulEquivOfMulEquiv_mk'
  结论: {k : Localization映射 T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
  证明: f.map_mk' (fun y : S => H ▸ Set.mem_image_of_mem j y.2) _ _

@[to_additive]

Depends on / 依赖: Set.mem_image_of_mem, f.map_mk, map_mk, mem_image_of_mem
-/
theorem mulEquivOfMulEquiv_mk' {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
    (x y) :
    f.mulEquivOfMulEquiv k H (f.mk' x y) = k.mk' (j x) ⟨j y, H ▸ Set.mem_image_of_mem j y.2⟩ :=
  f.map_mk' (fun y : S => H ▸ Set.mem_image_of_mem j y.2) _ _

@[to_additive]
/--
theorem `of_mulEquivOfMulEquiv_apply` / 定理 `of_mulEquivOfMulEquiv_apply`

English:
theorem of_mulEquivOfMulEquiv_apply
  statement: {k : LocalizationMap T Q} {j : M ≃* P}
  proof: Submonoid.LocalizationMap.ext_iff.1 (f.mulEquivOfLocalizations_right_inv (k.ofMulEquivOfDom H)) x

@[to_additive]

中文:
定理 of_mulEquivOfMulEquiv_apply
  结论: {k : Localization映射 T Q} {j : M ≃* P}
  证明: Submonoid.LocalizationMap.ext_iff.1 (f.mulEquivOfLocalizations_right_inv (k.ofMulEquivOfDom H)) x

@[to_additive]

Depends on / 依赖: LocalizationMap, Submonoid, Submonoid.LocalizationMap.ext_iff, ext_iff, f.mulEquivOfLocalizations_right_inv, k.ofMulEquivOfDom, mulEquivOfLocalizations_right_inv, ofMulEquivOfDom
-/
theorem of_mulEquivOfMulEquiv_apply {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) (x) :
    f.ofMulEquivOfLocalizations (f.mulEquivOfMulEquiv k H) x = k (j x) :=
  Submonoid.LocalizationMap.ext_iff.1 (f.mulEquivOfLocalizations_right_inv (k.ofMulEquivOfDom H)) x

@[to_additive]
/--
theorem `of_mulEquivOfMulEquiv` / 定理 `of_mulEquivOfMulEquiv`

English:
theorem of_mulEquivOfMulEquiv
  given: {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
  proof: MonoidHom.ext f.of_mulEquivOfMulEquiv_apply H

中文:
定理 of_mulEquivOfMulEquiv
  条件: {k : Localization映射 T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
  证明: MonoidHom.ext f.of_mulEquivOfMulEquiv_apply H

Depends on / 依赖: MonoidHom, MonoidHom.ext, f.of_mulEquivOfMulEquiv_apply, of_mulEquivOfMulEquiv_apply
-/
theorem of_mulEquivOfMulEquiv {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T) :
    (f.ofMulEquivOfLocalizations (f.mulEquivOfMulEquiv k H)).toMonoidHom =
      k.toMonoidHom.comp j.toMonoidHom :=
MonoidHom.ext f.of_mulEquivOfMulEquiv_apply H

end LocalizationMap

end Submonoid

namespace Localization

variable (f : Submonoid.LocalizationMap S N)

/-- Given a Localization map `f : M →* N` for a Submonoid `S`, we get an isomorphism between
the Localization of `M` at `S` as a quotient type and `N`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for a Submonoid `S`, we get an isomorphism between
the Localization of `M` at `S` as a quotient type and `N`. -/]
/--
Definition of `mulEquivOfQuotient` / `mulEquivOfQuotient` 的定义

English:
definition mulEquivOfQuotient
  signature: (f : Submonoid.LocalizationMap S N)
  body: (monoidOf S).mulEquivOfLocalizations f

中文:
定义 mulEquivOfQuotient
  签名: (f : 子幺半群.Localization映射 S N)
  定义体: (monoidOf S).mulEquivOfLocalizations f

Depends on / 依赖: monoidOf, mulEquivOfLocalizations
-/
noncomputable def mulEquivOfQuotient (f : Submonoid.LocalizationMap S N) : Localization S ≃* N :=
  (monoidOf S).mulEquivOfLocalizations f

variable {f}

@[to_additive (attr := simp)]
/--
theorem `mulEquivOfQuotient_apply` / 定理 `mulEquivOfQuotient_apply`

English:
theorem mulEquivOfQuotient_apply
  given: (x)
  statement: mulEquivOfQuotient f x = (monoidOf S).lift f.map_units x
  proof: rfl

@[to_additive]

中文:
定理 mulEquivOfQuotient_apply
  条件: (x)
  结论: mulEquivOfQuotient f x = (monoidOf S).lift f.map_units x
  证明: rfl

@[to_additive]
-/
theorem mulEquivOfQuotient_apply (x) : mulEquivOfQuotient f x = (monoidOf S).lift f.map_units x :=
  rfl

@[to_additive]
/--
theorem `mulEquivOfQuotient_mk'` / 定理 `mulEquivOfQuotient_mk'`

English:
theorem mulEquivOfQuotient_mk'
  given: (x y)
  statement: mulEquivOfQuotient f ((monoidOf S).mk' x y) = f.mk' x y
  proof: (monoidOf S).lift_mk' _ _ _

@[to_additive]

中文:
定理 mulEquivOfQuotient_mk'
  条件: (x y)
  结论: mulEquivOfQuotient f ((monoidOf S).mk' x y) = f.mk' x y
  证明: (monoidOf S).lift_mk' _ _ _

@[to_additive]

Depends on / 依赖: lift_mk, monoidOf
-/
theorem mulEquivOfQuotient_mk' (x y) : mulEquivOfQuotient f ((monoidOf S).mk' x y) = f.mk' x y :=
  (monoidOf S).lift_mk' _ _ _

@[to_additive]
/--
theorem `mulEquivOfQuotient_mk` / 定理 `mulEquivOfQuotient_mk`

English:
theorem mulEquivOfQuotient_mk
  given: (x y)
  statement: mulEquivOfQuotient f (mk x y) = f.mk' x y
  proof: by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_mk' _ _

@[to_additive]

中文:
定理 mulEquivOfQuotient_mk
  条件: (x y)
  结论: mulEquivOfQuotient f (mk x y) = f.mk' x y
  证明: by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_mk' _ _

@[to_additive]

Depends on / 依赖: _apply, mk_eq_monoidOf_mk, mulEquivOfQuotient_mk
-/
theorem mulEquivOfQuotient_mk (x y) : mulEquivOfQuotient f (mk x y) = f.mk' x y := by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_mk' _ _

@[to_additive]
/--
theorem `mulEquivOfQuotient_monoidOf` / 定理 `mulEquivOfQuotient_monoidOf`

English:
theorem mulEquivOfQuotient_monoidOf
  given: (x)
  statement: mulEquivOfQuotient f (monoidOf S x) = f x
  proof: by simp

@[to_additive (attr := simp)]

中文:
定理 mulEquivOfQuotient_monoidOf
  条件: (x)
  结论: mulEquivOfQuotient f (monoidOf S x) = f x
  证明: by simp

@[to_additive (attr := simp)]
-/
theorem mulEquivOfQuotient_monoidOf (x) : mulEquivOfQuotient f (monoidOf S x) = f x := by simp

@[to_additive (attr := simp)]
/--
theorem `mulEquivOfQuotient_symm_mk'` / 定理 `mulEquivOfQuotient_symm_mk'`

English:
theorem mulEquivOfQuotient_symm_mk'
  given: (x y)
  proof: f.lift_mk' (monoidOf S).map_units _ _

@[to_additive]

中文:
定理 mulEquivOfQuotient_symm_mk'
  条件: (x y)
  证明: f.lift_mk' (monoidOf S).map_units _ _

@[to_additive]

Depends on / 依赖: f.lift_mk, lift_mk, map_units, monoidOf
-/
theorem mulEquivOfQuotient_symm_mk' (x y) :
    (mulEquivOfQuotient f).symm (f.mk' x y) = (monoidOf S).mk' x y :=
  f.lift_mk' (monoidOf S).map_units _ _

@[to_additive]
/--
theorem `mulEquivOfQuotient_symm_mk` / 定理 `mulEquivOfQuotient_symm_mk`

English:
theorem mulEquivOfQuotient_symm_mk
  given: (x y)
  statement: (mulEquivOfQuotient f).symm (f.mk' x y) = mk x y
  proof: by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_symm_mk' _ _

@[to_additive (attr := simp)]

中文:
定理 mulEquivOfQuotient_symm_mk
  条件: (x y)
  结论: (mulEquivOfQuotient f).symm (f.mk' x y) = mk x y
  证明: by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_symm_mk' _ _

@[to_additive (attr := simp)]

Depends on / 依赖: _apply, mk_eq_monoidOf_mk, mulEquivOfQuotient_symm_mk
-/
theorem mulEquivOfQuotient_symm_mk (x y) : (mulEquivOfQuotient f).symm (f.mk' x y) = mk x y := by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_symm_mk' _ _

@[to_additive (attr := simp)]
/--
theorem `mulEquivOfQuotient_symm_monoidOf` / 定理 `mulEquivOfQuotient_symm_monoidOf`

English:
theorem mulEquivOfQuotient_symm_monoidOf
  given: (x)
  statement: (mulEquivOfQuotient f).symm (f x) = monoidOf S x
  proof: f.lift_eq (monoidOf S).map_units _

中文:
定理 mulEquivOfQuotient_symm_monoidOf
  条件: (x)
  结论: (mulEquivOfQuotient f).symm (f x) = monoidOf S x
  证明: f.lift_eq (monoidOf S).map_units _

Depends on / 依赖: f.lift_eq, lift_eq, map_units, monoidOf
-/
theorem mulEquivOfQuotient_symm_monoidOf (x) : (mulEquivOfQuotient f).symm (f x) = monoidOf S x :=
  f.lift_eq (monoidOf S).map_units _

end Localization

end CommMonoid
