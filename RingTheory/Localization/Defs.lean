/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.Data.Fintype.Prod
public import Mathlib.GroupTheory.MonoidLocalization.Divisibility
public import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.Tactic.Ring

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R` such that `f x = f y`, there exists `c ∈ M` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variable (R S P Q : Type*) [CommRing R] [CommRing S] [CommRing P] [CommRing Q]
variable [Algebra R S] [Algebra P Q] (M : Submonoid R) (T : Submonoid P)
```

## Main definitions

* `IsLocalization (M : Submonoid R) (S : Type*)` is a typeclass expressing that `S` is a
  localization of `R` at `M`, i.e. the canonical map `algebraMap R S : R →+* S` is a
  localization map (satisfying the above properties).
* `IsLocalization.mk' S` is a surjection sending `(x, y) : R × M` to `f x * (f y)⁻¹`
* `IsLocalization.lift` is the ring homomorphism from `S` induced by a homomorphism from `R`
  which maps elements of `M` to invertible elements of the codomain.
* `IsLocalization.map S Q` is the ring homomorphism from `S` to `Q` which maps elements
  of `M` to elements of `T`
* `IsLocalization.ringEquivOfRingEquiv`: if `R` and `P` are isomorphic by an isomorphism
  sending `M` to `T`, then `S` and `Q` are isomorphic

## Main results

* `Localization M S`, a construction of the localization as a quotient type, defined in
  `GroupTheory.MonoidLocalization`, has `CommRing`, `Algebra R` and `IsLocalization M`
  instances if `R` is a ring. `Localization.Away`, `Localization.AtPrime` and `FractionRing`
  are abbreviations for `Localization`s and have their corresponding `IsLocalization` instances

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : LocalizationMap M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `IsLocalization` a predicate on the `algebraMap R S`,
we can ensure the localization map commutes nicely with other `algebraMap`s.

To prove most lemmas about a localization map `algebraMap R S` in this file we invoke the
corresponding proof for the underlying `CommMonoid` localization map
`IsLocalization.toLocalizationMap M S`, which can be found in `GroupTheory.MonoidLocalization`
and the namespace `Submonoid.LocalizationMap`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → Localization M` equals the surjection
`LocalizationMap.mk'` induced by the map `algebraMap : R →+* Localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `LocalizationMap.mk'` induced by any localization map.

The proof that "a `CommRing` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[Field K]` instead of just `[CommRing K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section

assert_not_exists AlgHom Ideal

open Function

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

/--
Definition of `IsLocalization'` / `IsLocalization'` 的定义

English:
class IsLocalization'
  parameters: : Prop extends M.IsLocalizationMap (algebraMap R S)
  extends: M.IsLocalizationMap (algebraMap R S)
  (no additional axioms)

中文:
类 是Localization'
  参数: : 命题 extends M.是Localization映射 (algebraMap R S)
  继承: M.是Localization映射 (algebraMap R S)
  (无附加公理)
-/
class IsLocalization' : Prop extends M.IsLocalizationMap (algebraMap R S)

/--
Definition of `IsLocalization` / `IsLocalization` 的定义

English:
abbreviation IsLocalization
  body: @IsLocalization'

中文:
缩写 是Localization
  定义体: @IsLocalization'

Depends on / 依赖: IsLocalization
-/
abbrev IsLocalization := @IsLocalization'

/--
theorem `isLocalization_iff_isLocalizationMap` / 定理 `isLocalization_iff_isLocalizationMap`

English:
theorem isLocalization_iff_isLocalizationMap
  proof: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

中文:
定理 isLocalization_iff_isLocalizationMap
  证明: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
-/
theorem isLocalization_iff_isLocalizationMap :
    IsLocalization M S ↔ M.IsLocalizationMap (algebraMap R S) :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/--
theorem `isLocalization_iff` / 定理 `isLocalization_iff`

English:
theorem isLocalization_iff
  statement: IsLocalization M S ↔
  proof: by
  rw [isLocalization_iff_isLocalizationMap]; rw [Submonoid.isLocalizationMap_iff]

中文:
定理 isLocalization_iff
  结论: 是Localization M S ↔
  证明: by
  rw [isLocalization_iff_isLocalizationMap]; rw [Submonoid.isLocalizationMap_iff]

Depends on / 依赖: Submonoid, Submonoid.isLocalizationMap_iff, isLocalizationMap_iff, isLocalization_iff_isLocalizationMap
-/
theorem isLocalization_iff : IsLocalization M S ↔
    (forall y : M, IsUnit (algebraMap R S y)) ∧
    (forall z : S, exists x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1) ∧
    forall {x y : R}, algebraMap R S x = algebraMap R S y -> exists c : M, c * x = c * y := by
  rw [isLocalization_iff_isLocalizationMap]; rw [Submonoid.isLocalizationMap_iff]

variable {M}

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

section

/--
theorem `map_units` / 定理 `map_units`

English:
theorem map_units
  statement: forall y : M, IsUnit (algebraMap R S y)
  proof: IsLocalization'.toIsLocalizationMap.map_units

中文:
定理 map_units
  结论: 对任意 y : M, 是单位 (algebraMap R S y)
  证明: IsLocalization'.toIsLocalizationMap.map_units

Depends on / 依赖: IsLocalization, map_units, toIsLocalizationMap, toIsLocalizationMap.map_units
-/
theorem map_units : forall y : M, IsUnit (algebraMap R S y) :=
  IsLocalization'.toIsLocalizationMap.map_units

variable (M) {S}
/--
theorem `surj` / 定理 `surj`

English:
theorem surj
  statement: forall z : S, exists x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1
  proof: IsLocalization'.toIsLocalizationMap.surj

中文:
定理 surj
  结论: 对任意 z : S, 存在 x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1
  证明: IsLocalization'.toIsLocalizationMap.surj

Depends on / 依赖: IsLocalization, toIsLocalizationMap, toIsLocalizationMap.surj
-/
theorem surj : forall z : S, exists x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1 :=
  IsLocalization'.toIsLocalizationMap.surj

variable {M} in
/--
theorem `exists_of_eq` / 定理 `exists_of_eq`

English:
theorem exists_of_eq
  given: {x y : R}
  statement: algebraMap R S x = algebraMap R S y -> exists c : M, c * x = c * y
  proof: IsLocalization'.toIsLocalizationMap.exists_of_eq

中文:
定理 存在_of_eq
  条件: {x y : R}
  结论: algebraMap R S x = algebraMap R S y -> 存在 c : M, c * x = c * y
  证明: IsLocalization'.toIsLocalizationMap.exists_of_eq

Depends on / 依赖: IsLocalization, exists_of_eq, toIsLocalizationMap, toIsLocalizationMap.exists_of_eq
-/
theorem exists_of_eq {x y : R} : algebraMap R S x = algebraMap R S y -> exists c : M, c * x = c * y :=
  IsLocalization'.toIsLocalizationMap.exists_of_eq

variable (S)

variable {M} in
/--
theorem `smul_bijective` / 定理 `smul_bijective`

English:
theorem smul_bijective
  given: (m : M)
  statement: Bijective fun s : S => m • s
  proof: by
  simpa only [Submonoid.smul_def, Algebra.smul_def] using! (map_units S m).smul_bijective

中文:
定理 smul_bijective
  条件: (m : M)
  结论: 双射 fun s : S => m • s
  证明: by
  simpa only [Submonoid.smul_def, Algebra.smul_def] using! (map_units S m).smul_bijective

Depends on / 依赖: Algebra, Algebra.smul_def, Submonoid, Submonoid.smul_def, map_units, smul_bijective, smul_def
-/
theorem smul_bijective (m : M) : Bijective fun s : S => m • s := by
  simpa only [Submonoid.smul_def, Algebra.smul_def] using! (map_units S m).smul_bijective

/--
Definition of `toLocalizationMap` / `toLocalizationMap` 的定义

English:
abbreviation toLocalizationMap
  signature: : M.LocalizationMap S where
  body: algebraMap R S
  toFun := algebraMap R S
  isLocalizationMap := IsLocalization'.toIsLocalizationMap

@[simp]

中文:
缩写 toLocalizationMap
  签名: : M.Localization映射 S where
  定义体: algebraMap R S
  toFun := algebraMap R S
  isLocalizationMap := IsLocalization'.toIsLocalizationMap

@[simp]

Depends on / 依赖: algebraMap
-/
abbrev toLocalizationMap : M.LocalizationMap S where
  __ := algebraMap R S
  toFun := algebraMap R S
  isLocalizationMap := IsLocalization'.toIsLocalizationMap

@[simp]
/--
lemma `toLocalizationMap_toMonoidHom` / 引理 `toLocalizationMap_toMonoidHom`

English:
lemma toLocalizationMap_toMonoidHom
  proof: rfl

中文:
引理 toLocalizationMap_toMonoidHom
  证明: rfl
-/
lemma toLocalizationMap_toMonoidHom :
    (toLocalizationMap M S).toMonoidHom = (.ofClass (algebraMap R S) : R ->*₀ S) := rfl

/--
lemma `coe_toLocalizationMap` / 引理 `coe_toLocalizationMap`

English:
lemma coe_toLocalizationMap
  statement: ⇑(toLocalizationMap M S) = algebraMap R S
  proof: rfl

中文:
引理 coe_toLocalizationMap
  结论: ⇑(toLocalizationMap M S) = algebraMap R S
  证明: rfl
-/
@[simp] lemma coe_toLocalizationMap : ⇑(toLocalizationMap M S) = algebraMap R S := rfl

/--
lemma `toLocalizationMap_apply` / 引理 `toLocalizationMap_apply`

English:
lemma toLocalizationMap_apply
  given: (x)
  statement: toLocalizationMap M S x = algebraMap R S x
  proof: rfl

中文:
引理 toLocalizationMap_apply
  条件: (x)
  结论: toLocalizationMap M S x = algebraMap R S x
  证明: rfl
-/
lemma toLocalizationMap_apply (x) : toLocalizationMap M S x = algebraMap R S x := rfl

/--
theorem `surj₂` / 定理 `surj₂`

English:
theorem surj₂
  statement: forall z w : S, exists z' w' : R, exists d : M,
  proof: (toLocalizationMap M S).surj₂

中文:
定理 surj₂
  结论: 对任意 z w : S, 存在 z' w' : R, 存在 d : M,
  证明: (toLocalizationMap M S).surj₂

Depends on / 依赖: toLocalizationMap
-/
theorem surj₂ : forall z w : S, exists z' w' : R, exists d : M,
    (z * algebraMap R S d = algebraMap R S z') ∧ (w * algebraMap R S d = algebraMap R S w') :=
  (toLocalizationMap M S).surj₂

/--
theorem `eq_iff_exists` / 定理 `eq_iff_exists`

English:
theorem eq_iff_exists
  given: {x y}
  statement: algebraMap R S x = algebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
  proof: (toLocalizationMap M S).eq_iff_exists

中文:
定理 eq_iff_存在
  条件: {x y}
  结论: algebraMap R S x = algebraMap R S y ↔ 存在 c : M, ↑c * x = ↑c * y
  证明: (toLocalizationMap M S).eq_iff_exists

Depends on / 依赖: eq_iff_exists, toLocalizationMap
-/
theorem eq_iff_exists {x y} : algebraMap R S x = algebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y :=
  (toLocalizationMap M S).eq_iff_exists

variable {S}

/--
theorem `injective_iff_isRegular` / 定理 `injective_iff_isRegular`

English:
theorem injective_iff_isRegular
  statement: Injective (algebraMap R S) ↔ forall c : M, IsRegular (c : R)
  proof: (toLocalizationMap M S).injective_iff.trans .symm Subtype.forall

中文:
定理 injective_iff_isRegular
  结论: 单射 (algebraMap R S) ↔ 对任意 c : M, 是正则 (c : R)
  证明: (toLocalizationMap M S).injective_iff.trans .symm Subtype.forall

Depends on / 依赖: Subtype, Subtype.forall, injective_iff, injective_iff.trans, toLocalizationMap
-/
theorem injective_iff_isRegular : Injective (algebraMap R S) ↔ forall c : M, IsRegular (c : R) :=
(toLocalizationMap M S).injective_iff.trans .symm Subtype.forall

/--
theorem `of_le` / 定理 `of_le`

English:
theorem of_le
  given: (N : Submonoid R) (h₁ : M <= N) (h₂ : forall r in N, IsUnit (algebraMap R S r))
  proof: h₂ r r.2
  surj s :=
    have ⟨⟨x, y, hy⟩, H⟩ := IsLocalization.surj M s
    ⟨⟨x, y, h₁ hy⟩, H⟩
  exists_of_eq {x y} := by
    rw [IsLocalization.eq_iff_exists M]
    rintro ⟨c, hc⟩
    exact ⟨⟨c, h₁ c.2⟩, hc⟩

中文:
定理 of_le
  条件: (N : 子幺半群 R) (h₁ : M <= N) (h₂ : 对任意 r in N, 是单位 (algebraMap R S r))
  证明: h₂ r r.2
  surj s :=
    have ⟨⟨x, y, hy⟩, H⟩ := IsLocalization.surj M s
    ⟨⟨x, y, h₁ hy⟩, H⟩
  exists_of_eq {x y} := by
    rw [IsLocalization.eq_iff_exists M]
    rintro ⟨c, hc⟩
    exact ⟨⟨c, h₁ c.2⟩, hc⟩
-/
theorem of_le (N : Submonoid R) (h₁ : M <= N) (h₂ : forall r in N, IsUnit (algebraMap R S r)) :
    IsLocalization N S where
  map_units r := h₂ r r.2
  surj s :=
    have ⟨⟨x, y, hy⟩, H⟩ := IsLocalization.surj M s
    ⟨⟨x, y, h₁ hy⟩, H⟩
  exists_of_eq {x y} := by
    rw [IsLocalization.eq_iff_exists M]
    rintro ⟨c, hc⟩
    exact ⟨⟨c, h₁ c.2⟩, hc⟩

/--
theorem `of_le_of_exists_dvd` / 定理 `of_le_of_exists_dvd`

English:
theorem of_le_of_exists_dvd
  given: (N : Submonoid R) (h₁ : M <= N) (h₂ : forall n in N, exists m in M, n ∣ m)
  proof: of_le M N h₁ fun n hn => have ⟨m, hm, dvd⟩ := h₂ n hn
    isUnit_of_dvd_unit (map_dvd _ dvd) (map_units S ⟨m, hm⟩)

中文:
定理 of_le_of_存在_dvd
  条件: (N : 子幺半群 R) (h₁ : M <= N) (h₂ : 对任意 n in N, 存在 m in M, n ∣ m)
  证明: of_le M N h₁ fun n hn => have ⟨m, hm, dvd⟩ := h₂ n hn
    isUnit_of_dvd_unit (map_dvd _ dvd) (map_units S ⟨m, hm⟩)

Depends on / 依赖: isUnit_of_dvd_unit, map_dvd, map_units, of_le
-/
theorem of_le_of_exists_dvd (N : Submonoid R) (h₁ : M <= N) (h₂ : forall n in N, exists m in M, n ∣ m) :
    IsLocalization N S :=
  of_le M N h₁ fun n hn => have ⟨m, hm, dvd⟩ := h₂ n hn
    isUnit_of_dvd_unit (map_dvd _ dvd) (map_units S ⟨m, hm⟩)

/--
theorem `algebraMap_isUnit_iff` / 定理 `algebraMap_isUnit_iff`

English:
theorem algebraMap_isUnit_iff
  given: {x : R}
  statement: IsUnit (algebraMap R S x) ↔ exists m in M, x ∣ m
  proof: (toLocalizationMap M S).map_isUnit_iff

中文:
定理 algebraMap_isUnit_iff
  条件: {x : R}
  结论: 是单位 (algebraMap R S x) ↔ 存在 m in M, x ∣ m
  证明: (toLocalizationMap M S).map_isUnit_iff

Depends on / 依赖: map_isUnit_iff, toLocalizationMap
-/
theorem algebraMap_isUnit_iff {x : R} : IsUnit (algebraMap R S x) ↔ exists m in M, x ∣ m :=
  (toLocalizationMap M S).map_isUnit_iff

end

variable (M) {S}

/--
Definition of `sec` / `sec` 的定义

English:
definition sec
  signature: (z : S)
  body: Classical.choose IsLocalization.surj _ z

@[simp]

中文:
定义 sec
  签名: (z : S)
  定义体: Classical.choose IsLocalization.surj _ z

@[simp]

Depends on / 依赖: Classical, Classical.choose, IsLocalization, IsLocalization.surj
-/
noncomputable def sec (z : S) : R × M :=
Classical.choose IsLocalization.surj _ z

@[simp]
/--
theorem `toLocalizationMap_sec` / 定理 `toLocalizationMap_sec`

English:
theorem toLocalizationMap_sec
  statement: (toLocalizationMap M S).sec = sec M
  proof: rfl

中文:
定理 toLocalizationMap_sec
  结论: (toLocalizationMap M S).sec = sec M
  证明: rfl
-/
theorem toLocalizationMap_sec : (toLocalizationMap M S).sec = sec M :=
  rfl

/--
theorem `sec_spec` / 定理 `sec_spec`

English:
theorem sec_spec
  given: (z : S)
  proof: Classical.choose_spec IsLocalization.surj _ z

中文:
定理 sec_spec
  条件: (z : S)
  证明: Classical.choose_spec IsLocalization.surj _ z

Depends on / 依赖: Classical, Classical.choose_spec, IsLocalization, IsLocalization.surj, choose_spec
-/
theorem sec_spec (z : S) :
    z * algebraMap R S (IsLocalization.sec M z).2 = algebraMap R S (IsLocalization.sec M z).1 :=
Classical.choose_spec IsLocalization.surj _ z

/--
theorem `sec_spec'` / 定理 `sec_spec'`

English:
theorem sec_spec'
  given: (z : S)
  proof: by
  rw [mul_comm]; rw [sec_spec]

中文:
定理 sec_spec'
  条件: (z : S)
  证明: by
  rw [mul_comm]; rw [sec_spec]

Depends on / 依赖: mul_comm, sec_spec
-/
theorem sec_spec' (z : S) :
    algebraMap R S (IsLocalization.sec M z).1 = algebraMap R S (IsLocalization.sec M z).2 * z := by
  rw [mul_comm]; rw [sec_spec]

variable {M}

/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: (h : 0 in M)
  statement: Subsingleton S
  proof: (toLocalizationMap M S).subsingleton h

中文:
定理 subsingleton
  条件: (h : 0 in M)
  结论: 子单例 S
  证明: (toLocalizationMap M S).subsingleton h

Depends on / 依赖: subsingleton, toLocalizationMap
-/
theorem subsingleton (h : 0 in M) : Subsingleton S := (toLocalizationMap M S).subsingleton h

/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  statement: Subsingleton S ↔ 0 in M
  proof: (toLocalizationMap M S).subsingleton_iff

中文:
定理 subsingleton_iff
  结论: 子单例 S ↔ 0 in M
  证明: (toLocalizationMap M S).subsingleton_iff
-/
protected theorem subsingleton_iff : Subsingleton S ↔ 0 in M :=
  (toLocalizationMap M S).subsingleton_iff

/--
theorem `map_right_cancel` / 定理 `map_right_cancel`

English:
theorem map_right_cancel
  given: {x y} {c : M} (h : algebraMap R S (c * x) = algebraMap R S (c * y))
  proof: (toLocalizationMap M S).map_right_cancel h

中文:
定理 map_right_cancel
  条件: {x y} {c : M} (h : algebraMap R S (c * x) = algebraMap R S (c * y))
  证明: (toLocalizationMap M S).map_right_cancel h

Depends on / 依赖: map_right_cancel, toLocalizationMap
-/
theorem map_right_cancel {x y} {c : M} (h : algebraMap R S (c * x) = algebraMap R S (c * y)) :
    algebraMap R S x = algebraMap R S y :=
  (toLocalizationMap M S).map_right_cancel h

/--
theorem `map_left_cancel` / 定理 `map_left_cancel`

English:
theorem map_left_cancel
  given: {x y} {c : M} (h : algebraMap R S (x * c) = algebraMap R S (y * c))
  proof: (toLocalizationMap M S).map_left_cancel h

中文:
定理 map_left_cancel
  条件: {x y} {c : M} (h : algebraMap R S (x * c) = algebraMap R S (y * c))
  证明: (toLocalizationMap M S).map_left_cancel h

Depends on / 依赖: map_left_cancel, toLocalizationMap
-/
theorem map_left_cancel {x y} {c : M} (h : algebraMap R S (x * c) = algebraMap R S (y * c)) :
    algebraMap R S x = algebraMap R S y :=
  (toLocalizationMap M S).map_left_cancel h

/--
theorem `eq_zero_of_fst_eq_zero` / 定理 `eq_zero_of_fst_eq_zero`

English:
theorem eq_zero_of_fst_eq_zero
  statement: {z x} {y : M} (h : z * algebraMap R S y = algebraMap R S x)
  proof: by
  rw [hx]; rw [(algebraMap R S).map_zero] at h
  exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units S y)).1 h

中文:
定理 eq_zero_of_fst_eq_zero
  结论: {z x} {y : M} (h : z * algebraMap R S y = algebraMap R S x)
  证明: by
  rw [hx]; rw [(algebraMap R S).map_zero] at h
  exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units S y)).1 h

Depends on / 依赖: IsLocalization, IsLocalization.map_units, IsUnit, IsUnit.mul_left_eq_zero, algebraMap, map_units, map_zero, mul_left_eq_zero
-/
theorem eq_zero_of_fst_eq_zero {z x} {y : M} (h : z * algebraMap R S y = algebraMap R S x)
    (hx : x = 0) : z = 0 := by
  rw [hx]; rw [(algebraMap R S).map_zero] at h
  exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units S y)).1 h

variable (M S)

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: (r : R)
  statement: algebraMap R S r = 0 ↔ exists m : M, ↑m * r = 0
  proof: (toLocalizationMap M S).map_eq_zero_iff

中文:
定理 map_eq_zero_iff
  条件: (r : R)
  结论: algebraMap R S r = 0 ↔ 存在 m : M, ↑m * r = 0
  证明: (toLocalizationMap M S).map_eq_zero_iff

Depends on / 依赖: map_eq_zero_iff, toLocalizationMap
-/
theorem map_eq_zero_iff (r : R) : algebraMap R S r = 0 ↔ exists m : M, ↑m * r = 0 :=
  (toLocalizationMap M S).map_eq_zero_iff

variable {M}

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (x : R) (y : M)
  body: (toLocalizationMap M S).mk' x y

@[simp]

中文:
定义 mk'
  签名: (x : R) (y : M)
  定义体: (toLocalizationMap M S).mk' x y

@[simp]
-/
noncomputable def mk' (x : R) (y : M) : S :=
  (toLocalizationMap M S).mk' x y

@[simp]
/--
theorem `mk'_sec` / 定理 `mk'_sec`

English:
theorem mk'_sec
  given: (z : S)
  statement: mk' S (IsLocalization.sec M z).1 (IsLocalization.sec M z).2 = z
  proof: (toLocalizationMap M S).mk'_sec _

中文:
定理 mk'_sec
  条件: (z : S)
  结论: mk' S (是Localization.sec M z).1 (是Localization.sec M z).2 = z
  证明: (toLocalizationMap M S).mk'_sec _
-/
theorem mk'_sec (z : S) : mk' S (IsLocalization.sec M z).1 (IsLocalization.sec M z).2 = z :=
  (toLocalizationMap M S).mk'_sec _

/--
theorem `mk'_mul` / 定理 `mk'_mul`

English:
theorem mk'_mul
  given: (x₁ x₂ : R) (y₁ y₂ : M)
  statement: mk' S (x₁ * x₂) (y₁ * y₂) = mk' S x₁ y₁ * mk' S x₂ y₂
  proof: (toLocalizationMap M S).mk'_mul _ _ _ _

中文:
定理 mk'_mul
  条件: (x₁ x₂ : R) (y₁ y₂ : M)
  结论: mk' S (x₁ * x₂) (y₁ * y₂) = mk' S x₁ y₁ * mk' S x₂ y₂
  证明: (toLocalizationMap M S).mk'_mul _ _ _ _
-/
theorem mk'_mul (x₁ x₂ : R) (y₁ y₂ : M) : mk' S (x₁ * x₂) (y₁ * y₂) = mk' S x₁ y₁ * mk' S x₂ y₂ :=
  (toLocalizationMap M S).mk'_mul _ _ _ _

/--
theorem `mk'_one` / 定理 `mk'_one`

English:
theorem mk'_one
  given: (x)
  statement: mk' S x (1 : M) = algebraMap R S x
  proof: (toLocalizationMap M S).mk'_one _

@[simp]

中文:
定理 mk'_one
  条件: (x)
  结论: mk' S x (1 : M) = algebraMap R S x
  证明: (toLocalizationMap M S).mk'_one _

@[simp]
-/
theorem mk'_one (x) : mk' S x (1 : M) = algebraMap R S x :=
  (toLocalizationMap M S).mk'_one _

@[simp]
/--
theorem `mk'_spec` / 定理 `mk'_spec`

English:
theorem mk'_spec
  given: (x) (y : M)
  statement: mk' S x y * algebraMap R S y = algebraMap R S x
  proof: (toLocalizationMap M S).mk'_spec _ _

@[simp]

中文:
定理 mk'_spec
  条件: (x) (y : M)
  结论: mk' S x y * algebraMap R S y = algebraMap R S x
  证明: (toLocalizationMap M S).mk'_spec _ _

@[simp]
-/
theorem mk'_spec (x) (y : M) : mk' S x y * algebraMap R S y = algebraMap R S x :=
  (toLocalizationMap M S).mk'_spec _ _

@[simp]
/--
theorem `mk'_spec'` / 定理 `mk'_spec'`

English:
theorem mk'_spec'
  given: (x) (y : M)
  statement: algebraMap R S y * mk' S x y = algebraMap R S x
  proof: (toLocalizationMap M S).mk'_spec' _ _

@[simp]

中文:
定理 mk'_spec'
  条件: (x) (y : M)
  结论: algebraMap R S y * mk' S x y = algebraMap R S x
  证明: (toLocalizationMap M S).mk'_spec' _ _

@[simp]
-/
theorem mk'_spec' (x) (y : M) : algebraMap R S y * mk' S x y = algebraMap R S x :=
  (toLocalizationMap M S).mk'_spec' _ _

@[simp]
/--
theorem `mk'_spec_mk` / 定理 `mk'_spec_mk`

English:
theorem mk'_spec_mk
  given: (x) (y : R) (hy : y in M)
  proof: mk'_spec S x ⟨y, hy⟩

@[simp]

中文:
定理 mk'_spec_mk
  条件: (x) (y : R) (hy : y in M)
  证明: mk'_spec S x ⟨y, hy⟩

@[simp]
-/
theorem mk'_spec_mk (x) (y : R) (hy : y in M) :
    mk' S x ⟨y, hy⟩ * algebraMap R S y = algebraMap R S x :=
  mk'_spec S x ⟨y, hy⟩

@[simp]
/--
theorem `mk'_spec'_mk` / 定理 `mk'_spec'_mk`

English:
theorem mk'_spec'_mk
  given: (x) (y : R) (hy : y in M)
  proof: mk'_spec' S x ⟨y, hy⟩

中文:
定理 mk'_spec'_mk
  条件: (x) (y : R) (hy : y in M)
  证明: mk'_spec' S x ⟨y, hy⟩
-/
theorem mk'_spec'_mk (x) (y : R) (hy : y in M) :
    algebraMap R S y * mk' S x ⟨y, hy⟩ = algebraMap R S x :=
  mk'_spec' S x ⟨y, hy⟩

variable {S}

/--
theorem `eq_mk'_iff_mul_eq` / 定理 `eq_mk'_iff_mul_eq`

English:
theorem eq_mk'_iff_mul_eq
  given: {x} {y : M} {z}
  proof: (toLocalizationMap M S).eq_mk'_iff_mul_eq

中文:
定理 eq_mk'_iff_mul_eq
  条件: {x} {y : M} {z}
  证明: (toLocalizationMap M S).eq_mk'_iff_mul_eq

Depends on / 依赖: _iff_mul_eq, eq_mk, toLocalizationMap
-/
theorem eq_mk'_iff_mul_eq {x} {y : M} {z} :
    z = mk' S x y ↔ z * algebraMap R S y = algebraMap R S x :=
  (toLocalizationMap M S).eq_mk'_iff_mul_eq

/--
theorem `eq_mk'_of_mul_eq` / 定理 `eq_mk'_of_mul_eq`

English:
theorem eq_mk'_of_mul_eq
  given: {x : R} {y : M} {z : R} (h : z * y = x)
  statement: (algebraMap R S) z = mk' S x y
  proof: eq_mk'_iff_mul_eq.mpr (by rw [← h, map_mul])

中文:
定理 eq_mk'_of_mul_eq
  条件: {x : R} {y : M} {z : R} (h : z * y = x)
  结论: (algebraMap R S) z = mk' S x y
  证明: eq_mk'_iff_mul_eq.mpr (by rw [← h, map_mul])
-/
theorem eq_mk'_of_mul_eq {x : R} {y : M} {z : R} (h : z * y = x) : (algebraMap R S) z = mk' S x y :=
  eq_mk'_iff_mul_eq.mpr (by rw [← h, map_mul])

/--
theorem `mk'_eq_iff_eq_mul` / 定理 `mk'_eq_iff_eq_mul`

English:
theorem mk'_eq_iff_eq_mul
  given: {x} {y : M} {z}
  proof: (toLocalizationMap M S).mk'_eq_iff_eq_mul

中文:
定理 mk'_eq_iff_eq_mul
  条件: {x} {y : M} {z}
  证明: (toLocalizationMap M S).mk'_eq_iff_eq_mul
-/
theorem mk'_eq_iff_eq_mul {x} {y : M} {z} :
    mk' S x y = z ↔ algebraMap R S x = z * algebraMap R S y :=
  (toLocalizationMap M S).mk'_eq_iff_eq_mul

/--
theorem `mk'_add_eq_iff_add_mul_eq_mul` / 定理 `mk'_add_eq_iff_add_mul_eq_mul`

English:
theorem mk'_add_eq_iff_add_mul_eq_mul
  given: {x} {y : M} {z₁ z₂}
  proof: by
  rw [← mk'_spec S x y]; rw [← IsUnit.mul_left_inj (IsLocalization.map_units S y)]; rw [right_distrib]

中文:
定理 mk'_add_eq_iff_add_mul_eq_mul
  条件: {x} {y : M} {z₁ z₂}
  证明: by
  rw [← mk'_spec S x y]; rw [← IsUnit.mul_left_inj (IsLocalization.map_units S y)]; rw [right_distrib]
-/
theorem mk'_add_eq_iff_add_mul_eq_mul {x} {y : M} {z₁ z₂} :
    mk' S x y + z₁ = z₂ ↔ algebraMap R S x + z₁ * algebraMap R S y = z₂ * algebraMap R S y := by
  rw [← mk'_spec S x y]; rw [← IsUnit.mul_left_inj (IsLocalization.map_units S y)]; rw [right_distrib]

/--
theorem `mk'_pow` / 定理 `mk'_pow`

English:
theorem mk'_pow
  given: (x : R) (y : M) (n : Nat)
  statement: mk' S (x ^ n) (y ^ n) = mk' S x y ^ n
  proof: by
  simp_rw [IsLocalization.mk'_eq_iff_eq_mul, SubmonoidClass.coe_pow, map_pow, ← mul_pow]
  simp

中文:
定理 mk'_pow
  条件: (x : R) (y : M) (n : 自然数)
  结论: mk' S (x ^ n) (y ^ n) = mk' S x y ^ n
  证明: by
  simp_rw [IsLocalization.mk'_eq_iff_eq_mul, SubmonoidClass.coe_pow, map_pow, ← mul_pow]
  simp
-/
theorem mk'_pow (x : R) (y : M) (n : Nat) : mk' S (x ^ n) (y ^ n) = mk' S x y ^ n := by
  simp_rw [IsLocalization.mk'_eq_iff_eq_mul, SubmonoidClass.coe_pow, map_pow, ← mul_pow]
  simp

variable (M)

/--
theorem `mk'_surjective` / 定理 `mk'_surjective`

English:
theorem mk'_surjective
  statement: Surjective fun ((r, m) : R × M) => mk' S r m
  proof: fun z =>
  let ⟨r, hr⟩ := IsLocalization.surj _ z
  ⟨r, (eq_mk'_iff_mul_eq.2 hr).symm⟩

中文:
定理 mk'_surjective
  结论: 满射 fun ((r, m) : R × M) => mk' S r m
  证明: fun z =>
  let ⟨r, hr⟩ := IsLocalization.surj _ z
  ⟨r, (eq_mk'_iff_mul_eq.2 hr).symm⟩
-/
theorem mk'_surjective : Surjective fun ((r, m) : R × M) => mk' S r m := fun z =>
  let ⟨r, hr⟩ := IsLocalization.surj _ z
  ⟨r, (eq_mk'_iff_mul_eq.2 hr).symm⟩

/--
theorem `exists_mk'_eq` / 定理 `exists_mk'_eq`

English:
theorem exists_mk'_eq
  given: (z : S)
  statement: exists (x : R) (y : M), mk' S x y = z
  proof: let ⟨⟨r, m⟩, hz⟩ := mk'_surjective M z; ⟨r, m, hz⟩

中文:
定理 存在_mk'_eq
  条件: (z : S)
  结论: 存在 (x : R) (y : M), mk' S x y = z
  证明: let ⟨⟨r, m⟩, hz⟩ := mk'_surjective M z; ⟨r, m, hz⟩

Depends on / 依赖: _surjective
-/
theorem exists_mk'_eq (z : S) : exists (x : R) (y : M), mk' S x y = z :=
  let ⟨⟨r, m⟩, hz⟩ := mk'_surjective M z; ⟨r, m, hz⟩

variable (S) in
/-- The localization of a `Fintype` is a `Fintype`. Cannot be an instance. -/
@[instance_reducible]
/--
Definition of `fintype'` / `fintype'` 的定义

English:
definition fintype'
  signature: [Fintype R]
  body: have := Classical.propDecidable
.ofSurjective (Function.uncurry <| IsLocalization.mk' S) mk'_surjective M

中文:
定义 fintype'
  签名: [有限类型 R]
  定义体: have := Classical.propDecidable
.ofSurjective (Function.uncurry <| IsLocalization.mk' S) mk'_surjective M

Depends on / 依赖: Classical, Classical.propDecidable, Function, Function.uncurry, IsLocalization, IsLocalization.mk, _surjective, ofSurjective, propDecidable, uncurry
-/
noncomputable def fintype' [Fintype R] : Fintype S :=
  have := Classical.propDecidable
.ofSurjective (Function.uncurry <| IsLocalization.mk' S) mk'_surjective M

variable {M}

/-- Localizing at a submonoid with 0 inside it leads to the trivial ring. -/
@[instance_reducible]
/--
Definition of `uniqueOfZeroMem` / `uniqueOfZeroMem` 的定义

English:
definition uniqueOfZeroMem
  signature: (h : (0 : R) in M)
  body: uniqueOfZeroEqOne by simpa using IsLocalization.map_units S ⟨0, h⟩

中文:
定义 uniqueOfZeroMem
  签名: (h : (0 : R) in M)
  定义体: uniqueOfZeroEqOne by simpa using IsLocalization.map_units S ⟨0, h⟩

Depends on / 依赖: IsLocalization, IsLocalization.map_units, map_units, uniqueOfZeroEqOne
-/
def uniqueOfZeroMem (h : (0 : R) in M) : Unique S :=
uniqueOfZeroEqOne by simpa using IsLocalization.map_units S ⟨0, h⟩

/--
theorem `mk'_eq_iff_eq` / 定理 `mk'_eq_iff_eq`

English:
theorem mk'_eq_iff_eq
  given: {x₁ x₂} {y₁ y₂ : M}
  proof: (toLocalizationMap M S).mk'_eq_iff_eq

中文:
定理 mk'_eq_iff_eq
  条件: {x₁ x₂} {y₁ y₂ : M}
  证明: (toLocalizationMap M S).mk'_eq_iff_eq
-/
theorem mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (y₂ * x₁) = algebraMap R S (y₁ * x₂) :=
  (toLocalizationMap M S).mk'_eq_iff_eq

/--
theorem `mk'_eq_iff_eq'` / 定理 `mk'_eq_iff_eq'`

English:
theorem mk'_eq_iff_eq'
  given: {x₁ x₂} {y₁ y₂ : M}
  proof: (toLocalizationMap M S).mk'_eq_iff_eq'

中文:
定理 mk'_eq_iff_eq'
  条件: {x₁ x₂} {y₁ y₂ : M}
  证明: (toLocalizationMap M S).mk'_eq_iff_eq'
-/
theorem mk'_eq_iff_eq' {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (x₁ * y₂) = algebraMap R S (x₂ * y₁) :=
  (toLocalizationMap M S).mk'_eq_iff_eq'

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {a₁ b₁} {a₂ b₂ : M}
  proof: (toLocalizationMap M S).eq

中文:
定理 eq
  条件: {a₁ b₁} {a₂ b₂ : M}
  证明: (toLocalizationMap M S).eq
-/
protected theorem eq {a₁ b₁} {a₂ b₂ : M} :
    mk' S a₁ a₂ = mk' S b₁ b₂ ↔ exists c : M, ↑c * (↑b₂ * a₁) = c * (a₂ * b₁) :=
  (toLocalizationMap M S).eq

/--
theorem `mk'_eq_zero_iff` / 定理 `mk'_eq_zero_iff`

English:
theorem mk'_eq_zero_iff
  given: (x : R) (s : M)
  statement: mk' S x s = 0 ↔ exists m : M, ↑m * x = 0
  proof: (toLocalizationMap M S).mk'_eq_zero_iff x s

@[simp]

中文:
定理 mk'_eq_zero_iff
  条件: (x : R) (s : M)
  结论: mk' S x s = 0 ↔ 存在 m : M, ↑m * x = 0
  证明: (toLocalizationMap M S).mk'_eq_zero_iff x s

@[simp]
-/
theorem mk'_eq_zero_iff (x : R) (s : M) : mk' S x s = 0 ↔ exists m : M, ↑m * x = 0 :=
  (toLocalizationMap M S).mk'_eq_zero_iff x s

@[simp]
/--
theorem `mk'_zero` / 定理 `mk'_zero`

English:
theorem mk'_zero
  given: (s : M)
  statement: IsLocalization.mk' S 0 s = 0
  proof: (toLocalizationMap M S).mk'_zero s

中文:
定理 mk'_zero
  条件: (s : M)
  结论: 是Localization.mk' S 0 s = 0
  证明: (toLocalizationMap M S).mk'_zero s
-/
theorem mk'_zero (s : M) : IsLocalization.mk' S 0 s = 0 :=
  (toLocalizationMap M S).mk'_zero s

/--
theorem `ne_zero_of_mk'_ne_zero` / 定理 `ne_zero_of_mk'_ne_zero`

English:
theorem ne_zero_of_mk'_ne_zero
  given: {x : R} {y : M} (hxy : IsLocalization.mk' S x y != 0)
  statement: x != 0
  proof: by
  rintro rfl
  exact hxy (IsLocalization.mk'_zero _)

中文:
定理 ne_zero_of_mk'_ne_zero
  条件: {x : R} {y : M} (hxy : 是Localization.mk' S x y != 0)
  结论: x != 0
  证明: by
  rintro rfl
  exact hxy (IsLocalization.mk'_zero _)

Depends on / 依赖: IsLocalization, IsLocalization.mk, _zero, e.symm
-/
theorem ne_zero_of_mk'_ne_zero {x : R} {y : M} (hxy : IsLocalization.mk' S x y != 0) : x != 0 := by
  rintro rfl
  exact hxy (IsLocalization.mk'_zero _)

/--
lemma `isRegular_mk'` / 引理 `isRegular_mk'`

English:
lemma isRegular_mk'
  given: (hM : forall m in M, IsRegular m) {r : R} {m : M}
  proof: by
  have (n : M) (x y : R) : n * x = n * y ↔ x = y := (hM _ n.2).1.eq_iff
  simp +contextual only [← isLeftRegular_iff_isRegular, IsLeftRegular, Function.Injective,
    (mk'_surjective M).forall, ← mk'_mul, Prod.forall, Subtype.forall, IsLocalization.eq,
    Submonoid.coe_mul, this, exists_const, m

中文:
引理 isRegular_mk'
  条件: (hM : 对任意 m in M, 是正则 m) {r : R} {m : M}
  证明: by
  have (n : M) (x y : R) : n * x = n * y ↔ x = y := (hM _ n.2).1.eq_iff
  simp +contextual only [← isLeftRegular_iff_isRegular, IsLeftRegular, Function.Injective,
    (mk'_surjective M).forall, ← mk'_mul, Prod.forall, Subtype.forall, IsLocalization.eq,
    Submonoid.coe_mul, this, exists_const, m
-/
@[simp] lemma isRegular_mk' (hM : forall m in M, IsRegular m) {r : R} {m : M} :
    IsRegular (IsLocalization.mk' S r m) ↔ IsRegular r := by
  have (n : M) (x y : R) : n * x = n * y ↔ x = y := (hM _ n.2).1.eq_iff
  simp +contextual only [← isLeftRegular_iff_isRegular, IsLeftRegular, Function.Injective,
    (mk'_surjective M).forall, ← mk'_mul, Prod.forall, Subtype.forall, IsLocalization.eq,
    Submonoid.coe_mul, this, exists_const, mul_assoc]
  simp_rw [← mul_left_comm r]
  exact ⟨fun h a b => by simpa using h a 1 M.one_mem b 1 M.one_mem, fun h ha s hs b t ht => @h _ _⟩

include M in
variable (M) in
/--
theorem `noZeroDivisors` / 定理 `noZeroDivisors`

English:
theorem noZeroDivisors
  given: [NoZeroDivisors R]
  statement: NoZeroDivisors S
  proof: (toLocalizationMap M S).noZeroDivisors

中文:
定理 noZeroDivisors
  条件: [无零因子 R]
  结论: 无零因子 S
  证明: (toLocalizationMap M S).noZeroDivisors

Depends on / 依赖: noZeroDivisors, toLocalizationMap
-/
theorem noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors S :=
  (toLocalizationMap M S).noZeroDivisors

/--
theorem `sec_fst_ne_zero` / 定理 `sec_fst_ne_zero`

English:
theorem sec_fst_ne_zero
  given: {x : S} (hx : x != 0)
  statement: (sec M x).fst != 0
  proof: mt (fun h => by rw [← mk'_sec (M := M) S x, h, mk'_zero]) hx

中文:
定理 sec_fst_ne_zero
  条件: {x : S} (hx : x != 0)
  结论: (sec M x).fst != 0
  证明: mt (fun h => by rw [← mk'_sec (M := M) S x, h, mk'_zero]) hx

Depends on / 依赖: _sec, _zero
-/
theorem sec_fst_ne_zero {x : S} (hx : x != 0) : (sec M x).fst != 0 :=
  mt (fun h => by rw [← mk'_sec (M := M) S x, h, mk'_zero]) hx

section Ext

/--
theorem `eq_iff_eq` / 定理 `eq_iff_eq`

English:
theorem eq_iff_eq
  given: [Algebra R P] [IsLocalization M P] {x y}
  proof: (toLocalizationMap M S).eq_iff_eq (toLocalizationMap M P)

中文:
定理 eq_iff_eq
  条件: [代数 R P] [是Localization M P] {x y}
  证明: (toLocalizationMap M S).eq_iff_eq (toLocalizationMap M P)

Depends on / 依赖: eq_iff_eq, toLocalizationMap
-/
theorem eq_iff_eq [Algebra R P] [IsLocalization M P] {x y} :
    algebraMap R S x = algebraMap R S y ↔ algebraMap R P x = algebraMap R P y :=
  (toLocalizationMap M S).eq_iff_eq (toLocalizationMap M P)

/--
theorem `mk'_eq_iff_mk'_eq` / 定理 `mk'_eq_iff_mk'_eq`

English:
theorem mk'_eq_iff_mk'_eq
  given: [Algebra R P] [IsLocalization M P] {x₁ x₂} {y₁ y₂ : M}
  proof: (toLocalizationMap M S).mk'_eq_iff_mk'_eq (toLocalizationMap M P)

中文:
定理 mk'_eq_iff_mk'_eq
  条件: [代数 R P] [是Localization M P] {x₁ x₂} {y₁ y₂ : M}
  证明: (toLocalizationMap M S).mk'_eq_iff_mk'_eq (toLocalizationMap M P)
-/
theorem mk'_eq_iff_mk'_eq [Algebra R P] [IsLocalization M P] {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ mk' P x₁ y₁ = mk' P x₂ y₂ :=
  (toLocalizationMap M S).mk'_eq_iff_mk'_eq (toLocalizationMap M P)

/--
theorem `mk'_eq_of_eq` / 定理 `mk'_eq_of_eq`

English:
theorem mk'_eq_of_eq
  given: {a₁ b₁ : R} {a₂ b₂ : M} (H : ↑a₂ * b₁ = ↑b₂ * a₁)
  proof: (toLocalizationMap M S).mk'_eq_of_eq H

中文:
定理 mk'_eq_of_eq
  条件: {a₁ b₁ : R} {a₂ b₂ : M} (H : ↑a₂ * b₁ = ↑b₂ * a₁)
  证明: (toLocalizationMap M S).mk'_eq_of_eq H
-/
theorem mk'_eq_of_eq {a₁ b₁ : R} {a₂ b₂ : M} (H : ↑a₂ * b₁ = ↑b₂ * a₁) :
    mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (toLocalizationMap M S).mk'_eq_of_eq H

/--
theorem `mk'_eq_of_eq'` / 定理 `mk'_eq_of_eq'`

English:
theorem mk'_eq_of_eq'
  given: {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * ↑a₂ = a₁ * ↑b₂)
  proof: (toLocalizationMap M S).mk'_eq_of_eq' H

中文:
定理 mk'_eq_of_eq'
  条件: {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * ↑a₂ = a₁ * ↑b₂)
  证明: (toLocalizationMap M S).mk'_eq_of_eq' H
-/
theorem mk'_eq_of_eq' {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * ↑a₂ = a₁ * ↑b₂) :
    mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (toLocalizationMap M S).mk'_eq_of_eq' H

/--
theorem `mk'_cancel` / 定理 `mk'_cancel`

English:
theorem mk'_cancel
  given: (a : R) (b c : M)
  proof: (toLocalizationMap M S).mk'_cancel _ _ _

中文:
定理 mk'_cancel
  条件: (a : R) (b c : M)
  证明: (toLocalizationMap M S).mk'_cancel _ _ _
-/
theorem mk'_cancel (a : R) (b c : M) :
    mk' S (a * c) (b * c) = mk' S a b := (toLocalizationMap M S).mk'_cancel _ _ _

variable (S)

@[simp]
/--
theorem `mk'_self` / 定理 `mk'_self`

English:
theorem mk'_self
  given: {x : R} (hx : x in M)
  statement: mk' S x ⟨x, hx⟩ = 1
  proof: (toLocalizationMap M S).mk'_self _ hx

@[simp]

中文:
定理 mk'_self
  条件: {x : R} (hx : x in M)
  结论: mk' S x ⟨x, hx⟩ = 1
  证明: (toLocalizationMap M S).mk'_self _ hx

@[simp]
-/
theorem mk'_self {x : R} (hx : x in M) : mk' S x ⟨x, hx⟩ = 1 :=
  (toLocalizationMap M S).mk'_self _ hx

@[simp]
/--
theorem `mk'_self'` / 定理 `mk'_self'`

English:
theorem mk'_self'
  given: {x : M}
  statement: mk' S (x : R) x = 1
  proof: (toLocalizationMap M S).mk'_self' _

中文:
定理 mk'_self'
  条件: {x : M}
  结论: mk' S (x : R) x = 1
  证明: (toLocalizationMap M S).mk'_self' _
-/
theorem mk'_self' {x : M} : mk' S (x : R) x = 1 :=
  (toLocalizationMap M S).mk'_self' _

/--
theorem `mk'_self''` / 定理 `mk'_self''`

English:
theorem mk'_self''
  given: {x : M}
  statement: mk' S x.1 x = 1
  proof: mk'_self' _

中文:
定理 mk'_self''
  条件: {x : M}
  结论: mk' S x.1 x = 1
  证明: mk'_self' _
-/
theorem mk'_self'' {x : M} : mk' S x.1 x = 1 :=
  mk'_self' _

end Ext

/--
theorem `mul_mk'_eq_mk'_of_mul` / 定理 `mul_mk'_eq_mk'_of_mul`

English:
theorem mul_mk'_eq_mk'_of_mul
  given: (x y : R) (z : M)
  proof: (toLocalizationMap M S).mul_mk'_eq_mk'_of_mul _ _ _

中文:
定理 mul_mk'_eq_mk'_of_mul
  条件: (x y : R) (z : M)
  证明: (toLocalizationMap M S).mul_mk'_eq_mk'_of_mul _ _ _

Depends on / 依赖: _eq_mk, _of_mul, mul_mk, toLocalizationMap
-/
theorem mul_mk'_eq_mk'_of_mul (x y : R) (z : M) :
    (algebraMap R S) x * mk' S y z = mk' S (x * y) z :=
  (toLocalizationMap M S).mul_mk'_eq_mk'_of_mul _ _ _

/--
theorem `mk'_eq_mul_mk'_one` / 定理 `mk'_eq_mul_mk'_one`

English:
theorem mk'_eq_mul_mk'_one
  given: (x : R) (y : M)
  statement: mk' S x y = (algebraMap R S) x * mk' S 1 y
  proof: ((toLocalizationMap M S).mul_mk'_one_eq_mk' _ _).symm

@[simp]

中文:
定理 mk'_eq_mul_mk'_one
  条件: (x : R) (y : M)
  结论: mk' S x y = (algebraMap R S) x * mk' S 1 y
  证明: ((toLocalizationMap M S).mul_mk'_one_eq_mk' _ _).symm

@[simp]
-/
theorem mk'_eq_mul_mk'_one (x : R) (y : M) : mk' S x y = (algebraMap R S) x * mk' S 1 y :=
  ((toLocalizationMap M S).mul_mk'_one_eq_mk' _ _).symm

@[simp]
/--
theorem `mk'_mul_cancel_left` / 定理 `mk'_mul_cancel_left`

English:
theorem mk'_mul_cancel_left
  given: (x : R) (y : M)
  statement: mk' S (y * x : R) y = (algebraMap R S) x
  proof: (toLocalizationMap M S).mk'_mul_cancel_left _ _

中文:
定理 mk'_mul_cancel_left
  条件: (x : R) (y : M)
  结论: mk' S (y * x : R) y = (algebraMap R S) x
  证明: (toLocalizationMap M S).mk'_mul_cancel_left _ _
-/
theorem mk'_mul_cancel_left (x : R) (y : M) : mk' S (y * x : R) y = (algebraMap R S) x :=
  (toLocalizationMap M S).mk'_mul_cancel_left _ _

/--
theorem `mk'_mul_cancel_right` / 定理 `mk'_mul_cancel_right`

English:
theorem mk'_mul_cancel_right
  given: (x : R) (y : M)
  statement: mk' S (x * y) y = (algebraMap R S) x
  proof: (toLocalizationMap M S).mk'_mul_cancel_right _ _

@[simp]

中文:
定理 mk'_mul_cancel_right
  条件: (x : R) (y : M)
  结论: mk' S (x * y) y = (algebraMap R S) x
  证明: (toLocalizationMap M S).mk'_mul_cancel_right _ _

@[simp]
-/
theorem mk'_mul_cancel_right (x : R) (y : M) : mk' S (x * y) y = (algebraMap R S) x :=
  (toLocalizationMap M S).mk'_mul_cancel_right _ _

@[simp]
/--
theorem `mk'_mul_mk'_eq_one` / 定理 `mk'_mul_mk'_eq_one`

English:
theorem mk'_mul_mk'_eq_one
  given: (x y : M)
  statement: mk' S (x : R) y * mk' S (y : R) x = 1
  proof: by
  rw [← mk'_mul]; rw [mul_comm]; exact mk'_self _ _

中文:
定理 mk'_mul_mk'_eq_one
  条件: (x y : M)
  结论: mk' S (x : R) y * mk' S (y : R) x = 1
  证明: by
  rw [← mk'_mul]; rw [mul_comm]; exact mk'_self _ _
-/
theorem mk'_mul_mk'_eq_one (x y : M) : mk' S (x : R) y * mk' S (y : R) x = 1 := by
  rw [← mk'_mul]; rw [mul_comm]; exact mk'_self _ _

/--
theorem `mk'_mul_mk'_eq_one'` / 定理 `mk'_mul_mk'_eq_one'`

English:
theorem mk'_mul_mk'_eq_one'
  given: (x : R) (y : M) (h : x in M)
  statement: mk' S x y * mk' S (y : R) ⟨x, h⟩ = 1
  proof: mk'_mul_mk'_eq_one ⟨x, h⟩ _

中文:
定理 mk'_mul_mk'_eq_one'
  条件: (x : R) (y : M) (h : x in M)
  结论: mk' S x y * mk' S (y : R) ⟨x, h⟩ = 1
  证明: mk'_mul_mk'_eq_one ⟨x, h⟩ _
-/
theorem mk'_mul_mk'_eq_one' (x : R) (y : M) (h : x in M) : mk' S x y * mk' S (y : R) ⟨x, h⟩ = 1 :=
  mk'_mul_mk'_eq_one ⟨x, h⟩ _

/--
theorem `smul_mk'` / 定理 `smul_mk'`

English:
theorem smul_mk'
  given: (x y : R) (m : M)
  statement: x • mk' S y m = mk' S (x * y) m
  proof: by
  nth_rw 2 [← one_mul m]
  rw [mk'_mul]; rw [mk'_one]; rw [Algebra.smul_def]

中文:
定理 smul_mk'
  条件: (x y : R) (m : M)
  结论: x • mk' S y m = mk' S (x * y) m
  证明: by
  nth_rw 2 [← one_mul m]
  rw [mk'_mul]; rw [mk'_one]; rw [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, _mul, _one, nth_rw, one_mul, smul_def
-/
theorem smul_mk' (x y : R) (m : M) : x • mk' S y m = mk' S (x * y) m := by
  nth_rw 2 [← one_mul m]
  rw [mk'_mul]; rw [mk'_one]; rw [Algebra.smul_def]

/--
theorem `smul_mk'_one` / 定理 `smul_mk'_one`

English:
theorem smul_mk'_one
  given: (x : R) (m : M)
  statement: x • mk' S 1 m = mk' S x m
  proof: by
  rw [smul_mk']; rw [mul_one]

中文:
定理 smul_mk'_one
  条件: (x : R) (m : M)
  结论: x • mk' S 1 m = mk' S x m
  证明: by
  rw [smul_mk']; rw [mul_one]
-/
@[simp] theorem smul_mk'_one (x : R) (m : M) : x • mk' S 1 m = mk' S x m := by
  rw [smul_mk']; rw [mul_one]

/--
lemma `smul_mk'_self` / 引理 `smul_mk'_self`

English:
lemma smul_mk'_self
  given: {m : M} {r : R}
  proof: by
  rw [smul_mk']; rw [mk'_mul_cancel_left]

@[simps]

中文:
引理 smul_mk'_self
  条件: {m : M} {r : R}
  证明: by
  rw [smul_mk']; rw [mk'_mul_cancel_left]

@[simps]
-/
@[simp] lemma smul_mk'_self {m : M} {r : R} :
    (m : R) • mk' S r m = algebraMap R S r := by
  rw [smul_mk']; rw [mk'_mul_cancel_left]

@[simps]
/--
Instance `invertible_mk'_one` / 实例 `invertible_mk'_one`

English:
instance invertible_mk'_one
  signature: (s : M)
  body: algebraMap R S s
  invOf_mul_self := by simp
  mul_invOf_self := by simp

中文:
实例 invertible_mk'_one
  签名: (s : M)
  定义体: algebraMap R S s
  invOf_mul_self := by simp
  mul_invOf_self := by simp

Depends on / 依赖: algebraMap
-/
noncomputable instance invertible_mk'_one (s : M) :
    Invertible (IsLocalization.mk' S (1 : R) s) where
  invOf := algebraMap R S s
  invOf_mul_self := by simp
  mul_invOf_self := by simp

section

variable (M)

/--
theorem `isUnit_comp` / 定理 `isUnit_comp`

English:
theorem isUnit_comp
  given: (j : S ->+* P) (y : M)
  statement: IsUnit (j.comp (algebraMap R S) y)
  proof: (toLocalizationMap M S).isUnit_comp j.toMonoidHom _

中文:
定理 isUnit_comp
  条件: (j : S ->+* P) (y : M)
  结论: 是单位 (j.comp (algebraMap R S) y)
  证明: (toLocalizationMap M S).isUnit_comp j.toMonoidHom _

Depends on / 依赖: isUnit_comp, j.toMonoidHom, toLocalizationMap, toMonoidHom
-/
theorem isUnit_comp (j : S ->+* P) (y : M) : IsUnit (j.comp (algebraMap R S) y) :=
  (toLocalizationMap M S).isUnit_comp j.toMonoidHom _

end

/--
theorem `eq_of_eq` / 定理 `eq_of_eq`

English:
theorem eq_of_eq
  statement: {g : R ->+* P} (hg : forall y : M, IsUnit (g y)) {x y}
  proof: Submonoid.LocalizationMap.eq_of_eq (toLocalizationMap M S) (g := g.toMonoidHom) hg h

中文:
定理 eq_of_eq
  结论: {g : R ->+* P} (hg : 对任意 y : M, 是单位 (g y)) {x y}
  证明: Submonoid.LocalizationMap.eq_of_eq (toLocalizationMap M S) (g := g.toMonoidHom) hg h

Depends on / 依赖: LocalizationMap, Submonoid, Submonoid.LocalizationMap.eq_of_eq, eq_of_eq, g.toMonoidHom, toLocalizationMap, toMonoidHom
-/
theorem eq_of_eq {g : R ->+* P} (hg : forall y : M, IsUnit (g y)) {x y}
    (h : (algebraMap R S) x = (algebraMap R S) y) : g x = g y :=
  Submonoid.LocalizationMap.eq_of_eq (toLocalizationMap M S) (g := g.toMonoidHom) hg h

/--
theorem `mk'_add` / 定理 `mk'_add`

English:
theorem mk'_add
  given: (x₁ x₂ : R) (y₁ y₂ : M)
  proof: mk'_eq_iff_eq_mul.2
    Eq.symm
      (by
        rw [mul_comm (_ + _)]; rw [mul_add]; rw [mul_mk'_eq_mk'_of_mul]; rw [mk'_add_eq_iff_add_mul_eq_mul]; rw [mul_comm (_ * _)]; rw [← mul_assoc]; rw [add_comm]; rw [← map_mul]; rw [mul_mk'_eq_mk'_of_mul]; rw [mk'_add_eq_iff_add_mul_eq_mul]
        simp o

中文:
定理 mk'_add
  条件: (x₁ x₂ : R) (y₁ y₂ : M)
  证明: mk'_eq_iff_eq_mul.2
    Eq.symm
      (by
        rw [mul_comm (_ + _)]; rw [mul_add]; rw [mul_mk'_eq_mk'_of_mul]; rw [mk'_add_eq_iff_add_mul_eq_mul]; rw [mul_comm (_ * _)]; rw [← mul_assoc]; rw [add_comm]; rw [← map_mul]; rw [mul_mk'_eq_mk'_of_mul]; rw [mk'_add_eq_iff_add_mul_eq_mul]
        simp o
-/
theorem mk'_add (x₁ x₂ : R) (y₁ y₂ : M) :
    mk' S (x₁ * y₂ + x₂ * y₁) (y₁ * y₂) = mk' S x₁ y₁ + mk' S x₂ y₂ :=
mk'_eq_iff_eq_mul.2
    Eq.symm
      (by
        rw [mul_comm (_ + _)]; rw [mul_add]; rw [mul_mk'_eq_mk'_of_mul]; rw [mk'_add_eq_iff_add_mul_eq_mul]; rw [mul_comm (_ * _)]; rw [← mul_assoc]; rw [add_comm]; rw [← map_mul]; rw [mul_mk'_eq_mk'_of_mul]; rw [mk'_add_eq_iff_add_mul_eq_mul]
        simp only [map_add, Submonoid.coe_mul, map_mul]
        ring)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul_add_inv_left` / 定理 `mul_add_inv_left`

English:
theorem mul_add_inv_left
  given: {g : R ->+* P} (h : forall y : M, IsUnit (g y)) (y : M) (w z₁ z₂ : P)
  proof: by
  rw [mul_comm]; rw [← one_mul z₁]; rw [← Units.inv_mul (IsUnit.liftRight (g.toMonoidHom.domRestrict M) h y)]; rw [mul_assoc]; rw [← mul_add]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [Units.inv_mul_cancel_left]; rw [IsUnit.coe_liftRight]
  simp [RingHom.toMonoidHom_eq_coe, MonoidHom.domRestrict_appl

中文:
定理 mul_add_inv_left
  条件: {g : R ->+* P} (h : 对任意 y : M, 是单位 (g y)) (y : M) (w z₁ z₂ : P)
  证明: by
  rw [mul_comm]; rw [← one_mul z₁]; rw [← Units.inv_mul (IsUnit.liftRight (g.toMonoidHom.domRestrict M) h y)]; rw [mul_assoc]; rw [← mul_add]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [Units.inv_mul_cancel_left]; rw [IsUnit.coe_liftRight]
  simp [RingHom.toMonoidHom_eq_coe, MonoidHom.domRestrict_appl

Depends on / 依赖: IsUnit, IsUnit.coe_liftRight, IsUnit.liftRight, MonoidHom, MonoidHom.domRestrict_apply, RingHom, RingHom.toMonoidHom_eq_coe, Units.inv_mul, Units.inv_mul_cancel_left, Units.inv_mul_eq_iff_eq_mul, coe_liftRight, domRestrict, domRestrict_apply, g.toMonoidHom.domRestrict, inv_mul, inv_mul_cancel_left, inv_mul_eq_iff_eq_mul, liftRight, mul_add, mul_assoc
-/
theorem mul_add_inv_left {g : R ->+* P} (h : forall y : M, IsUnit (g y)) (y : M) (w z₁ z₂ : P) :
    w * ↑(IsUnit.liftRight (g.toMonoidHom.domRestrict M) h y)⁻¹ + z₁ =
    z₂ ↔ w + g y * z₁ = g y * z₂ := by
  rw [mul_comm]; rw [← one_mul z₁]; rw [← Units.inv_mul (IsUnit.liftRight (g.toMonoidHom.domRestrict M) h y)]; rw [mul_assoc]; rw [← mul_add]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [Units.inv_mul_cancel_left]; rw [IsUnit.coe_liftRight]
  simp [RingHom.toMonoidHom_eq_coe, MonoidHom.domRestrict_apply]

/--
theorem `lift_spec_mul_add` / 定理 `lift_spec_mul_add`

English:
theorem lift_spec_mul_add
  given: {g : R ->+* P} (hg : forall y : M, IsUnit (g y)) (z w w' v)
  proof: by
  rw [mul_comm]; rw [Submonoid.LocalizationMap.lift_apply]; rw [← mul_assoc]; rw [mul_add_inv_left hg]; rw [mul_comm]
  rfl

中文:
定理 lift_spec_mul_add
  条件: {g : R ->+* P} (hg : 对任意 y : M, 是单位 (g y)) (z w w' v)
  证明: by
  rw [mul_comm]; rw [Submonoid.LocalizationMap.lift_apply]; rw [← mul_assoc]; rw [mul_add_inv_left hg]; rw [mul_comm]
  rfl

Depends on / 依赖: LocalizationMap, Submonoid, Submonoid.LocalizationMap.lift_apply, lift_apply, mul_add_inv_left, mul_assoc, mul_comm
-/
theorem lift_spec_mul_add {g : R ->+* P} (hg : forall y : M, IsUnit (g y)) (z w w' v) :
    ((toLocalizationMap M S).lift hg) z * w + w' = v ↔
      g ((toLocalizationMap M S).sec z).1 * w + g ((toLocalizationMap M S).sec z).2 * w' =
        g ((toLocalizationMap M S).sec z).2 * v := by
  rw [mul_comm]; rw [Submonoid.LocalizationMap.lift_apply]; rw [← mul_assoc]; rw [mul_add_inv_left hg]; rw [mul_comm]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {g : R ->+* P} (hg : forall y : M, IsUnit (g y))
  body: { (toLocalizationMap M S).lift₀ g.toMonoidWithZeroHom hg with
    map_add' := by
      intro x y
      dsimp
      rw [(toLocalizationMap M S).lift₀_def]; rw [(toLocalizationMap M S).lift_spec]; rw [mul_add]; rw [mul_comm]; rw [eq_comm]; rw [lift_spec_mul_add]; rw [add_comm]; rw [mul_comm]; rw [mul_

中文:
定义 lift
  签名: {g : R ->+* P} (hg : 对任意 y : M, 是单位 (g y))
  定义体: { (toLocalizationMap M S).lift₀ g.toMonoidWithZeroHom hg with
    map_add' := by
      intro x y
      dsimp
      rw [(toLocalizationMap M S).lift₀_def]; rw [(toLocalizationMap M S).lift_spec]; rw [mul_add]; rw [mul_comm]; rw [eq_comm]; rw [lift_spec_mul_add]; rw [add_comm]; rw [mul_comm]; rw [mul_

Depends on / 依赖: add_comm, eq_comm, eq_of_eq, g.toMonoidWithZeroHom, lift_spec, lift_spec_mul_add, map_add, map_mul, mul_add, mul_assoc, mul_comm, sec_sp, simp_rw, toLocalizationMap, toMonoidWithZeroHom
-/
noncomputable def lift {g : R ->+* P} (hg : forall y : M, IsUnit (g y)) : S ->+* P :=
  { (toLocalizationMap M S).lift₀ g.toMonoidWithZeroHom hg with
    map_add' := by
      intro x y
      dsimp
      rw [(toLocalizationMap M S).lift₀_def]; rw [(toLocalizationMap M S).lift_spec]; rw [mul_add]; rw [mul_comm]; rw [eq_comm]; rw [lift_spec_mul_add]; rw [add_comm]; rw [mul_comm]; rw [mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [lift_spec_mul_add]
      simp_rw [← mul_assoc]
      change g _ * g _ * g _ + g _ * g _ * g _ = g _ * g _ * g _
      simp_rw [← map_mul g, ← map_add g]
      apply eq_of_eq (S := S) hg
      simp only [sec_spec', toLocalizationMap_sec, map_add, map_mul]
      ring }

variable {g : R ->+* P} (hg : forall y : M, IsUnit (g y))

/--
theorem `lift_mk'` / 定理 `lift_mk'`

English:
theorem lift_mk'
  given: (x y)
  proof: (toLocalizationMap M S).lift_mk' _ _ _

中文:
定理 lift_mk'
  条件: (x y)
  证明: (toLocalizationMap M S).lift_mk' _ _ _

Depends on / 依赖: lift_mk, toLocalizationMap
-/
theorem lift_mk' (x y) :
    lift hg (mk' S x y) = g x * ↑(IsUnit.liftRight (g.toMonoidHom.domRestrict M) hg y)⁻¹ :=
  (toLocalizationMap M S).lift_mk' _ _ _

/--
theorem `lift_mk'_spec` / 定理 `lift_mk'_spec`

English:
theorem lift_mk'_spec
  given: (x v) (y : M)
  statement: lift hg (mk' S x y) = v ↔ g x = g y * v
  proof: (toLocalizationMap M S).lift_mk'_spec _ _ _ _

@[simp]

中文:
定理 lift_mk'_spec
  条件: (x v) (y : M)
  结论: lift hg (mk' S x y) = v ↔ g x = g y * v
  证明: (toLocalizationMap M S).lift_mk'_spec _ _ _ _

@[simp]
-/
theorem lift_mk'_spec (x v) (y : M) : lift hg (mk' S x y) = v ↔ g x = g y * v :=
  (toLocalizationMap M S).lift_mk'_spec _ _ _ _

@[simp]
/--
theorem `lift_eq` / 定理 `lift_eq`

English:
theorem lift_eq
  given: (x : R)
  statement: lift hg ((algebraMap R S) x) = g x
  proof: (toLocalizationMap M S).lift_eq _ _

中文:
定理 lift_eq
  条件: (x : R)
  结论: lift hg ((algebraMap R S) x) = g x
  证明: (toLocalizationMap M S).lift_eq _ _

Depends on / 依赖: lift_eq, toLocalizationMap
-/
theorem lift_eq (x : R) : lift hg ((algebraMap R S) x) = g x :=
  (toLocalizationMap M S).lift_eq _ _

/--
theorem `lift_eq_iff` / 定理 `lift_eq_iff`

English:
theorem lift_eq_iff
  given: {x y : R × M}
  proof: (toLocalizationMap M S).lift_eq_iff _

@[simp]

中文:
定理 lift_eq_iff
  条件: {x y : R × M}
  证明: (toLocalizationMap M S).lift_eq_iff _

@[simp]

Depends on / 依赖: lift_eq_iff, toLocalizationMap
-/
theorem lift_eq_iff {x y : R × M} :
    lift hg (mk' S x.1 x.2) = lift hg (mk' S y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
  (toLocalizationMap M S).lift_eq_iff _

@[simp]
/--
theorem `lift_comp` / 定理 `lift_comp`

English:
theorem lift_comp
  statement: (lift hg).comp (algebraMap R S) = g
  proof: RingHom.ext (DFunLike.ext_iff (F := MonoidHom _ _)).1 (toLocalizationMap M S).lift_comp _

@[simp]

中文:
定理 lift_comp
  结论: (lift hg).comp (algebraMap R S) = g
  证明: RingHom.ext (DFunLike.ext_iff (F := MonoidHom _ _)).1 (toLocalizationMap M S).lift_comp _

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, MonoidHom, RingHom, RingHom.ext, ext_iff, lift_comp, toLocalizationMap
-/
theorem lift_comp : (lift hg).comp (algebraMap R S) = g :=
RingHom.ext (DFunLike.ext_iff (F := MonoidHom _ _)).1 (toLocalizationMap M S).lift_comp _

@[simp]
/--
theorem `lift_of_comp` / 定理 `lift_of_comp`

English:
theorem lift_of_comp
  given: (j : S ->+* P)
  statement: lift (isUnit_comp M j) = j
  proof: RingHom.ext (DFunLike.ext_iff (F := MonoidHom _ _)).1
    (toLocalizationMap M S).lift_of_comp j.toMonoidHom

中文:
定理 lift_of_comp
  条件: (j : S ->+* P)
  结论: lift (isUnit_comp M j) = j
  证明: RingHom.ext (DFunLike.ext_iff (F := MonoidHom _ _)).1
    (toLocalizationMap M S).lift_of_comp j.toMonoidHom

Depends on / 依赖: DFunLike, DFunLike.ext_iff, MonoidHom, RingHom, RingHom.ext, ext_iff, j.toMonoidHom, lift_of_comp, toLocalizationMap, toMonoidHom
-/
theorem lift_of_comp (j : S ->+* P) : lift (isUnit_comp M j) = j :=
RingHom.ext (DFunLike.ext_iff (F := MonoidHom _ _)).1
    (toLocalizationMap M S).lift_of_comp j.toMonoidHom

variable (M)

section
include M

/--
theorem `monoidHom_ext` / 定理 `monoidHom_ext`

English:
theorem monoidHom_ext
  given: {P : Type*} [Monoid P] ⦃j k
  statement: S ->* P⦄
  proof: (toLocalizationMap M S).epic_of_localizationMap h

中文:
定理 monoidHom_ext
  条件: {P : 类型} [幺半群 P] ⦃j k
  结论: S ->* P⦄
  证明: (toLocalizationMap M S).epic_of_localizationMap h

Depends on / 依赖: epic_of_localizationMap, toLocalizationMap
-/
theorem monoidHom_ext {P : Type*} [Monoid P] ⦃j k : S ->* P⦄
    (h : j.comp (algebraMap R S : R ->* S) = k.comp (algebraMap R S)) : j = k :=
  (toLocalizationMap M S).epic_of_localizationMap h

/--
theorem `ringHom_ext` / 定理 `ringHom_ext`

English:
theorem ringHom_ext
  given: {P : Type*} [Semiring P] ⦃j k
  statement: S ->+* P⦄
  proof: RingHom.coe_monoidHom_injective monoidHom_ext M MonoidHom.ext RingHom.congr_fun h

中文:
定理 ringHom_ext
  条件: {P : 类型} [半环 P] ⦃j k
  结论: S ->+* P⦄
  证明: RingHom.coe_monoidHom_injective monoidHom_ext M MonoidHom.ext RingHom.congr_fun h

Depends on / 依赖: MonoidHom, MonoidHom.ext, RingHom, RingHom.coe_monoidHom_injective, RingHom.congr_fun, coe_monoidHom_injective, congr_fun, monoidHom_ext
-/
theorem ringHom_ext {P : Type*} [Semiring P] ⦃j k : S ->+* P⦄
    (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) :
    j = k :=
RingHom.coe_monoidHom_injective monoidHom_ext M MonoidHom.ext RingHom.congr_fun h

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {P : Type*} [Monoid P] (j k : S -> P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
  proof: let j' : MonoidHom S P :=
    { toFun := j, map_one' := hj1, map_mul' := hjm }
  let k' : MonoidHom S P :=
    { toFun := k, map_one' := hk1, map_mul' := hkm }
  have : j' = k' := monoidHom_ext M (MonoidHom.ext h)
  show j'.toFun = k'.toFun by rw [this]

中文:
定理 ext
  结论: {P : 类型} [幺半群 P] (j k : S -> P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
  证明: let j' : MonoidHom S P :=
    { toFun := j, map_one' := hj1, map_mul' := hjm }
  let k' : MonoidHom S P :=
    { toFun := k, map_one' := hk1, map_mul' := hkm }
  have : j' = k' := monoidHom_ext M (MonoidHom.ext h)
  show j'.toFun = k'.toFun by rw [this]
-/
protected theorem ext {P : Type*} [Monoid P] (j k : S -> P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
    (hjm : forall a b, j (a * b) = j a * j b) (hkm : forall a b, k (a * b) = k a * k b)
    (h : forall a, j (algebraMap R S a) = k (algebraMap R S a)) : j = k :=
  let j' : MonoidHom S P :=
    { toFun := j, map_one' := hj1, map_mul' := hjm }
  let k' : MonoidHom S P :=
    { toFun := k, map_one' := hk1, map_mul' := hkm }
  have : j' = k' := monoidHom_ext M (MonoidHom.ext h)
  show j'.toFun = k'.toFun by rw [this]
end

variable {M}

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: {j : S ->+* P} (hj : forall x, j ((algebraMap R S) x) = g x)
  statement: lift hg = j
  proof: RingHom.ext
(DFunLike.ext_iff (F := MonoidHom _ _)).1
      Submonoid.LocalizationMap.lift_unique (toLocalizationMap M S) (g := g.toMonoidHom) hg
        (j := j.toMonoidHom) hj

@[simp]

中文:
定理 lift_unique
  条件: {j : S ->+* P} (hj : 对任意 x, j ((algebraMap R S) x) = g x)
  结论: lift hg = j
  证明: RingHom.ext
(DFunLike.ext_iff (F := MonoidHom _ _)).1
      Submonoid.LocalizationMap.lift_unique (toLocalizationMap M S) (g := g.toMonoidHom) hg
        (j := j.toMonoidHom) hj

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, LocalizationMap, MonoidHom, RingHom, RingHom.ext, Submonoid, Submonoid.LocalizationMap.lift_unique, ext_iff, g.toMonoidHom, j.toMonoidHom, lift_unique, toLocalizationMap, toMonoidHom
-/
theorem lift_unique {j : S ->+* P} (hj : forall x, j ((algebraMap R S) x) = g x) : lift hg = j :=
RingHom.ext
(DFunLike.ext_iff (F := MonoidHom _ _)).1
      Submonoid.LocalizationMap.lift_unique (toLocalizationMap M S) (g := g.toMonoidHom) hg
        (j := j.toMonoidHom) hj

@[simp]
/--
theorem `lift_id` / 定理 `lift_id`

English:
theorem lift_id
  given: (x)
  statement: lift (map_units S : forall _ : M, IsUnit _) x = x
  proof: (toLocalizationMap M S).lift_id _

中文:
定理 lift_id
  条件: (x)
  结论: lift (map_units S : 对任意 _ : M, 是单位 _) x = x
  证明: (toLocalizationMap M S).lift_id _

Depends on / 依赖: lift_id, toLocalizationMap
-/
theorem lift_id (x) : lift (map_units S : forall _ : M, IsUnit _) x = x :=
  (toLocalizationMap M S).lift_id _

/--
theorem `lift_surjective_iff` / 定理 `lift_surjective_iff`

English:
theorem lift_surjective_iff
  proof: (toLocalizationMap M S).lift_surjective_iff hg

中文:
定理 lift_surjective_iff
  证明: (toLocalizationMap M S).lift_surjective_iff hg

Depends on / 依赖: lift_surjective_iff, toLocalizationMap
-/
theorem lift_surjective_iff :
    Surjective (lift hg : S -> P) ↔ forall v : P, exists x : R × M, v * g x.2 = g x.1 :=
  (toLocalizationMap M S).lift_surjective_iff hg

/--
theorem `lift_injective_iff` / 定理 `lift_injective_iff`

English:
theorem lift_injective_iff
  proof: (toLocalizationMap M S).lift_injective_iff hg

中文:
定理 lift_injective_iff
  证明: (toLocalizationMap M S).lift_injective_iff hg

Depends on / 依赖: lift_injective_iff, toLocalizationMap
-/
theorem lift_injective_iff :
    Injective (lift hg : S -> P) ↔ forall x y, algebraMap R S x = algebraMap R S y ↔ g x = g y :=
  (toLocalizationMap M S).lift_injective_iff hg

variable (M) in
include M in
/--
lemma `injective_iff_map_algebraMap_eq` / 引理 `injective_iff_map_algebraMap_eq`

English:
lemma injective_iff_map_algebraMap_eq
  given: {T} [CommSemiring T] (f : S ->+* T)
  proof: by
  rw [← IsLocalization.lift_of_comp (M := M) f]; rw [IsLocalization.lift_injective_iff]
  simp

中文:
引理 injective_iff_map_algebraMap_eq
  条件: {T} [交换半环 T] (f : S ->+* T)
  证明: by
  rw [← IsLocalization.lift_of_comp (M := M) f]; rw [IsLocalization.lift_injective_iff]
  simp

Depends on / 依赖: IsLocalization, IsLocalization.lift_injective_iff, IsLocalization.lift_of_comp, lift_injective_iff, lift_of_comp
-/
lemma injective_iff_map_algebraMap_eq {T} [CommSemiring T] (f : S ->+* T) :
    Function.Injective f ↔ forall x y,
      algebraMap R S x = algebraMap R S y ↔ f (algebraMap R S x) = f (algebraMap R S y) := by
  rw [← IsLocalization.lift_of_comp (M := M) f]; rw [IsLocalization.lift_injective_iff]
  simp

section Map

variable {T : Submonoid P} {Q : Type*} [CommSemiring Q]
variable [Algebra P Q] [IsLocalization T Q]

section

variable (Q)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (g : R ->+* P) (hy : M <= T.comap g)
  body: lift (M := M) (g := (algebraMap P Q).comp g) fun y => map_units _ ⟨g y, hy y.2⟩

中文:
定义 map
  签名: (g : R ->+* P) (hy : M <= T.comap g)
  定义体: lift (M := M) (g := (algebraMap P Q).comp g) fun y => map_units _ ⟨g y, hy y.2⟩

Depends on / 依赖: algebraMap, map_units
-/
noncomputable def map (g : R ->+* P) (hy : M <= T.comap g) : S ->+* Q :=
  lift (M := M) (g := (algebraMap P Q).comp g) fun y => map_units _ ⟨g y, hy y.2⟩

end

section
variable (hy : M <= T.comap g)
include hy

@[simp]
/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  given: (x)
  statement: map Q g hy ((algebraMap R S) x) = algebraMap P Q (g x)
  proof: lift_eq (fun y => map_units _ ⟨g y, hy y.2⟩) x

@[simp]

中文:
定理 map_eq
  条件: (x)
  结论: map Q g hy ((algebraMap R S) x) = algebraMap P Q (g x)
  证明: lift_eq (fun y => map_units _ ⟨g y, hy y.2⟩) x

@[simp]

Depends on / 依赖: lift_eq, map_units
-/
theorem map_eq (x) : map Q g hy ((algebraMap R S) x) = algebraMap P Q (g x) :=
  lift_eq (fun y => map_units _ ⟨g y, hy y.2⟩) x

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: (map Q g hy).comp (algebraMap R S) = (algebraMap P Q).comp g
  proof: lift_comp fun y => map_units _ ⟨g y, hy y.2⟩

中文:
定理 map_comp
  结论: (map Q g hy).comp (algebraMap R S) = (algebraMap P Q).comp g
  证明: lift_comp fun y => map_units _ ⟨g y, hy y.2⟩

Depends on / 依赖: lift_comp, map_units
-/
theorem map_comp : (map Q g hy).comp (algebraMap R S) = (algebraMap P Q).comp g :=
  lift_comp fun y => map_units _ ⟨g y, hy y.2⟩

/--
theorem `map_mk'` / 定理 `map_mk'`

English:
theorem map_mk'
  given: (x) (y : M)
  statement: map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩
  proof: Submonoid.LocalizationMap.map_mk' (toLocalizationMap M S) (g := g.toMonoidHom)
    (fun y => hy y.2) (k := toLocalizationMap T Q) ..

中文:
定理 map_mk'
  条件: (x) (y : M)
  结论: map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩
  证明: Submonoid.LocalizationMap.map_mk' (toLocalizationMap M S) (g := g.toMonoidHom)
    (fun y => hy y.2) (k := toLocalizationMap T Q) ..

Depends on / 依赖: LocalizationMap, Submonoid, Submonoid.LocalizationMap.map_mk, g.toMonoidHom, map_mk, toLocalizationMap, toMonoidHom
-/
theorem map_mk' (x) (y : M) : map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩ :=
  Submonoid.LocalizationMap.map_mk' (toLocalizationMap M S) (g := g.toMonoidHom)
    (fun y => hy y.2) (k := toLocalizationMap T Q) ..

/--
theorem `map_unique` / 定理 `map_unique`

English:
theorem map_unique
  given: (j : S ->+* Q) (hj : forall x : R, j (algebraMap R S x) = algebraMap P Q (g x))
  proof: lift_unique (fun y => map_units _ ⟨g y, hy y.2⟩) hj

中文:
定理 map_unique
  条件: (j : S ->+* Q) (hj : 对任意 x : R, j (algebraMap R S x) = algebraMap P Q (g x))
  证明: lift_unique (fun y => map_units _ ⟨g y, hy y.2⟩) hj

Depends on / 依赖: lift_unique, map_units
-/
theorem map_unique (j : S ->+* Q) (hj : forall x : R, j (algebraMap R S x) = algebraMap P Q (g x)) :
    map Q g hy = j :=
  lift_unique (fun y => map_units _ ⟨g y, hy y.2⟩) hj

/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  statement: {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W]
  proof: RingHom.ext fun x =>
    Submonoid.LocalizationMap.map_map (P := P) (toLocalizationMap M S) (fun y => hy y.2)
      (toLocalizationMap U W) (fun w => hl w.2) x

中文:
定理 map_comp_map
  结论: {A : 类型} [交换半环 A] {U : 子幺半群 A} {W} [交换半环 W]
  证明: RingHom.ext fun x =>
    Submonoid.LocalizationMap.map_map (P := P) (toLocalizationMap M S) (fun y => hy y.2)
      (toLocalizationMap U W) (fun w => hl w.2) x

Depends on / 依赖: LocalizationMap, RingHom, RingHom.ext, Submonoid, Submonoid.LocalizationMap.map_map, map_map, toLocalizationMap
-/
theorem map_comp_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W]
    [Algebra A W] [IsLocalization U W] {l : P ->+* A} (hl : T <= U.comap l) :
    (map W l hl).comp (map Q g hy : S ->+* _) = map W (l.comp g) fun _ hx => hl (hy hx) :=
  RingHom.ext fun x =>
    Submonoid.LocalizationMap.map_map (P := P) (toLocalizationMap M S) (fun y => hy y.2)
      (toLocalizationMap U W) (fun w => hl w.2) x

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W] [Algebra A W]
  proof: by
  rw [← map_comp_map (Q := Q) hy hl]; rfl

中文:
定理 map_map
  结论: {A : 类型} [交换半环 A] {U : 子幺半群 A} {W} [交换半环 W] [代数 A W]
  证明: by
  rw [← map_comp_map (Q := Q) hy hl]; rfl

Depends on / 依赖: map_comp_map
-/
theorem map_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W] [Algebra A W]
    [IsLocalization U W] {l : P ->+* A} (hl : T <= U.comap l) (x : S) :
    map W l hl (map Q g hy x) = map W (l.comp g) (fun _ hx => hl (hy hx)) x := by
  rw [← map_comp_map (Q := Q) hy hl]; rfl

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (x : S) (z : R)
  statement: map Q g hy (z • x : S) = g z • map Q g hy x
  proof: by
  rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [map_mul]; rw [map_eq]

中文:
定理 map_smul
  条件: (x : S) (z : R)
  结论: map Q g hy (z • x : S) = g z • map Q g hy x
  证明: by
  rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [map_mul]; rw [map_eq]
-/
protected theorem map_smul (x : S) (z : R) : map Q g hy (z • x : S) = g z • map Q g hy x := by
  rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [map_mul]; rw [map_eq]

end

@[simp]
/--
theorem `map_id_mk'` / 定理 `map_id_mk'`

English:
theorem map_id_mk'
  given: {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q] (x) (y : M)
  proof: map_mk' ..

@[simp]

中文:
定理 map_id_mk'
  条件: {Q : 类型} [交换半环 Q] [代数 R Q] [是Localization M Q] (x) (y : M)
  证明: map_mk' ..

@[simp]

Depends on / 依赖: map_mk
-/
theorem map_id_mk' {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q] (x) (y : M) :
    map Q (RingHom.id R) (le_refl M) (mk' S x y) = mk' Q x y :=
  map_mk' ..

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (z : S) (h : M <= M.comap (RingHom.id R) := le_refl M)
  proof: lift_id _

中文:
定理 map_id
  条件: (z : S) (h : M <= M.comap (环态射.id R) := le_refl M)
  证明: lift_id _

Depends on / 依赖: le_refl
-/
theorem map_id (z : S) (h : M <= M.comap (RingHom.id R) := le_refl M) :
    map S (RingHom.id _) h z = z :=
  lift_id _

section

variable (S Q)

set_option backward.isDefEq.respectTransparency false in
/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
@[simps apply]
/--
Definition of `ringEquivOfRingEquiv` / `ringEquivOfRingEquiv` 的定义

English:
definition ringEquivOfRingEquiv
  signature: (h : R ≃+* P) (H : M.map h.toMonoidHom = T)
  body: have H' : T.map h.symm.toMonoidHom = M := by
    rw [← M.map_id]; rw [← H]; rw [Submonoid.map_map]
    congr
    ext
    apply h.symm_apply_apply
  { map Q (h : R ->+* P) (M.le_comap_of_map_le (le_of_eq H)) with
    toFun := map Q (h : R ->+* P) (M.le_comap_of_map_le (le_of_eq H))
    invFun := map 

中文:
定义 ringEquivOfRingEquiv
  签名: (h : R ≃+* P) (H : M.map h.toMonoidHom = T)
  定义体: have H' : T.map h.symm.toMonoidHom = M := by
    rw [← M.map_id]; rw [← H]; rw [Submonoid.map_map]
    congr
    ext
    apply h.symm_apply_apply
  { map Q (h : R ->+* P) (M.le_comap_of_map_le (le_of_eq H)) with
    toFun := map Q (h : R ->+* P) (M.le_comap_of_map_le (le_of_eq H))
    invFun := map 

Depends on / 依赖: M.le_comap_of_map_le, M.map_id, RingHom, RingHom.id, RingHom.id_apply, Submonoid, Submonoid.map_map, T.le_comap_of_map_le, T.map, h.symm, h.symm.toMonoidHom, h.symm_apply_apply, id_apply, invFun, le_comap_of_map_le, le_of_eq, left_inv, map_id, map_map, map_unique
-/
noncomputable def ringEquivOfRingEquiv (h : R ≃+* P) (H : M.map h.toMonoidHom = T) : S ≃+* Q :=
  have H' : T.map h.symm.toMonoidHom = M := by
    rw [← M.map_id]; rw [← H]; rw [Submonoid.map_map]
    congr
    ext
    apply h.symm_apply_apply
  { map Q (h : R ->+* P) (M.le_comap_of_map_le (le_of_eq H)) with
    toFun := map Q (h : R ->+* P) (M.le_comap_of_map_le (le_of_eq H))
    invFun := map S (h.symm : P ->+* R) (T.le_comap_of_map_le (le_of_eq H'))
    left_inv := fun x => by
      rw [map_map]; rw [map_unique _ (RingHom.id _)]; rw [RingHom.id_apply]
      simp
    right_inv := fun x => by
      rw [map_map]; rw [map_unique _ (RingHom.id _)]; rw [RingHom.id_apply]
      simp }

end

/--
theorem `ringEquivOfRingEquiv_eq_map` / 定理 `ringEquivOfRingEquiv_eq_map`

English:
theorem ringEquivOfRingEquiv_eq_map
  given: {j : R ≃+* P} (H : M.map j.toMonoidHom = T)
  proof: rfl

中文:
定理 ringEquivOfRingEquiv_eq_map
  条件: {j : R ≃+* P} (H : M.map j.toMonoidHom = T)
  证明: rfl
-/
theorem ringEquivOfRingEquiv_eq_map {j : R ≃+* P} (H : M.map j.toMonoidHom = T) :
    (ringEquivOfRingEquiv S Q j H : S ->+* Q) =
      map Q (j : R ->+* P) (M.le_comap_of_map_le (le_of_eq H)) :=
  rfl

/--
theorem `ringEquivOfRingEquiv_eq` / 定理 `ringEquivOfRingEquiv_eq`

English:
theorem ringEquivOfRingEquiv_eq
  given: {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x)
  proof: by
  simp

中文:
定理 ringEquivOfRingEquiv_eq
  条件: {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x)
  证明: by
  simp
-/
theorem ringEquivOfRingEquiv_eq {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x) :
    ringEquivOfRingEquiv S Q j H ((algebraMap R S) x) = algebraMap P Q (j x) := by
  simp

/--
theorem `ringEquivOfRingEquiv_mk'` / 定理 `ringEquivOfRingEquiv_mk'`

English:
theorem ringEquivOfRingEquiv_mk'
  given: {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x : R) (y : M)
  proof: by
  simp [map_mk']

@[simp]

中文:
定理 ringEquivOfRingEquiv_mk'
  条件: {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x : R) (y : M)
  证明: by
  simp [map_mk']

@[simp]

Depends on / 依赖: map_mk
-/
theorem ringEquivOfRingEquiv_mk' {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x : R) (y : M) :
    ringEquivOfRingEquiv S Q j H (mk' S x y) =
      mk' Q (j x) ⟨j y, show j y in T from H ▸ Set.mem_image_of_mem j y.2⟩ := by
  simp [map_mk']

@[simp]
/--
theorem `ringEquivOfRingEquiv_symm` / 定理 `ringEquivOfRingEquiv_symm`

English:
theorem ringEquivOfRingEquiv_symm
  given: {j : R ≃+* P} (H : M.map j = T)
  proof: rfl

中文:
定理 ringEquivOfRingEquiv_symm
  条件: {j : R ≃+* P} (H : M.map j = T)
  证明: rfl
-/
theorem ringEquivOfRingEquiv_symm {j : R ≃+* P} (H : M.map j = T) :
    (ringEquivOfRingEquiv S Q j H).symm =
      ringEquivOfRingEquiv Q S j.symm (show T.map (j : R ≃* P).symm = M by
        rw [← H]; rw [← Submonoid.comap_equiv_eq_map_symm]; rw [← Submonoid.map_coe_toMulEquiv]; rw [Submonoid.comap_map_eq_of_injective (j : R ≃* P).injective]) := rfl

end Map

section

variable (M S) (Q : Type*) [CommSemiring Q] [Algebra P Q]

/--
theorem `map_injective_of_injective` / 定理 `map_injective_of_injective`

English:
theorem map_injective_of_injective
  given: (h : Function.Injective g) [IsLocalization (M.map g) Q]
  proof: (toLocalizationMap M S).map_injective_of_injective h (toLocalizationMap (M.map g) Q)

中文:
定理 map_injective_of_injective
  条件: (h : 函数.单射 g) [是Localization (M.map g) Q]
  证明: (toLocalizationMap M S).map_injective_of_injective h (toLocalizationMap (M.map g) Q)

Depends on / 依赖: M.map, map_injective_of_injective, toLocalizationMap
-/
theorem map_injective_of_injective (h : Function.Injective g) [IsLocalization (M.map g) Q] :
    Function.Injective (map Q g M.le_comap_map : S -> Q) :=
  (toLocalizationMap M S).map_injective_of_injective h (toLocalizationMap (M.map g) Q)

/--
theorem `map_surjective_of_surjective` / 定理 `map_surjective_of_surjective`

English:
theorem map_surjective_of_surjective
  given: (h : Function.Surjective g) [IsLocalization (M.map g) Q]
  proof: (toLocalizationMap M S).map_surjective_of_surjective h (toLocalizationMap (M.map g) Q)

中文:
定理 map_surjective_of_surjective
  条件: (h : 函数.满射 g) [是Localization (M.map g) Q]
  证明: (toLocalizationMap M S).map_surjective_of_surjective h (toLocalizationMap (M.map g) Q)

Depends on / 依赖: M.map, map_surjective_of_surjective, toLocalizationMap
-/
theorem map_surjective_of_surjective (h : Function.Surjective g) [IsLocalization (M.map g) Q] :
    Function.Surjective (map Q g M.le_comap_map : S -> Q) :=
  (toLocalizationMap M S).map_surjective_of_surjective h (toLocalizationMap (M.map g) Q)

end

end IsLocalization

section

variable (M)

/--
theorem `isLocalization_of_base_ringEquiv` / 定理 `isLocalization_of_base_ringEquiv`

English:
theorem isLocalization_of_base_ringEquiv
  given: [IsLocalization M S] (h : R ≃+* P)
  proof: ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
    IsLocalization (M.map h) S := by
  let : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  constructor; constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert! IsLocalization.map_units S ⟨y, hy⟩
    dsimp only [RingHom.algebraMap

中文:
定理 isLocalization_of_base_ringEquiv
  条件: [是Localization M S] (h : R ≃+* P)
  证明: ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
    IsLocalization (M.map h) S := by
  let : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  constructor; constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert! IsLocalization.map_units S ⟨y, hy⟩
    dsimp only [RingHom.algebraMap

Depends on / 依赖: algebraMap, h.symm.toRingHom, toAlgebra, toRingHom
-/
theorem isLocalization_of_base_ringEquiv [IsLocalization M S] (h : R ≃+* P) :
    haveI := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
    IsLocalization (M.map h) S := by
  let : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  constructor; constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert! IsLocalization.map_units S ⟨y, hy⟩
    dsimp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    exact congr_arg _ (h.symm_apply_apply _)
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M y
    refine ⟨⟨h x, _, _, s.prop, rfl⟩, ?_⟩
    dsimp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at e ⊢
    convert! e <;> exact h.symm_apply_apply _
  · intro x y
    rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.comp_apply]; rw [RingHom.comp_apply]; rw [IsLocalization.eq_iff_exists M S]
    simp [← h.toEquiv.apply_eq_iff_eq]

/--
theorem `isLocalization_iff_of_base_ringEquiv` / 定理 `isLocalization_iff_of_base_ringEquiv`

English:
theorem isLocalization_iff_of_base_ringEquiv
  given: (h : R ≃+* P)
  proof: ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
      IsLocalization (M.map h) S := by
  let : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  refine ⟨fun _ => isLocalization_of_base_ringEquiv M S h, ?_⟩
  intro (H : IsLocalization (Submonoid.map (h : R ≃* P) M) S)
  convert! 

中文:
定理 isLocalization_iff_of_base_ringEquiv
  条件: (h : R ≃+* P)
  证明: ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
      IsLocalization (M.map h) S := by
  let : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  refine ⟨fun _ => isLocalization_of_base_ringEquiv M S h, ?_⟩
  intro (H : IsLocalization (Submonoid.map (h : R ≃* P) M) S)
  convert! 

Depends on / 依赖: algebraMap, h.symm.toRingHom, toAlgebra, toRingHom
-/
theorem isLocalization_iff_of_base_ringEquiv (h : R ≃+* P) :
    IsLocalization M S ↔
      haveI := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
      IsLocalization (M.map h) S := by
  let : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  refine ⟨fun _ => isLocalization_of_base_ringEquiv M S h, ?_⟩
  intro (H : IsLocalization (Submonoid.map (h : R ≃* P) M) S)
  convert! isLocalization_of_base_ringEquiv (Submonoid.map (h : R ≃* P) M) S h.symm
  · rw [← Submonoid.map_coe_toMulEquiv, RingEquiv.coe_toMulEquiv_symm, ←
      Submonoid.comap_equiv_eq_map_symm, Submonoid.comap_map_eq_of_injective]
    exact h.toEquiv.injective
  rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.comp_assoc]
  simp only [RingHom.comp_id, RingEquiv.symm_symm, RingEquiv.symm_toRingHom_comp_toRingHom]
  apply Algebra.algebra_ext
  intro r
  rw [RingHom.algebraMap_toAlgebra]

/--
theorem `of_ringEquiv_left` / 定理 `of_ringEquiv_left`

English:
theorem of_ringEquiv_left
  statement: {S : Type*} [CommSemiring S] {K : Type*} [CommSemiring K]
  proof: by
  rw [IsLocalization.isLocalization_iff_of_base_ringEquiv _ _ e]; rw [hM]
  convert! (inferInstance : IsLocalization M₁ K)
  exact Algebra.algebra_ext _ _ (by simp [RingHom.algebraMap_toAlgebra, h])

中文:
定理 of_ringEquiv_left
  结论: {S : 类型} [交换半环 S] {K : 类型} [交换半环 K]
  证明: by
  rw [IsLocalization.isLocalization_iff_of_base_ringEquiv _ _ e]; rw [hM]
  convert! (inferInstance : IsLocalization M₁ K)
  exact Algebra.algebra_ext _ _ (by simp [RingHom.algebraMap_toAlgebra, h])

Depends on / 依赖: Algebra, Algebra.algebra_ext, IsLocalization, IsLocalization.isLocalization_iff_of_base_ringEquiv, RingHom, RingHom.algebraMap_toAlgebra, algebraMap_toAlgebra, algebra_ext, convert, isLocalization_iff_of_base_ringEquiv
-/
theorem of_ringEquiv_left {S : Type*} [CommSemiring S] {K : Type*} [CommSemiring K]
    [Algebra R K] (e : R ≃+* S) [Algebra S K] {M₁ : Submonoid S} {M₂ : Submonoid R}
    (hM : M₂.map e = M₁) (h : forall x, algebraMap R K x = algebraMap S K (e x)) [IsLocalization M₁ K] :
    IsLocalization M₂ K := by
  rw [IsLocalization.isLocalization_iff_of_base_ringEquiv _ _ e]; rw [hM]
  convert! (inferInstance : IsLocalization M₁ K)
  exact Algebra.algebra_ext _ _ (by simp [RingHom.algebraMap_toAlgebra, h])

end

variable (M)

/--
theorem `nonZeroDivisors_le_comap` / 定理 `nonZeroDivisors_le_comap`

English:
theorem nonZeroDivisors_le_comap
  given: [IsLocalization M S]
  proof: (toLocalizationMap M S).nonZeroDivisors_le_comap

中文:
定理 nonZeroDivisors_le_comap
  条件: [是Localization M S]
  证明: (toLocalizationMap M S).nonZeroDivisors_le_comap

Depends on / 依赖: nonZeroDivisors_le_comap, toLocalizationMap
-/
theorem nonZeroDivisors_le_comap [IsLocalization M S] :
    nonZeroDivisors R <= (nonZeroDivisors S).comap (algebraMap R S) :=
  (toLocalizationMap M S).nonZeroDivisors_le_comap

/--
theorem `map_nonZeroDivisors_le` / 定理 `map_nonZeroDivisors_le`

English:
theorem map_nonZeroDivisors_le
  given: [IsLocalization M S]
  proof: (toLocalizationMap M S).map_nonZeroDivisors_le

中文:
定理 map_nonZeroDivisors_le
  条件: [是Localization M S]
  证明: (toLocalizationMap M S).map_nonZeroDivisors_le

Depends on / 依赖: map_nonZeroDivisors_le, toLocalizationMap
-/
theorem map_nonZeroDivisors_le [IsLocalization M S] :
    (nonZeroDivisors R).map (algebraMap R S) <= nonZeroDivisors S :=
  (toLocalizationMap M S).map_nonZeroDivisors_le

end IsLocalization

namespace Localization

open IsLocalization

/-! ### Constructing a localization at a given submonoid -/

section

/--
Instance `instUniqueLocalization` / 实例 `instUniqueLocalization`

English:
instance instUniqueLocalization
  signature: [Subsingleton R]
  body: by
    with_unfolding_all change a = mk 1 1
    exact Localization.induction_on a fun _ => by
      congr <;> apply Subsingleton.elim

中文:
实例 instUniqueLocalization
  签名: [子单例 R]
  定义体: by
    with_unfolding_all change a = mk 1 1
    exact Localization.induction_on a fun _ => by
      congr <;> apply Subsingleton.elim

Depends on / 依赖: Localization, Localization.induction_on, Subsingleton, Subsingleton.elim, induction_on, with_unfolding_all
-/
instance instUniqueLocalization [Subsingleton R] : Unique (Localization M) where
  uniq a := by
    with_unfolding_all change a = mk 1 1
    exact Localization.induction_on a fun _ => by
      congr <;> apply Subsingleton.elim

/--
theorem `add_mk` / 定理 `add_mk`

English:
theorem add_mk
  given: (a b c d)
  statement: (mk a b : Localization M) + mk c d =
  proof: by
  rw [add_comm (b * c) (d * a)]; rw [mul_comm b d]
  exact OreLocalization.oreDiv_add_oreDiv

中文:
定理 add_mk
  条件: (a b c d)
  结论: (mk a b : Localization M) + mk c d =
  证明: by
  rw [add_comm (b * c) (d * a)]; rw [mul_comm b d]
  exact OreLocalization.oreDiv_add_oreDiv

Depends on / 依赖: OreLocalization, OreLocalization.oreDiv_add_oreDiv, add_comm, mul_comm, oreDiv_add_oreDiv
-/
theorem add_mk (a b c d) : (mk a b : Localization M) + mk c d =
    mk ((b : R) * c + (d : R) * a) (b * d) := by
  rw [add_comm (b * c) (d * a)]; rw [mul_comm b d]
  exact OreLocalization.oreDiv_add_oreDiv

/--
theorem `add_mk_self` / 定理 `add_mk_self`

English:
theorem add_mk_self
  given: (a b c)
  statement: (mk a b : Localization M) + mk c b = mk (a + c) b
  proof: by
  rw [add_mk]; rw [mk_eq_mk_iff]; rw [r_eq_r']
  refine (r' M).symm ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul]
  ring

中文:
定理 add_mk_self
  条件: (a b c)
  结论: (mk a b : Localization M) + mk c b = mk (a + c) b
  证明: by
  rw [add_mk]; rw [mk_eq_mk_iff]; rw [r_eq_r']
  refine (r' M).symm ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul]
  ring

Depends on / 依赖: Submonoid, Submonoid.coe_mul, Submonoid.coe_one, add_mk, coe_mul, coe_one, mk_eq_mk_iff, r_eq_r
-/
theorem add_mk_self (a b c) : (mk a b : Localization M) + mk c b = mk (a + c) b := by
  rw [add_mk]; rw [mk_eq_mk_iff]; rw [r_eq_r']
  refine (r' M).symm ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul]
  ring

/-- For any given denominator `b : M`, the map `a ↦ a / b` is an `AddMonoidHom` from `R` to
  `Localization M`. -/
@[simps]
/--
Definition of `mkAddMonoidHom` / `mkAddMonoidHom` 的定义

English:
definition mkAddMonoidHom
  signature: (b : M)
  body: mk a b
  map_zero' := mk_zero _
  map_add' _ _ := (add_mk_self _ _ _).symm

中文:
定义 mkAddMonoidHom
  签名: (b : M)
  定义体: mk a b
  map_zero' := mk_zero _
  map_add' _ _ := (add_mk_self _ _ _).symm
-/
def mkAddMonoidHom (b : M) : R ->+ Localization M where
  toFun a := mk a b
  map_zero' := mk_zero _
  map_add' _ _ := (add_mk_self _ _ _).symm

/--
theorem `mk_sum` / 定理 `mk_sum`

English:
theorem mk_sum
  given: {ι : Type*} (f : ι -> R) (s : Finset ι) (b : M)
  proof: map_sum (mkAddMonoidHom b) f s

中文:
定理 mk_sum
  条件: {ι : 类型} (f : ι -> R) (s : 有限集 ι) (b : M)
  证明: map_sum (mkAddMonoidHom b) f s

Depends on / 依赖: map_sum, mkAddMonoidHom
-/
theorem mk_sum {ι : Type*} (f : ι -> R) (s : Finset ι) (b : M) :
    mk (∑ i in s, f i) b = ∑ i in s, mk (f i) b :=
  map_sum (mkAddMonoidHom b) f s

/--
theorem `mk_list_sum` / 定理 `mk_list_sum`

English:
theorem mk_list_sum
  given: (l : List R) (b : M)
  statement: mk l.sum b = (l.map fun a => mk a b).sum
  proof: map_list_sum (mkAddMonoidHom b) l

中文:
定理 mk_list_sum
  条件: (l : 列表 R) (b : M)
  结论: mk l.求和 b = (l.map fun a => mk a b).求和
  证明: map_list_sum (mkAddMonoidHom b) l

Depends on / 依赖: map_list_sum, mkAddMonoidHom
-/
theorem mk_list_sum (l : List R) (b : M) : mk l.sum b = (l.map fun a => mk a b).sum :=
  map_list_sum (mkAddMonoidHom b) l

/--
theorem `mk_multiset_sum` / 定理 `mk_multiset_sum`

English:
theorem mk_multiset_sum
  given: (l : Multiset R) (b : M)
  statement: mk l.sum b = (l.map fun a => mk a b).sum
  proof: (mkAddMonoidHom b).map_multiset_sum l

中文:
定理 mk_multiset_sum
  条件: (l : Multiset R) (b : M)
  结论: mk l.求和 b = (l.map fun a => mk a b).求和
  证明: (mkAddMonoidHom b).map_multiset_sum l

Depends on / 依赖: map_multiset_sum, mkAddMonoidHom
-/
theorem mk_multiset_sum (l : Multiset R) (b : M) : mk l.sum b = (l.map fun a => mk a b).sum :=
  (mkAddMonoidHom b).map_multiset_sum l

/--
Instance `isLocalization` / 实例 `isLocalization`

English:
instance isLocalization
  signature: : IsLocalization M (Localization M)
  body: ⟨(Localization.monoidOf M).isLocalizationMap⟩

中文:
实例 isLocalization
  签名: : 是Localization M (Localization M)
  定义体: ⟨(Localization.monoidOf M).isLocalizationMap⟩

Depends on / 依赖: Localization, Localization.monoidOf, isLocalizationMap, monoidOf
-/
instance isLocalization : IsLocalization M (Localization M) :=
  ⟨(Localization.monoidOf M).isLocalizationMap⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoZeroDivisors
  signature: R] : NoZeroDivisors (Localization M)
  body: IsLocalization.noZeroDivisors M

中文:
实例 [无零因子
  签名: R] : 无零因子 (Localization M)
  定义体: IsLocalization.noZeroDivisors M

Depends on / 依赖: IsLocalization, IsLocalization.noZeroDivisors, noZeroDivisors
-/
instance [NoZeroDivisors R] : NoZeroDivisors (Localization M) := IsLocalization.noZeroDivisors M

end

@[simp]
/--
theorem `toLocalizationMap_eq_monoidOf` / 定理 `toLocalizationMap_eq_monoidOf`

English:
theorem toLocalizationMap_eq_monoidOf
  statement: toLocalizationMap M (Localization M) = monoidOf M
  proof: rfl

中文:
定理 toLocalizationMap_eq_monoidOf
  结论: toLocalizationMap M (Localization M) = monoidOf M
  证明: rfl
-/
theorem toLocalizationMap_eq_monoidOf : toLocalizationMap M (Localization M) = monoidOf M :=
  rfl

/--
theorem `monoidOf_eq_algebraMap` / 定理 `monoidOf_eq_algebraMap`

English:
theorem monoidOf_eq_algebraMap
  given: (x)
  statement: monoidOf M x = algebraMap R (Localization M) x
  proof: rfl

中文:
定理 monoidOf_eq_algebraMap
  条件: (x)
  结论: monoidOf M x = algebraMap R (Localization M) x
  证明: rfl
-/
theorem monoidOf_eq_algebraMap (x) : monoidOf M x = algebraMap R (Localization M) x :=
  rfl

/--
theorem `mk_one_eq_algebraMap` / 定理 `mk_one_eq_algebraMap`

English:
theorem mk_one_eq_algebraMap
  given: (x)
  statement: mk x 1 = algebraMap R (Localization M) x
  proof: rfl

中文:
定理 mk_one_eq_algebraMap
  条件: (x)
  结论: mk x 1 = algebraMap R (Localization M) x
  证明: rfl
-/
theorem mk_one_eq_algebraMap (x) : mk x 1 = algebraMap R (Localization M) x :=
  rfl

/--
theorem `mk_eq_mk'_apply` / 定理 `mk_eq_mk'_apply`

English:
theorem mk_eq_mk'_apply
  given: (x y)
  statement: mk x y = IsLocalization.mk' (Localization M) x y
  proof: by
  rw [mk_eq_monoidOf_mk'_apply]; rw [mk']; rw [toLocalizationMap_eq_monoidOf]

中文:
定理 mk_eq_mk'_apply
  条件: (x y)
  结论: mk x y = 是Localization.mk' (Localization M) x y
  证明: by
  rw [mk_eq_monoidOf_mk'_apply]; rw [mk']; rw [toLocalizationMap_eq_monoidOf]

Depends on / 依赖: _apply, mk_eq_monoidOf_mk, toLocalizationMap_eq_monoidOf
-/
theorem mk_eq_mk'_apply (x y) : mk x y = IsLocalization.mk' (Localization M) x y := by
  rw [mk_eq_monoidOf_mk'_apply]; rw [mk']; rw [toLocalizationMap_eq_monoidOf]

/--
theorem `mk_eq_mk'` / 定理 `mk_eq_mk'`

English:
theorem mk_eq_mk'
  statement: (mk : R -> M -> Localization M) = IsLocalization.mk' (Localization M)
  proof: mk_eq_monoidOf_mk'

中文:
定理 mk_eq_mk'
  结论: (mk : R -> M -> Localization M) = 是Localization.mk' (Localization M)
  证明: mk_eq_monoidOf_mk'
-/
theorem mk_eq_mk' : (mk : R -> M -> Localization M) = IsLocalization.mk' (Localization M) :=
  mk_eq_monoidOf_mk'

/--
theorem `mk_algebraMap` / 定理 `mk_algebraMap`

English:
theorem mk_algebraMap
  given: {A : Type*} [CommSemiring A] [Algebra A R] (m : A)
  proof: by
  rw [mk_eq_mk']; rw [mk'_eq_iff_eq_mul]; rw [Submonoid.coe_one]; rw [map_one]; rw [mul_one]; rfl

中文:
定理 mk_algebraMap
  条件: {A : 类型} [交换半环 A] [代数 A R] (m : A)
  证明: by
  rw [mk_eq_mk']; rw [mk'_eq_iff_eq_mul]; rw [Submonoid.coe_one]; rw [map_one]; rw [mul_one]; rfl

Depends on / 依赖: Submonoid, Submonoid.coe_one, _eq_iff_eq_mul, coe_one, map_one, mk_eq_mk, mul_one
-/
theorem mk_algebraMap {A : Type*} [CommSemiring A] [Algebra A R] (m : A) :
    mk (algebraMap A R m) 1 = algebraMap A (Localization M) m := by
  rw [mk_eq_mk']; rw [mk'_eq_iff_eq_mul]; rw [Submonoid.coe_one]; rw [map_one]; rw [mul_one]; rfl

end Localization

namespace IsLocalization

variable [IsLocalization M S]

/--
theorem `to_map_eq_zero_iff` / 定理 `to_map_eq_zero_iff`

English:
theorem to_map_eq_zero_iff
  given: {x : R} (hM : M <= nonZeroDivisors R)
  statement: algebraMap R S x = 0 ↔ x = 0
  proof: by
  constructor <;> intro h
  · obtain ⟨c, hc⟩ := (map_eq_zero_iff M _ _).mp h
    exact (hM c.2).1 x hc
  · rw [h, map_zero]

中文:
定理 to_map_eq_zero_iff
  条件: {x : R} (hM : M <= nonZeroDivisors R)
  结论: algebraMap R S x = 0 ↔ x = 0
  证明: by
  constructor <;> intro h
  · obtain ⟨c, hc⟩ := (map_eq_zero_iff M _ _).mp h
    exact (hM c.2).1 x hc
  · rw [h, map_zero]

Depends on / 依赖: map_eq_zero_iff, map_zero
-/
theorem to_map_eq_zero_iff {x : R} (hM : M <= nonZeroDivisors R) : algebraMap R S x = 0 ↔ x = 0 := by
  constructor <;> intro h
  · obtain ⟨c, hc⟩ := (map_eq_zero_iff M _ _).mp h
    exact (hM c.2).1 x hc
  · rw [h, map_zero]

/--
theorem `injectiveₛ` / 定理 `injectiveₛ`

English:
theorem injectiveₛ
  given: (hM : forall m in M, IsRegular m)
  statement: Injective (algebraMap R S)
  proof: (toLocalizationMap M S).injective_iff.mpr hM

中文:
定理 injectiveₛ
  条件: (hM : 对任意 m in M, 是正则 m)
  结论: 单射 (algebraMap R S)
  证明: (toLocalizationMap M S).injective_iff.mpr hM
-/
protected theorem injectiveₛ (hM : forall m in M, IsRegular m) : Injective (algebraMap R S) :=
  (toLocalizationMap M S).injective_iff.mpr hM

/--
theorem `to_map_ne_zero_of_mem_nonZeroDivisors` / 定理 `to_map_ne_zero_of_mem_nonZeroDivisors`

English:
theorem to_map_ne_zero_of_mem_nonZeroDivisors
  statement: [Nontrivial R] (hM : M <= nonZeroDivisors R)
  proof: by
  rw [Ne]; rw [to_map_eq_zero_iff S hM]
  exact nonZeroDivisors.ne_zero hx

中文:
定理 to_map_ne_zero_of_mem_nonZeroDivisors
  结论: [非平凡 R] (hM : M <= nonZeroDivisors R)
  证明: by
  rw [Ne]; rw [to_map_eq_zero_iff S hM]
  exact nonZeroDivisors.ne_zero hx
-/
protected theorem to_map_ne_zero_of_mem_nonZeroDivisors [Nontrivial R] (hM : M <= nonZeroDivisors R)
    {x : R} (hx : x in nonZeroDivisors R) : algebraMap R S x != 0 := by
  rw [Ne]; rw [to_map_eq_zero_iff S hM]
  exact nonZeroDivisors.ne_zero hx

variable {S}

/--
theorem `sec_snd_ne_zero` / 定理 `sec_snd_ne_zero`

English:
theorem sec_snd_ne_zero
  given: [Nontrivial R] (hM : M <= nonZeroDivisors R) (x : S)
  proof: nonZeroDivisors.coe_ne_zero ⟨(sec M x).snd.val, hM (sec M x).snd.property⟩

中文:
定理 sec_snd_ne_zero
  条件: [非平凡 R] (hM : M <= nonZeroDivisors R) (x : S)
  证明: nonZeroDivisors.coe_ne_zero ⟨(sec M x).snd.val, hM (sec M x).snd.property⟩

Depends on / 依赖: coe_ne_zero, nonZeroDivisors, nonZeroDivisors.coe_ne_zero, property, snd.property, snd.val
-/
theorem sec_snd_ne_zero [Nontrivial R] (hM : M <= nonZeroDivisors R) (x : S) :
    ((sec M x).snd : R) != 0 :=
  nonZeroDivisors.coe_ne_zero ⟨(sec M x).snd.val, hM (sec M x).snd.property⟩

variable [IsDomain R]

variable (S) in
/--
theorem `isDomain_of_le_nonZeroDivisors` / 定理 `isDomain_of_le_nonZeroDivisors`

English:
theorem isDomain_of_le_nonZeroDivisors
  given: (hM : M <= nonZeroDivisors R)
  statement: IsDomain S where
  proof: (toLocalizationMap M S).isCancelMulZero
  __ : Nontrivial S := (toLocalizationMap M S).nontrivial fun h => zero_notMem_nonZeroDivisors (hM h)

中文:
定理 isDomain_of_le_nonZeroDivisors
  条件: (hM : M <= nonZeroDivisors R)
  结论: 是整环 S where
  证明: (toLocalizationMap M S).isCancelMulZero
  __ : Nontrivial S := (toLocalizationMap M S).nontrivial fun h => zero_notMem_nonZeroDivisors (hM h)

Depends on / 依赖: isCancelMulZero, toLocalizationMap
-/
theorem isDomain_of_le_nonZeroDivisors (hM : M <= nonZeroDivisors R) : IsDomain S where
  __ : IsCancelMulZero S := (toLocalizationMap M S).isCancelMulZero
  __ : Nontrivial S := (toLocalizationMap M S).nontrivial fun h => zero_notMem_nonZeroDivisors (hM h)

/--
theorem `isDomain_localization` / 定理 `isDomain_localization`

English:
theorem isDomain_localization
  given: {M : Submonoid R} (hM : M <= nonZeroDivisors R)
  proof: isDomain_of_le_nonZeroDivisors _ hM

中文:
定理 isDomain_localization
  条件: {M : 子幺半群 R} (hM : M <= nonZeroDivisors R)
  证明: isDomain_of_le_nonZeroDivisors _ hM

Depends on / 依赖: isDomain_of_le_nonZeroDivisors
-/
theorem isDomain_localization {M : Submonoid R} (hM : M <= nonZeroDivisors R) :
    IsDomain (Localization M) :=
  isDomain_of_le_nonZeroDivisors _ hM

end IsLocalization

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]

namespace Localization

/--
theorem `neg_mk` / 定理 `neg_mk`

English:
theorem neg_mk
  given: (a b)
  statement: -(mk a b : Localization M) = mk (-a) b
  proof: OreLocalization.neg_def _ _

中文:
定理 neg_mk
  条件: (a b)
  结论: -(mk a b : Localization M) = mk (-a) b
  证明: OreLocalization.neg_def _ _

Depends on / 依赖: OreLocalization, OreLocalization.neg_def, neg_def
-/
theorem neg_mk (a b) : -(mk a b : Localization M) = mk (-a) b := OreLocalization.neg_def _ _

/--
theorem `sub_mk` / 定理 `sub_mk`

English:
theorem sub_mk
  given: (a c) (b d)
  statement: (mk a b : Localization M) - mk c d =
  proof: by
  rw [sub_eq_add_neg]; rw [neg_mk]; rw [add_mk]; rw [add_comm]; rw [mul_neg]; rw [← sub_eq_add_neg]

中文:
定理 sub_mk
  条件: (a c) (b d)
  结论: (mk a b : Localization M) - mk c d =
  证明: by
  rw [sub_eq_add_neg]; rw [neg_mk]; rw [add_mk]; rw [add_comm]; rw [mul_neg]; rw [← sub_eq_add_neg]

Depends on / 依赖: add_comm, add_mk, mul_neg, neg_mk, sub_eq_add_neg
-/
theorem sub_mk (a c) (b d) : (mk a b : Localization M) - mk c d =
    mk ((d : R) * a - b * c) (b * d) := by
  rw [sub_eq_add_neg]; rw [neg_mk]; rw [add_mk]; rw [add_comm]; rw [mul_neg]; rw [← sub_eq_add_neg]

end Localization

namespace IsLocalization

variable [IsLocalization M S]

/--
theorem `mk'_neg` / 定理 `mk'_neg`

English:
theorem mk'_neg
  given: (x : R) (y : M)
  proof: by
  rw [eq_comm]; rw [eq_mk'_iff_mul_eq]; rw [neg_mul]; rw [map_neg]; rw [mk'_spec]

中文:
定理 mk'_neg
  条件: (x : R) (y : M)
  证明: by
  rw [eq_comm]; rw [eq_mk'_iff_mul_eq]; rw [neg_mul]; rw [map_neg]; rw [mk'_spec]
-/
theorem mk'_neg (x : R) (y : M) :
    mk' S (-x) y = -mk' S x y := by
  rw [eq_comm]; rw [eq_mk'_iff_mul_eq]; rw [neg_mul]; rw [map_neg]; rw [mk'_spec]

/--
theorem `mk'_sub` / 定理 `mk'_sub`

English:
theorem mk'_sub
  given: (x₁ x₂ : R) (y₁ y₂ : M)
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [← mk'_neg]; rw [← mk'_add]; rw [neg_mul]

include M in

中文:
定理 mk'_sub
  条件: (x₁ x₂ : R) (y₁ y₂ : M)
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [← mk'_neg]; rw [← mk'_add]; rw [neg_mul]

include M in
-/
theorem mk'_sub (x₁ x₂ : R) (y₁ y₂ : M) :
    mk' S (x₁ * y₂ - x₂ * y₁) (y₁ * y₂) = mk' S x₁ y₁ - mk' S x₂ y₂ := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [← mk'_neg]; rw [← mk'_add]; rw [neg_mul]

include M in
/--
lemma `injective_of_map_algebraMap_zero` / 引理 `injective_of_map_algebraMap_zero`

English:
lemma injective_of_map_algebraMap_zero
  statement: {T} [CommRing T] (f : S ->+* T)
  proof: by
  rw [IsLocalization.injective_iff_map_algebraMap_eq M]
  refine fun x y => ⟨fun hz => hz ▸ rfl, fun hz => ?_⟩
  rw [← sub_eq_zero]; rw [← map_sub]; rw [← map_sub] at hz
  apply h at hz
  rwa [map_sub, sub_eq_zero] at hz

中文:
引理 injective_of_map_algebraMap_zero
  结论: {T} [交换环 T] (f : S ->+* T)
  证明: by
  rw [IsLocalization.injective_iff_map_algebraMap_eq M]
  refine fun x y => ⟨fun hz => hz ▸ rfl, fun hz => ?_⟩
  rw [← sub_eq_zero]; rw [← map_sub]; rw [← map_sub] at hz
  apply h at hz
  rwa [map_sub, sub_eq_zero] at hz

Depends on / 依赖: IsLocalization, IsLocalization.injective_iff_map_algebraMap_eq, injective_iff_map_algebraMap_eq, map_sub, sub_eq_zero
-/
lemma injective_of_map_algebraMap_zero {T} [CommRing T] (f : S ->+* T)
    (h : forall x, f (algebraMap R S x) = 0 -> algebraMap R S x = 0) :
    Function.Injective f := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq M]
  refine fun x y => ⟨fun hz => hz ▸ rfl, fun hz => ?_⟩
  rw [← sub_eq_zero]; rw [← map_sub]; rw [← map_sub] at hz
  apply h at hz
  rwa [map_sub, sub_eq_zero] at hz

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (hM : M <= nonZeroDivisors R)
  statement: Injective (algebraMap R S)
  proof: IsLocalization.injectiveₛ S fun _x hx => isRegular_iff_mem_nonZeroDivisors.mpr (hM hx)

中文:
定理 injective
  条件: (hM : M <= nonZeroDivisors R)
  结论: 单射 (algebraMap R S)
  证明: IsLocalization.injectiveₛ S fun _x hx => isRegular_iff_mem_nonZeroDivisors.mpr (hM hx)
-/
protected theorem injective (hM : M <= nonZeroDivisors R) : Injective (algebraMap R S) :=
  IsLocalization.injectiveₛ S fun _x hx => isRegular_iff_mem_nonZeroDivisors.mpr (hM hx)

end IsLocalization

end CommRing
