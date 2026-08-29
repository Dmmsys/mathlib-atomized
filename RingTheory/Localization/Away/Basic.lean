/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Localizations away from an element

## Main definitions

* `IsLocalization.Away (x : R) S` expresses that `S` is a localization away from `x`, as an
  abbreviation of `IsLocalization (Submonoid.powers x) S`.
* `exists_reduced_fraction' (hb : b ≠ 0)` produces a reduced fraction of the form `b = a * x^n` for
  some `n : ℤ` and some `a : R` that is not divisible by `x`.

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

namespace IsLocalization

section Away

variable (x : R)

/--
Definition of `Away` / `Away` 的定义

English:
abbreviation Away
  signature: (S : Type*) [CommSemiring S] [Algebra R S]
  body: IsLocalization (Submonoid.powers x) S

中文:
缩写 Away
  签名: (S : 类型) [交换半环 S] [代数 R S]
  定义体: IsLocalization (Submonoid.powers x) S

Depends on / 依赖: IsLocalization, Submonoid, Submonoid.powers, powers
-/
abbrev Away (S : Type*) [CommSemiring S] [Algebra R S] :=
  IsLocalization (Submonoid.powers x) S

namespace Away

variable [IsLocalization.Away x S]

/--
Definition of `invSelf` / `invSelf` 的定义

English:
definition invSelf
  signature: : S
  body: mk' S (1 : R) ⟨x, Submonoid.mem_powers _⟩

@[simp]

中文:
定义 invSelf
  签名: : S
  定义体: mk' S (1 : R) ⟨x, Submonoid.mem_powers _⟩

@[simp]

Depends on / 依赖: Submonoid, Submonoid.mem_powers, mem_powers
-/
noncomputable def invSelf : S :=
  mk' S (1 : R) ⟨x, Submonoid.mem_powers _⟩

@[simp]
/--
theorem `mul_invSelf` / 定理 `mul_invSelf`

English:
theorem mul_invSelf
  statement: algebraMap R S x * invSelf x = 1
  proof: by
  convert! IsLocalization.mk'_mul_mk'_eq_one (M := Submonoid.powers x) (S := S) _ 1
  symm
  apply IsLocalization.mk'_one

中文:
定理 mul_invSelf
  结论: algebraMap R S x * invSelf x = 1
  证明: by
  convert! IsLocalization.mk'_mul_mk'_eq_one (M := Submonoid.powers x) (S := S) _ 1
  symm
  apply IsLocalization.mk'_one

Depends on / 依赖: IsLocalization, IsLocalization.mk, Submonoid, Submonoid.powers, _eq_one, _mul_mk, _one, convert, powers
-/
theorem mul_invSelf : algebraMap R S x * invSelf x = 1 := by
  convert! IsLocalization.mk'_mul_mk'_eq_one (M := Submonoid.powers x) (S := S) _ 1
  symm
  apply IsLocalization.mk'_one

/--
Definition of `sec` / `sec` 的定义

English:
definition sec
  signature: (s : S)
  body: ⟨(IsLocalization.sec (Submonoid.powers x) s).1,
   (IsLocalization.sec (Submonoid.powers x) s).2.property.choose⟩

中文:
定义 sec
  签名: (s : S)
  定义体: ⟨(IsLocalization.sec (Submonoid.powers x) s).1,
   (IsLocalization.sec (Submonoid.powers x) s).2.property.choose⟩

Depends on / 依赖: IsLocalization, IsLocalization.sec, Submonoid, Submonoid.powers, powers, property, property.choose
-/
noncomputable def sec (s : S) : R × Nat :=
  ⟨(IsLocalization.sec (Submonoid.powers x) s).1,
   (IsLocalization.sec (Submonoid.powers x) s).2.property.choose⟩

/--
lemma `sec_spec` / 引理 `sec_spec`

English:
lemma sec_spec
  given: (s : S)
  statement: s * (algebraMap R S) (x ^ (IsLocalization.Away.sec x s).2) =
  proof: by
  simp only [IsLocalization.Away.sec, ← IsLocalization.sec_spec]
  congr
  exact (IsLocalization.sec (Submonoid.powers x) s).2.property.choose_spec

中文:
引理 sec_spec
  条件: (s : S)
  结论: s * (algebraMap R S) (x ^ (是Localization.Away.sec x s).2) =
  证明: by
  simp only [IsLocalization.Away.sec, ← IsLocalization.sec_spec]
  congr
  exact (IsLocalization.sec (Submonoid.powers x) s).2.property.choose_spec

Depends on / 依赖: IsLocalization, IsLocalization.Away.sec, IsLocalization.sec, IsLocalization.sec_spec, Submonoid, Submonoid.powers, choose_spec, powers, property, property.choose_spec, sec_spec
-/
lemma sec_spec (s : S) : s * (algebraMap R S) (x ^ (IsLocalization.Away.sec x s).2) =
    algebraMap R S (IsLocalization.Away.sec x s).1 := by
  simp only [IsLocalization.Away.sec, ← IsLocalization.sec_spec]
  congr
  exact (IsLocalization.sec (Submonoid.powers x) s).2.property.choose_spec

/--
lemma `algebraMap_pow_isUnit` / 引理 `algebraMap_pow_isUnit`

English:
lemma algebraMap_pow_isUnit
  given: (n : Nat)
  statement: IsUnit (algebraMap R S x ^ n)
  proof: IsUnit.pow _ IsLocalization.map_units _ (⟨x, 1, by simp⟩ : Submonoid.powers x)

中文:
引理 algebraMap_pow_isUnit
  条件: (n : 自然数)
  结论: 是单位 (algebraMap R S x ^ n)
  证明: IsUnit.pow _ IsLocalization.map_units _ (⟨x, 1, by simp⟩ : Submonoid.powers x)

Depends on / 依赖: IsLocalization, IsLocalization.map_units, IsUnit, IsUnit.pow, Submonoid, Submonoid.powers, map_units, powers
-/
lemma algebraMap_pow_isUnit (n : Nat) : IsUnit (algebraMap R S x ^ n) :=
IsUnit.pow _ IsLocalization.map_units _ (⟨x, 1, by simp⟩ : Submonoid.powers x)

/--
lemma `algebraMap_isUnit` / 引理 `algebraMap_isUnit`

English:
lemma algebraMap_isUnit
  statement: IsUnit (algebraMap R S x)
  proof: IsLocalization.map_units _ (⟨x, 1, by simp⟩ : Submonoid.powers x)

中文:
引理 algebraMap_isUnit
  结论: 是单位 (algebraMap R S x)
  证明: IsLocalization.map_units _ (⟨x, 1, by simp⟩ : Submonoid.powers x)

Depends on / 依赖: IsLocalization, IsLocalization.map_units, Submonoid, Submonoid.powers, map_units, powers
-/
lemma algebraMap_isUnit : IsUnit (algebraMap R S x) :=
  IsLocalization.map_units _ (⟨x, 1, by simp⟩ : Submonoid.powers x)

/--
theorem `associated_sec_fst` / 定理 `associated_sec_fst`

English:
theorem associated_sec_fst
  given: (s : S)
  proof: by
  rw [← IsLocalization.Away.sec_spec]; rw [map_pow]
exact associated_mul_unit_left _ _ .pow _ IsLocalization.Away.algebraMap_isUnit _

中文:
定理 associated_sec_fst
  条件: (s : S)
  证明: by
  rw [← IsLocalization.Away.sec_spec]; rw [map_pow]
exact associated_mul_unit_left _ _ .pow _ IsLocalization.Away.algebraMap_isUnit _

Depends on / 依赖: IsLocalization, IsLocalization.Away.algebraMap_isUnit, IsLocalization.Away.sec_spec, algebraMap_isUnit, associated_mul_unit_left, map_pow, sec_spec
-/
theorem associated_sec_fst (s : S) :
    Associated (algebraMap R S (IsLocalization.Away.sec x s).1) s := by
  rw [← IsLocalization.Away.sec_spec]; rw [map_pow]
exact associated_mul_unit_left _ _ .pow _ IsLocalization.Away.algebraMap_isUnit _

/--
lemma `algebraMap_isUnit_iff` / 引理 `algebraMap_isUnit_iff`

English:
lemma algebraMap_isUnit_iff
  given: {y : R}
  statement: IsUnit (algebraMap R S y) ↔ exists n, y ∣ x ^ n
  proof: (IsLocalization.algebraMap_isUnit_iff <| .powers x).trans by simp [Submonoid.mem_powers_iff]

中文:
引理 algebraMap_isUnit_iff
  条件: {y : R}
  结论: 是单位 (algebraMap R S y) ↔ 存在 n, y ∣ x ^ n
  证明: (IsLocalization.algebraMap_isUnit_iff <| .powers x).trans by simp [Submonoid.mem_powers_iff]

Depends on / 依赖: IsLocalization, IsLocalization.algebraMap_isUnit_iff, Submonoid, Submonoid.mem_powers_iff, algebraMap_isUnit_iff, mem_powers_iff, powers
-/
lemma algebraMap_isUnit_iff {y : R} : IsUnit (algebraMap R S y) ↔ exists n, y ∣ x ^ n :=
(IsLocalization.algebraMap_isUnit_iff <| .powers x).trans by simp [Submonoid.mem_powers_iff]

/--
lemma `surj` / 引理 `surj`

English:
lemma surj
  given: (z : S)
  statement: exists (n : Nat) (a : R), z * algebraMap R S x ^ n = algebraMap R S a
  proof: by
  obtain ⟨⟨a, ⟨-, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers x) z
  use n, a
  simpa using h

中文:
引理 surj
  条件: (z : S)
  结论: 存在 (n : 自然数) (a : R), z * algebraMap R S x ^ n = algebraMap R S a
  证明: by
  obtain ⟨⟨a, ⟨-, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers x) z
  use n, a
  simpa using h

Depends on / 依赖: IsLocalization, IsLocalization.surj, Submonoid, Submonoid.powers, powers
-/
lemma surj (z : S) : exists (n : Nat) (a : R), z * algebraMap R S x ^ n = algebraMap R S a := by
  obtain ⟨⟨a, ⟨-, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers x) z
  use n, a
  simpa using h

/--
lemma `exists_of_eq` / 引理 `exists_of_eq`

English:
lemma exists_of_eq
  given: {a b : R} (h : algebraMap R S a = algebraMap R S b)
  proof: by
  obtain ⟨⟨-, n, rfl⟩, hx⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers x) h
  use n

中文:
引理 存在_of_eq
  条件: {a b : R} (h : algebraMap R S a = algebraMap R S b)
  证明: by
  obtain ⟨⟨-, n, rfl⟩, hx⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers x) h
  use n

Depends on / 依赖: IsLocalization, IsLocalization.exists_of_eq, Submonoid, Submonoid.powers, exists_of_eq, powers
-/
lemma exists_of_eq {a b : R} (h : algebraMap R S a = algebraMap R S b) :
    exists (n : Nat), x ^ n * a = x ^ n * b := by
  obtain ⟨⟨-, n, rfl⟩, hx⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers x) h
  use n

/--
lemma `mk` / 引理 `mk`

English:
lemma mk
  statement: (r : R) (map_unit : IsUnit (algebraMap R S r))
  proof: by
    rintro ⟨-, n, rfl⟩
    simp only [map_pow]
    exact IsUnit.pow _ map_unit
  surj z := by
    obtain ⟨n, a, hn⟩ := surj z
    use ⟨a, ⟨r ^ n, n, rfl⟩⟩
    simpa using hn
  exists_of_eq {x y} h := by
    obtain ⟨n, hn⟩ := exists_of_eq x y h
    use ⟨r ^ n, n, rfl⟩

中文:
引理 mk
  结论: (r : R) (map_unit : 是单位 (algebraMap R S r))
  证明: by
    rintro ⟨-, n, rfl⟩
    simp only [map_pow]
    exact IsUnit.pow _ map_unit
  surj z := by
    obtain ⟨n, a, hn⟩ := surj z
    use ⟨a, ⟨r ^ n, n, rfl⟩⟩
    simpa using hn
  exists_of_eq {x y} h := by
    obtain ⟨n, hn⟩ := exists_of_eq x y h
    use ⟨r ^ n, n, rfl⟩

Depends on / 依赖: IsUnit, IsUnit.pow, exists_of_eq, map_pow, map_unit
-/
lemma mk (r : R) (map_unit : IsUnit (algebraMap R S r))
    (surj : forall s, exists (n : Nat) (a : R), s * algebraMap R S r ^ n = algebraMap R S a)
    (exists_of_eq : forall a b, algebraMap R S a = algebraMap R S b -> exists (n : Nat), r ^ n * a = r ^ n * b) :
    IsLocalization.Away r S where
  map_units := by
    rintro ⟨-, n, rfl⟩
    simp only [map_pow]
    exact IsUnit.pow _ map_unit
  surj z := by
    obtain ⟨n, a, hn⟩ := surj z
    use ⟨a, ⟨r ^ n, n, rfl⟩⟩
    simpa using hn
  exists_of_eq {x y} h := by
    obtain ⟨n, hn⟩ := exists_of_eq x y h
    use ⟨r ^ n, n, rfl⟩

/--
lemma `of_associated` / 引理 `of_associated`

English:
lemma of_associated
  given: {r r' : R} (h : Associated r r') [IsLocalization.Away r S]
  proof: by
  obtain ⟨u, rfl⟩ := h
  refine mk _ ?_ (fun s => ?_) (fun a b hab => ?_)
  · simp [algebraMap_isUnit r, IsUnit.map _ u.isUnit]
  · obtain ⟨n, a, hn⟩ := surj r s
    use n, a * u ^ n
    simp [mul_pow, ← mul_assoc, hn]
  · obtain ⟨n, hn⟩ := exists_of_eq r hab
    use n
    rw [mul_pow]; rw [mul_c

中文:
引理 of_associated
  条件: {r r' : R} (h : Associated r r') [是Localization.Away r S]
  证明: by
  obtain ⟨u, rfl⟩ := h
  refine mk _ ?_ (fun s => ?_) (fun a b hab => ?_)
  · simp [algebraMap_isUnit r, IsUnit.map _ u.isUnit]
  · obtain ⟨n, a, hn⟩ := surj r s
    use n, a * u ^ n
    simp [mul_pow, ← mul_assoc, hn]
  · obtain ⟨n, hn⟩ := exists_of_eq r hab
    use n
    rw [mul_pow]; rw [mul_c

Depends on / 依赖: IsUnit, IsUnit.map, algebraMap_isUnit, exists_of_eq, isUnit, mul_assoc, mul_comm, mul_pow, u.isUnit
-/
lemma of_associated {r r' : R} (h : Associated r r') [IsLocalization.Away r S] :
    IsLocalization.Away r' S := by
  obtain ⟨u, rfl⟩ := h
  refine mk _ ?_ (fun s => ?_) (fun a b hab => ?_)
  · simp [algebraMap_isUnit r, IsUnit.map _ u.isUnit]
  · obtain ⟨n, a, hn⟩ := surj r s
    use n, a * u ^ n
    simp [mul_pow, ← mul_assoc, hn]
  · obtain ⟨n, hn⟩ := exists_of_eq r hab
    use n
    rw [mul_pow]; rw [mul_comm (r ^ n)]; rw [mul_assoc]; rw [mul_assoc]; rw [hn]

/--
lemma `iff_of_associated` / 引理 `iff_of_associated`

English:
lemma iff_of_associated
  given: {r r' : R} (h : Associated r r')
  proof: ⟨fun _ => IsLocalization.Away.of_associated h, fun _ => IsLocalization.Away.of_associated h.symm⟩

中文:
引理 iff_of_associated
  条件: {r r' : R} (h : Associated r r')
  证明: ⟨fun _ => IsLocalization.Away.of_associated h, fun _ => IsLocalization.Away.of_associated h.symm⟩

Depends on / 依赖: IsLocalization, IsLocalization.Away.of_associated, h.symm, of_associated
-/
lemma iff_of_associated {r r' : R} (h : Associated r r') :
    IsLocalization.Away r S ↔ IsLocalization.Away r' S :=
  ⟨fun _ => IsLocalization.Away.of_associated h, fun _ => IsLocalization.Away.of_associated h.symm⟩

/--
lemma `isUnit_of_dvd` / 引理 `isUnit_of_dvd`

English:
lemma isUnit_of_dvd
  given: {r : R} (h : r ∣ x)
  statement: IsUnit (algebraMap R S r)
  proof: isUnit_of_dvd_unit (map_dvd _ h) (algebraMap_isUnit x)

中文:
引理 isUnit_of_dvd
  条件: {r : R} (h : r ∣ x)
  结论: 是单位 (algebraMap R S r)
  证明: isUnit_of_dvd_unit (map_dvd _ h) (algebraMap_isUnit x)

Depends on / 依赖: algebraMap_isUnit, isUnit_of_dvd_unit, map_dvd
-/
lemma isUnit_of_dvd {r : R} (h : r ∣ x) : IsUnit (algebraMap R S r) :=
  isUnit_of_dvd_unit (map_dvd _ h) (algebraMap_isUnit x)

variable {g : R ->+* P}

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (hg : IsUnit (g x))
  body: IsLocalization.lift fun y : Submonoid.powers x =>
    show IsUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn]; rw [g.map_pow]
      exact IsUnit.map (powMonoidHom n : P ->* P) hg

@[simp]

中文:
定义 lift
  签名: (hg : 是单位 (g x))
  定义体: IsLocalization.lift fun y : Submonoid.powers x =>
    show IsUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn]; rw [g.map_pow]
      exact IsUnit.map (powMonoidHom n : P ->* P) hg

@[simp]

Depends on / 依赖: IsLocalization, IsLocalization.lift, IsUnit, IsUnit.map, Submonoid, Submonoid.powers, g.map_pow, map_pow, powMonoidHom, powers
-/
noncomputable def lift (hg : IsUnit (g x)) : S ->+* P :=
  IsLocalization.lift fun y : Submonoid.powers x =>
    show IsUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn]; rw [g.map_pow]
      exact IsUnit.map (powMonoidHom n : P ->* P) hg

@[simp]
/--
theorem `lift_eq` / 定理 `lift_eq`

English:
theorem lift_eq
  given: (hg : IsUnit (g x)) (a : R)
  statement: lift x hg (algebraMap R S a) = g a
  proof: IsLocalization.lift_eq _ _

@[simp]

中文:
定理 lift_eq
  条件: (hg : 是单位 (g x)) (a : R)
  结论: lift x hg (algebraMap R S a) = g a
  证明: IsLocalization.lift_eq _ _

@[simp]

Depends on / 依赖: IsLocalization, IsLocalization.lift_eq, lift_eq
-/
theorem lift_eq (hg : IsUnit (g x)) (a : R) : lift x hg (algebraMap R S a) = g a :=
  IsLocalization.lift_eq _ _

@[simp]
/--
theorem `lift_comp` / 定理 `lift_comp`

English:
theorem lift_comp
  given: (hg : IsUnit (g x))
  statement: (lift x hg).comp (algebraMap R S) = g
  proof: IsLocalization.lift_comp _

中文:
定理 lift_comp
  条件: (hg : 是单位 (g x))
  结论: (lift x hg).comp (algebraMap R S) = g
  证明: IsLocalization.lift_comp _

Depends on / 依赖: IsLocalization, IsLocalization.lift_comp, lift_comp
-/
theorem lift_comp (hg : IsUnit (g x)) : (lift x hg).comp (algebraMap R S) = g :=
  IsLocalization.lift_comp _

section liftAlgHom

variable {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A S] [Algebra A P]
  [IsScalarTower A R S] {f : R ->ₐ[A] P} (hf : IsUnit (f x))
include hf

/--
Definition of `liftAlgHom` / `liftAlgHom` 的定义

English:
definition liftAlgHom
  signature: : S ->ₐ[A] P where
  body: lift x hf
  commutes' r := by simp [IsScalarTower.algebraMap_apply A R S]

中文:
定义 liftAlgHom
  签名: : S ->ₐ[A] P where
  定义体: lift x hf
  commutes' r := by simp [IsScalarTower.algebraMap_apply A R S]
-/
noncomputable def liftAlgHom : S ->ₐ[A] P where
  __ := lift x hf
  commutes' r := by simp [IsScalarTower.algebraMap_apply A R S]

/--
theorem `liftAlgHom_toRingHom` / 定理 `liftAlgHom_toRingHom`

English:
theorem liftAlgHom_toRingHom
  statement: (liftAlgHom x hf : S ->ₐ[A] P).toRingHom = lift x hf
  proof: rfl

@[simp]

中文:
定理 liftAlgHom_toRingHom
  结论: (liftAlgHom x hf : S ->ₐ[A] P).toRingHom = lift x hf
  证明: rfl

@[simp]
-/
theorem liftAlgHom_toRingHom : (liftAlgHom x hf : S ->ₐ[A] P).toRingHom = lift x hf := rfl

@[simp]
/--
theorem `coe_liftAlgHom` / 定理 `coe_liftAlgHom`

English:
theorem coe_liftAlgHom
  statement: ⇑(liftAlgHom x hf : S ->ₐ[A] P) = lift x hf
  proof: rfl

中文:
定理 coe_liftAlgHom
  结论: ⇑(liftAlgHom x hf : S ->ₐ[A] P) = lift x hf
  证明: rfl
-/
theorem coe_liftAlgHom : ⇑(liftAlgHom x hf : S ->ₐ[A] P) = lift x hf := rfl

/--
theorem `liftAlgHom_apply` / 定理 `liftAlgHom_apply`

English:
theorem liftAlgHom_apply
  given: (s : S)
  statement: liftAlgHom x hf s = lift x hf s
  proof: rfl

中文:
定理 liftAlgHom_apply
  条件: (s : S)
  结论: liftAlgHom x hf s = lift x hf s
  证明: rfl
-/
theorem liftAlgHom_apply (s : S) : liftAlgHom x hf s = lift x hf s := rfl

end liftAlgHom

/--
Definition of `awayToAwayLeft` / `awayToAwayLeft` 的定义

English:
definition awayToAwayLeft
  signature: (y : R) [Algebra R P] [IsLocalization.Away (y * x) P]
  body: lift x isUnit_of_dvd (y * x) (dvd_mul_left _ _)

中文:
定义 awayToAwayLeft
  签名: (y : R) [代数 R P] [是Localization.Away (y * x) P]
  定义体: lift x isUnit_of_dvd (y * x) (dvd_mul_left _ _)

Depends on / 依赖: dvd_mul_left, isUnit_of_dvd
-/
noncomputable def awayToAwayLeft (y : R) [Algebra R P] [IsLocalization.Away (y * x) P] : S ->+* P :=
lift x isUnit_of_dvd (y * x) (dvd_mul_left _ _)

/--
Definition of `awayToAwayRight` / `awayToAwayRight` 的定义

English:
definition awayToAwayRight
  signature: (y : R) [Algebra R P] [IsLocalization.Away (x * y) P]
  body: lift x isUnit_of_dvd (x * y) (dvd_mul_right _ _)

中文:
定义 awayToAwayRight
  签名: (y : R) [代数 R P] [是Localization.Away (x * y) P]
  定义体: lift x isUnit_of_dvd (x * y) (dvd_mul_right _ _)

Depends on / 依赖: dvd_mul_right, isUnit_of_dvd
-/
noncomputable def awayToAwayRight (y : R) [Algebra R P] [IsLocalization.Away (x * y) P] : S ->+* P :=
lift x isUnit_of_dvd (x * y) (dvd_mul_right _ _)

/--
theorem `awayToAwayLeft_eq` / 定理 `awayToAwayLeft_eq`

English:
theorem awayToAwayLeft_eq
  given: (y : R) [Algebra R P] [IsLocalization.Away (y * x) P] (a : R)
  proof: lift_eq _ _ _

中文:
定理 awayToAwayLeft_eq
  条件: (y : R) [代数 R P] [是Localization.Away (y * x) P] (a : R)
  证明: lift_eq _ _ _

Depends on / 依赖: lift_eq
-/
theorem awayToAwayLeft_eq (y : R) [Algebra R P] [IsLocalization.Away (y * x) P] (a : R) :
    awayToAwayLeft x y (algebraMap R S a) = algebraMap R P a :=
  lift_eq _ _ _

/--
theorem `awayToAwayRight_eq` / 定理 `awayToAwayRight_eq`

English:
theorem awayToAwayRight_eq
  given: (y : R) [Algebra R P] [IsLocalization.Away (x * y) P] (a : R)
  proof: lift_eq _ _ _

中文:
定理 awayToAwayRight_eq
  条件: (y : R) [代数 R P] [是Localization.Away (x * y) P] (a : R)
  证明: lift_eq _ _ _

Depends on / 依赖: lift_eq
-/
theorem awayToAwayRight_eq (y : R) [Algebra R P] [IsLocalization.Away (x * y) P] (a : R) :
    awayToAwayRight x y (algebraMap R S a) = algebraMap R P a :=
  lift_eq _ _ _

variable (S) (Q : Type*) [CommSemiring Q] [Algebra P Q]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* P) (r : R) [IsLocalization.Away r S]
  body: IsLocalization.map Q f
    (show Submonoid.powers r <= (Submonoid.powers (f r)).comap f by
      rintro x ⟨n, rfl⟩
      use n
      simp)

中文:
定义 map
  签名: (f : R ->+* P) (r : R) [是Localization.Away r S]
  定义体: IsLocalization.map Q f
    (show Submonoid.powers r <= (Submonoid.powers (f r)).comap f by
      rintro x ⟨n, rfl⟩
      use n
      simp)

Depends on / 依赖: IsLocalization, IsLocalization.map, Submonoid, Submonoid.powers, powers
-/
noncomputable def map (f : R ->+* P) (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (f r) Q] : S ->+* Q :=
  IsLocalization.map Q f
    (show Submonoid.powers r <= (Submonoid.powers (f r)).comap f by
      rintro x ⟨n, rfl⟩
      use n
      simp)

/--
lemma `map_injective_iff` / 引理 `map_injective_iff`

English:
lemma map_injective_iff
  statement: {S : Type*} [CommRing S] [Algebra R S]
  proof: by
  rw [injective_iff_map_eq_zero]
  trans forall a n, f r ^ n * f a = 0 -> exists m, r ^ m * a = 0
  · simp [(IsLocalization.mk'_surjective (.powers r)).forall, Submonoid.mem_powers_iff,
      IsLocalization.Away.map, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff]
  · refine ⟨fun H x hx =

中文:
引理 map_injective_iff
  结论: {S : 类型} [交换环 S] [代数 R S]
  证明: by
  rw [injective_iff_map_eq_zero]
  trans forall a n, f r ^ n * f a = 0 -> exists m, r ^ m * a = 0
  · simp [(IsLocalization.mk'_surjective (.powers r)).forall, Submonoid.mem_powers_iff,
      IsLocalization.Away.map, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff]
  · refine ⟨fun H x hx =

Depends on / 依赖: IsLocalization, IsLocalization.Away.map, IsLocalization.map_mk, IsLocalization.mk, Submonoid, Submonoid.mem_powers_iff, _eq_zero_iff, _surjective, injective_iff_map_eq_zero, map_mk, mem_powers_iff, mul_assoc, pow_add, powers
-/
lemma map_injective_iff {S : Type*} [CommRing S] [Algebra R S]
    (f : R ->+* P) (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (f r) Q] :
    Function.Injective (map S Q f r) ↔ forall a, f a = 0 -> exists n, r ^ n * a = 0 := by
  rw [injective_iff_map_eq_zero]
  trans forall a n, f r ^ n * f a = 0 -> exists m, r ^ m * a = 0
  · simp [(IsLocalization.mk'_surjective (.powers r)).forall, Submonoid.mem_powers_iff,
      IsLocalization.Away.map, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff]
  · refine ⟨fun H x hx => H x 0 (by simpa), fun H a n ha => ?_⟩
    obtain ⟨m, hm⟩ := H (r ^ n * a) (by simpa)
    exact ⟨m + n, by simp [pow_add, mul_assoc, *]⟩

/--
lemma `map_surjective_iff` / 引理 `map_surjective_iff`

English:
lemma map_surjective_iff
  statement: (f : R ->+* P) (r : R) [IsLocalization.Away r S]
  proof: by
  trans forall a n, exists b m k, f (r ^ (k + n) * b) = f r ^ (k + m) * a
  · simp [Function.Surjective, (IsLocalization.mk'_surjective (.powers (f r))).forall, ← map_pow,
      (IsLocalization.mk'_surjective (.powers r)).exists, Submonoid.mem_powers_iff, pow_add,
      IsLocalization.Away.map, I

中文:
引理 map_surjective_iff
  结论: (f : R ->+* P) (r : R) [是Localization.Away r S]
  证明: by
  trans forall a n, exists b m k, f (r ^ (k + n) * b) = f r ^ (k + m) * a
  · simp [Function.Surjective, (IsLocalization.mk'_surjective (.powers (f r))).forall, ← map_pow,
      (IsLocalization.mk'_surjective (.powers r)).exists, Submonoid.mem_powers_iff, pow_add,
      IsLocalization.Away.map, I

Depends on / 依赖: Function, Function.Surjective, IsLocalization, IsLocalization.Away.map, IsLocalization.eq_iff_exists, IsLocalization.map_mk, IsLocalization.mk, Submonoid, Submonoid.mem_powers_iff, Surjective, _eq_iff_eq, _surjective, choose_spec, choose_spec.choose_spec.choose_spec, eq_iff_exists, map_mk, map_mul, map_pow, mem_powers_iff, mul_assoc
-/
lemma map_surjective_iff (f : R ->+* P) (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (f r) Q] :
    Function.Surjective (map S Q f r) ↔ forall a, exists b m, f b = f r ^ m * a := by
  trans forall a n, exists b m k, f (r ^ (k + n) * b) = f r ^ (k + m) * a
  · simp [Function.Surjective, (IsLocalization.mk'_surjective (.powers (f r))).forall, ← map_pow,
      (IsLocalization.mk'_surjective (.powers r)).exists, Submonoid.mem_powers_iff, pow_add,
      IsLocalization.Away.map, IsLocalization.map_mk', ← mul_assoc,
      IsLocalization.mk'_eq_iff_eq, ← map_mul, IsLocalization.eq_iff_exists (.powers (f r))]
  · refine ⟨fun H x => ⟨_, _, (H x 0).choose_spec.choose_spec.choose_spec⟩, fun H a n => ?_⟩
    obtain ⟨b, m, e⟩ := H a
    exact ⟨b, n + m, 0, by simp [e, pow_add]; ring_nf⟩

section Algebra

variable {A : Type*} [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]
variable (Aₚ : Type*) [CommSemiring Aₚ] [Algebra A Aₚ] [Algebra R Aₚ] [IsScalarTower R A Aₚ]
variable (Bₚ : Type*) [CommSemiring Bₚ] [Algebra B Bₚ] [Algebra R Bₚ] [IsScalarTower R B Bₚ]

instance {f : A ->+* B} (a : A) [Away (f a) Bₚ] : IsLocalization (.map f (.powers a)) Bₚ := by
  simpa

instance (x : R) [IsLocalization.Away (algebraMap R A x) Aₚ] :
    IsLocalization (Algebra.algebraMapSubmonoid A (.powers x)) Aₚ := by
  simpa

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapₐ` / `mapₐ` 的定义

English:
definition mapₐ
  signature: (f : A ->ₐ[R] B) (a : A) [Away a Aₚ] [Away (f a) Bₚ]
  body: ⟨map Aₚ Bₚ f.toRingHom a, fun r => by
    dsimp only [AlgHom.toRingHom_eq_coe, map, RingHom.coe_coe, OneHom.toFun_eq_coe]
    rw [IsScalarTower.algebraMap_apply R A Aₚ]; rw [IsScalarTower.algebraMap_eq R B Bₚ]
    simp⟩

@[simp]

中文:
定义 mapₐ
  签名: (f : A ->ₐ[R] B) (a : A) [Away a Aₚ] [Away (f a) Bₚ]
  定义体: ⟨map Aₚ Bₚ f.toRingHom a, fun r => by
    dsimp only [AlgHom.toRingHom_eq_coe, map, RingHom.coe_coe, OneHom.toFun_eq_coe]
    rw [IsScalarTower.algebraMap_apply R A Aₚ]; rw [IsScalarTower.algebraMap_eq R B Bₚ]
    simp⟩

@[simp]

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_eq, OneHom, OneHom.toFun_eq_coe, RingHom, RingHom.coe_coe, algebraMap_apply, algebraMap_eq, coe_coe, f.toRingHom, toFun_eq_coe, toRingHom, toRingHom_eq_coe
-/
noncomputable def mapₐ (f : A ->ₐ[R] B) (a : A) [Away a Aₚ] [Away (f a) Bₚ] : Aₚ ->ₐ[R] Bₚ :=
  ⟨map Aₚ Bₚ f.toRingHom a, fun r => by
    dsimp only [AlgHom.toRingHom_eq_coe, map, RingHom.coe_coe, OneHom.toFun_eq_coe]
    rw [IsScalarTower.algebraMap_apply R A Aₚ]; rw [IsScalarTower.algebraMap_eq R B Bₚ]
    simp⟩

@[simp]
/--
lemma `mapₐ_apply` / 引理 `mapₐ_apply`

English:
lemma mapₐ_apply
  given: (f : A ->ₐ[R] B) (a : A) [Away a Aₚ] [Away (f a) Bₚ] (x : Aₚ)
  proof: rfl

中文:
引理 mapₐ_apply
  条件: (f : A ->ₐ[R] B) (a : A) [Away a Aₚ] [Away (f a) Bₚ] (x : Aₚ)
  证明: rfl
-/
lemma mapₐ_apply (f : A ->ₐ[R] B) (a : A) [Away a Aₚ] [Away (f a) Bₚ] (x : Aₚ) :
    mapₐ Aₚ Bₚ f a x = map Aₚ Bₚ f.toRingHom a x :=
  rfl

variable {Aₚ} {Bₚ}

/--
lemma `mapₐ_injective_of_injective` / 引理 `mapₐ_injective_of_injective`

English:
lemma mapₐ_injective_of_injective
  statement: {f : A ->ₐ[R] B} (a : A) [Away a Aₚ] [Away (f a) Bₚ]
  proof: IsLocalization.map_injective_of_injective _ _ _ hf

中文:
引理 mapₐ_injective_of_injective
  结论: {f : A ->ₐ[R] B} (a : A) [Away a Aₚ] [Away (f a) Bₚ]
  证明: IsLocalization.map_injective_of_injective _ _ _ hf

Depends on / 依赖: IsLocalization, IsLocalization.map_injective_of_injective, map_injective_of_injective
-/
lemma mapₐ_injective_of_injective {f : A ->ₐ[R] B} (a : A) [Away a Aₚ] [Away (f a) Bₚ]
    (hf : Function.Injective f) : Function.Injective (mapₐ Aₚ Bₚ f a) :=
  IsLocalization.map_injective_of_injective _ _ _ hf

/--
lemma `mapₐ_surjective_of_surjective` / 引理 `mapₐ_surjective_of_surjective`

English:
lemma mapₐ_surjective_of_surjective
  statement: {f : A ->ₐ[R] B} (a : A) [Away a Aₚ] [Away (f a) Bₚ]
  proof: have : IsLocalization (Submonoid.map f.toRingHom (Submonoid.powers a)) Bₚ := by
    simp only [AlgHom.toRingHom_eq_coe, Submonoid.map_powers, RingHom.coe_coe]
    infer_instance
  IsLocalization.map_surjective_of_surjective _ _ _ hf

中文:
引理 mapₐ_surjective_of_surjective
  结论: {f : A ->ₐ[R] B} (a : A) [Away a Aₚ] [Away (f a) Bₚ]
  证明: have : IsLocalization (Submonoid.map f.toRingHom (Submonoid.powers a)) Bₚ := by
    simp only [AlgHom.toRingHom_eq_coe, Submonoid.map_powers, RingHom.coe_coe]
    infer_instance
  IsLocalization.map_surjective_of_surjective _ _ _ hf

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, IsLocalization, IsLocalization.map_surjective_of_surjective, RingHom, RingHom.coe_coe, Submonoid, Submonoid.map, Submonoid.map_powers, Submonoid.powers, coe_coe, f.toRingHom, infer_instance, map_powers, map_surjective_of_surjective, powers, toRingHom, toRingHom_eq_coe
-/
lemma mapₐ_surjective_of_surjective {f : A ->ₐ[R] B} (a : A) [Away a Aₚ] [Away (f a) Bₚ]
    (hf : Function.Surjective f) : Function.Surjective (mapₐ Aₚ Bₚ f a) :=
  have : IsLocalization (Submonoid.map f.toRingHom (Submonoid.powers a)) Bₚ := by
    simp only [AlgHom.toRingHom_eq_coe, Submonoid.map_powers, RingHom.coe_coe]
    infer_instance
  IsLocalization.map_surjective_of_surjective _ _ _ hf

end Algebra

/--
lemma `mul` / 引理 `mul`

English:
lemma mul
  statement: (T : Type*) [CommSemiring T] [Algebra S T]
  proof: by
  refine mk _ ?_ (fun z => ?_) (fun a b h => ?_)
  · simp only [map_mul, IsUnit.mul_iff, IsScalarTower.algebraMap_apply R S T]
    exact ⟨algebraMap_isUnit _, IsUnit.map _ (algebraMap_isUnit x)⟩
  · obtain ⟨m, p, hpq⟩ := surj (algebraMap R S y) z
    obtain ⟨n, a, hab⟩ := surj x p
    use m + n, 

中文:
引理 mul
  结论: (T : 类型) [交换半环 T] [代数 S T]
  证明: by
  refine mk _ ?_ (fun z => ?_) (fun a b h => ?_)
  · simp only [map_mul, IsUnit.mul_iff, IsScalarTower.algebraMap_apply R S T]
    exact ⟨algebraMap_isUnit _, IsUnit.map _ (algebraMap_isUnit x)⟩
  · obtain ⟨m, p, hpq⟩ := surj (algebraMap R S y) z
    obtain ⟨n, a, hab⟩ := surj x p
    use m + n, 

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, IsUnit, IsUnit.map, IsUnit.mul_iff, algebraMap, algebraMap_apply, algebraMap_isUnit, exists_of_e, map_mul, map_pow, mul_assoc, mul_iff, mul_pow, pow_add, repeat
-/
lemma mul (T : Type*) [CommSemiring T] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] (x y : R)
    [IsLocalization.Away x S] [IsLocalization.Away (algebraMap R S y) T] :
    IsLocalization.Away (y * x) T := by
  refine mk _ ?_ (fun z => ?_) (fun a b h => ?_)
  · simp only [map_mul, IsUnit.mul_iff, IsScalarTower.algebraMap_apply R S T]
    exact ⟨algebraMap_isUnit _, IsUnit.map _ (algebraMap_isUnit x)⟩
  · obtain ⟨m, p, hpq⟩ := surj (algebraMap R S y) z
    obtain ⟨n, a, hab⟩ := surj x p
    use m + n, a * x ^ m * y ^ n
    simp only [mul_pow, pow_add, map_pow, map_mul, ← mul_assoc, hpq,
      IsScalarTower.algebraMap_apply R S T, ← hab]
    ring
  · repeat rw [IsScalarTower.algebraMap_apply R S T] at h
    obtain ⟨n, hn⟩ := exists_of_eq (algebraMap R S y) h
    simp only [← map_pow, ← map_mul, ← map_mul] at hn
    obtain ⟨m, hm⟩ := exists_of_eq x hn
    use n + m
    convert_to y ^ m * x ^ n * (x ^ m * (y ^ n * a)) = y ^ m * x ^ n * (x ^ m * (y ^ n * b))
    · ring
    · ring
    · rw [hm]

/--
lemma `mul'` / 引理 `mul'`

English:
lemma mul'
  statement: (T : Type*) [CommSemiring T] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (x y : R)
  proof: mul_comm x y ▸ mul S T x y

中文:
引理 mul'
  结论: (T : 类型) [交换半环 T] [代数 S T] [代数 R T] [标量塔 R S T] (x y : R)
  证明: mul_comm x y ▸ mul S T x y

Depends on / 依赖: mul_comm
-/
lemma mul' (T : Type*) [CommSemiring T] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (x y : R)
    [IsLocalization.Away x S] [IsLocalization.Away (algebraMap R S y) T] :
    IsLocalization.Away (x * y) T :=
  mul_comm x y ▸ mul S T x y

/-- Localizing the localization of `R` at `x` at the image of `y` is the same as localizing
`R` at `y * x`. -/
instance (x y : R) [IsLocalization.Away x S] :
    IsLocalization.Away (y * x) (Localization.Away (algebraMap R S y)) :=
  IsLocalization.Away.mul S (Localization.Away (algebraMap R S y)) _ _

/-- Localizing the localization of `R` at `x` at the image of `y` is the same as localizing
`R` at `x * y`. -/
instance (x y : R) [IsLocalization.Away x S] :
    IsLocalization.Away (x * y) (Localization.Away (algebraMap R S y)) :=
  IsLocalization.Away.mul' S (Localization.Away (algebraMap R S y)) _ _

/--
lemma `commutes` / 引理 `commutes`

English:
lemma commutes
  statement: {R : Type*} [CommSemiring R] (S₁ S₂ T : Type*) [CommSemiring S₁]
  proof: by
  convert! IsLocalization.commutes S₁ S₂ T (Submonoid.powers x) (Submonoid.powers y)
  ext x
  simp

中文:
引理 commutes
  结论: {R : 类型} [交换半环 R] (S₁ S₂ T : 类型) [交换半环 S₁]
  证明: by
  convert! IsLocalization.commutes S₁ S₂ T (Submonoid.powers x) (Submonoid.powers y)
  ext x
  simp

Depends on / 依赖: IsLocalization, IsLocalization.commutes, Submonoid, Submonoid.powers, commutes, convert, powers
-/
lemma commutes {R : Type*} [CommSemiring R] (S₁ S₂ T : Type*) [CommSemiring S₁]
    [CommSemiring S₂] [CommSemiring T] [Algebra R S₁] [Algebra R S₂] [Algebra R T] [Algebra S₁ T]
    [Algebra S₂ T] [IsScalarTower R S₁ T] [IsScalarTower R S₂ T] (x y : R)
    [IsLocalization.Away x S₁] [IsLocalization.Away y S₂]
    [IsLocalization.Away (algebraMap R S₂ x) T] :
    IsLocalization.Away (algebraMap R S₁ y) T := by
  convert! IsLocalization.commutes S₁ S₂ T (Submonoid.powers x) (Submonoid.powers y)
  ext x
  simp

/--
theorem `isDomain` / 定理 `isDomain`

English:
theorem isDomain
  given: [IsDomain R] {x : R} (hx : x != 0) [IsLocalization.Away x S]
  statement: IsDomain S
  proof: IsLocalization.isDomain_of_le_nonZeroDivisors S
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx)

中文:
定理 isDomain
  条件: [是整环 R] {x : R} (hx : x != 0) [是Localization.Away x S]
  结论: 是整环 S
  证明: IsLocalization.isDomain_of_le_nonZeroDivisors S
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx)

Depends on / 依赖: IsLocalization, IsLocalization.isDomain_of_le_nonZeroDivisors, completeSpace_coe, isClosed_eq, isDomain_of_le_nonZeroDivisors, map_continuous, powers_le_nonZeroDivisors_of_noZeroDivisors
-/
theorem isDomain [IsDomain R] {x : R} (hx : x != 0) [IsLocalization.Away x S] : IsDomain S :=
  IsLocalization.isDomain_of_le_nonZeroDivisors S
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx)

end Away

end Away

variable [IsLocalization M S]

section AtUnits

variable (R) (S)

/--
Definition of `atUnit` / `atUnit` 的定义

English:
definition atUnit
  signature: (x : R) (e : IsUnit x) [IsLocalization.Away x S]
  body: atUnits R (Submonoid.powers x)
    (by rwa [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff])

中文:
定义 atUnit
  签名: (x : R) (e : 是单位 x) [是Localization.Away x S]
  定义体: atUnits R (Submonoid.powers x)
    (by rwa [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff])

Depends on / 依赖: Set.singleton_subset_iff, Submonoid, Submonoid.closure_le, Submonoid.powers, Submonoid.powers_eq_closure, atUnits, closure_le, powers, powers_eq_closure, singleton_subset_iff
-/
noncomputable def atUnit (x : R) (e : IsUnit x) [IsLocalization.Away x S] : R ≃ₐ[R] S :=
  atUnits R (Submonoid.powers x)
    (by rwa [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff])

/--
Definition of `atOne` / `atOne` 的定义

English:
definition atOne
  signature: [IsLocalization.Away (1 : R) S]
  body: @atUnit R _ S _ _ (1 : R) isUnit_one _

中文:
定义 atOne
  签名: [是Localization.Away (1 : R) S]
  定义体: @atUnit R _ S _ _ (1 : R) isUnit_one _

Depends on / 依赖: atUnit, isUnit_one
-/
noncomputable def atOne [IsLocalization.Away (1 : R) S] : R ≃ₐ[R] S :=
  @atUnit R _ S _ _ (1 : R) isUnit_one _

/--
theorem `away_of_isUnit_of_bijective` / 定理 `away_of_isUnit_of_bijective`

English:
theorem away_of_isUnit_of_bijective
  statement: {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S]
  proof: .of_le_isUnit_of_bijective (by simpa [Submonoid.powers_le] using! hr.map (algebraMap R S)) H

中文:
定理 away_of_isUnit_of_bijective
  结论: {R : 类型} (S : 类型) [交换半环 R] [交换半环 S]
  证明: .of_le_isUnit_of_bijective (by simpa [Submonoid.powers_le] using! hr.map (algebraMap R S)) H

Depends on / 依赖: Submonoid, Submonoid.powers_le, algebraMap, hr.map, of_le_isUnit_of_bijective, powers_le
-/
theorem away_of_isUnit_of_bijective {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] {r : R} (hr : IsUnit r) (H : Function.Bijective (algebraMap R S)) :
    IsLocalization.Away r S :=
  .of_le_isUnit_of_bijective (by simpa [Submonoid.powers_le] using! hr.map (algebraMap R S)) H

variable {R S}

/--
lemma `Away.mul_of_isUnit` / 引理 `Away.mul_of_isUnit`

English:
lemma Away.mul_of_isUnit
  given: (x y : R) [IsLocalization.Away x S] (h : IsUnit (algebraMap R S y))
  proof: have : Away (algebraMap R S y) S := away_of_isUnit_of_bijective _ h Function.bijective_id
  .mul' S _ _ _

中文:
引理 Away.mul_of_isUnit
  条件: (x y : R) [是Localization.Away x S] (h : 是单位 (algebraMap R S y))
  证明: have : Away (algebraMap R S y) S := away_of_isUnit_of_bijective _ h Function.bijective_id
  .mul' S _ _ _

Depends on / 依赖: Function, Function.bijective_id, algebraMap, away_of_isUnit_of_bijective, bijective_id
-/
lemma Away.mul_of_isUnit (x y : R) [IsLocalization.Away x S] (h : IsUnit (algebraMap R S y)) :
    IsLocalization.Away (x * y) S :=
  have : Away (algebraMap R S y) S := away_of_isUnit_of_bijective _ h Function.bijective_id
  .mul' S _ _ _

/--
lemma `Away.mul_of_isUnit'` / 引理 `Away.mul_of_isUnit'`

English:
lemma Away.mul_of_isUnit'
  given: (x y : R) [IsLocalization.Away y S] (h : IsUnit (algebraMap R S x))
  proof: have : Away (algebraMap R S x) S := away_of_isUnit_of_bijective _ h Function.bijective_id
  .mul S _ _ _

中文:
引理 Away.mul_of_isUnit'
  条件: (x y : R) [是Localization.Away y S] (h : 是单位 (algebraMap R S x))
  证明: have : Away (algebraMap R S x) S := away_of_isUnit_of_bijective _ h Function.bijective_id
  .mul S _ _ _

Depends on / 依赖: Function, Function.bijective_id, algebraMap, away_of_isUnit_of_bijective, bijective_id
-/
lemma Away.mul_of_isUnit' (x y : R) [IsLocalization.Away y S] (h : IsUnit (algebraMap R S x)) :
    IsLocalization.Away (x * y) S :=
  have : Away (algebraMap R S x) S := away_of_isUnit_of_bijective _ h Function.bijective_id
  .mul S _ _ _

/--
lemma `Away.mul_of_associated` / 引理 `Away.mul_of_associated`

English:
lemma Away.mul_of_associated
  statement: (x z : R) (y : S) [IsLocalization.Away x S]
  proof: by
  have : Away (algebraMap R S z) T := by rwa [iff_of_associated h]
  exact .mul' S _ _ _

中文:
引理 Away.mul_of_associated
  结论: (x z : R) (y : S) [是Localization.Away x S]
  证明: by
  have : Away (algebraMap R S z) T := by rwa [iff_of_associated h]
  exact .mul' S _ _ _

Depends on / 依赖: algebraMap, iff_of_associated
-/
lemma Away.mul_of_associated (x z : R) (y : S) [IsLocalization.Away x S]
    {T : Type*} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalization.Away y T]
    (h : Associated (algebraMap R S z) y) : IsLocalization.Away (x * z) T := by
  have : Away (algebraMap R S z) T := by rwa [iff_of_associated h]
  exact .mul' S _ _ _

end AtUnits

section Prod

/--
lemma `Away.algebraMap_surjective_of_isIdempotentElem` / 引理 `Away.algebraMap_surjective_of_isIdempotentElem`

English:
lemma Away.algebraMap_surjective_of_isIdempotentElem
  proof: by
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers e) x
  suffices exists a k, e ^ k * (a * e ^ n) = e ^ k * x by
    simpa [IsLocalization.eq_mk'_iff_mul_eq, ← map_pow, ← map_mul,
      IsLocalization.eq_iff_exists (.powers e), Submonoid.mem_powers_iff]
  refine ⟨x

中文:
引理 Away.algebraMap_surjective_of_isIdempotentElem
  证明: by
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers e) x
  suffices exists a k, e ^ k * (a * e ^ n) = e ^ k * x by
    simpa [IsLocalization.eq_mk'_iff_mul_eq, ← map_pow, ← map_mul,
      IsLocalization.eq_iff_exists (.powers e), Submonoid.mem_powers_iff]
  refine ⟨x

Depends on / 依赖: IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.eq_mk, IsLocalization.exists_mk, Submonoid, Submonoid.mem_powers_iff, _iff_mul_eq, eq_iff_exists, eq_mk, exists_mk, he.pow_succ_eq, map_mul, map_pow, mem_powers_iff, pow_succ_eq, powers
-/
lemma Away.algebraMap_surjective_of_isIdempotentElem
    (e : R) (he : IsIdempotentElem e) [IsLocalization.Away e S] :
    Function.Surjective (algebraMap R S) := by
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers e) x
  suffices exists a k, e ^ k * (a * e ^ n) = e ^ k * x by
    simpa [IsLocalization.eq_mk'_iff_mul_eq, ← map_pow, ← map_mul,
      IsLocalization.eq_iff_exists (.powers e), Submonoid.mem_powers_iff]
  refine ⟨x, 1, ?_⟩
  trans e ^ (n + 1) * x
  · ring
  · rw [he.pow_succ_eq]; ring

/--
lemma `away_of_isIdempotentElem_of_mul` / 引理 `away_of_isIdempotentElem_of_mul`

English:
lemma away_of_isIdempotentElem_of_mul
  proof: by
    obtain ⟨r, n, rfl⟩ := r
    simp [show algebraMap R S e = 1 by rw [← (algebraMap R S).map_one, H, mul_one, he]]
  surj z := by
    obtain ⟨z, rfl⟩ := H' z
    exact ⟨⟨z, 1⟩, by simp⟩
  exists_of_eq {x y} h := ⟨⟨e, Submonoid.mem_powers e⟩, (H x y).mp h⟩

中文:
引理 away_of_isIdempotentElem_of_mul
  证明: by
    obtain ⟨r, n, rfl⟩ := r
    simp [show algebraMap R S e = 1 by rw [← (algebraMap R S).map_one, H, mul_one, he]]
  surj z := by
    obtain ⟨z, rfl⟩ := H' z
    exact ⟨⟨z, 1⟩, by simp⟩
  exists_of_eq {x y} h := ⟨⟨e, Submonoid.mem_powers e⟩, (H x y).mp h⟩

Depends on / 依赖: Submonoid, Submonoid.mem_powers, algebraMap, exists_of_eq, map_one, mem_powers, mul_one
-/
lemma away_of_isIdempotentElem_of_mul
    {e : R} (he : IsIdempotentElem e)
    (H : forall x y, algebraMap R S x = algebraMap R S y ↔ e * x = e * y)
    (H' : Function.Surjective (algebraMap R S)) :
    IsLocalization.Away e S where
  map_units r := by
    obtain ⟨r, n, rfl⟩ := r
    simp [show algebraMap R S e = 1 by rw [← (algebraMap R S).map_one, H, mul_one, he]]
  surj z := by
    obtain ⟨z, rfl⟩ := H' z
    exact ⟨⟨z, 1⟩, by simp⟩
  exists_of_eq {x y} h := ⟨⟨e, Submonoid.mem_powers e⟩, (H x y).mp h⟩

/--
lemma `away_of_isIdempotentElem` / 引理 `away_of_isIdempotentElem`

English:
lemma away_of_isIdempotentElem
  statement: {R S} [CommRing R] [CommRing S] [Algebra R S]
  proof: away_of_isIdempotentElem_of_mul he (fun x y => by
    rw [← sub_eq_zero]; rw [← map_sub]; rw [← RingHom.mem_ker]; rw [H]; rw [← he.ker_toSpanSingleton_eq_span]; rw [LinearMap.mem_ker]; rw [LinearMap.toSpanSingleton_apply]; rw [sub_smul]; rw [sub_eq_zero]
    simp_rw [mul_comm e, smul_eq_mul]) H'

中文:
引理 away_of_isIdempotentElem
  结论: {R S} [交换环 R] [交换环 S] [代数 R S]
  证明: away_of_isIdempotentElem_of_mul he (fun x y => by
    rw [← sub_eq_zero]; rw [← map_sub]; rw [← RingHom.mem_ker]; rw [H]; rw [← he.ker_toSpanSingleton_eq_span]; rw [LinearMap.mem_ker]; rw [LinearMap.toSpanSingleton_apply]; rw [sub_smul]; rw [sub_eq_zero]
    simp_rw [mul_comm e, smul_eq_mul]) H'

Depends on / 依赖: LinearMap, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, RingHom, RingHom.mem_ker, away_of_isIdempotentElem_of_mul, he.ker_toSpanSingleton_eq_span, ker_toSpanSingleton_eq_span, map_sub, mem_ker, mul_comm, simp_rw, smul_eq_mul, sub_eq_zero, sub_smul, toSpanSingleton_apply
-/
lemma away_of_isIdempotentElem {R S} [CommRing R] [CommRing S] [Algebra R S]
    {e : R} (he : IsIdempotentElem e)
    (H : RingHom.ker (algebraMap R S) = Ideal.span {1 - e})
    (H' : Function.Surjective (algebraMap R S)) :
    IsLocalization.Away e S :=
  away_of_isIdempotentElem_of_mul he (fun x y => by
    rw [← sub_eq_zero]; rw [← map_sub]; rw [← RingHom.mem_ker]; rw [H]; rw [← he.ker_toSpanSingleton_eq_span]; rw [LinearMap.mem_ker]; rw [LinearMap.toSpanSingleton_apply]; rw [sub_smul]; rw [sub_eq_zero]
    simp_rw [mul_comm e, smul_eq_mul]) H'

/--
Instance `away_fst` / 实例 `away_fst`

English:
instance away_fst
  signature: {R S} [CommSemiring R] [CommSemiring S]
  body: (RingHom.fst R S).toAlgebra
    IsLocalization.Away (R := R × S) (1, 0) R :=
  letI := (RingHom.fst R S).toAlgebra
  away_of_isIdempotentElem_of_mul (by ext <;> simp)
    (fun ⟨xR, xS⟩ ⟨yR, yS⟩ => show xR = yR ↔ _ by simp) Prod.fst_surjective

中文:
实例 away_fst
  签名: {R S} [交换半环 R] [交换半环 S]
  定义体: (RingHom.fst R S).toAlgebra
    IsLocalization.Away (R := R × S) (1, 0) R :=
  letI := (RingHom.fst R S).toAlgebra
  away_of_isIdempotentElem_of_mul (by ext <;> simp)
    (fun ⟨xR, xS⟩ ⟨yR, yS⟩ => show xR = yR ↔ _ by simp) Prod.fst_surjective

Depends on / 依赖: RingHom, RingHom.fst, toAlgebra
-/
instance away_fst {R S} [CommSemiring R] [CommSemiring S] :
    letI := (RingHom.fst R S).toAlgebra
    IsLocalization.Away (R := R × S) (1, 0) R :=
  letI := (RingHom.fst R S).toAlgebra
  away_of_isIdempotentElem_of_mul (by ext <;> simp)
    (fun ⟨xR, xS⟩ ⟨yR, yS⟩ => show xR = yR ↔ _ by simp) Prod.fst_surjective

/--
Instance `away_snd` / 实例 `away_snd`

English:
instance away_snd
  signature: {R S} [CommSemiring R] [CommSemiring S]
  body: (RingHom.snd R S).toAlgebra
    IsLocalization.Away (R := R × S) (0, 1) S :=
  letI := (RingHom.snd R S).toAlgebra
  away_of_isIdempotentElem_of_mul (by ext <;> simp)
    (fun ⟨xR, xS⟩ ⟨yR, yS⟩ => show xS = yS ↔ _ by simp) Prod.snd_surjective

中文:
实例 away_snd
  签名: {R S} [交换半环 R] [交换半环 S]
  定义体: (RingHom.snd R S).toAlgebra
    IsLocalization.Away (R := R × S) (0, 1) S :=
  letI := (RingHom.snd R S).toAlgebra
  away_of_isIdempotentElem_of_mul (by ext <;> simp)
    (fun ⟨xR, xS⟩ ⟨yR, yS⟩ => show xS = yS ↔ _ by simp) Prod.snd_surjective

Depends on / 依赖: RingHom, RingHom.snd, toAlgebra
-/
instance away_snd {R S} [CommSemiring R] [CommSemiring S] :
    letI := (RingHom.snd R S).toAlgebra
    IsLocalization.Away (R := R × S) (0, 1) S :=
  letI := (RingHom.snd R S).toAlgebra
  away_of_isIdempotentElem_of_mul (by ext <;> simp)
    (fun ⟨xR, xS⟩ ⟨yR, yS⟩ => show xS = yS ↔ _ by simp) Prod.snd_surjective

end Prod

section

variable {S T : Type*} [CommRing S] [CommRing T] [Algebra S T]

open scoped Pointwise in
/--
lemma `Away.of_surjective` / 引理 `Away.of_surjective`

English:
lemma Away.of_surjective
  statement: (h₁ : Function.Surjective (algebraMap S T))
  proof: by
  refine .mk _ hr (fun t => ?_) fun x y h => ⟨n, ?_⟩
  · obtain ⟨s, rfl⟩ := h₁ t
    exact ⟨0, by simp⟩
  · rw [← sub_eq_zero, ← mul_sub]
    exact hn ⟨x - y, by simp [h]⟩

中文:
引理 Away.of_surjective
  结论: (h₁ : 函数.满射 (algebraMap S T))
  证明: by
  refine .mk _ hr (fun t => ?_) fun x y h => ⟨n, ?_⟩
  · obtain ⟨s, rfl⟩ := h₁ t
    exact ⟨0, by simp⟩
  · rw [← sub_eq_zero, ← mul_sub]
    exact hn ⟨x - y, by simp [h]⟩

Depends on / 依赖: mul_sub, sub_eq_zero
-/
lemma Away.of_surjective (h₁ : Function.Surjective (algebraMap S T))
    {r : S} (hr : IsUnit (algebraMap S T r))
    (n : Nat) (hn : r ^ n • RingHom.ker (algebraMap S T) <= ⊥) :
    IsLocalization.Away r T := by
  refine .mk _ hr (fun t => ?_) fun x y h => ⟨n, ?_⟩
  · obtain ⟨s, rfl⟩ := h₁ t
    exact ⟨0, by simp⟩
  · rw [← sub_eq_zero, ← mul_sub]
    exact hn ⟨x - y, by simp [h]⟩

open scoped Pointwise in
/--
lemma `Away.of_surjective_of_isScalarTower` / 引理 `Away.of_surjective_of_isScalarTower`

English:
lemma Away.of_surjective_of_isScalarTower
  statement: {R : Type*}
  proof: by
  refine Away.of_surjective h₁ ?_ n ?_
  · rwa [← IsScalarTower.algebraMap_apply]
  · rw [← (RingHom.ker (algebraMap S T)).map_comap_of_surjective _ h₂, ← map_pow,
      ← Ideal.map_pointwise_smul, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq]
    rwa [RingHom.ker_eq_comap_bot (algebraMap R S

中文:
引理 Away.of_surjective_of_isScalarTower
  结论: {R : 类型}
  证明: by
  refine Away.of_surjective h₁ ?_ n ?_
  · rwa [← IsScalarTower.algebraMap_apply]
  · rw [← (RingHom.ker (algebraMap S T)).map_comap_of_surjective _ h₂, ← map_pow,
      ← Ideal.map_pointwise_smul, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq]
    rwa [RingHom.ker_eq_comap_bot (algebraMap R S

Depends on / 依赖: Away.of_surjective, Ideal.map_le_iff_le_comap, Ideal.map_pointwise_smul, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_eq, RingHom, RingHom.comap_ker, RingHom.ker, RingHom.ker_eq_comap_bot, algebraMap, algebraMap_apply, algebraMap_eq, comap_ker, ker_eq_comap_bot, map_comap_of_surjective, map_le_iff_le_comap, map_pointwise_smul, map_pow, of_surjective
-/
lemma Away.of_surjective_of_isScalarTower {R : Type*}
    [CommRing R] [Algebra R S] [Algebra R T] [IsScalarTower R S T]
    (h₁ : Function.Surjective (algebraMap S T))
    (h₂ : Function.Surjective (algebraMap R S))
    (r : R) (hr : IsUnit (algebraMap R T r))
    {n : Nat} (hn : r ^ n • RingHom.ker (algebraMap R T) <= RingHom.ker (algebraMap R S)) :
    IsLocalization.Away (algebraMap R S r) T := by
  refine Away.of_surjective h₁ ?_ n ?_
  · rwa [← IsScalarTower.algebraMap_apply]
  · rw [← (RingHom.ker (algebraMap S T)).map_comap_of_surjective _ h₂, ← map_pow,
      ← Ideal.map_pointwise_smul, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq]
    rwa [RingHom.ker_eq_comap_bot (algebraMap R S), ← Ideal.map_le_iff_le_comap] at hn

end

end IsLocalization

namespace Localization

open IsLocalization

variable {M}

/--
Definition of `awayLift` / `awayLift` 的定义

English:
abbreviation awayLift
  signature: (f : R ->+* P) (r : R) (hr : IsUnit (f r))
  body: IsLocalization.Away.lift r hr

中文:
缩写 awayLift
  签名: (f : R ->+* P) (r : R) (hr : 是单位 (f r))
  定义体: IsLocalization.Away.lift r hr

Depends on / 依赖: IsLocalization, IsLocalization.Away.lift
-/
noncomputable abbrev awayLift (f : R ->+* P) (r : R) (hr : IsUnit (f r)) :
    Localization.Away r ->+* P :=
  IsLocalization.Away.lift r hr

/--
lemma `awayLift_mk` / 引理 `awayLift_mk`

English:
lemma awayLift_mk
  statement: {A : Type*} [CommSemiring A] (f : R ->+* A) (r : R)
  proof: by
  simp [Localization.mk_eq_mk', awayLift, Away.lift, IsLocalization.lift_mk',
    Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight, mul_assoc, ← mul_pow, (mul_comm _ _).trans hv]

中文:
引理 awayLift_mk
  结论: {A : 类型} [交换半环 A] (f : R ->+* A) (r : R)
  证明: by
  simp [Localization.mk_eq_mk', awayLift, Away.lift, IsLocalization.lift_mk',
    Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight, mul_assoc, ← mul_pow, (mul_comm _ _).trans hv]

Depends on / 依赖: Away.lift, IsLocalization, IsLocalization.lift_mk, IsUnit, IsUnit.liftRight, Localization, Localization.mk_eq_mk, Units.mul_inv_eq_iff_eq_mul, awayLift, liftRight, lift_mk, mk_eq_mk, mul_assoc, mul_comm, mul_inv_eq_iff_eq_mul, mul_pow
-/
lemma awayLift_mk {A : Type*} [CommSemiring A] (f : R ->+* A) (r : R)
    (a : R) (v : A) (hv : f r * v = 1) (j : Nat) :
    Localization.awayLift f r (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)
      (Localization.mk a ⟨r ^ j, j, rfl⟩) = f a * v ^ j := by
  simp [Localization.mk_eq_mk', awayLift, Away.lift, IsLocalization.lift_mk',
    Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight, mul_assoc, ← mul_pow, (mul_comm _ _).trans hv]

/--
Definition of `awayMap` / `awayMap` 的定义

English:
abbreviation awayMap
  signature: (f : R ->+* P) (r : R)
  body: IsLocalization.Away.map _ _ f r

中文:
缩写 awayMap
  签名: (f : R ->+* P) (r : R)
  定义体: IsLocalization.Away.map _ _ f r

Depends on / 依赖: IsLocalization, IsLocalization.Away.map
-/
noncomputable abbrev awayMap (f : R ->+* P) (r : R) :
    Localization.Away r ->+* Localization.Away (f r) :=
  IsLocalization.Away.map _ _ f r

/--
lemma `awayMap_injective_iff` / 引理 `awayMap_injective_iff`

English:
lemma awayMap_injective_iff
  given: {R : Type*} [CommRing R] {f : R ->+* S} {r : R}
  proof: IsLocalization.Away.map_injective_iff _ _ _

omit [Algebra R S] in

中文:
引理 awayMap_injective_iff
  条件: {R : 类型} [交换环 R] {f : R ->+* S} {r : R}
  证明: IsLocalization.Away.map_injective_iff _ _ _

omit [Algebra R S] in

Depends on / 依赖: IsLocalization, IsLocalization.Away.map_injective_iff, map_injective_iff
-/
lemma awayMap_injective_iff {R : Type*} [CommRing R] {f : R ->+* S} {r : R} :
    Function.Injective (Localization.awayMap f r) ↔ forall a, f a = 0 -> exists n, r ^ n * a = 0 :=
  IsLocalization.Away.map_injective_iff _ _ _

omit [Algebra R S] in
/--
lemma `awayMap_surjective_iff` / 引理 `awayMap_surjective_iff`

English:
lemma awayMap_surjective_iff
  given: {f : R ->+* S} {r : R}
  proof: IsLocalization.Away.map_surjective_iff _ _ _ _

中文:
引理 awayMap_surjective_iff
  条件: {f : R ->+* S} {r : R}
  证明: IsLocalization.Away.map_surjective_iff _ _ _ _

Depends on / 依赖: IsLocalization, IsLocalization.Away.map_surjective_iff, map_surjective_iff
-/
lemma awayMap_surjective_iff {f : R ->+* S} {r : R} :
    Function.Surjective (Localization.awayMap f r) ↔ forall a, exists b m, f b = f r ^ m * a :=
  IsLocalization.Away.map_surjective_iff _ _ _ _

/--
lemma `awayMap_injective_of_dvd` / 引理 `awayMap_injective_of_dvd`

English:
lemma awayMap_injective_of_dvd
  statement: {R : Type*} [CommRing R] (f : R ->+* S)
  proof: by
  simp only [awayMap_injective_iff] at H ⊢
  obtain ⟨b, rfl⟩ := h
  refine fun x hx => ?_
  obtain ⟨n, hn⟩ := H x hx
  exact ⟨n, by simp [mul_pow, mul_assoc, mul_left_comm (a ^ n), hn]⟩

omit [Algebra R S] in

中文:
引理 awayMap_injective_of_dvd
  结论: {R : 类型} [交换环 R] (f : R ->+* S)
  证明: by
  simp only [awayMap_injective_iff] at H ⊢
  obtain ⟨b, rfl⟩ := h
  refine fun x hx => ?_
  obtain ⟨n, hn⟩ := H x hx
  exact ⟨n, by simp [mul_pow, mul_assoc, mul_left_comm (a ^ n), hn]⟩

omit [Algebra R S] in

Depends on / 依赖: awayMap_injective_iff, mul_assoc, mul_left_comm, mul_pow
-/
lemma awayMap_injective_of_dvd {R : Type*} [CommRing R] (f : R ->+* S)
    {a b : R} (h : a ∣ b) (H : Function.Injective (awayMap f a)) :
    Function.Injective (awayMap f b) := by
  simp only [awayMap_injective_iff] at H ⊢
  obtain ⟨b, rfl⟩ := h
  refine fun x hx => ?_
  obtain ⟨n, hn⟩ := H x hx
  exact ⟨n, by simp [mul_pow, mul_assoc, mul_left_comm (a ^ n), hn]⟩

omit [Algebra R S] in
/--
lemma `awayMap_surjective_of_dvd` / 引理 `awayMap_surjective_of_dvd`

English:
lemma awayMap_surjective_of_dvd
  statement: (f : R ->+* S)
  proof: by
  simp only [awayMap_surjective_iff] at H ⊢
  obtain ⟨b, rfl⟩ := h
  refine fun x => ?_
  obtain ⟨c, m, e⟩ := H x
  exact ⟨b ^ m * c, m, by simp [mul_pow, e, mul_assoc, mul_left_comm]⟩

中文:
引理 awayMap_surjective_of_dvd
  结论: (f : R ->+* S)
  证明: by
  simp only [awayMap_surjective_iff] at H ⊢
  obtain ⟨b, rfl⟩ := h
  refine fun x => ?_
  obtain ⟨c, m, e⟩ := H x
  exact ⟨b ^ m * c, m, by simp [mul_pow, e, mul_assoc, mul_left_comm]⟩

Depends on / 依赖: awayMap_surjective_iff, mul_assoc, mul_left_comm, mul_pow
-/
lemma awayMap_surjective_of_dvd (f : R ->+* S)
    {a b : R} (h : a ∣ b) (H : Function.Surjective (awayMap f a)) :
    Function.Surjective (awayMap f b) := by
  simp only [awayMap_surjective_iff] at H ⊢
  obtain ⟨b, rfl⟩ := h
  refine fun x => ?_
  obtain ⟨c, m, e⟩ := H x
  exact ⟨b ^ m * c, m, by simp [mul_pow, e, mul_assoc, mul_left_comm]⟩

/--
lemma `awayMap_bijective_of_dvd` / 引理 `awayMap_bijective_of_dvd`

English:
lemma awayMap_bijective_of_dvd
  statement: {R : Type*} [CommRing R] (f : R ->+* S)
  proof: ⟨awayMap_injective_of_dvd f h H.1, awayMap_surjective_of_dvd f h H.2⟩

omit [Algebra R S] in

中文:
引理 awayMap_bijective_of_dvd
  结论: {R : 类型} [交换环 R] (f : R ->+* S)
  证明: ⟨awayMap_injective_of_dvd f h H.1, awayMap_surjective_of_dvd f h H.2⟩

omit [Algebra R S] in

Depends on / 依赖: awayMap_injective_of_dvd, awayMap_surjective_of_dvd
-/
lemma awayMap_bijective_of_dvd {R : Type*} [CommRing R] (f : R ->+* S)
    {a b : R} (h : a ∣ b) (H : Function.Bijective (awayMap f a)) :
    Function.Bijective (awayMap f b) :=
  ⟨awayMap_injective_of_dvd f h H.1, awayMap_surjective_of_dvd f h H.2⟩

omit [Algebra R S] in
/--
lemma `awayMap_awayMap_surjective` / 引理 `awayMap_awayMap_surjective`

English:
lemma awayMap_awayMap_surjective
  statement: (f : R ->+* S) (a b : R)
  proof: by
  rw [awayMap_surjective_iff] at H ⊢
  suffices forall (s : S) (n : Nat), exists c l m k, f (a ^ (k + n) * c) =
      f (a ^ (k + l) * b ^ m) * s by
    simpa [Function.Surjective, (IsLocalization.mk'_surjective (.powers (f a))).forall, ← map_pow,
      (IsLocalization.mk'_surjective (.powers a))

中文:
引理 awayMap_awayMap_surjective
  结论: (f : R ->+* S) (a b : R)
  证明: by
  rw [awayMap_surjective_iff] at H ⊢
  suffices forall (s : S) (n : Nat), exists c l m k, f (a ^ (k + n) * c) =
      f (a ^ (k + l) * b ^ m) * s by
    simpa [Function.Surjective, (IsLocalization.mk'_surjective (.powers (f a))).forall, ← map_pow,
      (IsLocalization.mk'_surjective (.powers a))

Depends on / 依赖: Function, Function.Surjective, IsLocalization, IsLocalization.Away.map, IsLocalization.eq_iff_exists, IsLocalization.map_mk, IsLocalization.mk, Localization, Localization.awayMap, Submonoid, Submonoid.mem_powers_iff, Surjective, _eq_iff_eq, _surjective, awayMap, awayMap_surjective_iff, eq_iff_exists, map_mk, map_mul, map_pow
-/
lemma awayMap_awayMap_surjective (f : R ->+* S) (a b : R)
    (H : Function.Surjective (awayMap f (a * b))) :
    Function.Surjective (awayMap (awayMap f a) (algebraMap _ _ b)) := by
  rw [awayMap_surjective_iff] at H ⊢
  suffices forall (s : S) (n : Nat), exists c l m k, f (a ^ (k + n) * c) =
      f (a ^ (k + l) * b ^ m) * s by
    simpa [Function.Surjective, (IsLocalization.mk'_surjective (.powers (f a))).forall, ← map_pow,
      (IsLocalization.mk'_surjective (.powers a)).exists, Submonoid.mem_powers_iff, pow_add,
      Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk', ← mul_assoc,
      IsLocalization.mk'_eq_iff_eq, ← map_mul, IsLocalization.eq_iff_exists (.powers (f a)),
      IsLocalization.mul_mk'_eq_mk'_of_mul]
  intro s n
  obtain ⟨c, m, e⟩ := H s
  exact ⟨c, n + m, m, 0, by simp [e, pow_add]; ring⟩

variable {A : Type*} [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]

/--
Definition of `awayMapₐ` / `awayMapₐ` 的定义

English:
abbreviation awayMapₐ
  signature: (f : A ->ₐ[R] B) (a : A)
  body: IsLocalization.Away.mapₐ _ _ f a

中文:
缩写 awayMapₐ
  签名: (f : A ->ₐ[R] B) (a : A)
  定义体: IsLocalization.Away.mapₐ _ _ f a

Depends on / 依赖: IsLocalization, IsLocalization.Away.map
-/
noncomputable abbrev awayMapₐ (f : A ->ₐ[R] B) (a : A) :
    Localization.Away a ->ₐ[R] Localization.Away (f a) :=
  IsLocalization.Away.mapₐ _ _ f a

/--
theorem `algebraMap_injective_of_span_eq_top` / 定理 `algebraMap_injective_of_span_eq_top`

English:
theorem algebraMap_injective_of_span_eq_top
  given: (s : Set R) (span_eq : Ideal.span s = ⊤)
  proof: fun x y eq => by
  suffices Module.eqIdeal R x y = ⊤ by simpa [Module.eqIdeal] using (Ideal.eq_top_iff_one _).mp this
  by_contra ne
  have ⟨r, hrs, disj⟩ := Ideal.exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  have ⟨⟨_, n, rfl⟩, eq⟩ := (IsLocalization.eq_iff_exists (

中文:
定理 algebraMap_injective_of_span_eq_top
  条件: (s : 集合 R) (span_eq : 理想.span s = ⊤)
  证明: fun x y eq => by
  suffices Module.eqIdeal R x y = ⊤ by simpa [Module.eqIdeal] using (Ideal.eq_top_iff_one _).mp this
  by_contra ne
  have ⟨r, hrs, disj⟩ := Ideal.exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  have ⟨⟨_, n, rfl⟩, eq⟩ := (IsLocalization.eq_iff_exists (

Depends on / 依赖: Ideal.eq_top_iff_one, Ideal.exists_disjoint_powers_of_span_eq_top, IsLocalization, IsLocalization.eq_iff_exists, Module, Module.eqIdeal, Set.disjoint_left.mp, congr_fun, disjoint_left, eqIdeal, eq_iff_exists, eq_top_iff_one, exists_disjoint_powers_of_span_eq_top, powers, span_eq
-/
theorem algebraMap_injective_of_span_eq_top (s : Set R) (span_eq : Ideal.span s = ⊤) :
    Function.Injective (algebraMap R <| Π a : s, Away a.1) := fun x y eq => by
  suffices Module.eqIdeal R x y = ⊤ by simpa [Module.eqIdeal] using (Ideal.eq_top_iff_one _).mp this
  by_contra ne
  have ⟨r, hrs, disj⟩ := Ideal.exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  have ⟨⟨_, n, rfl⟩, eq⟩ := (IsLocalization.eq_iff_exists (.powers r.1) _).mp (congr_fun eq r)
  exact Set.disjoint_left.mp disj eq ⟨n, rfl⟩

/--
theorem `existsUnique_algebraMap_eq_of_span_eq_top` / 定理 `existsUnique_algebraMap_eq_of_span_eq_top`

English:
theorem existsUnique_algebraMap_eq_of_span_eq_top
  statement: (s : Set R) (span_eq : Ideal.span s = ⊤)
  proof: by
  have mem := (Ideal.eq_top_iff_one _).mp span_eq; clear span_eq
  wlog finset_eq : exists t : Finset R, t = s generalizing s
  · have ⟨t, hts, mem⟩ := Submodule.mem_span_finite_of_mem_span mem
    have ⟨r, eq, uniq⟩ := this t (fun a => f ⟨a, hts a.2⟩)
      (fun a b => h ⟨a, hts a.2⟩ ⟨b, hts b.2

中文:
定理 存在Unique_algebraMap_eq_of_span_eq_top
  结论: (s : 集合 R) (span_eq : 理想.span s = ⊤)
  证明: by
  have mem := (Ideal.eq_top_iff_one _).mp span_eq; clear span_eq
  wlog finset_eq : exists t : Finset R, t = s generalizing s
  · have ⟨t, hts, mem⟩ := Submodule.mem_span_finite_of_mem_span mem
    have ⟨r, eq, uniq⟩ := this t (fun a => f ⟨a, hts a.2⟩)
      (fun a b => h ⟨a, hts a.2⟩ ⟨b, hts b.2

Depends on / 依赖: Away.awayToAwayLeft, awayToAwayLeft
-/
theorem existsUnique_algebraMap_eq_of_span_eq_top (s : Set R) (span_eq : Ideal.span s = ⊤)
    (f : Π a : s, Away a.1) (h : forall a b : s,
      Away.awayToAwayRight (P := Away (a * b : R)) a.1 b (f a) = Away.awayToAwayLeft b.1 a (f b)) :
    exists! r : R, forall a : s, algebraMap R _ r = f a := by
  have mem := (Ideal.eq_top_iff_one _).mp span_eq; clear span_eq
  wlog finset_eq : exists t : Finset R, t = s generalizing s
  · have ⟨t, hts, mem⟩ := Submodule.mem_span_finite_of_mem_span mem
    have ⟨r, eq, uniq⟩ := this t (fun a => f ⟨a, hts a.2⟩)
      (fun a b => h ⟨a, hts a.2⟩ ⟨b, hts b.2⟩) mem ⟨_, rfl⟩
    refine ⟨r, fun a => ?_, fun _ eq => uniq _ fun a => eq ⟨a, hts a.2⟩⟩
    replace hts := Set.insert_subset a.2 hts
    classical
    have ⟨r', eq, _⟩ := this ({a.1} union t) (fun a => f ⟨a, hts a.2⟩) (fun a b =>
      h ⟨a, hts a.2⟩ ⟨b, hts b.2⟩) (Ideal.span_mono (fun _ => .inr) mem) ⟨{a.1} union t, by simp⟩
    exact (congr_arg _ (uniq _ fun b => eq ⟨b, .inr b.2⟩).symm).trans (eq ⟨a, .inl rfl⟩)
  have span_eq := (Ideal.eq_top_iff_one _).mpr mem
  refine existsUnique_of_exists_of_unique ?_ fun x y hx hy =>
    algebraMap_injective_of_span_eq_top s span_eq (funext fun a => (hx a).trans (hy a).symm)
  obtain ⟨s, rfl⟩ := finset_eq
  choose n r eq using fun a => Away.surj a.1 (f a)
  let N := s.attach.sup n
  let r a := a ^ (N - n a) * r a
  have eq a : f a * algebraMap R _ (a ^ N) = algebraMap R _ (r a) := by
    rw [map_mul]; rw [← eq]; rw [mul_left_comm]; rw [← map_pow]; rw [← map_mul]; rw [← pow_add]; rw [Nat.sub_add_cancel (Finset.le_sup <| s.mem_attach a)]
  have eq2 a b : exists N', (a * b) ^ N' * (r a * b ^ N) = (a * b) ^ N' * (r b * a ^ N) :=
Away.exists_of_eq (S := Away (a * b : R)) _ by
      simp_rw [map_mul, ← Away.awayToAwayRight_eq (S := Away a.1) a.1 b (r a),
        ← Away.awayToAwayLeft_eq (S := Away b.1) b.1 a (r b), ← eq, map_mul,
        Away.awayToAwayRight_eq, Away.awayToAwayLeft_eq, h, mul_assoc, ← map_mul, mul_comm]
  choose N' hN' using eq2
  let N' := (s ×ˢ s).attach.sup fun a => N'
    ⟨_, (Finset.mem_product.mp a.2).1⟩ ⟨_, (Finset.mem_product.mp a.2).2⟩
  have eq2 a b : (a * b) ^ N' * (r a * b ^ N) = (a * b) ^ N' * (r b * a ^ N) := by
    dsimp only [N']; rw [← Nat.sub_add_cancel (Finset.le_sup <| (Finset.mem_attach _ ⟨⟨a, b⟩,
      Finset.mk_mem_product a.2 b.2⟩)), pow_add, mul_assoc, hN', ← mul_assoc]
  let N := N' + N
  let r a := a ^ N' * r a
  have eq a : f a * algebraMap R _ (a ^ N) = algebraMap R _ (r a) := by
    rw [map_mul]; rw [← eq]; rw [mul_left_comm]; rw [← map_mul]; rw [← pow_add]
  have eq2 a b : r a * b ^ N = r b * a ^ N := by
    rw [pow_add]; rw [mul_mul_mul_comm]; rw [← mul_pow]; rw [eq2]; rw [mul_comm a.1]; rw [mul_pow]; rw [mul_mul_mul_comm]; rw [← pow_add]
have ⟨c, eq1⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
(Ideal.eq_top_iff_one _).mp (Set.image_eq_range _ _ ▸ Ideal.span_pow_eq_top _ span_eq N)
  refine ⟨∑ b, c b * r b, fun a => ((Away.algebraMap_isUnit a.1).pow N).mul_left_inj.mp ?_⟩
  simp_rw [← map_pow, eq, ← map_mul, Finset.sum_mul, mul_assoc, eq2 _ a, mul_left_comm (c _),
    ← Finset.mul_sum, ← smul_eq_mul (a := c _), eq1, mul_one]

/--
theorem `Away.isDomain` / 定理 `Away.isDomain`

English:
theorem Away.isDomain
  given: [IsDomain R] {x : R} (hx : x != 0)
  statement: IsDomain (Localization.Away x)
  proof: IsLocalization.Away.isDomain (Localization.Away x) hx

中文:
定理 Away.isDomain
  条件: [是整环 R] {x : R} (hx : x != 0)
  结论: 是整环 (Localization.Away x)
  证明: IsLocalization.Away.isDomain (Localization.Away x) hx

Depends on / 依赖: IsLocalization, IsLocalization.Away.isDomain, Localization, Localization.Away, isDomain
-/
theorem Away.isDomain [IsDomain R] {x : R} (hx : x != 0) : IsDomain (Localization.Away x) :=
  IsLocalization.Away.isDomain (Localization.Away x) hx

end Localization

end CommSemiring

open Localization

variable {R : Type*} [CommSemiring R]

section NumDen

open IsLocalization

variable (x : R)
variable (B : Type*) [CommSemiring B] [Algebra R B] [IsLocalization.Away x B]

/--
Definition of `selfZPow` / `selfZPow` 的定义

English:
definition selfZPow
  signature: (m : Int)
  body: if _ : 0 <= m then algebraMap _ _ x ^ m.natAbs else mk' _ (1 : R) (Submonoid.pow x m.natAbs)

中文:
定义 selfZPow
  签名: (m : 整数)
  定义体: if _ : 0 <= m then algebraMap _ _ x ^ m.natAbs else mk' _ (1 : R) (Submonoid.pow x m.natAbs)

Depends on / 依赖: Submonoid, Submonoid.pow, algebraMap, m.natAbs, natAbs
-/
noncomputable def selfZPow (m : Int) : B :=
  if _ : 0 <= m then algebraMap _ _ x ^ m.natAbs else mk' _ (1 : R) (Submonoid.pow x m.natAbs)

/--
theorem `selfZPow_of_nonneg` / 定理 `selfZPow_of_nonneg`

English:
theorem selfZPow_of_nonneg
  given: {n : Int} (hn : 0 <= n)
  statement: selfZPow x B n = algebraMap R B x ^ n.natAbs
  proof: dif_pos hn

@[simp]

中文:
定理 selfZPow_of_nonneg
  条件: {n : 整数} (hn : 0 <= n)
  结论: selfZPow x B n = algebraMap R B x ^ n.natAbs
  证明: dif_pos hn

@[simp]

Depends on / 依赖: dif_pos
-/
theorem selfZPow_of_nonneg {n : Int} (hn : 0 <= n) : selfZPow x B n = algebraMap R B x ^ n.natAbs :=
  dif_pos hn

@[simp]
/--
theorem `selfZPow_natCast` / 定理 `selfZPow_natCast`

English:
theorem selfZPow_natCast
  given: (d : Nat)
  statement: selfZPow x B d = algebraMap R B x ^ d
  proof: selfZPow_of_nonneg _ _ (Int.natCast_nonneg d)

@[simp]

中文:
定理 selfZPow_natCast
  条件: (d : 自然数)
  结论: selfZPow x B d = algebraMap R B x ^ d
  证明: selfZPow_of_nonneg _ _ (Int.natCast_nonneg d)

@[simp]

Depends on / 依赖: Int.natCast_nonneg, natCast_nonneg, selfZPow_of_nonneg
-/
theorem selfZPow_natCast (d : Nat) : selfZPow x B d = algebraMap R B x ^ d :=
  selfZPow_of_nonneg _ _ (Int.natCast_nonneg d)

@[simp]
/--
theorem `selfZPow_zero` / 定理 `selfZPow_zero`

English:
theorem selfZPow_zero
  statement: selfZPow x B 0 = 1
  proof: by
  simp [selfZPow_of_nonneg _ _ le_rfl]

中文:
定理 selfZPow_zero
  结论: selfZPow x B 0 = 1
  证明: by
  simp [selfZPow_of_nonneg _ _ le_rfl]

Depends on / 依赖: le_rfl, selfZPow_of_nonneg
-/
theorem selfZPow_zero : selfZPow x B 0 = 1 := by
  simp [selfZPow_of_nonneg _ _ le_rfl]

/--
theorem `selfZPow_of_neg` / 定理 `selfZPow_of_neg`

English:
theorem selfZPow_of_neg
  given: {n : Int} (hn : n < 0)
  proof: dif_neg hn.not_ge

中文:
定理 selfZPow_of_neg
  条件: {n : 整数} (hn : n < 0)
  证明: dif_neg hn.not_ge

Depends on / 依赖: dif_neg, hn.not_ge, not_ge
-/
theorem selfZPow_of_neg {n : Int} (hn : n < 0) :
    selfZPow x B n = mk' _ (1 : R) (Submonoid.pow x n.natAbs) :=
  dif_neg hn.not_ge

/--
theorem `selfZPow_of_nonpos` / 定理 `selfZPow_of_nonpos`

English:
theorem selfZPow_of_nonpos
  given: {n : Int} (hn : n <= 0)
  proof: by
  by_cases hn0 : n = 0
  · simp [hn0, selfZPow_zero, Submonoid.pow_apply]
  · simp [selfZPow_of_neg _ _ (lt_of_le_of_ne hn hn0)]

@[simp]

中文:
定理 selfZPow_of_nonpos
  条件: {n : 整数} (hn : n <= 0)
  证明: by
  by_cases hn0 : n = 0
  · simp [hn0, selfZPow_zero, Submonoid.pow_apply]
  · simp [selfZPow_of_neg _ _ (lt_of_le_of_ne hn hn0)]

@[simp]

Depends on / 依赖: Submonoid, Submonoid.pow_apply, lt_of_le_of_ne, pow_apply, selfZPow_of_neg, selfZPow_zero
-/
theorem selfZPow_of_nonpos {n : Int} (hn : n <= 0) :
    selfZPow x B n = mk' _ (1 : R) (Submonoid.pow x n.natAbs) := by
  by_cases hn0 : n = 0
  · simp [hn0, selfZPow_zero, Submonoid.pow_apply]
  · simp [selfZPow_of_neg _ _ (lt_of_le_of_ne hn hn0)]

@[simp]
/--
theorem `selfZPow_neg_natCast` / 定理 `selfZPow_neg_natCast`

English:
theorem selfZPow_neg_natCast
  given: (d : Nat)
  statement: selfZPow x B (-d) = mk' _ (1 : R) (Submonoid.pow x d)
  proof: by
  simp [selfZPow_of_nonpos _ _ (neg_nonpos.mpr (Int.natCast_nonneg d))]

中文:
定理 selfZPow_neg_natCast
  条件: (d : 自然数)
  结论: selfZPow x B (-d) = mk' _ (1 : R) (子幺半群.pow x d)
  证明: by
  simp [selfZPow_of_nonpos _ _ (neg_nonpos.mpr (Int.natCast_nonneg d))]

Depends on / 依赖: Int.natCast_nonneg, natCast_nonneg, neg_nonpos, neg_nonpos.mpr, selfZPow_of_nonpos
-/
theorem selfZPow_neg_natCast (d : Nat) : selfZPow x B (-d) = mk' _ (1 : R) (Submonoid.pow x d) := by
  simp [selfZPow_of_nonpos _ _ (neg_nonpos.mpr (Int.natCast_nonneg d))]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `selfZPow_sub_natCast` / 定理 `selfZPow_sub_natCast`

English:
theorem selfZPow_sub_natCast
  given: {n m : Nat}
  proof: by
  by_cases! h : m <= n
  · rw [IsLocalization.eq_mk'_iff_mul_eq, Submonoid.pow_apply, Subtype.coe_mk, ← Int.ofNat_sub h,
      selfZPow_natCast, ← map_pow, ← map_mul, ← pow_add, Nat.sub_add_cancel h]
  · rw [← neg_sub, ← Int.ofNat_sub h.le, selfZPow_neg_natCast, IsLocalization.mk'_eq_iff_eq]
    

中文:
定理 selfZPow_sub_natCast
  条件: {n m : 自然数}
  证明: by
  by_cases! h : m <= n
  · rw [IsLocalization.eq_mk'_iff_mul_eq, Submonoid.pow_apply, Subtype.coe_mk, ← Int.ofNat_sub h,
      selfZPow_natCast, ← map_pow, ← map_mul, ← pow_add, Nat.sub_add_cancel h]
  · rw [← neg_sub, ← Int.ofNat_sub h.le, selfZPow_neg_natCast, IsLocalization.mk'_eq_iff_eq]
    

Depends on / 依赖: Int.ofNat_sub, IsLocalization, IsLocalization.eq_mk, IsLocalization.mk, Nat.sub_add_cancel, Submonoid, Submonoid.pow_apply, Subtype, Subtype.coe_mk, _eq_iff_eq, _iff_mul_eq, coe_mk, eq_mk, h.le, map_mul, map_pow, neg_sub, ofNat_sub, pow_add, pow_apply
-/
theorem selfZPow_sub_natCast {n m : Nat} :
    selfZPow x B (n - m) = mk' _ (x ^ n) (Submonoid.pow x m) := by
  by_cases! h : m <= n
  · rw [IsLocalization.eq_mk'_iff_mul_eq, Submonoid.pow_apply, Subtype.coe_mk, ← Int.ofNat_sub h,
      selfZPow_natCast, ← map_pow, ← map_mul, ← pow_add, Nat.sub_add_cancel h]
  · rw [← neg_sub, ← Int.ofNat_sub h.le, selfZPow_neg_natCast, IsLocalization.mk'_eq_iff_eq]
    simp [Submonoid.pow_apply, ← pow_add, Nat.sub_add_cancel h.le]

@[simp]
/--
theorem `selfZPow_add` / 定理 `selfZPow_add`

English:
theorem selfZPow_add
  given: {n m : Int}
  statement: selfZPow x B (n + m) = selfZPow x B n * selfZPow x B m
  proof: by
  rcases le_or_gt 0 n with hn | hn <;> rcases le_or_gt 0 m with hm | hm
  · rw [selfZPow_of_nonneg _ _ hn, selfZPow_of_nonneg _ _ hm,
      selfZPow_of_nonneg _ _ (add_nonneg hn hm), Int.natAbs_add_of_nonneg hn hm, pow_add]
  · have : n + m = n.natAbs - m.natAbs := by
      rw [Int.natAbs_of_nonn

中文:
定理 selfZPow_add
  条件: {n m : 整数}
  结论: selfZPow x B (n + m) = selfZPow x B n * selfZPow x B m
  证明: by
  rcases le_or_gt 0 n with hn | hn <;> rcases le_or_gt 0 m with hm | hm
  · rw [selfZPow_of_nonneg _ _ hn, selfZPow_of_nonneg _ _ hm,
      selfZPow_of_nonneg _ _ (add_nonneg hn hm), Int.natAbs_add_of_nonneg hn hm, pow_add]
  · have : n + m = n.natAbs - m.natAbs := by
      rw [Int.natAbs_of_nonn

Depends on / 依赖: Int.natAbs_add_of_nonneg, Int.natAbs_of_nonneg, Int.ofNat_natAbs_of_nonpos, IsLocalization, IsLocalization.mk, _eq_mul_mk, _one, add_nonneg, hm.le, le_or_gt, m.natAbs, map_pow, n.natAbs, natAbs, natAbs_add_of_nonneg, natAbs_of_nonneg, ofNat_natAbs_of_nonpos, pow_add, selfZPow_of_neg, selfZPow_of_nonneg
-/
theorem selfZPow_add {n m : Int} : selfZPow x B (n + m) = selfZPow x B n * selfZPow x B m := by
  rcases le_or_gt 0 n with hn | hn <;> rcases le_or_gt 0 m with hm | hm
  · rw [selfZPow_of_nonneg _ _ hn, selfZPow_of_nonneg _ _ hm,
      selfZPow_of_nonneg _ _ (add_nonneg hn hm), Int.natAbs_add_of_nonneg hn hm, pow_add]
  · have : n + m = n.natAbs - m.natAbs := by
      rw [Int.natAbs_of_nonneg hn]; rw [Int.ofNat_natAbs_of_nonpos hm.le]; rw [sub_neg_eq_add]
    rw [selfZPow_of_nonneg _ _ hn]; rw [selfZPow_of_neg _ _ hm]; rw [this]; rw [selfZPow_sub_natCast]; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [map_pow]
  · have : n + m = m.natAbs - n.natAbs := by
      rw [Int.natAbs_of_nonneg hm]; rw [Int.ofNat_natAbs_of_nonpos hn.le]; rw [sub_neg_eq_add]; rw [add_comm]
    rw [selfZPow_of_nonneg _ _ hm]; rw [selfZPow_of_neg _ _ hn]; rw [this]; rw [selfZPow_sub_natCast]; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [map_pow]; rw [mul_comm]
  · rw [selfZPow_of_neg _ _ hn, selfZPow_of_neg _ _ hm, selfZPow_of_neg _ _ (add_neg hn hm),
      Int.natAbs_add_of_nonpos hn.le hm.le, ← mk'_mul, one_mul]
    congr
    ext
    simp [pow_add]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `selfZPow_mul_neg` / 定理 `selfZPow_mul_neg`

English:
theorem selfZPow_mul_neg
  given: (d : Int)
  statement: selfZPow x B d * selfZPow x B (-d) = 1
  proof: by
  by_cases! hd : d <= 0
  · rw [selfZPow_of_nonpos x B hd, selfZPow_of_nonneg, ← map_pow, Int.natAbs_neg,
      Submonoid.pow_apply, IsLocalization.mk'_spec, map_one]
    apply nonneg_of_neg_nonpos
    rwa [neg_neg]
  · rw [selfZPow_of_nonneg x B hd.le, selfZPow_of_nonpos, ← map_pow, Int.natAbs_n

中文:
定理 selfZPow_mul_neg
  条件: (d : 整数)
  结论: selfZPow x B d * selfZPow x B (-d) = 1
  证明: by
  by_cases! hd : d <= 0
  · rw [selfZPow_of_nonpos x B hd, selfZPow_of_nonneg, ← map_pow, Int.natAbs_neg,
      Submonoid.pow_apply, IsLocalization.mk'_spec, map_one]
    apply nonneg_of_neg_nonpos
    rwa [neg_neg]
  · rw [selfZPow_of_nonneg x B hd.le, selfZPow_of_nonpos, ← map_pow, Int.natAbs_n

Depends on / 依赖: Int.natAbs_neg, IsLocalization, IsLocalization.mk, Submonoid, Submonoid.pow_apply, _spec, hd.le, le_of_lt, map_one, map_pow, natAbs_neg, neg_neg, nonneg_of_neg_nonpos, nonpos_of_neg_nonneg, pow_apply, selfZPow_of_nonneg, selfZPow_of_nonpos
-/
theorem selfZPow_mul_neg (d : Int) : selfZPow x B d * selfZPow x B (-d) = 1 := by
  by_cases! hd : d <= 0
  · rw [selfZPow_of_nonpos x B hd, selfZPow_of_nonneg, ← map_pow, Int.natAbs_neg,
      Submonoid.pow_apply, IsLocalization.mk'_spec, map_one]
    apply nonneg_of_neg_nonpos
    rwa [neg_neg]
  · rw [selfZPow_of_nonneg x B hd.le, selfZPow_of_nonpos, ← map_pow, Int.natAbs_neg,
      Submonoid.pow_apply, IsLocalization.mk'_spec'_mk, map_one]
    refine nonpos_of_neg_nonneg (le_of_lt ?_)
    rwa [neg_neg]

/--
theorem `selfZPow_neg_mul` / 定理 `selfZPow_neg_mul`

English:
theorem selfZPow_neg_mul
  given: (d : Int)
  statement: selfZPow x B (-d) * selfZPow x B d = 1
  proof: by
  rw [mul_comm]; rw [selfZPow_mul_neg x B d]

中文:
定理 selfZPow_neg_mul
  条件: (d : 整数)
  结论: selfZPow x B (-d) * selfZPow x B d = 1
  证明: by
  rw [mul_comm]; rw [selfZPow_mul_neg x B d]

Depends on / 依赖: mul_comm, selfZPow_mul_neg
-/
theorem selfZPow_neg_mul (d : Int) : selfZPow x B (-d) * selfZPow x B d = 1 := by
  rw [mul_comm]; rw [selfZPow_mul_neg x B d]

/--
theorem `selfZPow_pow_sub` / 定理 `selfZPow_pow_sub`

English:
theorem selfZPow_pow_sub
  given: (a : R) (b : B) (m d : Int)
  proof: by
  rw [sub_eq_add_neg]; rw [selfZPow_add]; rw [mul_assoc]; rw [mul_comm _ (mk' B a 1)]; rw [← mul_assoc]
  constructor
  · intro h
    have := congr_arg (fun s : B => s * selfZPow x B d) h
    rwa [mul_assoc, mul_assoc, selfZPow_neg_mul, mul_one, mul_comm b _] at this
  · intro h
    have := congr

中文:
定理 selfZPow_pow_sub
  条件: (a : R) (b : B) (m d : 整数)
  证明: by
  rw [sub_eq_add_neg]; rw [selfZPow_add]; rw [mul_assoc]; rw [mul_comm _ (mk' B a 1)]; rw [← mul_assoc]
  constructor
  · intro h
    have := congr_arg (fun s : B => s * selfZPow x B d) h
    rwa [mul_assoc, mul_assoc, selfZPow_neg_mul, mul_one, mul_comm b _] at this
  · intro h
    have := congr

Depends on / 依赖: congr_arg, mul_assoc, mul_comm, mul_one, selfZPow, selfZPow_add, selfZPow_mul_neg, selfZPow_neg_mul, sub_eq_add_neg
-/
theorem selfZPow_pow_sub (a : R) (b : B) (m d : Int) :
    selfZPow x B (m - d) * mk' B a (1 : Submonoid.powers x) = b ↔
      selfZPow x B m * mk' B a (1 : Submonoid.powers x) = selfZPow x B d * b := by
  rw [sub_eq_add_neg]; rw [selfZPow_add]; rw [mul_assoc]; rw [mul_comm _ (mk' B a 1)]; rw [← mul_assoc]
  constructor
  · intro h
    have := congr_arg (fun s : B => s * selfZPow x B d) h
    rwa [mul_assoc, mul_assoc, selfZPow_neg_mul, mul_one, mul_comm b _] at this
  · intro h
    have := congr_arg (fun s : B => s * selfZPow x B (-d)) h
    rwa [mul_comm _ b, mul_assoc b _ _, selfZPow_mul_neg, mul_one] at this

variable {R : Type*} [CommRing R] (x : R) (B : Type*) [CommRing B]
variable [Algebra R B] [IsLocalization.Away x B] [IsDomain R] [WfDvdMonoid R]

/--
theorem `exists_reduced_fraction'` / 定理 `exists_reduced_fraction'`

English:
theorem exists_reduced_fraction'
  given: {b : B} (hb : b != 0) (hx : Irreducible x)
  proof: by
  obtain ⟨⟨a₀, y⟩, H⟩ := surj (Submonoid.powers x) b
  obtain ⟨d, hy⟩ := (Submonoid.mem_powers_iff y.1 x).mp y.2
  have ha₀ : a₀ != 0 := by
    have := isDomain_of_le_nonZeroDivisors B
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    simp only [← hy, map_pow] at H
    apply ((in

中文:
定理 存在_reduced_fraction'
  条件: {b : B} (hb : b != 0) (hx : 不可约 x)
  证明: by
  obtain ⟨⟨a₀, y⟩, H⟩ := surj (Submonoid.powers x) b
  obtain ⟨d, hy⟩ := (Submonoid.mem_powers_iff y.1 x).mp y.2
  have ha₀ : a₀ != 0 := by
    have := isDomain_of_le_nonZeroDivisors B
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    simp only [← hy, map_pow] at H
    apply ((in

Depends on / 依赖: IsLocalization, IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors, Submonoid, Submonoid.mem_powers_iff, Submonoid.powers, algebraMap, hx.ne_zer, hx.ne_zero, injective_iff_map_eq_zero, isDomain_of_le_nonZeroDivisors, map_pow, mem_powers_iff, mpr.mt, mul_ne_zero, ne_zer, ne_zero, pow_ne_zero, powers, powers_le_nonZeroDivisors_of_noZeroDivisors, to_map_ne_zero_of_mem_nonZeroDivisors
-/
theorem exists_reduced_fraction' {b : B} (hb : b != 0) (hx : Irreducible x) :
    exists (a : R) (n : Int), ¬x ∣ a ∧ selfZPow x B n * algebraMap R B a = b := by
  obtain ⟨⟨a₀, y⟩, H⟩ := surj (Submonoid.powers x) b
  obtain ⟨d, hy⟩ := (Submonoid.mem_powers_iff y.1 x).mp y.2
  have ha₀ : a₀ != 0 := by
    have := isDomain_of_le_nonZeroDivisors B
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    simp only [← hy, map_pow] at H
    apply ((injective_iff_map_eq_zero' (algebraMap R B)).mp _ a₀).mpr.mt
    · rw [← H]
      apply mul_ne_zero hb (pow_ne_zero _ _)
      exact
        IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors B
          (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
          (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero)
    · exact IsLocalization.injective B (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
  simp only [← hy] at H
  obtain ⟨m, a, hyp1, hyp2⟩ := WfDvdMonoid.max_power_factor ha₀ hx
  refine ⟨a, m - d, ?_⟩
  rw [← mk'_one (M := Submonoid.powers x) B]; rw [selfZPow_pow_sub]; rw [selfZPow_natCast]; rw [selfZPow_natCast]; rw [← map_pow _ _ d]; rw [mul_comm _ b]; rw [H]; rw [hyp2]; rw [map_mul]; rw [map_pow _ _ m]
  exact ⟨hyp1, congr_arg _ (IsLocalization.mk'_one _ _)⟩

end NumDen
