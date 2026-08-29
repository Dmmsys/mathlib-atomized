/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# `S`-integers and `S`-units of fraction fields of Dedekind domains

Let `K` be the field of fractions of a Dedekind domain `R`, and let `S` be a set of prime ideals in
the height one spectrum of `R`. An `S`-integer of `K` is defined to have `v`-adic valuation at most
one for all primes ideals `v` away from `S`, whereas an `S`-unit of `Kˣ` is defined to have `v`-adic
valuation exactly one for all prime ideals `v` away from `S`.

This file defines the subalgebra of `S`-integers of `K` and the subgroup of `S`-units of `Kˣ`, where
`K` can be specialised to the case of a number field or a function field separately.

## Main definitions

* `Set.integer`: `S`-integers.
* `Set.unit`: `S`-units.
* TODO: localised notation for `S`-integers.

## Main statements

* `Set.unitEquivUnitsInteger`: `S`-units are units of `S`-integers.
* `IsDedekindDomain.integer_empty`: `∅`-integers is the usual ring of integers.
* TODO: proof that `S`-units is the kernel of a map to a product.
* TODO: finite generation of `S`-units and Dirichlet's `S`-unit theorem.

## References

* [D Marcus, *Number Fields*][marcus1977number]
* [J W S Cassels, A Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

S integer, S-integer, S unit, S-unit
-/

@[expose] public section


noncomputable section

open IsDedekindDomain

open scoped nonZeroDivisors

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set <| HeightOneSpectrum R) (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## `S`-integers -/

namespace Set

/-- The `R`-subalgebra of `S`-integers of `K`. -/
@[simps!]
/--
Definition of `integer` / `integer` 的定义

English:
definition integer
  signature: : Subalgebra R K
  body: {
    (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.toSubring).copy
{x : K | forall (v) (_ : v ∉ S), v.valuation K x <= 1}
      Set.ext fun _ => by simp [SetLike.mem_coe] with
    algebraMap_mem' := fun x v _ => v.valuation_le_one x }

中文:
定义 integer
  签名: : 子代数 R K
  定义体: {
    (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.toSubring).copy
{x : K | forall (v) (_ : v ∉ S), v.valuation K x <= 1}
      Set.ext fun _ => by simp [SetLike.mem_coe] with
    algebraMap_mem' := fun x v _ => v.valuation_le_one x }

Depends on / 依赖: Set.ext, SetLike, SetLike.mem_coe, algebraMap_mem, mem_coe, toSubring, v.valuation, v.valuation_le_one, valuation, valuationSubring, valuationSubring.toSubring, valuation_le_one
-/
def integer : Subalgebra R K :=
  {
    (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.toSubring).copy
{x : K | forall (v) (_ : v ∉ S), v.valuation K x <= 1}
      Set.ext fun _ => by simp [SetLike.mem_coe] with
    algebraMap_mem' := fun x v _ => v.valuation_le_one x }

/--
theorem `integer_eq` / 定理 `integer_eq`

English:
theorem integer_eq
  proof: SetLike.ext' by ext; simp

中文:
定理 integer_eq
  证明: SetLike.ext' by ext; simp

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem integer_eq :
    (S.integer K).toSubring =
      ⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.toSubring :=
SetLike.ext' by ext; simp

/--
theorem `integer_valuation_le_one` / 定理 `integer_valuation_le_one`

English:
theorem integer_valuation_le_one
  given: (x : S.integer K) {v : HeightOneSpectrum R} (hv : v ∉ S)
  proof: x.property v hv

中文:
定理 integer_valuation_le_one
  条件: (x : S.integer K) {v : 高一谱 R} (hv : v ∉ S)
  证明: x.property v hv

Depends on / 依赖: property, x.property
-/
theorem integer_valuation_le_one (x : S.integer K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation K x <= 1 :=
  x.property v hv

end Set

namespace IsDedekindDomain

variable (R)

/--
lemma `integer_univ` / 引理 `integer_univ`

English:
lemma integer_univ
  statement: (Set.univ : Set (HeightOneSpectrum R)).integer K = ⊤
  proof: by
  ext
  tauto

中文:
引理 integer_univ
  结论: (集合.univ : 集合 (高一谱 R)).integer K = ⊤
  证明: by
  ext
  tauto
-/
@[simp] lemma integer_univ : (Set.univ : Set (HeightOneSpectrum R)).integer K = ⊤ := by
  ext
  tauto

/--
lemma `integer_empty` / 引理 `integer_empty`

English:
lemma integer_empty
  statement: (∅ : Set (HeightOneSpectrum R)).integer K = ⊥
  proof: by
  ext x
  simp only [Set.integer, Set.mem_empty_iff_false, not_false_eq_true, true_implies]
  refine ⟨HeightOneSpectrum.mem_integers_of_valuation_le_one K x, ?_⟩
  rintro ⟨y, rfl⟩ v
  exact v.valuation_le_one y

中文:
引理 integer_empty
  结论: (∅ : 集合 (高一谱 R)).integer K = ⊥
  证明: by
  ext x
  simp only [Set.integer, Set.mem_empty_iff_false, not_false_eq_true, true_implies]
  refine ⟨HeightOneSpectrum.mem_integers_of_valuation_le_one K x, ?_⟩
  rintro ⟨y, rfl⟩ v
  exact v.valuation_le_one y
-/
@[simp] lemma integer_empty : (∅ : Set (HeightOneSpectrum R)).integer K = ⊥ := by
  ext x
  simp only [Set.integer, Set.mem_empty_iff_false, not_false_eq_true, true_implies]
  refine ⟨HeightOneSpectrum.mem_integers_of_valuation_le_one K x, ?_⟩
  rintro ⟨y, rfl⟩ v
  exact v.valuation_le_one y

end IsDedekindDomain
/-! ## `S`-units -/

namespace Set

/-- The subgroup of `S`-units of `Kˣ`. -/
@[simps!]
/--
Definition of `unit` / `unit` 的定义

English:
definition unit
  signature: : Subgroup Kˣ
  body: (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup).copy
{x : Kˣ | forall (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation K x = 1}
    Set.ext fun _ => by
      simp only [mem_ofPred, SetLike.mem_coe, Subgroup.mem_iInf, Valuation.mem_unitGroup_iff]

中文:
定义 unit
  签名: : 子群 Kˣ
  定义体: (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup).copy
{x : Kˣ | forall (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation K x = 1}
    Set.ext fun _ => by
      simp only [mem_ofPred, SetLike.mem_coe, Subgroup.mem_iInf, Valuation.mem_unitGroup_iff]

Depends on / 依赖: HeightOneSpectrum, Set.ext, SetLike, SetLike.mem_coe, Subgroup, Subgroup.mem_iInf, Valuation, Valuation.mem_unitGroup_iff, mem_coe, mem_iInf, mem_ofPred, mem_unitGroup_iff, unitGroup, v.valuation, valuation, valuationSubring, valuationSubring.unitGroup
-/
def unit : Subgroup Kˣ :=
  (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup).copy
{x : Kˣ | forall (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation K x = 1}
    Set.ext fun _ => by
      simp only [mem_ofPred, SetLike.mem_coe, Subgroup.mem_iInf, Valuation.mem_unitGroup_iff]

/--
theorem `unit_eq` / 定理 `unit_eq`

English:
theorem unit_eq
  proof: Subgroup.copy_eq _ _ _

中文:
定理 unit_eq
  证明: Subgroup.copy_eq _ _ _

Depends on / 依赖: Subgroup, Subgroup.copy_eq, copy_eq
-/
theorem unit_eq :
    S.unit K = ⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup :=
  Subgroup.copy_eq _ _ _

/--
theorem `unit_valuation_eq_one` / 定理 `unit_valuation_eq_one`

English:
theorem unit_valuation_eq_one
  given: (x : S.unit K) {v : HeightOneSpectrum R} (hv : v ∉ S)
  proof: x.property v hv

中文:
定理 unit_valuation_eq_one
  条件: (x : S.unit K) {v : 高一谱 R} (hv : v ∉ S)
  证明: x.property v hv

Depends on / 依赖: property, x.property
-/
theorem unit_valuation_eq_one (x : S.unit K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation K (x : Kˣ) = 1 :=
  x.property v hv

/-- The group of `S`-units is the group of units of the ring of `S`-integers. -/
@[simps apply_val_coe symm_apply_coe]
/--
Definition of `unitEquivUnitsInteger` / `unitEquivUnitsInteger` 的定义

English:
definition unitEquivUnitsInteger
  signature: : S.unit K ≃* (S.integer K)ˣ where
  body: ⟨⟨((x : Kˣ) : K), fun v hv => (x.property v hv).le⟩,
      ⟨((x⁻¹ : Kˣ) : K), fun v hv => (x⁻¹.property v hv).le⟩,
      Subtype.ext x.val.val_inv, Subtype.ext x.val.inv_val⟩
  invFun x :=
    ⟨Units.mk0 x fun hx => x.ne_zero (ZeroMemClass.coe_eq_zero.mp hx),
    fun v hv =>
eq_one_of_one_le_mul_left (x.val.property v hv) (x.inv.property v hv)
Eq.ge by
          rw [← map_mul]; rw [Units.val_mk0]; rw [Subtype.mk_eq_mk.mp x.val_inv]; rw [map_one]⟩
  map_mul' _ _ := by ext; rfl

中文:
定义 unitEquivUnits整数eger
  签名: : S.unit K ≃* (S.integer K)ˣ where
  定义体: ⟨⟨((x : Kˣ) : K), fun v hv => (x.property v hv).le⟩,
      ⟨((x⁻¹ : Kˣ) : K), fun v hv => (x⁻¹.property v hv).le⟩,
      Subtype.ext x.val.val_inv, Subtype.ext x.val.inv_val⟩
  invFun x :=
    ⟨Units.mk0 x fun hx => x.ne_zero (ZeroMemClass.coe_eq_zero.mp hx),
    fun v hv =>
eq_one_of_one_le_mul_left (x.val.property v hv) (x.inv.property v hv)
Eq.ge by
          rw [← map_mul]; rw [Units.val_mk0]; rw [Subtype.mk_eq_mk.mp x.val_inv]; rw [map_one]⟩
  map_mul' _ _ := by ext; rfl

Depends on / 依赖: Eq.ge, Subtype, Subtype.ext, Subtype.mk_eq_mk.mp, Units.mk0, Units.val_mk0, ZeroMemClass, ZeroMemClass.coe_eq_zero.mp, coe_eq_zero, eq_one_of_one_le_mul_left, invFun, inv_val, map_mul, map_one, mk_eq_mk, ne_zero, property, val_inv, val_mk0, x.inv.property
-/
def unitEquivUnitsInteger : S.unit K ≃* (S.integer K)ˣ where
  toFun x :=
    ⟨⟨((x : Kˣ) : K), fun v hv => (x.property v hv).le⟩,
      ⟨((x⁻¹ : Kˣ) : K), fun v hv => (x⁻¹.property v hv).le⟩,
      Subtype.ext x.val.val_inv, Subtype.ext x.val.inv_val⟩
  invFun x :=
    ⟨Units.mk0 x fun hx => x.ne_zero (ZeroMemClass.coe_eq_zero.mp hx),
    fun v hv =>
eq_one_of_one_le_mul_left (x.val.property v hv) (x.inv.property v hv)
Eq.ge by
          rw [← map_mul]; rw [Units.val_mk0]; rw [Subtype.mk_eq_mk.mp x.val_inv]; rw [map_one]⟩
  map_mul' _ _ := by ext; rfl

end Set
