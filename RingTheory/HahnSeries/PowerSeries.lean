/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.Data.Finsupp.PWO

/-!
# Comparison between Hahn series and power series

If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `R⟦Γ⟧`. When `R` is a semiring and `Γ = ℕ`, then
we get the more familiar semiring of formal power series with coefficients in `R`.

## Main Definitions
* `toPowerSeries` the isomorphism from `R⟦ℕ⟧` to `PowerSeries R`.
* `ofPowerSeries` the inverse, casting a `PowerSeries R` to a `R⟦ℕ⟧`.

## Instances
* For `Finite σ`, the instance `NoZeroDivisors R⟦σ →₀ ℕ⟧`,
  deduced from the case of `MvPowerSeries`
  The case of `R⟦ℕ⟧` is taken care of by `instNoZeroDivisors`.

## TODO
* Build an API for the variable `X` (defined to be `single 1 1 : R⟦Γ⟧`) in analogy to
  `X : R[X]` and `X : PowerSeries R`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


open Finset Function Pointwise Polynomial

noncomputable section

variable {Γ R : Type*}

namespace HahnSeries

section Semiring

variable [Semiring R]

/-- The ring `R⟦ℕ⟧` is isomorphic to `PowerSeries R`. -/
@[simps]
/--
Definition of `toPowerSeries` / `toPowerSeries` 的定义

English:
definition toPowerSeries
  signature: : R⟦Nat⟧ ≃+* PowerSeries R where
  body: PowerSeries.mk f.coeff
  invFun f := ⟨fun n => PowerSeries.coeff n f, .of_linearOrder _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, coeff_mul

中文:
定义 toPowerSeries
  签名: : R⟦自然数⟧ ≃+* PowerSeries R where
  定义体: PowerSeries.mk f.coeff
  invFun f := ⟨fun n => PowerSeries.coeff n f, .of_linearOrder _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, coeff_mul

Depends on / 依赖: PowerSeries, PowerSeries.mk, f.coeff
-/
def toPowerSeries : R⟦Nat⟧ ≃+* PowerSeries R where
  toFun f := PowerSeries.mk f.coeff
  invFun f := ⟨fun n => PowerSeries.coeff n f, .of_linearOrder _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, coeff_mul]
    classical
refine (sum_filter_ne_zero _).symm.trans (sum_congr ?_ fun _ _ => rfl).trans
      sum_filter_ne_zero _
    ext m
    simp only [HasAntidiagonal.mem_antidiagonal, Finset.mem_antidiagonal, and_congr_left_iff,
      mem_filter, mem_support]
    rintro h
    rw [and_iff_right (left_ne_zero_of_mul h)]; rw [and_iff_right (right_ne_zero_of_mul h)]

/--
theorem `coeff_toPowerSeries` / 定理 `coeff_toPowerSeries`

English:
theorem coeff_toPowerSeries
  given: {f : R⟦Nat⟧} {n : Nat}
  proof: PowerSeries.coeff_mk _ _

中文:
定理 coeff_toPowerSeries
  条件: {f : R⟦自然数⟧} {n : 自然数}
  证明: PowerSeries.coeff_mk _ _

Depends on / 依赖: PowerSeries, PowerSeries.coeff_mk, coeff_mk
-/
theorem coeff_toPowerSeries {f : R⟦Nat⟧} {n : Nat} :
    PowerSeries.coeff n (toPowerSeries f) = f.coeff n :=
  PowerSeries.coeff_mk _ _

/--
theorem `coeff_toPowerSeries_symm` / 定理 `coeff_toPowerSeries_symm`

English:
theorem coeff_toPowerSeries_symm
  given: {f : PowerSeries R} {n : Nat}
  proof: rfl

中文:
定理 coeff_toPowerSeries_symm
  条件: {f : PowerSeries R} {n : 自然数}
  证明: rfl
-/
theorem coeff_toPowerSeries_symm {f : PowerSeries R} {n : Nat} :
    (HahnSeries.toPowerSeries.symm f).coeff n = PowerSeries.coeff n f :=
  rfl

variable (Γ R) [Semiring Γ] [PartialOrder Γ] [IsStrictOrderedRing Γ]

/--
Definition of `ofPowerSeries` / `ofPowerSeries` 的定义

English:
definition ofPowerSeries
  signature: : PowerSeries R ->+* R⟦Γ⟧
  body: (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (RingEquiv.toRingHom toPowerSeries.symm)

中文:
定义 ofPowerSeries
  签名: : PowerSeries R ->+* R⟦Γ⟧
  定义体: (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (RingEquiv.toRingHom toPowerSeries.symm)

Depends on / 依赖: HahnSeries, HahnSeries.embDomainRingHom, Nat.castAddMonoidHom, Nat.cast_le, Nat.strictMono_cast.injective, RingEquiv, RingEquiv.toRingHom, castAddMonoidHom, cast_le, embDomainRingHom, injective, strictMono_cast, toPowerSeries, toPowerSeries.symm, toRingHom
-/
def ofPowerSeries : PowerSeries R ->+* R⟦Γ⟧ :=
  (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (RingEquiv.toRingHom toPowerSeries.symm)

variable {Γ R}

/--
theorem `ofPowerSeries_injective` / 定理 `ofPowerSeries_injective`

English:
theorem ofPowerSeries_injective
  statement: Function.Injective (ofPowerSeries Γ R)
  proof: embDomain_injective.comp toPowerSeries.symm.injective

中文:
定理 ofPowerSeries_injective
  结论: Function.Injective (ofPowerSeries Γ R)
  证明: embDomain_injective.comp toPowerSeries.symm.injective

Depends on / 依赖: embDomain_injective, embDomain_injective.comp, injective, toPowerSeries, toPowerSeries.symm.injective
-/
theorem ofPowerSeries_injective : Function.Injective (ofPowerSeries Γ R) :=
  embDomain_injective.comp toPowerSeries.symm.injective

-- Not `@[simp]` since the RHS is more complicated and it makes linter failures elsewhere
/--
theorem `ofPowerSeries_apply` / 定理 `ofPowerSeries_apply`

English:
theorem ofPowerSeries_apply
  given: (x : PowerSeries R)
  proof: rfl

中文:
定理 ofPowerSeries_apply
  条件: (x : PowerSeries R)
  证明: rfl
-/
theorem ofPowerSeries_apply (x : PowerSeries R) :
    ofPowerSeries Γ R x = embDomain Nat.castOrderEmbedding (toPowerSeries.symm x) :=
  rfl

/--
theorem `ofPowerSeries_apply_coeff` / 定理 `ofPowerSeries_apply_coeff`

English:
theorem ofPowerSeries_apply_coeff
  given: (x : PowerSeries R) (n : Nat)
  proof: by
  trans (embDomain (Nat.castOrderEmbedding (α := Γ)) (toPowerSeries.symm x)).coeff
    (Nat.castOrderEmbedding n)
  · simp [ofPowerSeries_apply]
  rw [embDomain_coeff]
  simp

@[simp]

中文:
定理 ofPowerSeries_apply_coeff
  条件: (x : PowerSeries R) (n : 自然数)
  证明: by
  trans (embDomain (Nat.castOrderEmbedding (α := Γ)) (toPowerSeries.symm x)).coeff
    (Nat.castOrderEmbedding n)
  · simp [ofPowerSeries_apply]
  rw [embDomain_coeff]
  simp

@[simp]

Depends on / 依赖: Nat.castOrderEmbedding, castOrderEmbedding, embDomain, embDomain_coeff, ofPowerSeries_apply, toPowerSeries, toPowerSeries.symm
-/
theorem ofPowerSeries_apply_coeff (x : PowerSeries R) (n : Nat) :
    (ofPowerSeries Γ R x).coeff n = PowerSeries.coeff n x := by
  trans (embDomain (Nat.castOrderEmbedding (α := Γ)) (toPowerSeries.symm x)).coeff
    (Nat.castOrderEmbedding n)
  · simp [ofPowerSeries_apply]
  rw [embDomain_coeff]
  simp

@[simp]
/--
theorem `ofPowerSeries_C` / 定理 `ofPowerSeries_C`

English:
theorem ofPowerSeries_C
  given: (r : R)
  statement: ofPowerSeries Γ R (PowerSeries.C r) = HahnSeries.C r
  proof: by
  ext n
  simp only [ofPowerSeries_apply, C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_single]
  split_ifs with hn
  · subst hn
    convert! embDomain_coeff (a := 0) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply

中文:
定理 ofPowerSeries_C
  条件: (r : R)
  结论: ofPowerSeries Γ R (PowerSeries.C r) = HahnSeries.C r
  证明: by
  ext n
  simp only [ofPowerSeries_apply, C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_single]
  split_ifs with hn
  · subst hn
    convert! embDomain_coeff (a := 0) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply

Depends on / 依赖: MonoidHom, MonoidHom.coe_mk, Ne.symm, OneHom, OneHom.coe_mk, PowerSeries, PowerSeries.coeff_C, RingHom, RingHom.coe_mk, Set.mem_image, coe_mk, coeff_C, coeff_single, contextual, convert, embDomain_coeff, embDomain_notin_image_support, mem_image, mem_support, not_exists
-/
theorem ofPowerSeries_C (r : R) : ofPowerSeries Γ R (PowerSeries.C r) = HahnSeries.C r := by
  ext n
  simp only [ofPowerSeries_apply, C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_single]
  split_ifs with hn
  · subst hn
    convert! embDomain_coeff (a := 0) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_C]
    intro
    simp +contextual [Ne.symm hn]

@[simp]
/--
theorem `ofPowerSeries_X` / 定理 `ofPowerSeries_X`

English:
theorem ofPowerSeries_X
  statement: ofPowerSeries Γ R PowerSeries.X = single 1 1
  proof: by
  ext n
  simp only [coeff_single, ofPowerSeries_apply]
  split_ifs with hn
  · rw [hn]
    convert! embDomain_coeff (a := 1) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_X]
    intro

中文:
定理 ofPowerSeries_X
  结论: ofPowerSeries Γ R PowerSeries.X = single 1 1
  证明: by
  ext n
  simp only [coeff_single, ofPowerSeries_apply]
  split_ifs with hn
  · rw [hn]
    convert! embDomain_coeff (a := 1) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_X]
    intro

Depends on / 依赖: Ne.symm, PowerSeries, PowerSeries.coeff_X, Set.mem_image, coeff_X, coeff_single, contextual, convert, embDomain_coeff, embDomain_notin_image_support, mem_image, mem_support, not_exists, ofPowerSeries_apply, split_ifs, toPowerSeries_symm_apply_coeff
-/
theorem ofPowerSeries_X : ofPowerSeries Γ R PowerSeries.X = single 1 1 := by
  ext n
  simp only [coeff_single, ofPowerSeries_apply]
  split_ifs with hn
  · rw [hn]
    convert! embDomain_coeff (a := 1) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_X]
    intro
    simp +contextual [Ne.symm hn]

/--
theorem `ofPowerSeries_X_pow` / 定理 `ofPowerSeries_X_pow`

English:
theorem ofPowerSeries_X_pow
  given: {R} [Semiring R] (n : Nat)
  proof: by
  simp

中文:
定理 ofPowerSeries_X_pow
  条件: {R} [Semiring R] (n : 自然数)
  证明: by
  simp
-/
theorem ofPowerSeries_X_pow {R} [Semiring R] (n : Nat) :
    ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1 := by
  simp

set_option backward.isDefEq.respectTransparency false in
-- Lemmas converting Hahn series over a finite index type to and from `MvPowerSeries`
/-- The ring `R⟦σ →₀ ℕ⟧` is isomorphic to `MvPowerSeries σ R` for a `Finite` `σ`.
We take the index set of the hahn series to be `Finsupp` rather than `pi`,
even though we assume `Finite σ` as this is more natural for alignment with `MvPowerSeries`.
After importing `Mathlib/Algebra/Order/Pi.lean` the ring `R⟦σ → ℕ⟧` could be constructed
instead.
-/
@[simps]
/--
Definition of `toMvPowerSeries` / `toMvPowerSeries` 的定义

English:
definition toMvPowerSeries
  signature: {σ : Type*} [Finite σ]
  body: f.coeff
  invFun f := ⟨(f : (σ ->₀ Nat) -> R), Set.isPWO_of_wellQuasiOrderedLE _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    classical
      change (f * g).coeff n = _
      simp_rw [coeff_mul]
ref

中文:
定义 toMvPowerSeries
  签名: {σ : 类型} [Finite σ]
  定义体: f.coeff
  invFun f := ⟨(f : (σ ->₀ Nat) -> R), Set.isPWO_of_wellQuasiOrderedLE _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    classical
      change (f * g).coeff n = _
      simp_rw [coeff_mul]
ref

Depends on / 依赖: f.coeff
-/
def toMvPowerSeries {σ : Type*} [Finite σ] : R⟦σ ->₀ Nat⟧ ≃+* MvPowerSeries σ R where
  toFun f := f.coeff
  invFun f := ⟨(f : (σ ->₀ Nat) -> R), Set.isPWO_of_wellQuasiOrderedLE _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    classical
      change (f * g).coeff n = _
      simp_rw [coeff_mul]
refine (sum_filter_ne_zero _).symm.trans (sum_congr ?_ fun _ _ => rfl).trans
        sum_filter_ne_zero _
      ext m
      simp only [and_congr_left_iff, Finset.mem_antidiagonal, mem_filter, mem_support,
        HasAntidiagonal.mem_antidiagonal]
      rintro h
      rw [and_iff_right (left_ne_zero_of_mul h)]; rw [and_iff_right (right_ne_zero_of_mul h)]

variable {σ : Type*} [Finite σ]

-- TODO : generalize to all (?) rings of Hahn Series
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoZeroDivisors
  signature: R] : NoZeroDivisors (R⟦σ ->₀ Nat⟧)
  body: toMvPowerSeries.toMulEquiv.noZeroDivisors (A := R⟦σ ->₀ Nat⟧) (MvPowerSeries σ R)

中文:
实例 [NoZeroDivisors
  签名: R] : NoZeroDivisors (R⟦σ ->₀ 自然数⟧)
  定义体: toMvPowerSeries.toMulEquiv.noZeroDivisors (A := R⟦σ ->₀ Nat⟧) (MvPowerSeries σ R)

Depends on / 依赖: MvPowerSeries, noZeroDivisors, toMulEquiv, toMvPowerSeries, toMvPowerSeries.toMulEquiv.noZeroDivisors
-/
instance [NoZeroDivisors R] : NoZeroDivisors (R⟦σ ->₀ Nat⟧) :=
  toMvPowerSeries.toMulEquiv.noZeroDivisors (A := R⟦σ ->₀ Nat⟧) (MvPowerSeries σ R)

/--
theorem `coeff_toMvPowerSeries` / 定理 `coeff_toMvPowerSeries`

English:
theorem coeff_toMvPowerSeries
  given: {f : R⟦σ ->₀ Nat⟧} {n : σ ->₀ Nat}
  proof: rfl

中文:
定理 coeff_toMvPowerSeries
  条件: {f : R⟦σ ->₀ 自然数⟧} {n : σ ->₀ 自然数}
  证明: rfl
-/
theorem coeff_toMvPowerSeries {f : R⟦σ ->₀ Nat⟧} {n : σ ->₀ Nat} :
    MvPowerSeries.coeff n (toMvPowerSeries f) = f.coeff n :=
  rfl

/--
theorem `coeff_toMvPowerSeries_symm` / 定理 `coeff_toMvPowerSeries_symm`

English:
theorem coeff_toMvPowerSeries_symm
  given: {f : MvPowerSeries σ R} {n : σ ->₀ Nat}
  proof: rfl

中文:
定理 coeff_toMvPowerSeries_symm
  条件: {f : MvPowerSeries σ R} {n : σ ->₀ 自然数}
  证明: rfl
-/
theorem coeff_toMvPowerSeries_symm {f : MvPowerSeries σ R} {n : σ ->₀ Nat} :
    (HahnSeries.toMvPowerSeries.symm f).coeff n = MvPowerSeries.coeff n f :=
  rfl

end Semiring

section Algebra

variable (R) [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

/-- The `R`-algebra `A⟦ℕ⟧` is isomorphic to `PowerSeries A`. -/
@[simps!]
/--
Definition of `toPowerSeriesAlg` / `toPowerSeriesAlg` 的定义

English:
definition toPowerSeriesAlg
  signature: : A⟦Nat⟧ ≃ₐ[R] PowerSeries A
  body: { toPowerSeries with
    commutes' := fun r => by
      ext n
      cases n <;> simp [algebraMap_apply, PowerSeries.algebraMap_apply] }

中文:
定义 toPowerSeriesAlg
  签名: : A⟦自然数⟧ ≃ₐ[R] PowerSeries A
  定义体: { toPowerSeries with
    commutes' := fun r => by
      ext n
      cases n <;> simp [algebraMap_apply, PowerSeries.algebraMap_apply] }

Depends on / 依赖: PowerSeries, PowerSeries.algebraMap_apply, algebraMap_apply, commutes, mul_comm, toPowerSeries
-/
def toPowerSeriesAlg : A⟦Nat⟧ ≃ₐ[R] PowerSeries A :=
  { toPowerSeries with
    commutes' := fun r => by
      ext n
      cases n <;> simp [algebraMap_apply, PowerSeries.algebraMap_apply] }

variable (Γ) [Semiring Γ] [PartialOrder Γ] [IsStrictOrderedRing Γ]

/-- Casting a power series as a Hahn series with coefficients from a strictly ordered semiring. -/
@[simps!]
/--
Definition of `ofPowerSeriesAlg` / `ofPowerSeriesAlg` 的定义

English:
definition ofPowerSeriesAlg
  signature: : PowerSeries A ->ₐ[R] A⟦Γ⟧
  body: (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (AlgEquiv.toAlgHom (toPowerSeriesAlg R).symm)

中文:
定义 ofPowerSeriesAlg
  签名: : PowerSeries A ->ₐ[R] A⟦Γ⟧
  定义体: (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (AlgEquiv.toAlgHom (toPowerSeriesAlg R).symm)

Depends on / 依赖: AlgEquiv, AlgEquiv.toAlgHom, HahnSeries, HahnSeries.embDomainAlgHom, Nat.castAddMonoidHom, Nat.cast_le, Nat.strictMono_cast.injective, castAddMonoidHom, cast_le, embDomainAlgHom, injective, strictMono_cast, toAlgHom, toPowerSeriesAlg
-/
def ofPowerSeriesAlg : PowerSeries A ->ₐ[R] A⟦Γ⟧ :=
  (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (AlgEquiv.toAlgHom (toPowerSeriesAlg R).symm)

/--
Instance `powerSeriesAlgebra` / 实例 `powerSeriesAlgebra`

English:
instance powerSeriesAlgebra
  signature: {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)]
  body: RingHom.toAlgebra (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))

中文:
实例 powerSeriesAlgebra
  签名: {S : 类型} [CommSemiring S] [Algebra S (PowerSeries R)]
  定义体: RingHom.toAlgebra (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))

Depends on / 依赖: CommSemigroup, CommSemigroup.mul_comm, PowerSeries, RingHom, RingHom.toAlgebra, algebraMap, mul_comm, ofPowerSeries, toAlgebra
-/
instance powerSeriesAlgebra {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)] :
    Algebra S R⟦Γ⟧ :=
RingHom.toAlgebra (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))

variable {R}
variable {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)]

/--
theorem `algebraMap_apply'` / 定理 `algebraMap_apply'`

English:
theorem algebraMap_apply'
  given: (x : S)
  proof: rfl

@[simp]

中文:
定理 algebraMap_apply'
  条件: (x : S)
  证明: rfl

@[simp]
-/
theorem algebraMap_apply' (x : S) :
    algebraMap S R⟦Γ⟧ x = ofPowerSeries Γ R (algebraMap S (PowerSeries R) x) :=
  rfl

@[simp]
/--
theorem `_root_.Polynomial.algebraMap_hahnSeries_apply` / 定理 `_root_.Polynomial.algebraMap_hahnSeries_apply`

English:
theorem _root_.Polynomial.algebraMap_hahnSeries_apply
  given: (f : R[X])
  proof: rfl

中文:
定理 _root_.Polynomial.algebraMap_hahnSeries_apply
  条件: (f : R[X])
  证明: rfl
-/
theorem _root_.Polynomial.algebraMap_hahnSeries_apply (f : R[X]) :
    algebraMap R[X] R⟦Γ⟧ f = ofPowerSeries Γ R f :=
  rfl

/--
theorem `_root_.Polynomial.algebraMap_hahnSeries_injective` / 定理 `_root_.Polynomial.algebraMap_hahnSeries_injective`

English:
theorem _root_.Polynomial.algebraMap_hahnSeries_injective
  proof: ofPowerSeries_injective.comp (Polynomial.coe_injective R)

中文:
定理 _root_.Polynomial.algebraMap_hahnSeries_injective
  证明: ofPowerSeries_injective.comp (Polynomial.coe_injective R)

Depends on / 依赖: Polynomial, Polynomial.coe_injective, coe_injective, ofPowerSeries_injective, ofPowerSeries_injective.comp
-/
theorem _root_.Polynomial.algebraMap_hahnSeries_injective :
    Function.Injective (algebraMap R[X] R⟦Γ⟧) :=
  ofPowerSeries_injective.comp (Polynomial.coe_injective R)

end Algebra

end HahnSeries
