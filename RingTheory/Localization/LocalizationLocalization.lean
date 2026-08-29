/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Localizations of localizations

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section



open Function

namespace IsLocalization

section LocalizationLocalization

variable {R : Type*} [CommSemiring R] (M : Submonoid R) {S : Type*} [CommSemiring S] [Algebra R S]
variable (N : Submonoid S) (T : Type*) [CommSemiring T] [Algebra R T]


section

variable [Algebra S T] [IsScalarTower R S T]

-- This should only be defined when `S` is the localization `M⁻¹R`, hence the nolint.
/-- Localizing w.r.t. `M ⊆ R` and then w.r.t. `N ⊆ S = M⁻¹R` is equal to the localization of `R`
w.r.t. this submonoid. See `localization_localization_isLocalization`.
-/
@[nolint unusedArguments]
/--
Definition of `localizationLocalizationSubmodule` / `localizationLocalizationSubmodule` 的定义

English:
definition localizationLocalizationSubmodule
  signature: : Submonoid R
  body: (N ⊔ M.map (algebraMap R S)).comap (algebraMap R S)

中文:
定义 localizationLocalizationSubmodule
  签名: : 子幺半群 R
  定义体: (N ⊔ M.map (algebraMap R S)).comap (algebraMap R S)

Depends on / 依赖: M.map, algebraMap
-/
def localizationLocalizationSubmodule : Submonoid R :=
  (N ⊔ M.map (algebraMap R S)).comap (algebraMap R S)

variable {M N}

@[simp]
/--
theorem `mem_localizationLocalizationSubmodule` / 定理 `mem_localizationLocalizationSubmodule`

English:
theorem mem_localizationLocalizationSubmodule
  given: {x : R}
  proof: by
  rw [localizationLocalizationSubmodule]; rw [Submonoid.mem_comap]; rw [Submonoid.mem_sup]
  constructor
  · rintro ⟨y, hy, _, ⟨z, hz, rfl⟩, e⟩
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, e.symm⟩
  · rintro ⟨y, z, e⟩
    exact ⟨y, y.prop, _, ⟨z, z.prop, rfl⟩, e.symm⟩

中文:
定理 mem_localizationLocalizationSubmodule
  条件: {x : R}
  证明: by
  rw [localizationLocalizationSubmodule]; rw [Submonoid.mem_comap]; rw [Submonoid.mem_sup]
  constructor
  · rintro ⟨y, hy, _, ⟨z, hz, rfl⟩, e⟩
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, e.symm⟩
  · rintro ⟨y, z, e⟩
    exact ⟨y, y.prop, _, ⟨z, z.prop, rfl⟩, e.symm⟩

Depends on / 依赖: Submonoid, Submonoid.mem_comap, Submonoid.mem_sup, e.symm, localizationLocalizationSubmodule, mem_comap, mem_sup, y.prop, z.prop
-/
theorem mem_localizationLocalizationSubmodule {x : R} :
    x in localizationLocalizationSubmodule M N ↔
      exists (y : N) (z : M), algebraMap R S x = y * algebraMap R S z := by
  rw [localizationLocalizationSubmodule]; rw [Submonoid.mem_comap]; rw [Submonoid.mem_sup]
  constructor
  · rintro ⟨y, hy, _, ⟨z, hz, rfl⟩, e⟩
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, e.symm⟩
  · rintro ⟨y, z, e⟩
    exact ⟨y, y.prop, _, ⟨z, z.prop, rfl⟩, e.symm⟩

variable (M N)
variable [IsLocalization M S]

/--
theorem `localization_localization_map_units` / 定理 `localization_localization_map_units`

English:
theorem localization_localization_map_units
  statement: [IsLocalization N T]
  proof: by
  obtain ⟨y', z, eq⟩ := mem_localizationLocalizationSubmodule.mp y.prop
  rw [IsScalarTower.algebraMap_apply R S T]; rw [eq]; rw [map_mul]; rw [IsUnit.mul_iff]
  exact ⟨IsLocalization.map_units T y', (IsLocalization.map_units _ z).map (algebraMap S T)⟩

中文:
定理 localization_localization_map_units
  结论: [是Localization N T]
  证明: by
  obtain ⟨y', z, eq⟩ := mem_localizationLocalizationSubmodule.mp y.prop
  rw [IsScalarTower.algebraMap_apply R S T]; rw [eq]; rw [map_mul]; rw [IsUnit.mul_iff]
  exact ⟨IsLocalization.map_units T y', (IsLocalization.map_units _ z).map (algebraMap S T)⟩

Depends on / 依赖: IsLocalization, IsLocalization.map_units, IsScalarTower, IsScalarTower.algebraMap_apply, IsUnit, IsUnit.mul_iff, algebraMap, algebraMap_apply, map_mul, map_units, mem_localizationLocalizationSubmodule, mem_localizationLocalizationSubmodule.mp, mul_iff, y.prop
-/
theorem localization_localization_map_units [IsLocalization N T]
    (y : localizationLocalizationSubmodule M N) : IsUnit (algebraMap R T y) := by
  obtain ⟨y', z, eq⟩ := mem_localizationLocalizationSubmodule.mp y.prop
  rw [IsScalarTower.algebraMap_apply R S T]; rw [eq]; rw [map_mul]; rw [IsUnit.mul_iff]
  exact ⟨IsLocalization.map_units T y', (IsLocalization.map_units _ z).map (algebraMap S T)⟩

/--
theorem `localization_localization_surj` / 定理 `localization_localization_surj`

English:
theorem localization_localization_surj
  given: [IsLocalization N T] (x : T)
  proof: by
  rcases IsLocalization.surj N x with ⟨⟨y, s⟩, eq₁⟩
  -- x = y / s
  rcases IsLocalization.surj M y with ⟨⟨z, t⟩, eq₂⟩
  -- y = z / t
  rcases IsLocalization.surj M (s : S) with ⟨⟨z', t'⟩, eq₃⟩
  -- s = z' / t'
  dsimp only at eq₁ eq₂ eq₃
  refine ⟨⟨z * t', z' * t, ?_⟩, ?_⟩ -- x = y / s = (z * t') / (z' * t)
  · rw [mem_localizationLocalizationSubmodule]
    refine ⟨s, t * t', ?_⟩
    rw [map_mul]; rw [← eq₃]; rw [mul_assoc]; rw [← map_mul]; rw [mul_comm t]; rw [Submonoid.coe_mul]
  · simp only [map_mul, IsScalarTower.algebraMap_apply R S T, ← eq₃, ← eq₂, ← eq₁]
    ring

中文:
定理 localization_localization_surj
  条件: [是Localization N T] (x : T)
  证明: by
  rcases IsLocalization.surj N x with ⟨⟨y, s⟩, eq₁⟩
  -- x = y / s
  rcases IsLocalization.surj M y with ⟨⟨z, t⟩, eq₂⟩
  -- y = z / t
  rcases IsLocalization.surj M (s : S) with ⟨⟨z', t'⟩, eq₃⟩
  -- s = z' / t'
  dsimp only at eq₁ eq₂ eq₃
  refine ⟨⟨z * t', z' * t, ?_⟩, ?_⟩ -- x = y / s = (z * t') / (z' * t)
  · rw [mem_localizationLocalizationSubmodule]
    refine ⟨s, t * t', ?_⟩
    rw [map_mul]; rw [← eq₃]; rw [mul_assoc]; rw [← map_mul]; rw [mul_comm t]; rw [Submonoid.coe_mul]
  · simp only [map_mul, IsScalarTower.algebraMap_apply R S T, ← eq₃, ← eq₂, ← eq₁]
    ring

Depends on / 依赖: IsLocalization, IsLocalization.surj, coe_add, coe_smul, coe_zero, continuous_fst, continuous_fst.fun_add, continuous_fst.fun_const_smul, continuous_snd, continuous_snd.fun_const_smul, fun_add, fun_const_smul, isClosed_eq, smul_add, smul_zero
-/
theorem localization_localization_surj [IsLocalization N T] (x : T) :
    exists y : R × localizationLocalizationSubmodule M N,
        x * algebraMap R T y.2 = algebraMap R T y.1 := by
  rcases IsLocalization.surj N x with ⟨⟨y, s⟩, eq₁⟩
  -- x = y / s
  rcases IsLocalization.surj M y with ⟨⟨z, t⟩, eq₂⟩
  -- y = z / t
  rcases IsLocalization.surj M (s : S) with ⟨⟨z', t'⟩, eq₃⟩
  -- s = z' / t'
  dsimp only at eq₁ eq₂ eq₃
  refine ⟨⟨z * t', z' * t, ?_⟩, ?_⟩ -- x = y / s = (z * t') / (z' * t)
  · rw [mem_localizationLocalizationSubmodule]
    refine ⟨s, t * t', ?_⟩
    rw [map_mul]; rw [← eq₃]; rw [mul_assoc]; rw [← map_mul]; rw [mul_comm t]; rw [Submonoid.coe_mul]
  · simp only [map_mul, IsScalarTower.algebraMap_apply R S T, ← eq₃, ← eq₂, ← eq₁]
    ring

/--
theorem `localization_localization_exists_of_eq` / 定理 `localization_localization_exists_of_eq`

English:
theorem localization_localization_exists_of_eq
  given: [IsLocalization N T] (x y : R)
  proof: by
  rw [IsScalarTower.algebraMap_apply R S T]; rw [IsScalarTower.algebraMap_apply R S T]; rw [IsLocalization.eq_iff_exists N T]
  rintro ⟨z, eq₁⟩
  rcases IsLocalization.surj M (z : S) with ⟨⟨z', s⟩, eq₂⟩
  dsimp only at eq₂
  suffices (algebraMap R S) (x * z' : R) = (algebraMap R S) (y * z') by
    obtain ⟨c, eq₃ : ↑c * (x * z') = ↑c * (y * z')⟩ := (IsLocalization.eq_iff_exists M S).mp this
    refine ⟨⟨c * z', ?_⟩, ?_⟩
    · rw [mem_localizationLocalizationSubmodule]
      refine ⟨z, c * s, ?_⟩
      rw [map_mul]; rw [← eq₂]; rw [Submonoid.coe_mul]; rw [map_mul]; rw [mul_left_comm]
    · rwa [mul_comm _ z', mul_comm _ z', ← mul_assoc, ← mul_assoc] at eq₃
  rw [map_mul]; rw [map_mul]; rw [← eq₂]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm _ (z : S)]; rw [eq₁]; rw [mul_comm _ (z : S)]

中文:
定理 localization_localization_存在_of_eq
  条件: [是Localization N T] (x y : R)
  证明: by
  rw [IsScalarTower.algebraMap_apply R S T]; rw [IsScalarTower.algebraMap_apply R S T]; rw [IsLocalization.eq_iff_exists N T]
  rintro ⟨z, eq₁⟩
  rcases IsLocalization.surj M (z : S) with ⟨⟨z', s⟩, eq₂⟩
  dsimp only at eq₂
  suffices (algebraMap R S) (x * z' : R) = (algebraMap R S) (y * z') by
    obtain ⟨c, eq₃ : ↑c * (x * z') = ↑c * (y * z')⟩ := (IsLocalization.eq_iff_exists M S).mp this
    refine ⟨⟨c * z', ?_⟩, ?_⟩
    · rw [mem_localizationLocalizationSubmodule]
      refine ⟨z, c * s, ?_⟩
      rw [map_mul]; rw [← eq₂]; rw [Submonoid.coe_mul]; rw [map_mul]; rw [mul_left_comm]
    · rwa [mul_comm _ z', mul_comm _ z', ← mul_assoc, ← mul_assoc] at eq₃
  rw [map_mul]; rw [map_mul]; rw [← eq₂]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm _ (z : S)]; rw [eq₁]; rw [mul_comm _ (z : S)]

Depends on / 依赖: IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.surj, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply, eq_iff_exists, map_mul, mem_localizationLocalizationSubmodule
-/
theorem localization_localization_exists_of_eq [IsLocalization N T] (x y : R) :
    algebraMap R T x = algebraMap R T y ->
      exists c : localizationLocalizationSubmodule M N, ↑c * x = ↑c * y := by
  rw [IsScalarTower.algebraMap_apply R S T]; rw [IsScalarTower.algebraMap_apply R S T]; rw [IsLocalization.eq_iff_exists N T]
  rintro ⟨z, eq₁⟩
  rcases IsLocalization.surj M (z : S) with ⟨⟨z', s⟩, eq₂⟩
  dsimp only at eq₂
  suffices (algebraMap R S) (x * z' : R) = (algebraMap R S) (y * z') by
    obtain ⟨c, eq₃ : ↑c * (x * z') = ↑c * (y * z')⟩ := (IsLocalization.eq_iff_exists M S).mp this
    refine ⟨⟨c * z', ?_⟩, ?_⟩
    · rw [mem_localizationLocalizationSubmodule]
      refine ⟨z, c * s, ?_⟩
      rw [map_mul]; rw [← eq₂]; rw [Submonoid.coe_mul]; rw [map_mul]; rw [mul_left_comm]
    · rwa [mul_comm _ z', mul_comm _ z', ← mul_assoc, ← mul_assoc] at eq₃
  rw [map_mul]; rw [map_mul]; rw [← eq₂]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm _ (z : S)]; rw [eq₁]; rw [mul_comm _ (z : S)]

/--
theorem `localization_localization_isLocalization` / 定理 `localization_localization_isLocalization`

English:
theorem localization_localization_isLocalization
  given: [IsLocalization N T]
  proof: localization_localization_map_units M N T
  surj := localization_localization_surj M N T
  exists_of_eq := localization_localization_exists_of_eq M N T _ _

include M in

中文:
定理 localization_localization_isLocalization
  条件: [是Localization N T]
  证明: localization_localization_map_units M N T
  surj := localization_localization_surj M N T
  exists_of_eq := localization_localization_exists_of_eq M N T _ _

include M in

Depends on / 依赖: localization_localization_map_units
-/
theorem localization_localization_isLocalization [IsLocalization N T] :
    IsLocalization (localizationLocalizationSubmodule M N) T where
  map_units := localization_localization_map_units M N T
  surj := localization_localization_surj M N T
  exists_of_eq := localization_localization_exists_of_eq M N T _ _

include M in
/--
theorem `localization_localization_isLocalization_of_has_all_units` / 定理 `localization_localization_isLocalization_of_has_all_units`

English:
theorem localization_localization_isLocalization_of_has_all_units
  statement: [IsLocalization N T]
  proof: by
  convert! localization_localization_isLocalization M N T using 1
  dsimp [localizationLocalizationSubmodule]
  congr
  symm
  rw [sup_eq_left]
  rintro _ ⟨x, hx, rfl⟩
  exact H _ (IsLocalization.map_units _ ⟨x, hx⟩)

include M in

中文:
定理 localization_localization_isLocalization_of_has_all_units
  结论: [是Localization N T]
  证明: by
  convert! localization_localization_isLocalization M N T using 1
  dsimp [localizationLocalizationSubmodule]
  congr
  symm
  rw [sup_eq_left]
  rintro _ ⟨x, hx, rfl⟩
  exact H _ (IsLocalization.map_units _ ⟨x, hx⟩)

include M in

Depends on / 依赖: IsLocalization, IsLocalization.map_units, convert, localizationLocalizationSubmodule, localization_localization_isLocalization, map_units, sup_eq_left
-/
theorem localization_localization_isLocalization_of_has_all_units [IsLocalization N T]
    (H : forall x : S, IsUnit x -> x in N) : IsLocalization (N.comap (algebraMap R S)) T := by
  convert! localization_localization_isLocalization M N T using 1
  dsimp [localizationLocalizationSubmodule]
  congr
  symm
  rw [sup_eq_left]
  rintro _ ⟨x, hx, rfl⟩
  exact H _ (IsLocalization.map_units _ ⟨x, hx⟩)

include M in
/--
theorem `isLocalization_isLocalization_atPrime_isLocalization` / 定理 `isLocalization_isLocalization_atPrime_isLocalization`

English:
theorem isLocalization_isLocalization_atPrime_isLocalization
  statement: (p : Ideal S) [Hp : p.IsPrime]
  proof: by
  apply localization_localization_isLocalization_of_has_all_units M p.primeCompl T
  intro x hx hx'
  exact (Hp.1 : ¬_) (p.eq_top_of_isUnit_mem hx' hx)

中文:
定理 isLocalization_isLocalization_atPrime_isLocalization
  结论: (p : 理想 S) [Hp : p.是素]
  证明: by
  apply localization_localization_isLocalization_of_has_all_units M p.primeCompl T
  intro x hx hx'
  exact (Hp.1 : ¬_) (p.eq_top_of_isUnit_mem hx' hx)

Depends on / 依赖: eq_top_of_isUnit_mem, localization_localization_isLocalization_of_has_all_units, p.eq_top_of_isUnit_mem, p.primeCompl, primeCompl
-/
theorem isLocalization_isLocalization_atPrime_isLocalization (p : Ideal S) [Hp : p.IsPrime]
    [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T (p.comap (algebraMap R S)) := by
  apply localization_localization_isLocalization_of_has_all_units M p.primeCompl T
  intro x hx hx'
  exact (Hp.1 : ¬_) (p.eq_top_of_isUnit_mem hx' hx)

instance (p : Ideal (Localization M)) [p.IsPrime] : Algebra R (Localization.AtPrime p) :=
  inferInstance

instance (p : Ideal (Localization M)) [p.IsPrime] :
    IsScalarTower R (Localization M) (Localization.AtPrime p) :=
  IsScalarTower.of_algebraMap_eq' rfl

/--
Instance `isLocalization_atPrime_localization_atPrime` / 实例 `isLocalization_atPrime_localization_atPrime`

English:
instance isLocalization_atPrime_localization_atPrime
  signature: (p : Ideal (Localization M))
  body: isLocalization_isLocalization_atPrime_isLocalization M _ _

中文:
实例 isLocalization_atPrime_localization_atPrime
  签名: (p : 理想 (Localization M))
  定义体: isLocalization_isLocalization_atPrime_isLocalization M _ _

Depends on / 依赖: isLocalization_isLocalization_atPrime_isLocalization
-/
instance isLocalization_atPrime_localization_atPrime (p : Ideal (Localization M))
    [p.IsPrime] : IsLocalization.AtPrime (Localization.AtPrime p) (p.comap (algebraMap R _)) :=
  isLocalization_isLocalization_atPrime_isLocalization M _ _

/--
Definition of `localizationLocalizationAtPrimeIsoLocalization` / `localizationLocalizationAtPrimeIsoLocalization` 的定义

English:
definition localizationLocalizationAtPrimeIsoLocalization
  signature: (p : Ideal (Localization M))
  body: IsLocalization.algEquiv (p.comap (algebraMap R (Localization M))).primeCompl _ _

中文:
定义 localizationLocalizationAtPrimeIsoLocalization
  签名: (p : 理想 (Localization M))
  定义体: IsLocalization.algEquiv (p.comap (algebraMap R (Localization M))).primeCompl _ _

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv, Localization, algEquiv, algebraMap, p.comap, primeCompl
-/
noncomputable def localizationLocalizationAtPrimeIsoLocalization (p : Ideal (Localization M))
    [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap R (Localization M))) ≃ₐ[R] Localization.AtPrime p :=
  IsLocalization.algEquiv (p.comap (algebraMap R (Localization M))).primeCompl _ _

end

variable (S)

/--
Definition of `localizationAlgebraOfSubmonoidLe` / `localizationAlgebraOfSubmonoidLe` 的定义

English:
abbreviation localizationAlgebraOfSubmonoidLe
  signature: (M N : Submonoid R) (h : M <= N)
  body: (@IsLocalization.lift R _ M S _ _ T _ _ (algebraMap R T)
    (fun y => map_units T ⟨↑y, h y.prop⟩)).toAlgebra

中文:
缩写 localizationAlgebraOfSubmonoidLe
  签名: (M N : 子幺半群 R) (h : M <= N)
  定义体: (@IsLocalization.lift R _ M S _ _ T _ _ (algebraMap R T)
    (fun y => map_units T ⟨↑y, h y.prop⟩)).toAlgebra

Depends on / 依赖: IsLocalization, IsLocalization.lift, algebraMap, map_units, toAlgebra, y.prop
-/
noncomputable abbrev localizationAlgebraOfSubmonoidLe (M N : Submonoid R) (h : M <= N)
    [IsLocalization M S] [IsLocalization N T] : Algebra S T :=
  (@IsLocalization.lift R _ M S _ _ T _ _ (algebraMap R T)
    (fun y => map_units T ⟨↑y, h y.prop⟩)).toAlgebra

/--
theorem `localization_isScalarTower_of_submonoid_le` / 定理 `localization_isScalarTower_of_submonoid_le`

English:
theorem localization_isScalarTower_of_submonoid_le
  statement: (M N : Submonoid R) (h : M <= N)
  proof: letI := localizationAlgebraOfSubmonoidLe S T M N h
  IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm

中文:
定理 localization_isScalarTower_of_submonoid_le
  结论: (M N : 子幺半群 R) (h : M <= N)
  证明: letI := localizationAlgebraOfSubmonoidLe S T M N h
  IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm

Depends on / 依赖: IsLocalization, IsLocalization.lift_comp, IsScalarTower, IsScalarTower.of_algebraMap_eq, lift_comp, localizationAlgebraOfSubmonoidLe, of_algebraMap_eq
-/
theorem localization_isScalarTower_of_submonoid_le (M N : Submonoid R) (h : M <= N)
    [IsLocalization M S] [IsLocalization N T] :
    @IsScalarTower R S T _ (localizationAlgebraOfSubmonoidLe S T M N h).toSMul _ :=
  letI := localizationAlgebraOfSubmonoidLe S T M N h
  IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm

/--
Instance `instAlgebraLocalizationAtPrime` / 实例 `instAlgebraLocalizationAtPrime`

English:
instance instAlgebraLocalizationAtPrime
  signature: (x : Ideal R) [H : x.IsPrime] [IsDomain R]
  body: localizationAlgebraOfSubmonoidLe _ _ x.primeCompl (nonZeroDivisors R)
    (by
      intro a ha
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact fun h => ha (h.symm ▸ x.zero_mem))

中文:
实例 instAlgebraLocalizationAtPrime
  签名: (x : 理想 R) [H : x.是素] [是整环 R]
  定义体: localizationAlgebraOfSubmonoidLe _ _ x.primeCompl (nonZeroDivisors R)
    (by
      intro a ha
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact fun h => ha (h.symm ▸ x.zero_mem))

Depends on / 依赖: h.symm, localizationAlgebraOfSubmonoidLe, mem_nonZeroDivisors_iff_ne_zero, nonZeroDivisors, primeCompl, x.primeCompl, x.zero_mem, zero_mem
-/
noncomputable instance instAlgebraLocalizationAtPrime (x : Ideal R) [H : x.IsPrime] [IsDomain R] :
    Algebra (Localization.AtPrime x) (Localization (nonZeroDivisors R)) :=
  localizationAlgebraOfSubmonoidLe _ _ x.primeCompl (nonZeroDivisors R)
    (by
      intro a ha
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact fun h => ha (h.symm ▸ x.zero_mem))

instance {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime] :
    IsScalarTower R (Localization.AtPrime p) (FractionRing R) :=
  localization_isScalarTower_of_submonoid_le (Localization.AtPrime p) (FractionRing R)
    p.primeCompl (nonZeroDivisors R) p.primeCompl_le_nonZeroDivisors

/--
theorem `isLocalization_of_submonoid_le` / 定理 `isLocalization_of_submonoid_le`

English:
theorem isLocalization_of_submonoid_le
  statement: (M N : Submonoid R) (h : M <= N) [IsLocalization M S]
  proof: by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert! IsLocalization.map_units T ⟨y, hy⟩
    exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
  surj y := by
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj N y
    refine ⟨⟨algebraMap R S x, _, _, s.prop, rfl⟩, ?_⟩
    simpa [← IsScalarTower.algebraMap_apply] using! e
  exists_of_eq {x₁ x₂} := by
    obtain ⟨⟨y₁, s₁⟩, e₁⟩ := IsLocalization.surj M x₁
    obtain ⟨⟨y₂, s₂⟩, e₂⟩ := IsLocalization.surj M x₂
    refine (Set.exists_image_iff (algebraMap R S) N fun c => c * x₁ = c * x₂).mpr.comp ?_
    dsimp only at e₁ e₂ ⊢
    suffices algebraMap R T (y₁ * s₂) = algebraMap R T (y₂ * s₁) ->
        exists a : N, algebraMap R S (a * (y₁ * s₂)) = algebraMap R S (a * (y₂ * s₁)) by
      have h₁ := @IsUnit.mul_left_inj T _ _ (algebraMap S T x₁) (algebraMap S T x₂)
        (IsLocalization.map_units T ⟨(s₁ : R), h s₁.prop⟩)
      have h₂ := @IsUnit.mul_left_inj T _ _ ((algebraMap S T x₁) * (algebraMap R T s₁))
        ((algebraMap S T x₂) * (algebraMap R T s₁))
        (IsLocalization.map_units T ⟨(s₂ : R), h s₂.prop⟩)
      simp only [IsScalarTower.algebraMap_apply R S T] at h₁ h₂
      simp only [IsScalarTower.algebraMap_apply R S T, map_mul, ← e₁, ← e₂, ← mul_assoc,
        mul_right_comm _ (algebraMap R S s₂),
        (IsLocalization.map_units S s₁).mul_left_inj,
        (IsLocalization.map_units S s₂).mul_left_inj] at this
      rw [h₂]; rw [h₁] at this
      simpa only [mul_comm] using! this
    simp_rw [IsLocalization.eq_iff_exists N T, IsLocalization.eq_iff_exists M S]
    intro ⟨a, e⟩
    exact ⟨a, 1, by convert! e using 1 <;> simp⟩

中文:
定理 isLocalization_of_submonoid_le
  结论: (M N : 子幺半群 R) (h : M <= N) [是Localization M S]
  证明: by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert! IsLocalization.map_units T ⟨y, hy⟩
    exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
  surj y := by
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj N y
    refine ⟨⟨algebraMap R S x, _, _, s.prop, rfl⟩, ?_⟩
    simpa [← IsScalarTower.algebraMap_apply] using! e
  exists_of_eq {x₁ x₂} := by
    obtain ⟨⟨y₁, s₁⟩, e₁⟩ := IsLocalization.surj M x₁
    obtain ⟨⟨y₂, s₂⟩, e₂⟩ := IsLocalization.surj M x₂
    refine (Set.exists_image_iff (algebraMap R S) N fun c => c * x₁ = c * x₂).mpr.comp ?_
    dsimp only at e₁ e₂ ⊢
    suffices algebraMap R T (y₁ * s₂) = algebraMap R T (y₂ * s₁) ->
        exists a : N, algebraMap R S (a * (y₁ * s₂)) = algebraMap R S (a * (y₂ * s₁)) by
      have h₁ := @IsUnit.mul_left_inj T _ _ (algebraMap S T x₁) (algebraMap S T x₂)
        (IsLocalization.map_units T ⟨(s₁ : R), h s₁.prop⟩)
      have h₂ := @IsUnit.mul_left_inj T _ _ ((algebraMap S T x₁) * (algebraMap R T s₁))
        ((algebraMap S T x₂) * (algebraMap R T s₁))
        (IsLocalization.map_units T ⟨(s₂ : R), h s₂.prop⟩)
      simp only [IsScalarTower.algebraMap_apply R S T] at h₁ h₂
      simp only [IsScalarTower.algebraMap_apply R S T, map_mul, ← e₁, ← e₂, ← mul_assoc,
        mul_right_comm _ (algebraMap R S s₂),
        (IsLocalization.map_units S s₁).mul_left_inj,
        (IsLocalization.map_units S s₂).mul_left_inj] at this
      rw [h₂]; rw [h₁] at this
      simpa only [mul_comm] using! this
    simp_rw [IsLocalization.eq_iff_exists N T, IsLocalization.eq_iff_exists M S]
    intro ⟨a, e⟩
    exact ⟨a, 1, by convert! e using 1 <;> simp⟩

Depends on / 依赖: IsLocalization, IsLocalization.map_units, IsLocalization.surj, IsScalarTower, IsScalarTower.algebraMap_apply, Set.exists_image_iff, algebraMap, algebraMap_apply, convert, exists_image_iff, exists_of_eq, map_units, mpr.comp, s.prop
-/
theorem isLocalization_of_submonoid_le (M N : Submonoid R) (h : M <= N) [IsLocalization M S]
    [IsLocalization N T] [Algebra S T] [IsScalarTower R S T] :
    IsLocalization (N.map (algebraMap R S)) T where
  map_units := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert! IsLocalization.map_units T ⟨y, hy⟩
    exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
  surj y := by
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj N y
    refine ⟨⟨algebraMap R S x, _, _, s.prop, rfl⟩, ?_⟩
    simpa [← IsScalarTower.algebraMap_apply] using! e
  exists_of_eq {x₁ x₂} := by
    obtain ⟨⟨y₁, s₁⟩, e₁⟩ := IsLocalization.surj M x₁
    obtain ⟨⟨y₂, s₂⟩, e₂⟩ := IsLocalization.surj M x₂
    refine (Set.exists_image_iff (algebraMap R S) N fun c => c * x₁ = c * x₂).mpr.comp ?_
    dsimp only at e₁ e₂ ⊢
    suffices algebraMap R T (y₁ * s₂) = algebraMap R T (y₂ * s₁) ->
        exists a : N, algebraMap R S (a * (y₁ * s₂)) = algebraMap R S (a * (y₂ * s₁)) by
      have h₁ := @IsUnit.mul_left_inj T _ _ (algebraMap S T x₁) (algebraMap S T x₂)
        (IsLocalization.map_units T ⟨(s₁ : R), h s₁.prop⟩)
      have h₂ := @IsUnit.mul_left_inj T _ _ ((algebraMap S T x₁) * (algebraMap R T s₁))
        ((algebraMap S T x₂) * (algebraMap R T s₁))
        (IsLocalization.map_units T ⟨(s₂ : R), h s₂.prop⟩)
      simp only [IsScalarTower.algebraMap_apply R S T] at h₁ h₂
      simp only [IsScalarTower.algebraMap_apply R S T, map_mul, ← e₁, ← e₂, ← mul_assoc,
        mul_right_comm _ (algebraMap R S s₂),
        (IsLocalization.map_units S s₁).mul_left_inj,
        (IsLocalization.map_units S s₂).mul_left_inj] at this
      rw [h₂]; rw [h₁] at this
      simpa only [mul_comm] using! this
    simp_rw [IsLocalization.eq_iff_exists N T, IsLocalization.eq_iff_exists M S]
    intro ⟨a, e⟩
    exact ⟨a, 1, by convert! e using 1 <;> simp⟩

/--
theorem `isLocalization_of_is_exists_mul_mem` / 定理 `isLocalization_of_is_exists_mul_mem`

English:
theorem isLocalization_of_is_exists_mul_mem
  statement: (M N : Submonoid R) [IsLocalization M S] (h : M <= N)
  proof: by
    obtain ⟨m, hm⟩ := h' y
    have := IsLocalization.map_units S ⟨_, hm⟩
    rw [map_mul] at this
    exact (IsUnit.mul_iff.mp this).2
  surj z := by
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M z
    exact ⟨⟨y, _, h s.prop⟩, e⟩
  exists_of_eq {_ _} := by
    rw [IsLocalization.eq_iff_exists M]
    exact fun ⟨x, hx⟩ => ⟨⟨_, h x.prop⟩, hx⟩

中文:
定理 isLocalization_of_is_存在_mul_mem
  结论: (M N : 子幺半群 R) [是Localization M S] (h : M <= N)
  证明: by
    obtain ⟨m, hm⟩ := h' y
    have := IsLocalization.map_units S ⟨_, hm⟩
    rw [map_mul] at this
    exact (IsUnit.mul_iff.mp this).2
  surj z := by
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M z
    exact ⟨⟨y, _, h s.prop⟩, e⟩
  exists_of_eq {_ _} := by
    rw [IsLocalization.eq_iff_exists M]
    exact fun ⟨x, hx⟩ => ⟨⟨_, h x.prop⟩, hx⟩

Depends on / 依赖: IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.map_units, IsLocalization.surj, IsUnit, IsUnit.mul_iff.mp, eq_iff_exists, exists_of_eq, map_mul, map_units, mul_iff, s.prop, x.prop
-/
theorem isLocalization_of_is_exists_mul_mem (M N : Submonoid R) [IsLocalization M S] (h : M <= N)
    (h' : forall x : N, exists m : R, m * x in M) : IsLocalization N S where
  map_units y := by
    obtain ⟨m, hm⟩ := h' y
    have := IsLocalization.map_units S ⟨_, hm⟩
    rw [map_mul] at this
    exact (IsUnit.mul_iff.mp this).2
  surj z := by
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M z
    exact ⟨⟨y, _, h s.prop⟩, e⟩
  exists_of_eq {_ _} := by
    rw [IsLocalization.eq_iff_exists M]
    exact fun ⟨x, hx⟩ => ⟨⟨_, h x.prop⟩, hx⟩

/--
theorem `mk'_eq_algebraMap_mk'_of_submonoid_le` / 定理 `mk'_eq_algebraMap_mk'_of_submonoid_le`

English:
theorem mk'_eq_algebraMap_mk'_of_submonoid_le
  statement: {M N : Submonoid R} (h : M <= N) [IsLocalization M S]
  proof: mk'_eq_iff_eq_mul.mpr (by simp only [IsScalarTower.algebraMap_apply R S T, ← map_mul, mk'_spec])

中文:
定理 mk'_eq_algebraMap_mk'_of_submonoid_le
  结论: {M N : 子幺半群 R} (h : M <= N) [是Localization M S]
  证明: mk'_eq_iff_eq_mul.mpr (by simp only [IsScalarTower.algebraMap_apply R S T, ← map_mul, mk'_spec])
-/
theorem mk'_eq_algebraMap_mk'_of_submonoid_le {M N : Submonoid R} (h : M <= N) [IsLocalization M S]
    [IsLocalization N T] [Algebra S T] [IsScalarTower R S T] (x : R) (y : {a : R // a in M}) :
    mk' T x ⟨y.1, h y.2⟩ = algebraMap S T (mk' S x y) :=
  mk'_eq_iff_eq_mul.mpr (by simp only [IsScalarTower.algebraMap_apply R S T, ← map_mul, mk'_spec])

end LocalizationLocalization

end IsLocalization

namespace IsFractionRing

variable {R : Type*} [CommRing R] (M : Submonoid R)

open IsLocalization

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isFractionRing_of_isLocalization` / 定理 `isFractionRing_of_isLocalization`

English:
theorem isFractionRing_of_isLocalization
  statement: (S T : Type*) [CommRing S] [CommRing T] [Algebra R S]
  proof: by
  have := isLocalization_of_submonoid_le S T M (nonZeroDivisors R) hM
  refine @isLocalization_of_is_exists_mul_mem _ _ _ _ _ _ _ this ?_ ?_
  · exact map_nonZeroDivisors_le M S
  · rintro ⟨x, -, hx⟩
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M x
    use algebraMap R S s
    rw [mul_comm]; rw [Subtype.coe_mk]; rw [e]
    refine Set.mem_image_of_mem (algebraMap R S) (mem_nonZeroDivisors_iff_right.mpr ?_)
    intro z hz
    apply IsLocalization.injective S hM
    rw [map_zero]
    apply hx
    rw [← (map_units S s).mul_left_inj]; rw [mul_assoc]; rw [e]; rw [← map_mul]; rw [hz]; rw [map_zero]; rw [zero_mul]

中文:
定理 isFractionRing_of_isLocalization
  结论: (S T : 类型) [交换环 S] [交换环 T] [代数 R S]
  证明: by
  have := isLocalization_of_submonoid_le S T M (nonZeroDivisors R) hM
  refine @isLocalization_of_is_exists_mul_mem _ _ _ _ _ _ _ this ?_ ?_
  · exact map_nonZeroDivisors_le M S
  · rintro ⟨x, -, hx⟩
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M x
    use algebraMap R S s
    rw [mul_comm]; rw [Subtype.coe_mk]; rw [e]
    refine Set.mem_image_of_mem (algebraMap R S) (mem_nonZeroDivisors_iff_right.mpr ?_)
    intro z hz
    apply IsLocalization.injective S hM
    rw [map_zero]
    apply hx
    rw [← (map_units S s).mul_left_inj]; rw [mul_assoc]; rw [e]; rw [← map_mul]; rw [hz]; rw [map_zero]; rw [zero_mul]

Depends on / 依赖: IsLocalization, IsLocalization.injective, IsLocalization.surj, Set.mem_image_of_mem, Subtype, Subtype.coe_mk, algebraMap, coe_mk, injective, isLocalization_of_is_exists_mul_mem, isLocalization_of_submonoid_le, map_nonZeroDivisors_le, map_units, map_zero, mem_image_of_mem, mem_nonZeroDivisors_iff_right, mem_nonZeroDivisors_iff_right.mpr, mul_comm, mul_left_inj, nonZeroDivisors
-/
theorem isFractionRing_of_isLocalization (S T : Type*) [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] [IsLocalization M S] [IsFractionRing R T]
    (hM : M <= nonZeroDivisors R) : IsFractionRing S T := by
  have := isLocalization_of_submonoid_le S T M (nonZeroDivisors R) hM
  refine @isLocalization_of_is_exists_mul_mem _ _ _ _ _ _ _ this ?_ ?_
  · exact map_nonZeroDivisors_le M S
  · rintro ⟨x, -, hx⟩
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M x
    use algebraMap R S s
    rw [mul_comm]; rw [Subtype.coe_mk]; rw [e]
    refine Set.mem_image_of_mem (algebraMap R S) (mem_nonZeroDivisors_iff_right.mpr ?_)
    intro z hz
    apply IsLocalization.injective S hM
    rw [map_zero]
    apply hx
    rw [← (map_units S s).mul_left_inj]; rw [mul_assoc]; rw [e]; rw [← map_mul]; rw [hz]; rw [map_zero]; rw [zero_mul]

/--
theorem `isFractionRing_of_isDomain_of_isLocalization` / 定理 `isFractionRing_of_isDomain_of_isLocalization`

English:
theorem isFractionRing_of_isDomain_of_isLocalization
  statement: [IsDomain R] (S T : Type*) [CommRing S]
  proof: by
  have := IsFractionRing.nontrivial R T
  have := (algebraMap S T).domain_nontrivial
  apply isFractionRing_of_isLocalization M S T
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hx'
  apply @zero_ne_one S
  rw [← (algebraMap R S).map_one]; rw [← @mk'_one R _ M]; rw [@comm _ Eq]; rw [mk'_eq_zero_iff]
  exact ⟨⟨x, hx⟩, by simp [hx']⟩

中文:
定理 isFractionRing_of_isDomain_of_isLocalization
  结论: [是整环 R] (S T : 类型) [交换环 S]
  证明: by
  have := IsFractionRing.nontrivial R T
  have := (algebraMap S T).domain_nontrivial
  apply isFractionRing_of_isLocalization M S T
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hx'
  apply @zero_ne_one S
  rw [← (algebraMap R S).map_one]; rw [← @mk'_one R _ M]; rw [@comm _ Eq]; rw [mk'_eq_zero_iff]
  exact ⟨⟨x, hx⟩, by simp [hx']⟩

Depends on / 依赖: IsFractionRing, IsFractionRing.nontrivial, _eq_zero_iff, _one, algebraMap, domain_nontrivial, isFractionRing_of_isLocalization, map_one, mem_nonZeroDivisors_iff_ne_zero, nontrivial, zero_ne_one
-/
theorem isFractionRing_of_isDomain_of_isLocalization [IsDomain R] (S T : Type*) [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalization M S] [IsFractionRing R T] : IsFractionRing S T := by
  have := IsFractionRing.nontrivial R T
  have := (algebraMap S T).domain_nontrivial
  apply isFractionRing_of_isLocalization M S T
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hx'
  apply @zero_ne_one S
  rw [← (algebraMap R S).map_one]; rw [← @mk'_one R _ M]; rw [@comm _ Eq]; rw [mk'_eq_zero_iff]
  exact ⟨⟨x, hx⟩, by simp [hx']⟩

instance {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime] :
    IsFractionRing (Localization.AtPrime p) (FractionRing R) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl
    (Localization.AtPrime p) (FractionRing R)

end IsFractionRing
