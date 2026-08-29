/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Submodules in localizations of commutative rings

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
variable [Algebra R S]

namespace IsLocalization

-- This was previously a `hasCoe` instance, but if `S = R` then this will loop.
-- It could be a `hasCoeT` instance, but we keep it explicit here to avoid slowing down
-- the rest of the library.
/--
Definition of `coeSubmodule` / `coeSubmodule` 的定义

English:
definition coeSubmodule
  signature: (I : Ideal R)
  body: Submodule.map (Algebra.linearMap R S) I

中文:
定义 coeSubmodule
  签名: (I : 理想 R)
  定义体: Submodule.map (Algebra.linearMap R S) I

Depends on / 依赖: Algebra, Algebra.linearMap, Submodule, Submodule.map, linearMap
-/
def coeSubmodule (I : Ideal R) : Submodule R S :=
  Submodule.map (Algebra.linearMap R S) I

/--
theorem `mem_coeSubmodule` / 定理 `mem_coeSubmodule`

English:
theorem mem_coeSubmodule
  given: (I : Ideal R) {x : S}
  proof: Iff.rfl

中文:
定理 mem_coeSubmodule
  条件: (I : 理想 R) {x : S}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_coeSubmodule (I : Ideal R) {x : S} :
    x in coeSubmodule S I ↔ exists y : R, y in I ∧ algebraMap R S y = x :=
  Iff.rfl

/--
theorem `coeSubmodule_mono` / 定理 `coeSubmodule_mono`

English:
theorem coeSubmodule_mono
  given: {I J : Ideal R} (h : I <= J)
  statement: coeSubmodule S I <= coeSubmodule S J
  proof: Submodule.map_mono h

@[simp]

中文:
定理 coeSubmodule_mono
  条件: {I J : 理想 R} (h : I <= J)
  结论: coeSubmodule S I <= coeSubmodule S J
  证明: Submodule.map_mono h

@[simp]

Depends on / 依赖: Submodule, Submodule.map_mono, map_mono
-/
theorem coeSubmodule_mono {I J : Ideal R} (h : I <= J) : coeSubmodule S I <= coeSubmodule S J :=
  Submodule.map_mono h

@[simp]
/--
theorem `coeSubmodule_bot` / 定理 `coeSubmodule_bot`

English:
theorem coeSubmodule_bot
  statement: coeSubmodule S (⊥ : Ideal R) = ⊥
  proof: by
  rw [coeSubmodule]; rw [Submodule.map_bot]

@[simp]

中文:
定理 coeSubmodule_bot
  结论: coeSubmodule S (⊥ : 理想 R) = ⊥
  证明: by
  rw [coeSubmodule]; rw [Submodule.map_bot]

@[simp]

Depends on / 依赖: Submodule, Submodule.map_bot, coeSubmodule, map_bot
-/
theorem coeSubmodule_bot : coeSubmodule S (⊥ : Ideal R) = ⊥ := by
  rw [coeSubmodule]; rw [Submodule.map_bot]

@[simp]
/--
theorem `coeSubmodule_top` / 定理 `coeSubmodule_top`

English:
theorem coeSubmodule_top
  statement: coeSubmodule S (⊤ : Ideal R) = 1
  proof: by
  rw [coeSubmodule]; rw [Submodule.map_top]; rw [Submodule.one_eq_range]

@[simp]

中文:
定理 coeSubmodule_top
  结论: coeSubmodule S (⊤ : 理想 R) = 1
  证明: by
  rw [coeSubmodule]; rw [Submodule.map_top]; rw [Submodule.one_eq_range]

@[simp]

Depends on / 依赖: Submodule, Submodule.map_top, Submodule.one_eq_range, coeSubmodule, map_top, one_eq_range
-/
theorem coeSubmodule_top : coeSubmodule S (⊤ : Ideal R) = 1 := by
  rw [coeSubmodule]; rw [Submodule.map_top]; rw [Submodule.one_eq_range]

@[simp]
/--
theorem `coeSubmodule_sup` / 定理 `coeSubmodule_sup`

English:
theorem coeSubmodule_sup
  given: (I J : Ideal R)
  proof: Submodule.map_sup _ _ _

@[simp]

中文:
定理 coeSubmodule_sup
  条件: (I J : 理想 R)
  证明: Submodule.map_sup _ _ _

@[simp]

Depends on / 依赖: Submodule, Submodule.map_sup, map_sup
-/
theorem coeSubmodule_sup (I J : Ideal R) :
    coeSubmodule S (I ⊔ J) = coeSubmodule S I ⊔ coeSubmodule S J :=
  Submodule.map_sup _ _ _

@[simp]
/--
theorem `coeSubmodule_mul` / 定理 `coeSubmodule_mul`

English:
theorem coeSubmodule_mul
  given: (I J : Ideal R)
  proof: Submodule.map_mul _ _ (Algebra.ofId R S)

中文:
定理 coeSubmodule_mul
  条件: (I J : 理想 R)
  证明: Submodule.map_mul _ _ (Algebra.ofId R S)

Depends on / 依赖: Algebra, Algebra.ofId, Submodule, Submodule.map_mul, map_mul
-/
theorem coeSubmodule_mul (I J : Ideal R) :
    coeSubmodule S (I * J) = coeSubmodule S I * coeSubmodule S J :=
  Submodule.map_mul _ _ (Algebra.ofId R S)

/--
theorem `coeSubmodule_fg` / 定理 `coeSubmodule_fg`

English:
theorem coeSubmodule_fg
  given: (hS : Function.Injective (algebraMap R S)) (I : Ideal R)
  proof: ⟨Submodule.fg_of_fg_map_injective _ hS, Submodule.FG.map _⟩

@[simp]

中文:
定理 coeSubmodule_fg
  条件: (hS : 函数.单射 (algebraMap R S)) (I : 理想 R)
  证明: ⟨Submodule.fg_of_fg_map_injective _ hS, Submodule.FG.map _⟩

@[simp]

Depends on / 依赖: Submodule, Submodule.FG.map, Submodule.fg_of_fg_map_injective, fg_of_fg_map_injective
-/
theorem coeSubmodule_fg (hS : Function.Injective (algebraMap R S)) (I : Ideal R) :
    Submodule.FG (coeSubmodule S I) ↔ Submodule.FG I :=
  ⟨Submodule.fg_of_fg_map_injective _ hS, Submodule.FG.map _⟩

@[simp]
/--
theorem `coeSubmodule_span` / 定理 `coeSubmodule_span`

English:
theorem coeSubmodule_span
  given: (s : Set R)
  proof: by
  rw [IsLocalization.coeSubmodule]; rw [Ideal.span]; rw [Submodule.map_span]
  rfl

中文:
定理 coeSubmodule_span
  条件: (s : 集合 R)
  证明: by
  rw [IsLocalization.coeSubmodule]; rw [Ideal.span]; rw [Submodule.map_span]
  rfl

Depends on / 依赖: Ideal.span, IsLocalization, IsLocalization.coeSubmodule, Submodule, Submodule.map_span, coeSubmodule, map_span
-/
theorem coeSubmodule_span (s : Set R) :
    coeSubmodule S (Ideal.span s) = Submodule.span R (algebraMap R S '' s) := by
  rw [IsLocalization.coeSubmodule]; rw [Ideal.span]; rw [Submodule.map_span]
  rfl

/--
theorem `coeSubmodule_span_singleton` / 定理 `coeSubmodule_span_singleton`

English:
theorem coeSubmodule_span_singleton
  given: (x : R)
  proof: by
  rw [coeSubmodule_span]; rw [Set.image_singleton]

中文:
定理 coeSubmodule_span_singleton
  条件: (x : R)
  证明: by
  rw [coeSubmodule_span]; rw [Set.image_singleton]

Depends on / 依赖: Set.image_singleton, coeSubmodule_span, image_singleton
-/
theorem coeSubmodule_span_singleton (x : R) :
    coeSubmodule S (Ideal.span {x}) = Submodule.span R {(algebraMap R S) x} := by
  rw [coeSubmodule_span]; rw [Set.image_singleton]

variable [IsLocalization M S]

include M in
/--
theorem `isNoetherianRing` / 定理 `isNoetherianRing`

English:
theorem isNoetherianRing
  given: (h : IsNoetherianRing R)
  statement: IsNoetherianRing S
  proof: by
  rw [isNoetherianRing_iff]; rw [isNoetherian_iff] at h ⊢
  exact OrderEmbedding.wellFounded (IsLocalization.orderEmbedding M S).dual h

中文:
定理 isNoetherianRing
  条件: (h : 是Noether环 R)
  结论: 是Noether环 S
  证明: by
  rw [isNoetherianRing_iff]; rw [isNoetherian_iff] at h ⊢
  exact OrderEmbedding.wellFounded (IsLocalization.orderEmbedding M S).dual h

Depends on / 依赖: IsLinearTopology, IsLocalization, IsLocalization.orderEmbedding, OrderEmbedding, OrderEmbedding.wellFounded, isNoetherianRing_iff, isNoetherian_iff, orderEmbedding, wellFounded
-/
theorem isNoetherianRing (h : IsNoetherianRing R) : IsNoetherianRing S := by
  rw [isNoetherianRing_iff]; rw [isNoetherian_iff] at h ⊢
  exact OrderEmbedding.wellFounded (IsLocalization.orderEmbedding M S).dual h

instance {R} [CommRing R] [IsNoetherianRing R] (S : Submonoid R) :
    IsNoetherianRing (Localization S) :=
  IsLocalization.isNoetherianRing S _ ‹_›

/--
lemma `_root_.Algebra.EssFiniteType.isNoetherianRing` / 引理 `_root_.Algebra.EssFiniteType.isNoetherianRing`

English:
lemma _root_.Algebra.EssFiniteType.isNoetherianRing
  proof: by
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) _
    (Algebra.FiniteType.isNoetherianRing R _)

中文:
引理 _root_.代数.EssFiniteType.isNoetherianRing
  证明: by
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) _
    (Algebra.FiniteType.isNoetherianRing R _)

Depends on / 依赖: Algebra, Algebra.EssFiniteType.submonoid, Algebra.FiniteType.isNoetherianRing, EssFiniteType, FiniteType, IsLocalization, IsLocalization.isNoetherianRing, isNoetherianRing, submonoid
-/
lemma _root_.Algebra.EssFiniteType.isNoetherianRing
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S := by
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) _
    (Algebra.FiniteType.isNoetherianRing R _)
section NonZeroDivisors

variable {R : Type*} [CommRing R] {M : Submonoid R}
  {S : Type*} [CommRing S] [Algebra R S] [IsLocalization M S]

@[gcongr, mono]
/--
theorem `coeSubmodule_le_coeSubmodule` / 定理 `coeSubmodule_le_coeSubmodule`

English:
theorem coeSubmodule_le_coeSubmodule
  given: (h : M <= nonZeroDivisors R) {I J : Ideal R}
  proof: -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify the value of `f` here:
  Submodule.map_le_map_iff_of_injective (f := Algebra.linearMap R S) (IsLocalization.injective _ h)
    _ _

@[gcongr, mono]

中文:
定理 coeSubmodule_le_coeSubmodule
  条件: (h : M <= nonZeroDivisors R) {I J : 理想 R}
  证明: -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify the value of `f` here:
  Submodule.map_le_map_iff_of_injective (f := Algebra.linearMap R S) (IsLocalization.injective _ h)
    _ _

@[gcongr, mono]
-/
theorem coeSubmodule_le_coeSubmodule (h : M <= nonZeroDivisors R) {I J : Ideal R} :
    coeSubmodule S I <= coeSubmodule S J ↔ I <= J :=
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify the value of `f` here:
  Submodule.map_le_map_iff_of_injective (f := Algebra.linearMap R S) (IsLocalization.injective _ h)
    _ _

@[gcongr, mono]
/--
theorem `coeSubmodule_strictMono` / 定理 `coeSubmodule_strictMono`

English:
theorem coeSubmodule_strictMono
  given: (h : M <= nonZeroDivisors R)
  proof: strictMono_of_le_iff_le fun _ _ => (coeSubmodule_le_coeSubmodule h).symm

中文:
定理 coeSubmodule_strictMono
  条件: (h : M <= nonZeroDivisors R)
  证明: strictMono_of_le_iff_le fun _ _ => (coeSubmodule_le_coeSubmodule h).symm

Depends on / 依赖: coeSubmodule_le_coeSubmodule, strictMono_of_le_iff_le
-/
theorem coeSubmodule_strictMono (h : M <= nonZeroDivisors R) :
    StrictMono (coeSubmodule S : Ideal R -> Submodule R S) :=
  strictMono_of_le_iff_le fun _ _ => (coeSubmodule_le_coeSubmodule h).symm

variable (S)

/--
theorem `coeSubmodule_injective` / 定理 `coeSubmodule_injective`

English:
theorem coeSubmodule_injective
  given: (h : M <= nonZeroDivisors R)
  proof: .of_eq_imp_le fun hl => (coeSubmodule_le_coeSubmodule h).mp hl.le

中文:
定理 coeSubmodule_injective
  条件: (h : M <= nonZeroDivisors R)
  证明: .of_eq_imp_le fun hl => (coeSubmodule_le_coeSubmodule h).mp hl.le

Depends on / 依赖: coeSubmodule_le_coeSubmodule, hl.le, of_eq_imp_le
-/
theorem coeSubmodule_injective (h : M <= nonZeroDivisors R) :
    Function.Injective (coeSubmodule S : Ideal R -> Submodule R S) :=
  .of_eq_imp_le fun hl => (coeSubmodule_le_coeSubmodule h).mp hl.le

/--
theorem `coeSubmodule_isPrincipal` / 定理 `coeSubmodule_isPrincipal`

English:
theorem coeSubmodule_isPrincipal
  given: {I : Ideal R} (h : M <= nonZeroDivisors R)
  proof: by
  constructor <;> rintro ⟨⟨x, hx⟩⟩
  · have x_mem : x in coeSubmodule S I := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨x, _, rfl⟩ := (mem_coeSubmodule _ _).mp x_mem
    refine ⟨⟨x, coeSubmodule_injective S h ?_⟩⟩
    rw [Ideal.submodule_span_eq]; rw [hx]; rw [coeSubmodule_span_sin

中文:
定理 coeSubmodule_isPrincipal
  条件: {I : 理想 R} (h : M <= nonZeroDivisors R)
  证明: by
  constructor <;> rintro ⟨⟨x, hx⟩⟩
  · have x_mem : x in coeSubmodule S I := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨x, _, rfl⟩ := (mem_coeSubmodule _ _).mp x_mem
    refine ⟨⟨x, coeSubmodule_injective S h ?_⟩⟩
    rw [Ideal.submodule_span_eq]; rw [hx]; rw [coeSubmodule_span_sin

Depends on / 依赖: Ideal.submodule_span_eq, Submodule, Submodule.mem_span_singleton_self, algebraMap, coeSubmodule, coeSubmodule_injective, coeSubmodule_span_singleton, hx.symm, mem_coeSubmodule, mem_span_singleton_self, submodule_span_eq, x_mem
-/
theorem coeSubmodule_isPrincipal {I : Ideal R} (h : M <= nonZeroDivisors R) :
    (coeSubmodule S I).IsPrincipal ↔ I.IsPrincipal := by
  constructor <;> rintro ⟨⟨x, hx⟩⟩
  · have x_mem : x in coeSubmodule S I := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨x, _, rfl⟩ := (mem_coeSubmodule _ _).mp x_mem
    refine ⟨⟨x, coeSubmodule_injective S h ?_⟩⟩
    rw [Ideal.submodule_span_eq]; rw [hx]; rw [coeSubmodule_span_singleton]
  · refine ⟨⟨algebraMap R S x, ?_⟩⟩
    rw [hx]; rw [Ideal.submodule_span_eq]; rw [coeSubmodule_span_singleton]

end NonZeroDivisors

variable {S}

/--
theorem `mem_span_iff` / 定理 `mem_span_iff`

English:
theorem mem_span_iff
  statement: {N : Type*} [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  proof: by
  constructor
  · intro h
    refine Submodule.span_induction ?_ ?_ ?_ ?_ h
    · rintro x hx
      exact ⟨x, Submodule.subset_span hx, 1, by rw [mk'_one, map_one, one_smul]⟩
    · exact ⟨0, Submodule.zero_mem _, 1, by rw [mk'_one, map_one, one_smul]⟩
    · rintro _ _ _ _ ⟨y, hy, z, rfl⟩ ⟨y', hy'

中文:
定理 mem_span_iff
  结论: {N : 类型} [加法交换幺半群 N] [模 R N] [模 S N] [标量塔 R S N]
  证明: by
  constructor
  · intro h
    refine Submodule.span_induction ?_ ?_ ?_ ?_ h
    · rintro x hx
      exact ⟨x, Submodule.subset_span hx, 1, by rw [mk'_one, map_one, one_smul]⟩
    · exact ⟨0, Submodule.zero_mem _, 1, by rw [mk'_one, map_one, one_smul]⟩
    · rintro _ _ _ _ ⟨y, hy, z, rfl⟩ ⟨y', hy'

Depends on / 依赖: IsScalarTower, IsScalarTower.algeb, IsScalarTower.algebraMap_smul, Submodule, Submodule.add_mem, Submodule.smul_mem, Submodule.span_induction, Submodule.subset_span, Submodule.zero_mem, _one, add_mem, algebraMap_smul, map_one, one_smul, smul_add, smul_mem, span_induction, subset_span, zero_mem
-/
theorem mem_span_iff {N : Type*} [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    {x : N} {a : Set N} :
    x in Submodule.span S a ↔ exists y in Submodule.span R a, exists z : M, x = mk' S 1 z • y := by
  constructor
  · intro h
    refine Submodule.span_induction ?_ ?_ ?_ ?_ h
    · rintro x hx
      exact ⟨x, Submodule.subset_span hx, 1, by rw [mk'_one, map_one, one_smul]⟩
    · exact ⟨0, Submodule.zero_mem _, 1, by rw [mk'_one, map_one, one_smul]⟩
    · rintro _ _ _ _ ⟨y, hy, z, rfl⟩ ⟨y', hy', z', rfl⟩
      refine
        ⟨(z' : R) • y + (z : R) • y',
          Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hy'), z * z', ?_⟩
      rw [smul_add]; rw [← IsScalarTower.algebraMap_smul S (z : R)]; rw [←
        IsScalarTower.algebraMap_smul S (z' : R)]; rw [smul_smul]; rw [smul_smul]
      congr 1
      · rw [← mul_one (1 : R), mk'_mul, mul_assoc, mk'_spec, map_one, mul_one, mul_one]
      · rw [← mul_one (1 : R), mk'_mul, mul_right_comm, mk'_spec, map_one, mul_one, one_mul]
    · rintro a _ _ ⟨y, hy, z, rfl⟩
      obtain ⟨y', z', rfl⟩ := exists_mk'_eq M a
      refine ⟨y' • y, Submodule.smul_mem _ _ hy, z' * z, ?_⟩
      rw [← IsScalarTower.algebraMap_smul S y']; rw [smul_smul]; rw [← mk'_mul]; rw [smul_smul]; rw [mul_comm (mk' S _ _)]; rw [mul_mk'_eq_mk'_of_mul]
  · rintro ⟨y, hy, z, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.span_subset_span R S _ hy)

/--
theorem `mem_span_map` / 定理 `mem_span_map`

English:
theorem mem_span_map
  given: {x : S} {a : Set R}
  proof: by
  refine (mem_span_iff M).trans ?_
  constructor
  · rw [← coeSubmodule_span]
    rintro ⟨_, ⟨y, hy, rfl⟩, z, hz⟩
    refine ⟨y, hy, z, ?_⟩
    rw [hz]; rw [Algebra.linearMap_apply]; rw [smul_eq_mul]; rw [mul_comm]; rw [mul_mk'_eq_mk'_of_mul]; rw [mul_one]
  · rintro ⟨y, hy, z, hz⟩
    refine ⟨al

中文:
定理 mem_span_map
  条件: {x : S} {a : 集合 R}
  证明: by
  refine (mem_span_iff M).trans ?_
  constructor
  · rw [← coeSubmodule_span]
    rintro ⟨_, ⟨y, hy, rfl⟩, z, hz⟩
    refine ⟨y, hy, z, ?_⟩
    rw [hz]; rw [Algebra.linearMap_apply]; rw [smul_eq_mul]; rw [mul_comm]; rw [mul_mk'_eq_mk'_of_mul]; rw [mul_one]
  · rintro ⟨y, hy, z, hz⟩
    refine ⟨al

Depends on / 依赖: Algebra, Algebra.linearMap_apply, Submodule, Submodule.map_mem_span_algebraMap_image, _eq_mk, _of_mul, algebraMap, coeSubmodule_span, linearMap_apply, map_mem_span_algebraMap_image, mem_span_iff, mul_comm, mul_mk, mul_one, smul_eq_mul
-/
theorem mem_span_map {x : S} {a : Set R} :
    x in Ideal.span (algebraMap R S '' a) ↔ exists y in Ideal.span a, exists z : M, x = mk' S y z := by
  refine (mem_span_iff M).trans ?_
  constructor
  · rw [← coeSubmodule_span]
    rintro ⟨_, ⟨y, hy, rfl⟩, z, hz⟩
    refine ⟨y, hy, z, ?_⟩
    rw [hz]; rw [Algebra.linearMap_apply]; rw [smul_eq_mul]; rw [mul_comm]; rw [mul_mk'_eq_mk'_of_mul]; rw [mul_one]
  · rintro ⟨y, hy, z, hz⟩
    refine ⟨algebraMap R S y, Submodule.map_mem_span_algebraMap_image _ _ hy, z, ?_⟩
    rw [hz]; rw [smul_eq_mul]; rw [mul_comm]; rw [mul_mk'_eq_mk'_of_mul]; rw [mul_one]

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable {R K : Type*}

section CommRing

variable [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]

@[simp, mono, gcongr]
/--
theorem `coeSubmodule_le_coeSubmodule` / 定理 `coeSubmodule_le_coeSubmodule`

English:
theorem coeSubmodule_le_coeSubmodule
  given: {I J : Ideal R}
  proof: IsLocalization.coeSubmodule_le_coeSubmodule le_rfl

@[gcongr, mono]

中文:
定理 coeSubmodule_le_coeSubmodule
  条件: {I J : 理想 R}
  证明: IsLocalization.coeSubmodule_le_coeSubmodule le_rfl

@[gcongr, mono]

Depends on / 依赖: IsLocalization, IsLocalization.coeSubmodule_le_coeSubmodule, coeSubmodule_le_coeSubmodule, le_rfl
-/
theorem coeSubmodule_le_coeSubmodule {I J : Ideal R} :
    coeSubmodule K I <= coeSubmodule K J ↔ I <= J :=
  IsLocalization.coeSubmodule_le_coeSubmodule le_rfl

@[gcongr, mono]
/--
theorem `coeSubmodule_strictMono` / 定理 `coeSubmodule_strictMono`

English:
theorem coeSubmodule_strictMono
  statement: StrictMono (coeSubmodule K : Ideal R -> Submodule R K)
  proof: strictMono_of_le_iff_le fun _ _ => coeSubmodule_le_coeSubmodule.symm

中文:
定理 coeSubmodule_strictMono
  结论: 严格递增 (coeSubmodule K : 理想 R -> 子模 R K)
  证明: strictMono_of_le_iff_le fun _ _ => coeSubmodule_le_coeSubmodule.symm

Depends on / 依赖: coeSubmodule_le_coeSubmodule, coeSubmodule_le_coeSubmodule.symm, strictMono_of_le_iff_le
-/
theorem coeSubmodule_strictMono : StrictMono (coeSubmodule K : Ideal R -> Submodule R K) :=
  strictMono_of_le_iff_le fun _ _ => coeSubmodule_le_coeSubmodule.symm

variable (R K)

/--
theorem `coeSubmodule_injective` / 定理 `coeSubmodule_injective`

English:
theorem coeSubmodule_injective
  statement: Function.Injective (coeSubmodule K : Ideal R -> Submodule R K)
  proof: .of_eq_imp_le fun hl => coeSubmodule_le_coeSubmodule.mp hl.le

@[simp]

中文:
定理 coeSubmodule_injective
  结论: 函数.单射 (coeSubmodule K : 理想 R -> 子模 R K)
  证明: .of_eq_imp_le fun hl => coeSubmodule_le_coeSubmodule.mp hl.le

@[simp]

Depends on / 依赖: coeSubmodule_le_coeSubmodule, coeSubmodule_le_coeSubmodule.mp, hl.le, of_eq_imp_le
-/
theorem coeSubmodule_injective : Function.Injective (coeSubmodule K : Ideal R -> Submodule R K) :=
  .of_eq_imp_le fun hl => coeSubmodule_le_coeSubmodule.mp hl.le

@[simp]
/--
theorem `coeSubmodule_isPrincipal` / 定理 `coeSubmodule_isPrincipal`

English:
theorem coeSubmodule_isPrincipal
  given: {I : Ideal R}
  statement: (coeSubmodule K I).IsPrincipal ↔ I.IsPrincipal
  proof: IsLocalization.coeSubmodule_isPrincipal _ le_rfl

中文:
定理 coeSubmodule_isPrincipal
  条件: {I : 理想 R}
  结论: (coeSubmodule K I).是Principal ↔ I.是Principal
  证明: IsLocalization.coeSubmodule_isPrincipal _ le_rfl

Depends on / 依赖: IsLocalization, IsLocalization.coeSubmodule_isPrincipal, coeSubmodule_isPrincipal, le_rfl
-/
theorem coeSubmodule_isPrincipal {I : Ideal R} : (coeSubmodule K I).IsPrincipal ↔ I.IsPrincipal :=
  IsLocalization.coeSubmodule_isPrincipal _ le_rfl

end CommRing

end IsFractionRing
