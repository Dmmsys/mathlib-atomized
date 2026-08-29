/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# I-Primary Components of modules

Let `A` be a commutative ring and `I`, an ideal of `A`.
Given an `A`-Module `M` it's `I`-primary component is defined as
  $$M(I) := \bigcup_{i : \mathbb{N}} \text{torsionBySet A M } I ^ i.$$

For `P : HeightOneSpectrum A`, the main result of this file is that
  $$M \cong \bigoplus_{P} M(P).$$

## Main definitions

* `Ideal.primaryComponent` : The `I`-primary component of an `A`-module `M`.

-/

@[expose] public section

variable {A M M₁ M₂ : Type*} [CommRing A]

open IsDedekindDomain Submodule Module HeightOneSpectrum Set Function

namespace Ideal

variable (I : Ideal A)

section CommRing

section AddCommMonoid

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module A M] [Module A M₁]
    [Module A M₂]

open Set Function Submodule Module

variable (M)
/--
Definition of `primaryComponent` / `primaryComponent` 的定义

English:
definition primaryComponent
  signature: : Submodule A M
  body: ⨆ i : Nat, torsionBySet A M ↑(I ^ i)

中文:
定义 primaryComponent
  签名: : 子模 A M
  定义体: ⨆ i : Nat, torsionBySet A M ↑(I ^ i)

Depends on / 依赖: torsionBySet
-/
def primaryComponent : Submodule A M := ⨆ i : Nat, torsionBySet A M ↑(I ^ i)

/--
theorem `primaryComponent_mem` / 定理 `primaryComponent_mem`

English:
theorem primaryComponent_mem
  given: (x : M)
  proof: by
  simp only [primaryComponent, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall]
  constructor
  · intro a
    rw [Submodule.mem_iSup_of_directed] at a
    · simpa using a
    · intro x y
      use max x y
      simp [torsionBySet_le_torsionBySet_pow]
  · aesop (add safe Submodule.mem_i

中文:
定理 primaryComponent_mem
  条件: (x : M)
  证明: by
  simp only [primaryComponent, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall]
  constructor
  · intro a
    rw [Submodule.mem_iSup_of_directed] at a
    · simpa using a
    · intro x y
      use max x y
      simp [torsionBySet_le_torsionBySet_pow]
  · aesop (add safe Submodule.mem_i

Depends on / 依赖: SetLike, SetLike.coe_sort_coe, Submodule, Submodule.mem_iSup_of_directed, Submodule.mem_iSup_of_mem, Subtype, Subtype.forall, coe_sort_coe, mem_iSup_of_directed, mem_iSup_of_mem, mem_torsionBySet_iff, primaryComponent, torsionBySet_le_torsionBySet_pow
-/
theorem primaryComponent_mem (x : M) :
    x in primaryComponent M I ↔ exists n, x in torsionBySet A M ↑(I ^ n) := by
  simp only [primaryComponent, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall]
  constructor
  · intro a
    rw [Submodule.mem_iSup_of_directed] at a
    · simpa using a
    · intro x y
      use max x y
      simp [torsionBySet_le_torsionBySet_pow]
  · aesop (add safe Submodule.mem_iSup_of_mem)

/--
theorem `primaryComponent_map_mem` / 定理 `primaryComponent_map_mem`

English:
theorem primaryComponent_map_mem
  given: (φ : M₁ ->ₗ[A] M₂) (c : primaryComponent M₁ I)
  proof: by
  obtain ⟨c, hc⟩ := c
  simp only [primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall,
    ← map_smul] at ⊢ hc
  obtain ⟨n, hn⟩ := hc
  use n
  grind

中文:
定理 primaryComponent_map_mem
  条件: (φ : M₁ ->ₗ[A] M₂) (c : primaryComponent M₁ I)
  证明: by
  obtain ⟨c, hc⟩ := c
  simp only [primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall,
    ← map_smul] at ⊢ hc
  obtain ⟨n, hn⟩ := hc
  use n
  grind

Depends on / 依赖: SetLike, SetLike.coe_sort_coe, Subtype, Subtype.forall, coe_sort_coe, map_smul, mem_torsionBySet_iff, primaryComponent_mem
-/
theorem primaryComponent_map_mem (φ : M₁ ->ₗ[A] M₂) (c : primaryComponent M₁ I) :
    φ c in primaryComponent M₂ I := by
  obtain ⟨c, hc⟩ := c
  simp only [primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall,
    ← map_smul] at ⊢ hc
  obtain ⟨n, hn⟩ := hc
  use n
  grind

/-- Given an A-linear map between M₁ and M₂, `primaryComponent.map` is the
restriction to the I-primaryComponent components of M₁ and M₂. -/
@[simps!]
/--
Definition of `primaryComponent.map` / `primaryComponent.map` 的定义

English:
definition primaryComponent.map
  signature: (φ : M₁ ->ₗ[A] M₂)
  body: (φ.domRestrict (primaryComponent M₁ I)).codRestrict (primaryComponent M₂ I) (fun c =>
    by simpa only [LinearMap.domRestrict_apply] using primaryComponent_map_mem I φ c)

中文:
定义 primaryComponent.map
  签名: (φ : M₁ ->ₗ[A] M₂)
  定义体: (φ.domRestrict (primaryComponent M₁ I)).codRestrict (primaryComponent M₂ I) (fun c =>
    by simpa only [LinearMap.domRestrict_apply] using primaryComponent_map_mem I φ c)

Depends on / 依赖: LinearMap, LinearMap.domRestrict_apply, codRestrict, domRestrict, domRestrict_apply, primaryComponent, primaryComponent_map_mem
-/
def primaryComponent.map (φ : M₁ ->ₗ[A] M₂) : primaryComponent M₁ I ->ₗ[A] primaryComponent M₂ I :=
  (φ.domRestrict (primaryComponent M₁ I)).codRestrict (primaryComponent M₂ I) (fun c =>
    by simpa only [LinearMap.domRestrict_apply] using primaryComponent_map_mem I φ c)

/--
theorem `primaryComponent.map_ker_eq` / 定理 `primaryComponent.map_ker_eq`

English:
theorem primaryComponent.map_ker_eq
  given: (φ : M₁ ->ₗ[A] M₂)
  proof: by
  aesop (add norm [map, Subtype.ext_iff, primaryComponent_mem])

中文:
定理 primaryComponent.map_ker_eq
  条件: (φ : M₁ ->ₗ[A] M₂)
  证明: by
  aesop (add norm [map, Subtype.ext_iff, primaryComponent_mem])

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, primaryComponent_mem
-/
theorem primaryComponent.map_ker_eq (φ : M₁ ->ₗ[A] M₂) :
    (primaryComponent.map I φ).ker.map (primaryComponent M₁ I).subtype =
      (primaryComponent φ.ker I).map φ.ker.subtype := by
  aesop (add norm [map, Subtype.ext_iff, primaryComponent_mem])

/--
theorem `primaryComponent_torsionBySet_eq_inf` / 定理 `primaryComponent_torsionBySet_eq_inf`

English:
theorem primaryComponent_torsionBySet_eq_inf
  given: (I : Ideal A)
  proof: by
  ext x
  simp [primaryComponent_mem]

中文:
定理 primaryComponent_torsionBySet_eq_inf
  条件: (I : 理想 A)
  证明: by
  ext x
  simp [primaryComponent_mem]

Depends on / 依赖: primaryComponent_mem
-/
theorem primaryComponent_torsionBySet_eq_inf (I : Ideal A) :
    (primaryComponent (torsionBySet A M ↑I) I).map (Submodule.subtype _) =
    primaryComponent M I ⊓ torsionBySet A M ↑I := by
  ext x
  simp [primaryComponent_mem]

/--
theorem `primaryComponent_torsionBySet_of_isCoprime` / 定理 `primaryComponent_torsionBySet_of_isCoprime`

English:
theorem primaryComponent_torsionBySet_of_isCoprime
  given: (J : Ideal A) (hD : IsCoprime I J)
  proof: by
  have (n : Nat) : Disjoint (torsionBySet A M ↑(I ^ n)) (torsionBySet A M ↑J) :=
    Submodule.disjoint_torsionBySet_ideal (M := M) (Ideal.pow_sup_eq_top hD.sup_eq)
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective (torsionBySet A M ↑J))
  ext x
  simp only [mem_map, prima

中文:
定理 primaryComponent_torsionBySet_of_isCoprime
  条件: (J : 理想 A) (hD : IsCoprime I J)
  证明: by
  have (n : Nat) : Disjoint (torsionBySet A M ↑(I ^ n)) (torsionBySet A M ↑J) :=
    Submodule.disjoint_torsionBySet_ideal (M := M) (Ideal.pow_sup_eq_top hD.sup_eq)
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective (torsionBySet A M ↑J))
  ext x
  simp only [mem_map, prima

Depends on / 依赖: Disjoint, Ideal.pow_sup_eq_top, SetLike, SetLike.coe_sort_coe, SetLike.mk_smul_mk, Submodule, Submodule.disjoint_torsionBySet_ideal, Submodule.map_bot, Submodule.map_injective_of_injective, Submodule.subtype_injective, Subtype, Subtype.exists, Subtype.forall, coe_sort_coe, disjoint_torsionBySet_ideal, exists_and_left, exists_eq_right_right, exists_prop, hD.sup_eq, map_bot
-/
theorem primaryComponent_torsionBySet_of_isCoprime (J : Ideal A) (hD : IsCoprime I J) :
    primaryComponent (torsionBySet A M J) I = ⊥ := by
  have (n : Nat) : Disjoint (torsionBySet A M ↑(I ^ n)) (torsionBySet A M ↑J) :=
    Submodule.disjoint_torsionBySet_ideal (M := M) (Ideal.pow_sup_eq_top hD.sup_eq)
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective (torsionBySet A M ↑J))
  ext x
  simp only [mem_map, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.map_bot, Submodule.mem_bot]
  refine ⟨fun ⟨⟨n, _⟩, _⟩ => ?_, by simp_all⟩
  specialize this n
  simp_all [disjoint_def]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module A M]

open Submodule in
/--
theorem `primaryComponent_sup` / 定理 `primaryComponent_sup`

English:
theorem primaryComponent_sup
  given: (N₁ N₂ : Submodule A M) (hD : Disjoint N₁ N₂)
  proof: by
  ext x
  simp_all only [mem_map, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.mem_sup]
  constructor
  · rintro ⟨⟨w, h⟩, ⟨y, 

中文:
定理 primaryComponent_sup
  条件: (N₁ N₂ : 子模 A M) (hD : Disjoint N₁ N₂)
  证明: by
  ext x
  simp_all only [mem_map, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.mem_sup]
  constructor
  · rintro ⟨⟨w, h⟩, ⟨y, 

Depends on / 依赖: SetLike, SetLike.coe_sort_coe, SetLike.mk_smul_mk, Submodule, Submodule.disjoint_iff_add_eq_zero.mp, Submodule.mem_sup, Submodule.smul_mem, Subtype, Subtype.exists, Subtype.forall, coe_sort_coe, disjoint_iff_add_eq_zero, exists_and_left, exists_eq_right_right, exists_prop, mem_map, mem_sup, mem_torsionBySet_iff, mk_eq_zero, mk_smul_mk
-/
theorem primaryComponent_sup (N₁ N₂ : Submodule A M) (hD : Disjoint N₁ N₂) :
    (primaryComponent ↥(N₁ ⊔ N₂) I).map (N₁ ⊔ N₂).subtype =
    (primaryComponent N₁ I).map N₁.subtype ⊔ (primaryComponent N₂ I).map N₂.subtype := by
  ext x
  simp_all only [mem_map, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.mem_sup]
  constructor
  · rintro ⟨⟨w, h⟩, ⟨y, hy, z, hz, rfl⟩⟩
    refine ⟨y, ⟨⟨w, fun a ha => ?_⟩, by simp [hy]⟩, z, ⟨⟨w, fun a ha => ?_⟩, by simp [hz]⟩, rfl⟩
    · exact ((Submodule.disjoint_iff_add_eq_zero.mp hD) (Submodule.smul_mem N₁ a hy)
        (Submodule.smul_mem N₂ a hz) (h a ha ▸ (smul_add a y z).symm)).1
    · exact ((Submodule.disjoint_iff_add_eq_zero.mp hD) (Submodule.smul_mem N₁ a hy)
        (Submodule.smul_mem N₂ a hz) (h a ha ▸ (smul_add a y z).symm)).2
  · rintro ⟨y, ⟨⟨n₁, hy⟩, hymem⟩, z, ⟨⟨n₂, hz⟩, hzmem⟩, rfl⟩
    constructor
    · use (max n₁ n₂)
      intro a ha
      specialize hy a (Ideal.pow_le_pow_right (by simp : n₁ <= max n₁ n₂) ha)
      specialize hz a (Ideal.pow_le_pow_right (by simp : n₂ <= max n₁ n₂) ha)
      aesop
    · use y, hymem, z, hzmem

section IsDedekindDomain

variable [IsDedekindDomain A]

open scoped nonZeroDivisors

/--
theorem `iSup_primaryComponent_eq_top` / 定理 `iSup_primaryComponent_eq_top`

English:
theorem iSup_primaryComponent_eq_top
  given: (h : IsTorsion A M)
  proof: by
  rw [eq_top_iff']
  intro x
  obtain ⟨⟨a : A, ha : a in A⁰⟩, hmem : a • x = 0⟩ := h (x := x)
  replace hmem : x in torsionBySet A M (span {a}) := by
    simp_all [← torsionBySet_eq_torsionBySet_span {a}]
  have ha0 : span {a} != ⊥ := by simpa using nonZeroDivisors.ne_zero ha
  rw [← iInf_maxPowD

中文:
定理 iSup_primaryComponent_eq_top
  条件: (h : 是挠 A M)
  证明: by
  rw [eq_top_iff']
  intro x
  obtain ⟨⟨a : A, ha : a in A⁰⟩, hmem : a • x = 0⟩ := h (x := x)
  replace hmem : x in torsionBySet A M (span {a}) := by
    simp_all [← torsionBySet_eq_torsionBySet_span {a}]
  have ha0 : span {a} != ⊥ := by simpa using nonZeroDivisors.ne_zero ha
  rw [← iInf_maxPowD

Depends on / 依赖: Finite, Finite.fintype, Fintype, HeightOneSpectrum, eq_top_iff, fintype, hasFiniteMulSupport, iInf_maxPowDividing_eq, maxPowDi, maxPowDividing, mulSupport, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero, replace, torsionBySet, torsionBySet_eq_torsionBySet_span, v.maxPowDi, v.maxPowDividing
-/
theorem iSup_primaryComponent_eq_top (h : IsTorsion A M) :
    ⨆ P : HeightOneSpectrum A, primaryComponent M (P : Ideal A) = ⊤ := by
  rw [eq_top_iff']
  intro x
  obtain ⟨⟨a : A, ha : a in A⁰⟩, hmem : a • x = 0⟩ := h (x := x)
  replace hmem : x in torsionBySet A M (span {a}) := by
    simp_all [← torsionBySet_eq_torsionBySet_span {a}]
  have ha0 : span {a} != ⊥ := by simpa using nonZeroDivisors.ne_zero ha
  rw [← iInf_maxPowDividing_eq ha0] at hmem
  let : Fintype (mulSupport fun v : HeightOneSpectrum A => v.maxPowDividing (span {a})) :=
    Finite.fintype (hasFiniteMulSupport ha0)
  let S := (mulSupport fun v : HeightOneSpectrum A => v.maxPowDividing (span {a})).toFinset
  have : (⨅ i : HeightOneSpectrum A, i.maxPowDividing (span {a})) =
      (⨅ i in S, i.maxPowDividing (span {a})) := by
    ext x
    constructor
    · aesop
    · simp only [mem_iInf]
      intro h i
      by_cases htop : i.maxPowDividing (span {a}) = ⊤ <;> simp_all [S]
  have hPairwise : (S : Set (HeightOneSpectrum _)).Pairwise
      fun i j => i.maxPowDividing (span {a}) ⊔ j.maxPowDividing (span {a}) = ⊤ :=
    fun r hr s hs hrs => (isCoprime_pow_of_ne _ _ hrs _ _).sup_eq
  rw [this]; rw [← iSup_torsionBySet_ideal_eq_torsionBySet_iInf hPairwise] at hmem
  revert x
  rw [← SetLike.le_def]
  refine iSup_mono (fun P x hxmem => ?_)
  by_cases hPS : P in S
  · simp_all only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, mem_toFinset, mem_mulSupport,
      one_eq_top, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
      Subtype.forall, iSup_pos, S]
    exact ⟨(Associates.mk P.asIdeal).count (Associates.mk (span {a})).factors, fun _ b => hxmem _ b⟩
  · simp_all

variable (A M) in
/--
theorem `iSupIndep_primaryComponent` / 定理 `iSupIndep_primaryComponent`

English:
theorem iSupIndep_primaryComponent
  proof: by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s p hmem hsum
  simp only [primaryComponent_mem] at hmem
  choose! f hmem using hmem
  let m := s.sup f
  have hSupIndep : iSupIndep fun i : HeightOneSpectrum A => torsionBySet A M ↑(i.asIdeal ^ m) := by
    rw [iSupIndep_iff_supIndep]
  

中文:
定理 iSupIndep_primaryComponent
  证明: by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s p hmem hsum
  simp only [primaryComponent_mem] at hmem
  choose! f hmem using hmem
  let m := s.sup f
  have hSupIndep : iSupIndep fun i : HeightOneSpectrum A => torsionBySet A M ↑(i.asIdeal ^ m) := by
    rw [iSupIndep_iff_supIndep]
  

Depends on / 依赖: HeightOneSpectrum, SubtractionMonoid, asIdeal, hSupIndep, i.asIdeal, iSupIndep, iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero, iSupIndep_iff_supIndep, isCoprime_pow_of_ne, primaryComponent_mem, s.sup, supIndep_torsionBySet_ideal, sup_eq, toSubtractionMonoid, torsion, torsionBySet
-/
theorem iSupIndep_primaryComponent :
    iSupIndep fun P : HeightOneSpectrum A => primaryComponent M (P : Ideal A) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s p hmem hsum
  simp only [primaryComponent_mem] at hmem
  choose! f hmem using hmem
  let m := s.sup f
  have hSupIndep : iSupIndep fun i : HeightOneSpectrum A => torsionBySet A M ↑(i.asIdeal ^ m) := by
    rw [iSupIndep_iff_supIndep]
    exact fun _ => supIndep_torsionBySet_ideal
      fun _ _ _ _ hPQ => (isCoprime_pow_of_ne _ _ hPQ _ _).sup_eq
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hSupIndep
  apply hSupIndep _ _ ?_ hsum
  exact fun P hP => torsionBySet_le_torsionBySet_pow _ _ (Finset.le_sup hP) _ (hmem P hP)

/--
theorem `primaryComponent.map_surjective` / 定理 `primaryComponent.map_surjective`

English:
theorem primaryComponent.map_surjective
  statement: {M₁ M₂ : Type*}
  proof: by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨b, rfl⟩ : exists a, φ a = y := hf y
  obtain ⟨f, hf⟩ : exists f : Π₀ i : HeightOneSpectrum A, primaryComponent M₁ i.asIdeal,
      (DFinsupp.lsum Nat fun i : HeightOneSpectrum A =>
      (primaryComponent M₁ i.asIdeal).subtype) f = b := by
    simp only [← m

中文:
定理 primaryComponent.map_surjective
  结论: {M₁ M₂ : 类型}
  证明: by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨b, rfl⟩ : exists a, φ a = y := hf y
  obtain ⟨f, hf⟩ : exists f : Π₀ i : HeightOneSpectrum A, primaryComponent M₁ i.asIdeal,
      (DFinsupp.lsum Nat fun i : HeightOneSpectrum A =>
      (primaryComponent M₁ i.asIdeal).subtype) f = b := by
    simp only [← m

Depends on / 依赖: DFinsupp, DFinsupp.lsum, HeightOneSpectrum, Submodule, Submodule.disjoint_def.mp, Subtype, Subtype.ext, asIdeal, classical, disjoint_def, eq_comm, i.asIdeal, iSupIndep_primaryComponent, iSup_primaryComponent_eq_top, map_apply_coe, mem_iSup_iff_exists_dfinsupp, mem_top, primaryComponent, sub_eq_zero, subtype
-/
theorem primaryComponent.map_surjective {M₁ M₂ : Type*}
    [AddCommGroup M₁] [AddCommGroup M₂] [Module A M₁] [Module A M₂] (hM₁ : IsTorsion A M₁)
    (P : HeightOneSpectrum A) (φ : M₁ ->ₗ[A] M₂) (hf : Surjective φ) :
    Surjective (primaryComponent.map P.asIdeal φ) := by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨b, rfl⟩ : exists a, φ a = y := hf y
  obtain ⟨f, hf⟩ : exists f : Π₀ i : HeightOneSpectrum A, primaryComponent M₁ i.asIdeal,
      (DFinsupp.lsum Nat fun i : HeightOneSpectrum A =>
      (primaryComponent M₁ i.asIdeal).subtype) f = b := by
    simp only [← mem_iSup_iff_exists_dfinsupp, iSup_primaryComponent_eq_top hM₁, mem_top]
  refine ⟨f P, Subtype.ext ?_⟩
  simp only [map_apply_coe]
  rw [eq_comm]; rw [← sub_eq_zero]
  refine (Submodule.disjoint_def.mp (iSupIndep_primaryComponent A M₂ P)) _ ?_ ?_
  · exact Submodule.sub_mem _ hy (primaryComponent_map_mem _ _ _)
  · have hdiff : φ b - φ ↑(f P) = ∑ Q in f.support \ {P}, φ ↑(f Q) := by
      rw [sub_eq_iff_eq_add']; rw [← Finset.sum_eq_add_sum_sdiff_singleton P (fun P => φ (f P)) (by aesop)]
      simpa [DFinsupp.sumAddHom_apply, DFinsupp.sum] using congr(φ $hf).symm
    rw [hdiff]
exact Submodule.sum_mem _ fun Q hQ => Submodule.mem_iSup_of_mem Q
        Submodule.mem_iSup_of_mem (by grind) (primaryComponent_map_mem _ _ _)

end IsDedekindDomain

end AddCommGroup

end CommRing

end Ideal
