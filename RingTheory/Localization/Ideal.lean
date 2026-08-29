/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs

import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Ideals in localizations of commutative rings

## Implementation notes
See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions

-/

@[expose] public section


namespace IsLocalization

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
variable [Algebra R S] [IsLocalization M S]

variable {M S} in
/--
theorem `mk'_mem_iff` / 定理 `mk'_mem_iff`

English:
theorem mk'_mem_iff
  given: {x} {y : M} {I : Ideal S}
  statement: mk' S x y in I ↔ algebraMap R S x in I
  proof: by
  constructor <;> intro h
  · rw [← mk'_spec S x y, mul_comm]
    exact I.mul_mem_left ((algebraMap R S) y) h
  · rw [← mk'_spec S x y] at h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (map_units S y)
    have := I.mul_mem_left b h
    rwa [mul_comm, mul_assoc, hb, mul_one] at this

中文:
定理 mk'_mem_iff
  条件: {x} {y : M} {I : 理想 S}
  结论: mk' S x y in I ↔ algebraMap R S x in I
  证明: by
  constructor <;> intro h
  · rw [← mk'_spec S x y, mul_comm]
    exact I.mul_mem_left ((algebraMap R S) y) h
  · rw [← mk'_spec S x y] at h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (map_units S y)
    have := I.mul_mem_left b h
    rwa [mul_comm, mul_assoc, hb, mul_one] at this
-/
theorem mk'_mem_iff {x} {y : M} {I : Ideal S} : mk' S x y in I ↔ algebraMap R S x in I := by
  constructor <;> intro h
  · rw [← mk'_spec S x y, mul_comm]
    exact I.mul_mem_left ((algebraMap R S) y) h
  · rw [← mk'_spec S x y] at h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (map_units S y)
    have := I.mul_mem_left b h
    rwa [mul_comm, mul_assoc, hb, mul_one] at this

/--
Definition of `map_ideal` / `map_ideal` 的定义

English:
definition map_ideal
  signature: (I : Ideal R)
  body: Submodule.localized' S M (Algebra.linearMap R S) I

中文:
定义 map_ideal
  签名: (I : 理想 R)
  定义体: Submodule.localized' S M (Algebra.linearMap R S) I

Depends on / 依赖: e.symm
-/
private def map_ideal (I : Ideal R) : Ideal S :=
  Submodule.localized' S M (Algebra.linearMap R S) I

/--
theorem `mem_map_algebraMap_iff` / 定理 `mem_map_algebraMap_iff`

English:
theorem mem_map_algebraMap_iff
  given: {I : Ideal R} {z}
  statement: z in Ideal.map (algebraMap R S) I ↔
  proof: by
  rw [← show map_ideal M S I = Ideal.map (algebraMap R S) I by
    rw [map_ideal]; rw [Ideal.map]; rw [Ideal.span]; rw [Submodule.localized'_eq_span]; rw [Algebra.coe_linearMap],
    map_ideal, Submodule.mem_localized']
  constructor
  · rintro ⟨x, hx, s, rfl⟩
    exact ⟨⟨⟨x, hx⟩, s⟩, by rw [← Is

中文:
定理 mem_map_algebraMap_iff
  条件: {I : 理想 R} {z}
  结论: z in 理想.map (algebraMap R S) I ↔
  证明: by
  rw [← show map_ideal M S I = Ideal.map (algebraMap R S) I by
    rw [map_ideal]; rw [Ideal.map]; rw [Ideal.span]; rw [Submodule.localized'_eq_span]; rw [Algebra.coe_linearMap],
    map_ideal, Submodule.mem_localized']
  constructor
  · rintro ⟨x, hx, s, rfl⟩
    exact ⟨⟨⟨x, hx⟩, s⟩, by rw [← Is

Depends on / 依赖: Algebra, Algebra.coe_linearMap, Ideal.map, Ideal.span, IsLocalization, IsLocalization.eq_mk, IsLocalization.mk, Submodule, Submodule.localized, Submodule.mem_localized, _eq_mk, _eq_span, _iff_mul_eq, _spec, algebraMap, coe_linearMap, eq_comm, eq_mk, localized, map_ideal
-/
theorem mem_map_algebraMap_iff {I : Ideal R} {z} : z in Ideal.map (algebraMap R S) I ↔
    exists x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 := by
  rw [← show map_ideal M S I = Ideal.map (algebraMap R S) I by
    rw [map_ideal]; rw [Ideal.map]; rw [Ideal.span]; rw [Submodule.localized'_eq_span]; rw [Algebra.coe_linearMap],
    map_ideal, Submodule.mem_localized']
  constructor
  · rintro ⟨x, hx, s, rfl⟩
    exact ⟨⟨⟨x, hx⟩, s⟩, by rw [← IsLocalization.mk'_eq_mk', IsLocalization.mk'_spec]⟩
  · rintro ⟨⟨⟨x, hx⟩, s⟩, h⟩
    refine ⟨x, hx, s, ?_⟩
    rw [← IsLocalization.mk'_eq_mk']; rw [eq_comm]; rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact h

/--
lemma `mk'_mem_map_algebraMap_iff` / 引理 `mk'_mem_map_algebraMap_iff`

English:
lemma mk'_mem_map_algebraMap_iff
  given: (I : Ideal R) (x : R) (s : M)
  proof: by
  rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S s)]; rw [IsLocalization.mk'_spec']; rw [IsLocalization.mem_map_algebraMap_iff M]
  simp_rw [← map_mul, IsLocalization.eq_iff_exists M, mul_comm x, ← mul_assoc, ← Submonoid.coe_mul]
  exact ⟨fun ⟨⟨y, t⟩, c, h⟩ => ⟨_, (c * t).2, h ▸ I

中文:
引理 mk'_mem_map_algebraMap_iff
  条件: (I : 理想 R) (x : R) (s : M)
  证明: by
  rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S s)]; rw [IsLocalization.mk'_spec']; rw [IsLocalization.mem_map_algebraMap_iff M]
  simp_rw [← map_mul, IsLocalization.eq_iff_exists M, mul_comm x, ← mul_assoc, ← Submonoid.coe_mul]
  exact ⟨fun ⟨⟨y, t⟩, c, h⟩ => ⟨_, (c * t).2, h ▸ I
-/
lemma mk'_mem_map_algebraMap_iff (I : Ideal R) (x : R) (s : M) :
    IsLocalization.mk' S x s in I.map (algebraMap R S) ↔ exists s in M, s * x in I := by
  rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S s)]; rw [IsLocalization.mk'_spec']; rw [IsLocalization.mem_map_algebraMap_iff M]
  simp_rw [← map_mul, IsLocalization.eq_iff_exists M, mul_comm x, ← mul_assoc, ← Submonoid.coe_mul]
  exact ⟨fun ⟨⟨y, t⟩, c, h⟩ => ⟨_, (c * t).2, h ▸ I.mul_mem_left c.1 y.2⟩, fun ⟨s, hs, h⟩ =>
    ⟨⟨⟨_, h⟩, ⟨s, hs⟩⟩, 1, by simp⟩⟩

/--
lemma `algebraMap_mem_map_algebraMap_iff` / 引理 `algebraMap_mem_map_algebraMap_iff`

English:
lemma algebraMap_mem_map_algebraMap_iff
  given: (I : Ideal R) (x : R)
  proof: by
  rw [← IsLocalization.mk'_one (M := M)]; rw [mk'_mem_map_algebraMap_iff]

中文:
引理 algebraMap_mem_map_algebraMap_iff
  条件: (I : 理想 R) (x : R)
  证明: by
  rw [← IsLocalization.mk'_one (M := M)]; rw [mk'_mem_map_algebraMap_iff]

Depends on / 依赖: IsLocalization, IsLocalization.mk, _mem_map_algebraMap_iff, _one
-/
lemma algebraMap_mem_map_algebraMap_iff (I : Ideal R) (x : R) :
    algebraMap R S x in I.map (algebraMap R S) ↔
      exists m in M, m * x in I := by
  rw [← IsLocalization.mk'_one (M := M)]; rw [mk'_mem_map_algebraMap_iff]

/--
lemma `map_algebraMap_ne_top_iff_disjoint` / 引理 `map_algebraMap_ne_top_iff_disjoint`

English:
lemma map_algebraMap_ne_top_iff_disjoint
  given: (I : Ideal R)
  proof: by
  simp only [ne_eq, Ideal.eq_top_iff_one, ← map_one (algebraMap R S), not_iff_comm,
    IsLocalization.algebraMap_mem_map_algebraMap_iff M]
  simp [Set.disjoint_left]

中文:
引理 map_algebraMap_ne_top_iff_disjoint
  条件: (I : 理想 R)
  证明: by
  simp only [ne_eq, Ideal.eq_top_iff_one, ← map_one (algebraMap R S), not_iff_comm,
    IsLocalization.algebraMap_mem_map_algebraMap_iff M]
  simp [Set.disjoint_left]

Depends on / 依赖: Ideal.eq_top_iff_one, IsLocalization, IsLocalization.algebraMap_mem_map_algebraMap_iff, Set.disjoint_left, algebraMap, algebraMap_mem_map_algebraMap_iff, disjoint_left, eq_top_iff_one, map_one, ne_eq, not_iff_comm
-/
lemma map_algebraMap_ne_top_iff_disjoint (I : Ideal R) :
    I.map (algebraMap R S) != ⊤ ↔ Disjoint (M : Set R) (I : Set R) := by
  simp only [ne_eq, Ideal.eq_top_iff_one, ← map_one (algebraMap R S), not_iff_comm,
    IsLocalization.algebraMap_mem_map_algebraMap_iff M]
  simp [Set.disjoint_left]

set_option backward.isDefEq.respectTransparency false in
include M in
/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (I J : Ideal R)
  proof: by
  refine le_antisymm (Ideal.map_inf_le (algebraMap R S)) fun x hx => ?_
  simp only [Ideal.mem_inf, IsLocalization.mem_map_algebraMap_iff M, Prod.exists] at hx ⊢
  obtain ⟨⟨⟨i, hi⟩, mi, hi'⟩, ⟨j, hj⟩, mj, hj'⟩ := hx
  simp only [← IsLocalization.eq_mk'_iff_mul_eq] at hi' hj'
  obtain ⟨m, hm⟩ := I

中文:
定理 map_inf
  条件: (I J : 理想 R)
  证明: by
  refine le_antisymm (Ideal.map_inf_le (algebraMap R S)) fun x hx => ?_
  simp only [Ideal.mem_inf, IsLocalization.mem_map_algebraMap_iff M, Prod.exists] at hx ⊢
  obtain ⟨⟨⟨i, hi⟩, mi, hi'⟩, ⟨j, hj⟩, mj, hj'⟩ := hx
  simp only [← IsLocalization.eq_mk'_iff_mul_eq] at hi' hj'
  obtain ⟨m, hm⟩ := I
-/
protected theorem map_inf (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) = I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  refine le_antisymm (Ideal.map_inf_le (algebraMap R S)) fun x hx => ?_
  simp only [Ideal.mem_inf, IsLocalization.mem_map_algebraMap_iff M, Prod.exists] at hx ⊢
  obtain ⟨⟨⟨i, hi⟩, mi, hi'⟩, ⟨j, hj⟩, mj, hj'⟩ := hx
  simp only [← IsLocalization.eq_mk'_iff_mul_eq] at hi' hj'
  obtain ⟨m, hm⟩ := IsLocalization.eq.mp (hi'.symm.trans hj')
  rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm]; rw [← mul_comm (j : R)] at hm
  refine ⟨⟨i * (m * mj : M), I.mul_mem_right _ hi, hm ▸ J.mul_mem_right _ hj⟩, mi * (m * mj), ?_⟩
  rwa [← IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, IsLocalization.mk'_cancel]

/--
Definition of `mapFrameHom` / `mapFrameHom` 的定义

English:
definition mapFrameHom
  signature: : FrameHom (Ideal R) (Ideal S) where
  body: Ideal.map (algebraMap R S)
  map_inf' := IsLocalization.map_inf M S
  map_top' := Ideal.map_top (algebraMap R S)
  map_sSup' _ := (Ideal.gc_map_comap (algebraMap R S)).l_sSup.trans sSup_image.symm

@[simp]

中文:
定义 mapFrameHom
  签名: : 框架态射 (理想 R) (理想 S) where
  定义体: Ideal.map (algebraMap R S)
  map_inf' := IsLocalization.map_inf M S
  map_top' := Ideal.map_top (algebraMap R S)
  map_sSup' _ := (Ideal.gc_map_comap (algebraMap R S)).l_sSup.trans sSup_image.symm

@[simp]

Depends on / 依赖: Ideal.map, algebraMap
-/
def mapFrameHom : FrameHom (Ideal R) (Ideal S) where
  toFun := Ideal.map (algebraMap R S)
  map_inf' := IsLocalization.map_inf M S
  map_top' := Ideal.map_top (algebraMap R S)
  map_sSup' _ := (Ideal.gc_map_comap (algebraMap R S)).l_sSup.trans sSup_image.symm

@[simp]
/--
lemma `mapFrameHom_apply` / 引理 `mapFrameHom_apply`

English:
lemma mapFrameHom_apply
  given: (I : Ideal R)
  proof: rfl

include M in

中文:
引理 mapFrameHom_apply
  条件: (I : 理想 R)
  证明: rfl

include M in
-/
lemma mapFrameHom_apply (I : Ideal R) :
    IsLocalization.mapFrameHom M S I = I.map (algebraMap R S) :=
  rfl

include M in
/--
theorem `map_under` / 定理 `map_under`

English:
theorem map_under
  given: (J : Ideal S)
  proof: le_antisymm (Ideal.map_le_iff_le_comap.2 le_rfl) fun x hJ => by
    obtain ⟨r, s, hx⟩ := exists_mk'_eq M x
    rw [← hx] at hJ ⊢
    exact
      Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem _
          (show (algebraMap R S) r in J from
            mk'_spec S r s ▸ J.mul_mem_right ((algebra

中文:
定理 map_under
  条件: (J : 理想 S)
  证明: le_antisymm (Ideal.map_le_iff_le_comap.2 le_rfl) fun x hJ => by
    obtain ⟨r, s, hx⟩ := exists_mk'_eq M x
    rw [← hx] at hJ ⊢
    exact
      Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem _
          (show (algebraMap R S) r in J from
            mk'_spec S r s ▸ J.mul_mem_right ((algebra

Depends on / 依赖: Ideal.map_le_iff_le_comap, Ideal.mem_map_of_mem, Ideal.mul_mem_right, J.mul_mem_right, _spec, algebraMap, exists_mk, le_antisymm, le_rfl, map_le_iff_le_comap, mem_map_of_mem, mul_mem_right
-/
theorem map_under (J : Ideal S) :
    Ideal.map (algebraMap R S) (J.under R) = J :=
  le_antisymm (Ideal.map_le_iff_le_comap.2 le_rfl) fun x hJ => by
    obtain ⟨r, s, hx⟩ := exists_mk'_eq M x
    rw [← hx] at hJ ⊢
    exact
      Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem _
          (show (algebraMap R S) r in J from
            mk'_spec S r s ▸ J.mul_mem_right ((algebraMap R S) s) hJ))

@[deprecated (since := "2026-04-09")] alias map_comap := map_under

/--
theorem `under_map_of_isPrimary_disjoint` / 定理 `under_map_of_isPrimary_disjoint`

English:
theorem under_map_of_isPrimary_disjoint
  proof: by
  have key : Disjoint (M : Set R) I.radical := by
    contrapose hM
    rw [Set.not_disjoint_iff] at hM ⊢
    obtain ⟨a, ha, k, hk⟩ := hM
    exact ⟨a ^ k, pow_mem ha k, hk⟩
  refine le_antisymm (fun a ha => ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap]; rw [IsLocalization.mem_map_algebraMap_iff 

中文:
定理 under_map_of_isPrimary_disjoint
  证明: by
  have key : Disjoint (M : Set R) I.radical := by
    contrapose hM
    rw [Set.not_disjoint_iff] at hM ⊢
    obtain ⟨a, ha, k, hk⟩ := hM
    exact ⟨a ^ k, pow_mem ha k, hk⟩
  refine le_antisymm (fun a ha => ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap]; rw [IsLocalization.mem_map_algebraMap_iff 

Depends on / 依赖: Disjoint, I.radical, Ideal.le_comap_map, Ideal.mem_comap, IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.mem_map_algebraMap_iff, Set.not_disjoint_iff, algebraMap, contrapose, eq_iff_exists, le_antisymm, le_comap_map, map_mul, mem_comap, mem_map_algebraMap_iff, mul_comm, not_disjoint_iff, pow_mem, radical
-/
theorem under_map_of_isPrimary_disjoint
    {I : Ideal R} (hI : I.IsPrimary) (hM : Disjoint (M : Set R) I) :
    (Ideal.map (algebraMap R S) I).under R = I := by
  have key : Disjoint (M : Set R) I.radical := by
    contrapose hM
    rw [Set.not_disjoint_iff] at hM ⊢
    obtain ⟨a, ha, k, hk⟩ := hM
    exact ⟨a ^ k, pow_mem ha k, hk⟩
  refine le_antisymm (fun a ha => ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap]; rw [IsLocalization.mem_map_algebraMap_iff M S] at ha
  obtain ⟨⟨b, s⟩, h⟩ := ha
  replace h : algebraMap R S (s * a) = algebraMap R S b := by
    simpa only [← map_mul, mul_comm] using h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).1 h
  have : a * (c * s : M) in I := by
    rw [mul_comm]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [hc]
    exact I.mul_mem_left c b.2
  exact ((Ideal.isPrimary_iff.mp hI).2 this).resolve_right (Set.disjoint_left.mp key (c * s).2)

@[deprecated (since := "2026-04-09")] alias comap_map_of_isPrimary_disjoint :=
  under_map_of_isPrimary_disjoint

/--
theorem `under_map_of_isPrime_disjoint` / 定理 `under_map_of_isPrime_disjoint`

English:
theorem under_map_of_isPrime_disjoint
  given: {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I)
  proof: under_map_of_isPrimary_disjoint M S hI.isPrimary hM

@[deprecated (since := "2026-04-09")] alias comap_map_of_isPrime_disjoint :=
  under_map_of_isPrime_disjoint

中文:
定理 under_map_of_isPrime_disjoint
  条件: {I : 理想 R} (hI : I.是素) (hM : Disjoint (M : 集合 R) I)
  证明: under_map_of_isPrimary_disjoint M S hI.isPrimary hM

@[deprecated (since := "2026-04-09")] alias comap_map_of_isPrime_disjoint :=
  under_map_of_isPrime_disjoint

Depends on / 依赖: hI.isPrimary, isPrimary, under_map_of_isPrimary_disjoint
-/
theorem under_map_of_isPrime_disjoint {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) :
    (Ideal.map (algebraMap R S) I).under R = I :=
  under_map_of_isPrimary_disjoint M S hI.isPrimary hM

@[deprecated (since := "2026-04-09")] alias comap_map_of_isPrime_disjoint :=
  under_map_of_isPrime_disjoint

/--
theorem `liesOver_map_of_isPrime_disjoint` / 定理 `liesOver_map_of_isPrime_disjoint`

English:
theorem liesOver_map_of_isPrime_disjoint
  given: {I : Ideal R} [I.IsPrime] (hM : Disjoint (M : Set R) I)
  proof: ⟨(under_map_of_isPrime_disjoint M S ‹_› hM).symm⟩

中文:
定理 liesOver_map_of_isPrime_disjoint
  条件: {I : 理想 R} [I.是素] (hM : Disjoint (M : 集合 R) I)
  证明: ⟨(under_map_of_isPrime_disjoint M S ‹_› hM).symm⟩

Depends on / 依赖: under_map_of_isPrime_disjoint
-/
theorem liesOver_map_of_isPrime_disjoint {I : Ideal R} [I.IsPrime] (hM : Disjoint (M : Set R) I) :
    (I.map (algebraMap R S)).LiesOver I :=
  ⟨(under_map_of_isPrime_disjoint M S ‹_› hM).symm⟩

/--
Definition of `orderEmbedding` / `orderEmbedding` 的定义

English:
definition orderEmbedding
  signature: : Ideal S ↪o Ideal R where
  body: J.under R
  inj' := Function.LeftInverse.injective (map_under M S)
  map_rel_iff' := by
    rintro J₁ J₂
    constructor
    · exact fun hJ => (map_under M S) J₁ ▸ (map_under M S) J₂ ▸ Ideal.map_mono hJ
    · exact fun hJ => Ideal.comap_mono hJ

include M in

中文:
定义 orderEmbedding
  签名: : 理想 S ↪o 理想 R where
  定义体: J.under R
  inj' := Function.LeftInverse.injective (map_under M S)
  map_rel_iff' := by
    rintro J₁ J₂
    constructor
    · exact fun hJ => (map_under M S) J₁ ▸ (map_under M S) J₂ ▸ Ideal.map_mono hJ
    · exact fun hJ => Ideal.comap_mono hJ

include M in

Depends on / 依赖: J.under
-/
def orderEmbedding : Ideal S ↪o Ideal R where
  toFun J := J.under R
  inj' := Function.LeftInverse.injective (map_under M S)
  map_rel_iff' := by
    rintro J₁ J₂
    constructor
    · exact fun hJ => (map_under M S) J₁ ▸ (map_under M S) J₂ ▸ Ideal.map_mono hJ
    · exact fun hJ => Ideal.comap_mono hJ

include M in
/--
theorem `under_le_under_iff` / 定理 `under_le_under_iff`

English:
theorem under_le_under_iff
  given: {I J : Ideal S}
  proof: by
  exact (IsLocalization.orderEmbedding M S).le_iff_le

@[deprecated (since := "2026-04-09")] alias comap_le_comap_iff := under_le_under_iff

中文:
定理 under_le_under_iff
  条件: {I J : 理想 S}
  证明: by
  exact (IsLocalization.orderEmbedding M S).le_iff_le

@[deprecated (since := "2026-04-09")] alias comap_le_comap_iff := under_le_under_iff

Depends on / 依赖: IsLocalization, IsLocalization.orderEmbedding, le_iff_le, orderEmbedding
-/
theorem under_le_under_iff {I J : Ideal S} :
    I.under R <= J.under R ↔ I <= J := by
  exact (IsLocalization.orderEmbedding M S).le_iff_le

@[deprecated (since := "2026-04-09")] alias comap_le_comap_iff := under_le_under_iff

/--
theorem `isPrime_iff_isPrime_disjoint` / 定理 `isPrime_iff_isPrime_disjoint`

English:
theorem isPrime_iff_isPrime_disjoint
  given: (J : Ideal S)
  proof: by
  constructor
  · refine fun h =>
      ⟨⟨?_, ?_⟩,
        Set.disjoint_left.mpr fun m hm1 hm2 =>
          h.ne_top (Ideal.eq_top_of_isUnit_mem _ hm2 (map_units S ⟨m, hm1⟩))⟩
    · refine fun hJ => h.ne_top ?_
      rw [eq_top_iff]; rw [← (orderEmbedding M S).le_iff_le]
      exact le_of_eq hJ.s

中文:
定理 isPrime_iff_isPrime_disjoint
  条件: (J : 理想 S)
  证明: by
  constructor
  · refine fun h =>
      ⟨⟨?_, ?_⟩,
        Set.disjoint_left.mpr fun m hm1 hm2 =>
          h.ne_top (Ideal.eq_top_of_isUnit_mem _ hm2 (map_units S ⟨m, hm1⟩))⟩
    · refine fun hJ => h.ne_top ?_
      rw [eq_top_iff]; rw [← (orderEmbedding M S).le_iff_le]
      exact le_of_eq hJ.s

Depends on / 依赖: Ideal.eq_top_of_isUnit_mem, Ideal.mem_comap, Set.disjoint_left.mpr, disjoint_left, eq_top_iff, eq_top_of_isUnit_mem, h.left.ne_top, h.mem_or_mem, h.ne_top, hJ.symm, le_iff_le, le_of_eq, map_mul, map_units, mem_comap, mem_or_mem, ne_top, orderEmbedding
-/
theorem isPrime_iff_isPrime_disjoint (J : Ideal S) :
    J.IsPrime ↔ (J.under R).IsPrime ∧ Disjoint (M : Set R) (J.under R) := by
  constructor
  · refine fun h =>
      ⟨⟨?_, ?_⟩,
        Set.disjoint_left.mpr fun m hm1 hm2 =>
          h.ne_top (Ideal.eq_top_of_isUnit_mem _ hm2 (map_units S ⟨m, hm1⟩))⟩
    · refine fun hJ => h.ne_top ?_
      rw [eq_top_iff]; rw [← (orderEmbedding M S).le_iff_le]
      exact le_of_eq hJ.symm
    · intro x y hxy
      rw [Ideal.mem_comap]; rw [map_mul] at hxy
      exact h.mem_or_mem hxy
  · refine fun h => ⟨fun hJ => h.left.ne_top (eq_top_iff.2 ?_), ?_⟩
    · rwa [eq_top_iff, ← (orderEmbedding M S).le_iff_le] at hJ
    · intro x y hxy
      obtain ⟨a, s, ha⟩ := exists_mk'_eq M x
      obtain ⟨b, t, hb⟩ := exists_mk'_eq M y
      have : mk' S (a * b) (s * t) in J := by rwa [mk'_mul, ha, hb]
      rw [mk'_mem_iff]; rw [← Ideal.mem_comap] at this
      have this₂ := (h.1).mul_mem_iff_mem_or_mem.1 this
      rw [Ideal.mem_comap]; rw [Ideal.mem_comap] at this₂
      rwa [← ha, ← hb, mk'_mem_iff, mk'_mem_iff]

/--
theorem `isPrime_of_isPrime_disjoint` / 定理 `isPrime_of_isPrime_disjoint`

English:
theorem isPrime_of_isPrime_disjoint
  given: (I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I)
  proof: by
  rw [isPrime_iff_isPrime_disjoint M S]; rw [under_map_of_isPrime_disjoint M S hp hd]
  exact ⟨hp, hd⟩

中文:
定理 isPrime_of_isPrime_disjoint
  条件: (I : 理想 R) (hp : I.是素) (hd : Disjoint (M : 集合 R) ↑I)
  证明: by
  rw [isPrime_iff_isPrime_disjoint M S]; rw [under_map_of_isPrime_disjoint M S hp hd]
  exact ⟨hp, hd⟩

Depends on / 依赖: isPrime_iff_isPrime_disjoint, under_map_of_isPrime_disjoint
-/
theorem isPrime_of_isPrime_disjoint (I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) :
    (Ideal.map (algebraMap R S) I).IsPrime := by
  rw [isPrime_iff_isPrime_disjoint M S]; rw [under_map_of_isPrime_disjoint M S hp hd]
  exact ⟨hp, hd⟩

/--
theorem `disjoint_under_iff` / 定理 `disjoint_under_iff`

English:
theorem disjoint_under_iff
  given: (J : Ideal S)
  proof: by
  rw [← iff_not_comm]; rw [Set.not_disjoint_iff]
  constructor
  · rintro rfl
    exact ⟨1, M.one_mem, ⟨⟩⟩
  · rintro ⟨x, hxM, hxJ⟩
    exact J.eq_top_of_isUnit_mem hxJ (IsLocalization.map_units S ⟨x, hxM⟩)

@[deprecated (since := "2026-04-09")] alias disjoint_comap_iff := disjoint_under_iff

中文:
定理 disjoint_under_iff
  条件: (J : 理想 S)
  证明: by
  rw [← iff_not_comm]; rw [Set.not_disjoint_iff]
  constructor
  · rintro rfl
    exact ⟨1, M.one_mem, ⟨⟩⟩
  · rintro ⟨x, hxM, hxJ⟩
    exact J.eq_top_of_isUnit_mem hxJ (IsLocalization.map_units S ⟨x, hxM⟩)

@[deprecated (since := "2026-04-09")] alias disjoint_comap_iff := disjoint_under_iff

Depends on / 依赖: IsLocalization, IsLocalization.map_units, J.eq_top_of_isUnit_mem, M.one_mem, Set.not_disjoint_iff, eq_top_of_isUnit_mem, iff_not_comm, map_units, not_disjoint_iff, one_mem
-/
theorem disjoint_under_iff (J : Ideal S) :
    Disjoint (M : Set R) (J.under R) ↔ J != ⊤ := by
  rw [← iff_not_comm]; rw [Set.not_disjoint_iff]
  constructor
  · rintro rfl
    exact ⟨1, M.one_mem, ⟨⟩⟩
  · rintro ⟨x, hxM, hxJ⟩
    exact J.eq_top_of_isUnit_mem hxJ (IsLocalization.map_units S ⟨x, hxM⟩)

@[deprecated (since := "2026-04-09")] alias disjoint_comap_iff := disjoint_under_iff

/--
Definition of `orderIsoOfPrime` / `orderIsoOfPrime` 的定义

English:
definition orderIsoOfPrime
  signature: :
  body: ⟨p.1.under R, (isPrime_iff_isPrime_disjoint M S p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isPrime_of_isPrime_disjoint M S p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.ext (map_under M S J)
  right_inv I := Subtype.ext (under_map_of_isPrime_disjoint M S I.2.1 I.2.2)
  map_rel_iff' {I I'}

中文:
定义 orderIsoOfPrime
  签名: :
  定义体: ⟨p.1.under R, (isPrime_iff_isPrime_disjoint M S p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isPrime_of_isPrime_disjoint M S p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.ext (map_under M S J)
  right_inv I := Subtype.ext (under_map_of_isPrime_disjoint M S I.2.1 I.2.2)
  map_rel_iff' {I I'}
-/
@[simps] def orderIsoOfPrime :
    { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ Disjoint (M : Set R) ↑p } where
  toFun p := ⟨p.1.under R, (isPrime_iff_isPrime_disjoint M S p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isPrime_of_isPrime_disjoint M S p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.ext (map_under M S J)
  right_inv I := Subtype.ext (under_map_of_isPrime_disjoint M S I.2.1 I.2.2)
  map_rel_iff' {I I'} := by
    constructor
    · exact fun h => show I.val <= I'.val from map_under M S I.val ▸
        map_under M S I'.val ▸ Ideal.map_mono h
    exact fun h x hx => h hx

/--
Definition of `primeSpectrumOrderIso` / `primeSpectrumOrderIso` 的定义

English:
definition primeSpectrumOrderIso
  signature: :
  body: (PrimeSpectrum.equivSubtype S).trans (orderIsoOfPrime M S).trans
    ⟨⟨fun p => ⟨⟨p, p.2.1⟩, p.2.2⟩, fun p => ⟨p.1.1, p.1.2, p.2⟩, fun _ => rfl, fun _ => rfl⟩, .rfl⟩

include M in

中文:
定义 primeSpectrumOrderIso
  签名: :
  定义体: (PrimeSpectrum.equivSubtype S).trans (orderIsoOfPrime M S).trans
    ⟨⟨fun p => ⟨⟨p, p.2.1⟩, p.2.2⟩, fun p => ⟨p.1.1, p.1.2, p.2⟩, fun _ => rfl, fun _ => rfl⟩, .rfl⟩

include M in
-/
@[simps!] def primeSpectrumOrderIso :
    PrimeSpectrum S ≃o {p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal} :=
(PrimeSpectrum.equivSubtype S).trans (orderIsoOfPrime M S).trans
    ⟨⟨fun p => ⟨⟨p, p.2.1⟩, p.2.2⟩, fun p => ⟨p.1.1, p.1.2, p.2⟩, fun _ => rfl, fun _ => rfl⟩, .rfl⟩

include M in
/--
lemma `map_radical` / 引理 `map_radical`

English:
lemma map_radical
  given: (I : Ideal R)
  proof: by
  refine (I.map_radical_le (algebraMap R S)).antisymm ?_
  rintro x ⟨n, hn⟩
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp only [← IsLocalization.mk'_pow, IsLocalization.mk'_mem_map_algebraMap_iff M] at hn ⊢
  obtain ⟨s, hs, h⟩ := hn
  refine ⟨s, hs, n + 1, by convert! I.mul_mem_

中文:
引理 map_radical
  条件: (I : 理想 R)
  证明: by
  refine (I.map_radical_le (algebraMap R S)).antisymm ?_
  rintro x ⟨n, hn⟩
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp only [← IsLocalization.mk'_pow, IsLocalization.mk'_mem_map_algebraMap_iff M] at hn ⊢
  obtain ⟨s, hs, h⟩ := hn
  refine ⟨s, hs, n + 1, by convert! I.mul_mem_

Depends on / 依赖: I.map_radical_le, I.mul_mem_left, IsLocalization, IsLocalization.exists_mk, IsLocalization.mk, _mem_map_algebraMap_iff, _pow, algebraMap, antisymm, convert, exists_mk, map_radical_le, mul_mem_left
-/
lemma map_radical (I : Ideal R) :
    I.radical.map (algebraMap R S) = (I.map (algebraMap R S)).radical := by
  refine (I.map_radical_le (algebraMap R S)).antisymm ?_
  rintro x ⟨n, hn⟩
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp only [← IsLocalization.mk'_pow, IsLocalization.mk'_mem_map_algebraMap_iff M] at hn ⊢
  obtain ⟨s, hs, h⟩ := hn
  refine ⟨s, hs, n + 1, by convert! I.mul_mem_left (s ^ n * x) h; ring⟩

/--
theorem `ideal_eq_iInf_under_map_away` / 定理 `ideal_eq_iInf_under_map_away`

English:
theorem ideal_eq_iInf_under_map_away
  given: {S : Finset R} (hS : Ideal.span (α := R) S = ⊤) (I : Ideal R)
  proof: by
  apply le_antisymm
  · simp only [le_iInf₂_iff, ← Ideal.map_le_iff_le_comap, le_refl, implies_true]
  · intro x hx
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hS
    rintro ⟨s, hs⟩
    simp only [Ideal.mem_iInf, Ideal.mem_comap] at hx
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, e⟩ :=
      (IsL

中文:
定理 ideal_eq_iInf_under_map_away
  条件: {S : 有限集 R} (hS : 理想.span (α := R) S = ⊤) (I : 理想 R)
  证明: by
  apply le_antisymm
  · simp only [le_iInf₂_iff, ← Ideal.map_le_iff_le_comap, le_refl, implies_true]
  · intro x hx
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hS
    rintro ⟨s, hs⟩
    simp only [Ideal.mem_iInf, Ideal.mem_comap] at hx
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, e⟩ :=
      (IsL
-/
theorem ideal_eq_iInf_under_map_away {S : Finset R} (hS : Ideal.span (α := R) S = ⊤) (I : Ideal R) :
    I = ⨅ f in S, (I.map (algebraMap R (Localization.Away f))).under R := by
  apply le_antisymm
  · simp only [le_iInf₂_iff, ← Ideal.map_le_iff_le_comap, le_refl, implies_true]
  · intro x hx
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hS
    rintro ⟨s, hs⟩
    simp only [Ideal.mem_iInf, Ideal.mem_comap] at hx
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, e⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (.powers s) _).mp (hx s hs)
    dsimp only at e
    rw [← map_mul]; rw [IsLocalization.eq_iff_exists (.powers s)] at e
    obtain ⟨⟨_, m, rfl⟩, e⟩ := e
    use m + n
    dsimp at e ⊢
    rw [pow_add]; rw [mul_assoc]; rw [← mul_comm x]; rw [e]
    exact I.mul_mem_left _ y.2

@[deprecated (since := "2026-04-09")] alias ideal_eq_iInf_comap_map_away :=
  ideal_eq_iInf_under_map_away

/--
lemma `map_eq_top_of_not_subset` / 引理 `map_eq_top_of_not_subset`

English:
lemma map_eq_top_of_not_subset
  given: {I : Ideal R} (hle : ¬ (I : Set R) subseteq Mᶜ)
  proof: by
  simp only [Set.not_subset_iff_exists_mem_notMem, Set.mem_compl_iff, not_not] at hle
  obtain ⟨y, hy, hny⟩ := hle
  apply Ideal.eq_top_of_isUnit_mem
  · exact Ideal.mem_map_of_mem (algebraMap R _) hy
  · exact IsLocalization.map_units _ (⟨y, hny⟩ : M)

中文:
引理 map_eq_top_of_not_subset
  条件: {I : 理想 R} (hle : ¬ (I : 集合 R) subseteq Mᶜ)
  证明: by
  simp only [Set.not_subset_iff_exists_mem_notMem, Set.mem_compl_iff, not_not] at hle
  obtain ⟨y, hy, hny⟩ := hle
  apply Ideal.eq_top_of_isUnit_mem
  · exact Ideal.mem_map_of_mem (algebraMap R _) hy
  · exact IsLocalization.map_units _ (⟨y, hny⟩ : M)

Depends on / 依赖: Ideal.eq_top_of_isUnit_mem, Ideal.mem_map_of_mem, IsLocalization, IsLocalization.map_units, Set.mem_compl_iff, Set.not_subset_iff_exists_mem_notMem, algebraMap, eq_top_of_isUnit_mem, map_units, mem_compl_iff, mem_map_of_mem, not_not, not_subset_iff_exists_mem_notMem
-/
lemma map_eq_top_of_not_subset {I : Ideal R} (hle : ¬ (I : Set R) subseteq Mᶜ) :
    Ideal.map (algebraMap R S) I = ⊤ := by
  simp only [Set.not_subset_iff_exists_mem_notMem, Set.mem_compl_iff, not_not] at hle
  obtain ⟨y, hy, hny⟩ := hle
  apply Ideal.eq_top_of_isUnit_mem
  · exact Ideal.mem_map_of_mem (algebraMap R _) hy
  · exact IsLocalization.map_units _ (⟨y, hny⟩ : M)

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]
variable [Algebra R S] [IsLocalization M S]

include M in
/--
theorem `surjective_quotientMap_of_maximal_of_localization` / 定理 `surjective_quotientMap_of_maximal_of_localization`

English:
theorem surjective_quotientMap_of_maximal_of_localization
  statement: {I : Ideal S} [I.IsPrime] {J : Ideal R}
  proof: by
  intro s
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := exists_mk'_eq M s
  by_cases hM : (Ideal.Quotient.mk (I.comap (algebraMap R S))) m = 0
  · have : I = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [Ideal.Quotient.eq_zero_iff_mem]; rw [Ideal.mem_comap]

中文:
定理 surjective_quotientMap_of_maximal_of_localization
  结论: {I : 理想 S} [I.是素] {J : 理想 R}
  证明: by
  intro s
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := exists_mk'_eq M s
  by_cases hM : (Ideal.Quotient.mk (I.comap (algebraMap R S))) m = 0
  · have : I = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [Ideal.Quotient.eq_zero_iff_mem]; rw [Ideal.mem_comap]

Depends on / 依赖: I.comap, I.mul_mem_right, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.maximal_ideal_iff_isField_quoti, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.eq_top_iff_one, Ideal.mem_comap, Quotient, _eq_mul_mk, _one, _self, algebraMap, convert, eq_comm, eq_top_iff_one, eq_zero_iff_mem, exists_mk, maximal_ideal_iff_isField_quoti, mem_comap
-/
theorem surjective_quotientMap_of_maximal_of_localization {I : Ideal S} [I.IsPrime] {J : Ideal R}
    {H : J <= I.under R} (hI : (I.under R).IsMaximal) :
    Function.Surjective (Ideal.quotientMap I (algebraMap R S) H) := by
  intro s
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := exists_mk'_eq M s
  by_cases hM : (Ideal.Quotient.mk (I.comap (algebraMap R S))) m = 0
  · have : I = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [Ideal.Quotient.eq_zero_iff_mem]; rw [Ideal.mem_comap] at hM
      convert! I.mul_mem_right (mk' S (1 : R) ⟨m, hm⟩) hM
      rw [← mk'_eq_mul_mk'_one]; rw [mk'_self]
    exact ⟨0, eq_comm.1 (by simp [Ideal.Quotient.eq_zero_iff_mem, this])⟩
  · rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient] at hI
    obtain ⟨n, hn⟩ := hI.3 hM
    obtain ⟨rn, rfl⟩ := Ideal.Quotient.mk_surjective n
    refine ⟨(Ideal.Quotient.mk J) (r * rn), ?_⟩
    -- The rest of the proof is essentially just algebraic manipulations to prove the equality
    replace hn := congr_arg (Ideal.quotientMap I (algebraMap R S) le_rfl) hn
    rw [map_one]; rw [map_mul] at hn
    rw [Ideal.quotientMap_mk]; rw [← sub_eq_zero]; rw [← map_sub]; rw [Ideal.Quotient.eq_zero_iff_mem]; rw [←
      Ideal.Quotient.eq_zero_iff_mem]; rw [map_sub]; rw [sub_eq_zero]; rw [mk'_eq_mul_mk'_one]
    simp only [mul_eq_mul_left_iff, map_mul]
    refine
      Or.inl
        (mul_left_cancel₀ (M₀ := S ⧸ I)
          (fun hn =>
            hM
              (Ideal.Quotient.eq_zero_iff_mem.2
                (Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 hn))))
          (_root_.trans hn ?_))
    rw [← map_mul]; rw [← mk'_eq_mul_mk'_one]; rw [mk'_self]; rw [map_one]

open nonZeroDivisors

/--
theorem `bot_lt_under_prime` / 定理 `bot_lt_under_prime`

English:
theorem bot_lt_under_prime
  statement: [IsDomain R] (hM : M <= R⁰) (p : Ideal S) [hpp : p.IsPrime]
  proof: by
  have : IsDomain S := isDomain_of_le_nonZeroDivisors _ hM
  rw [← Ideal.comap_bot_of_injective (algebraMap R S) (IsLocalization.injective _ hM)]
  convert!
    (orderIsoOfPrime M S).lt_iff_lt.mpr
      (show (⟨⊥, Ideal.isPrime_bot⟩ : { p : Ideal S // p.IsPrime }) < ⟨p, hpp⟩ from hp0.bot_lt)

@[d

中文:
定理 bot_lt_under_prime
  结论: [是整环 R] (hM : M <= R⁰) (p : 理想 S) [hpp : p.是素]
  证明: by
  have : IsDomain S := isDomain_of_le_nonZeroDivisors _ hM
  rw [← Ideal.comap_bot_of_injective (algebraMap R S) (IsLocalization.injective _ hM)]
  convert!
    (orderIsoOfPrime M S).lt_iff_lt.mpr
      (show (⟨⊥, Ideal.isPrime_bot⟩ : { p : Ideal S // p.IsPrime }) < ⟨p, hpp⟩ from hp0.bot_lt)

@[d

Depends on / 依赖: Ideal.comap_bot_of_injective, Ideal.isPrime_bot, IsDomain, IsLocalization, IsLocalization.injective, IsPrime, algebraMap, bot_lt, comap_bot_of_injective, convert, hp0.bot_lt, injective, isDomain_of_le_nonZeroDivisors, isPrime_bot, lt_iff_lt, lt_iff_lt.mpr, orderIsoOfPrime, p.IsPrime
-/
theorem bot_lt_under_prime [IsDomain R] (hM : M <= R⁰) (p : Ideal S) [hpp : p.IsPrime]
    (hp0 : p != ⊥) : ⊥ < p.under R := by
  have : IsDomain S := isDomain_of_le_nonZeroDivisors _ hM
  rw [← Ideal.comap_bot_of_injective (algebraMap R S) (IsLocalization.injective _ hM)]
  convert!
    (orderIsoOfPrime M S).lt_iff_lt.mpr
      (show (⟨⊥, Ideal.isPrime_bot⟩ : { p : Ideal S // p.IsPrime }) < ⟨p, hpp⟩ from hp0.bot_lt)

@[deprecated (since := "2026-04-09")] alias bot_lt_comap_prime := bot_lt_under_prime

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/--
lemma `_root_.Module.IsTorsionFree.of_isLocalization` / 引理 `_root_.Module.IsTorsionFree.of_isLocalization`

English:
lemma _root_.Module.IsTorsionFree.of_isLocalization
  statement: [IsDomain R] [IsDomain S] {Rₚ Sₚ : Type*}
  proof: by
  have e : Algebra.algebraMapSubmonoid S M <= S⁰ :=
Submonoid.map_le_of_le_comap _ hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : algebraMap

中文:
引理 _root_.模.是无挠.of_isLocalization
  结论: [是整环 R] [是整环 S] {Rₚ Sₚ : 类型}
  证明: by
  have e : Algebra.algebraMapSubmonoid S M <= S⁰ :=
Submonoid.map_le_of_le_comap _ hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : algebraMap

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, FaithfulSMul, FaithfulSMul.algebraMap_injective, IsDomain, IsLocalization, IsLocalization.isDomain_of_le_nonZeroDivisors, IsLocalization.map, IsLocalization.map_comp, IsLocalization.ringHom_ext, IsScalarTower, IsScalarTower.algebraMap_eq, Submonoid, Submonoid.le_comap_map, Submonoid.map_le_of_le_comap, algebraMap, algebraMapSubmonoid, algebraMap_eq, algebraMap_injective, hM.trans
-/
lemma _root_.Module.IsTorsionFree.of_isLocalization [IsDomain R] [IsDomain S] {Rₚ Sₚ : Type*}
    [CommRing Rₚ] [IsDomain Rₚ] [CommRing Sₚ] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] {M : Submonoid R} (hM : M <= R⁰)
    [IsLocalization M Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ]
    [Module.IsTorsionFree R S] : Module.IsTorsionFree Rₚ Sₚ := by
  have e : Algebra.algebraMapSubmonoid S M <= S⁰ :=
Submonoid.map_le_of_le_comap _ hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
    (algebraMap R S) (Submonoid.le_comap_map M) := by
    apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  rw [Module.isTorsionFree_iff_algebraMap_injective]; rw [RingHom.injective_iff_ker_eq_bot]; rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp only [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    Subtype.exists, exists_prop, this] at hx ⊢
  obtain ⟨_, ⟨a, ha, rfl⟩, H⟩ := hx
  simp only [← map_mul,
    (injective_iff_map_eq_zero' _).mp (FaithfulSMul.algebraMap_injective R S)] at H
  exact ⟨a, ha, H⟩

/--
lemma `of_surjective` / 引理 `of_surjective`

English:
lemma of_surjective
  statement: {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S']
  proof: by
    rintro ⟨_, y, hy, rfl⟩
    simpa only [← RingHom.comp_apply, H] using (IsLocalization.map_units S ⟨y, hy⟩).map g
  surj := by
    intro z
    obtain ⟨z, rfl⟩ := hg z
    obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj M z
    refine ⟨⟨f r, _, s.1, s.2, rfl⟩, ?_⟩
    simpa only [map_mul, ← RingHom.c

中文:
引理 of_surjective
  结论: {R' S' : 类型} [交换环 R'] [交换环 S'] [代数 R' S']
  证明: by
    rintro ⟨_, y, hy, rfl⟩
    simpa only [← RingHom.comp_apply, H] using (IsLocalization.map_units S ⟨y, hy⟩).map g
  surj := by
    intro z
    obtain ⟨z, rfl⟩ := hg z
    obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj M z
    refine ⟨⟨f r, _, s.1, s.2, rfl⟩, ?_⟩
    simpa only [map_mul, ← RingHom.c

Depends on / 依赖: DFunLike, DFunLike.congr_arg, IsLocalization, IsLocalization.map_units, IsLocalization.surj, RingHom, RingHom.comp_ap, RingHom.comp_apply, comp_ap, comp_apply, congr_arg, exists_of_eq, map_mul, map_sub, map_units, sub_eq_zero
-/
lemma of_surjective {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S']
    (f : R ->+* R') (hf : Function.Surjective f) (g : S ->+* S') (hg : Function.Surjective g)
    (H : g.comp (algebraMap R S) = (algebraMap _ _).comp f)
    (H' : RingHom.ker g <= (RingHom.ker f).map (algebraMap R S)) : IsLocalization (M.map f) S' where
  map_units := by
    rintro ⟨_, y, hy, rfl⟩
    simpa only [← RingHom.comp_apply, H] using (IsLocalization.map_units S ⟨y, hy⟩).map g
  surj := by
    intro z
    obtain ⟨z, rfl⟩ := hg z
    obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj M z
    refine ⟨⟨f r, _, s.1, s.2, rfl⟩, ?_⟩
    simpa only [map_mul, ← RingHom.comp_apply, H] using DFunLike.congr_arg g e
  exists_of_eq := by
    intro x y e
    obtain ⟨x, rfl⟩ := hf x
    obtain ⟨y, rfl⟩ := hf y
    rw [← sub_eq_zero]; rw [← map_sub]; rw [← map_sub]; rw [← RingHom.comp_apply]; rw [← H]; rw [RingHom.comp_apply]; rw [← IsLocalization.mk'_one (M := M)] at e
    obtain ⟨r, hr, hr'⟩ := (IsLocalization.mk'_mem_map_algebraMap_iff M _ _ _ _).mp (H' e)
    exact ⟨⟨_, r, hr, rfl⟩, by simpa [sub_eq_zero, mul_sub] using hr'⟩

instance (I : Ideal R) :
    IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M) (S ⧸ I.map (algebraMap R S)) :=
  of_surjective M S (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (I.map (algebraMap R S))) Ideal.Quotient.mk_surjective rfl (by simp)

open Algebra in
instance {P : Ideal R} [P.IsPrime] [IsDomain R] [IsDomain S] [FaithfulSMul R S] :
    IsDomain (Localization (algebraMapSubmonoid S P.primeCompl)) :=
  isDomain_localization (map_le_nonZeroDivisors_of_injective _
    (FaithfulSMul.algebraMap_injective R S) P.primeCompl_le_nonZeroDivisors)

end CommRing

end IsLocalization
