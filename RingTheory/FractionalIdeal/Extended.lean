/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom, Xavier Roblot
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Extension of fractional ideals

This file defines the extension of a fractional ideal along a ring homomorphism.

## Main definitions

* `FractionalIdeal.extended`: Let `A` and `B` be commutative rings with respective localizations
  `IsLocalization M K` and `IsLocalization N L`. Let `f : A →+* B` be a ring homomorphism with
  `hf : M ≤ Submonoid.comap f N`. If `I : FractionalIdeal M K`, then the extension of `I` along
  `f` is `extended L hf I : FractionalIdeal N L`.
* `FractionalIdeal.extendedHom'`: The ring homomorphism version of `FractionalIdeal.extended`.
* `FractionalIdeal.extendedHom`: For `A ⊆ B` an extension of domains, the ring homomorphism that
  sends a fractional ideal of `A` to a fractional ideal of `B`.

## Main results

* `FractionalIdeal.extendedHom_injective`: the map `FractionalIdeal.extendedHom` is injective.
* `FractionalIdeal.extended_extended`: extending fractional ideals is compatible with composition
  of ring homomorphisms.
* `FractionalIdeal.extendedHom'_comp`: the homomorphisms induced by extension of fractional
  ideals compose in towers.
* `Ideal.map_algebraMap_injective`: For `A ⊆ B` an extension of Dedekind domains, the map that
  sends an ideal `I` of `A` to `I·B` is injective.

## Tags

fractional ideal, fractional ideals, extended, extension
-/

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- This is why this section is `noncomputable`.
-- See https://github.com/leanprover/lean4/issues/14084.
@[expose] public noncomputable section

open IsLocalization FractionalIdeal Module Submodule

namespace FractionalIdeal

section RingHom

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] {f : A ->+* B}
variable {K : Type*} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
variable (L : Type*) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
variable (hf : M <= Submonoid.comap f N)
variable (I : FractionalIdeal M K) (J : FractionalIdeal M K)

/--
Definition of `extended` / `extended` 的定义

English:
definition extended
  signature: (I : FractionalIdeal M K)
  body: span B (IsLocalization.map (S := K) L f hf) '' I
  property := by
    have ⟨a, ha, frac⟩ := I.isFractional
    refine ⟨f a, hf ha, fun b hb => ?_⟩
    refine span_induction (fun x hx => ?_) ⟨0, by simp⟩
      (fun x y _ _ hx hy => smul_add (f a) x y ▸ isInteger_add hx hy) (fun b c _ hc => ?_) hb
   

中文:
定义 extended
  签名: (I : FractionalIdeal M K)
  定义体: span B (IsLocalization.map (S := K) L f hf) '' I
  property := by
    have ⟨a, ha, frac⟩ := I.isFractional
    refine ⟨f a, hf ha, fun b hb => ?_⟩
    refine span_induction (fun x hx => ?_) ⟨0, by simp⟩
      (fun x y _ _ hx hy => smul_add (f a) x y ▸ isInteger_add hx hy) (fun b c _ hc => ?_) hb
   

Depends on / 依赖: IsLocalization, IsLocalization.map
-/
def extended (I : FractionalIdeal M K) : FractionalIdeal N L where
val := span B (IsLocalization.map (S := K) L f hf) '' I
  property := by
    have ⟨a, ha, frac⟩ := I.isFractional
    refine ⟨f a, hf ha, fun b hb => ?_⟩
    refine span_induction (fun x hx => ?_) ⟨0, by simp⟩
      (fun x y _ _ hx hy => smul_add (f a) x y ▸ isInteger_add hx hy) (fun b c _ hc => ?_) hb
    · rcases hx with ⟨k, kI, rfl⟩
      obtain ⟨c, hc⟩ := frac k kI
      exact ⟨f c, by simp [← IsLocalization.map_smul, ← hc]⟩
    · rw [← smul_assoc, smul_eq_mul, mul_comm (f a), ← smul_eq_mul, smul_assoc]
      exact isInteger_smul hc

local notation "map_f" => (IsLocalization.map (S := K) L f hf)

/--
lemma `mem_extended_iff` / 引理 `mem_extended_iff`

English:
lemma mem_extended_iff
  given: (x : L)
  statement: x in I.extended L hf ↔ x in span B (map_f '' I)
  proof: by
  constructor <;> { intro hx; simpa }

@[simp]

中文:
引理 mem_extended_iff
  条件: (x : L)
  结论: x in I.extended L hf ↔ x in span B (map_f '' I)
  证明: by
  constructor <;> { intro hx; simpa }

@[simp]
-/
lemma mem_extended_iff (x : L) : x in I.extended L hf ↔ x in span B (map_f '' I) := by
  constructor <;> { intro hx; simpa }

@[simp]
/--
lemma `coe_extended_eq_span` / 引理 `coe_extended_eq_span`

English:
lemma coe_extended_eq_span
  statement: I.extended L hf = span B (map_f '' I)
  proof: by
  ext; simp [mem_coe, mem_extended_iff]

@[simp]

中文:
引理 coe_extended_eq_span
  结论: I.extended L hf = span B (map_f '' I)
  证明: by
  ext; simp [mem_coe, mem_extended_iff]

@[simp]

Depends on / 依赖: mem_coe, mem_extended_iff
-/
lemma coe_extended_eq_span : I.extended L hf = span B (map_f '' I) := by
  ext; simp [mem_coe, mem_extended_iff]

@[simp]
/--
theorem `extended_zero` / 定理 `extended_zero`

English:
theorem extended_zero
  statement: extended L hf (0 : FractionalIdeal M K) = 0
  proof: have : ((0 : FractionalIdeal M K) : Set K) = {0} := by ext; simp
  coeToSubmodule_injective (by simp [this])

中文:
定理 extended_zero
  结论: extended L hf (0 : FractionalIdeal M K) = 0
  证明: have : ((0 : FractionalIdeal M K) : Set K) = {0} := by ext; simp
  coeToSubmodule_injective (by simp [this])

Depends on / 依赖: FractionalIdeal, coeToSubmodule_injective
-/
theorem extended_zero : extended L hf (0 : FractionalIdeal M K) = 0 :=
  have : ((0 : FractionalIdeal M K) : Set K) = {0} := by ext; simp
  coeToSubmodule_injective (by simp [this])

variable {I}

/--
theorem `extended_ne_zero` / 定理 `extended_ne_zero`

English:
theorem extended_ne_zero
  given: [IsDomain B] (hf' : Function.Injective f) (hI : I != 0) (hN : 0 ∉ N)
  proof: by
  simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    not_forall]
  obtain ⟨x, hx₁, hx₂⟩ : exists x in I, x != 0 := by simpa [ne_eq, eq_zero_iff] using hI
  r

中文:
定理 extended_ne_zero
  条件: [是整环 B] (hf' : 函数.单射 f) (hI : I != 0) (hN : 0 ∉ N)
  证明: by
  simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    not_forall]
  obtain ⟨x, hx₁, hx₂⟩ : exists x in I, x != 0 := by simpa [ne_eq, eq_zero_iff] using hI
  r

Depends on / 依赖: IsLocalization, IsLocalization.map_injective_of_injective, Set.mem_image, SetLike, SetLike.mem_coe, Submodule, Submodule.span_eq_bot, and_imp, coeToSubmodule_inj, coe_extended_eq_span, coe_zero, eq_zero_iff, forall_exists_index, map_injective_of_injective, map_ne_zero_iff, mem_coe, mem_image, ne_eq, not_forall, span_eq_bot
-/
theorem extended_ne_zero [IsDomain B] (hf' : Function.Injective f) (hI : I != 0) (hN : 0 ∉ N) :
    extended L hf I != 0 := by
  simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    not_forall]
  obtain ⟨x, hx₁, hx₂⟩ : exists x in I, x != 0 := by simpa [ne_eq, eq_zero_iff] using hI
  refine ⟨x, hx₁, ?_⟩
  exact (map_ne_zero_iff _ (IsLocalization.map_injective_of_injective' _ _ _ _ hN hf')).mpr hx₂

@[simp]
/--
theorem `extended_eq_zero_iff` / 定理 `extended_eq_zero_iff`

English:
theorem extended_eq_zero_iff
  given: [IsDomain B] (hf' : Function.Injective f) (hN : 0 ∉ N)
  proof: by
  refine ⟨?_, fun h => h ▸ extended_zero _ _⟩
  contrapose!
  exact fun h => extended_ne_zero L hf hf' h hN

中文:
定理 extended_eq_zero_iff
  条件: [是整环 B] (hf' : 函数.单射 f) (hN : 0 ∉ N)
  证明: by
  refine ⟨?_, fun h => h ▸ extended_zero _ _⟩
  contrapose!
  exact fun h => extended_ne_zero L hf hf' h hN

Depends on / 依赖: contrapose, extended_ne_zero, extended_zero
-/
theorem extended_eq_zero_iff [IsDomain B] (hf' : Function.Injective f) (hN : 0 ∉ N) :
    extended L hf I = 0 ↔ I = 0 := by
  refine ⟨?_, fun h => h ▸ extended_zero _ _⟩
  contrapose!
  exact fun h => extended_ne_zero L hf hf' h hN

variable (I)

@[simp]
/--
theorem `extended_one` / 定理 `extended_one`

English:
theorem extended_one
  statement: extended L hf (1 : FractionalIdeal M K) = 1
  proof: by
refine coeToSubmodule_injective Submodule.ext fun x => ⟨fun hx => span_induction
    ?_ (zero_mem _) (fun y z _ _ hy hz => add_mem hy hz) (fun b y _ hy => smul_mem _ b hy) hx, ?_⟩
  · rintro ⟨b, _, rfl⟩
    rw [Algebra.linearMap_apply]; rw [Algebra.algebraMap_eq_smul_one]
exact smul_mem _ _ subse

中文:
定理 extended_one
  结论: extended L hf (1 : FractionalIdeal M K) = 1
  证明: by
refine coeToSubmodule_injective Submodule.ext fun x => ⟨fun hx => span_induction
    ?_ (zero_mem _) (fun y z _ _ hy hz => add_mem hy hz) (fun b y _ hy => smul_mem _ b hy) hx, ?_⟩
  · rintro ⟨b, _, rfl⟩
    rw [Algebra.linearMap_apply]; rw [Algebra.algebraMap_eq_smul_one]
exact smul_mem _ _ subse

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Algebra.linearMap_apply, Submodule, Submodule.ext, add_mem, algebraMap_eq_smul_one, coeToSubmodule_injective, linearMap_apply, map_eq, one_mem_one, smul_mem, span_induction, subset_span, zero_mem
-/
theorem extended_one : extended L hf (1 : FractionalIdeal M K) = 1 := by
refine coeToSubmodule_injective Submodule.ext fun x => ⟨fun hx => span_induction
    ?_ (zero_mem _) (fun y z _ _ hy hz => add_mem hy hz) (fun b y _ hy => smul_mem _ b hy) hx, ?_⟩
  · rintro ⟨b, _, rfl⟩
    rw [Algebra.linearMap_apply]; rw [Algebra.algebraMap_eq_smul_one]
exact smul_mem _ _ subset_span ⟨1, by simpa using one_mem_one⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, ha, by rw [Algebra.linearMap_apply, Algebra.linearMap_apply, map_eq]⟩

/--
theorem `extended_le_one_of_le_one` / 定理 `extended_le_one_of_le_one`

English:
theorem extended_le_one_of_le_one
  given: (hI : I <= 1)
  statement: extended L hf I <= 1
  proof: by
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp hI
  intro x hx
  simp only [mem_extended_iff, mem_span_image_iff_exists_fun] at hx
  obtain ⟨s, hs, c, rfl⟩ := hx
  refine Submodule.sum_smul_mem _ _ fun ⟨x, hx⟩ h => ?_
  obtain ⟨a, ha, rfl⟩ := hI (hs hx)
  exact ⟨f a, by simp [map_eq]⟩

中文:
定理 extended_le_one_of_le_one
  条件: (hI : I <= 1)
  结论: extended L hf I <= 1
  证明: by
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp hI
  intro x hx
  simp only [mem_extended_iff, mem_span_image_iff_exists_fun] at hx
  obtain ⟨s, hs, c, rfl⟩ := hx
  refine Submodule.sum_smul_mem _ _ fun ⟨x, hx⟩ h => ?_
  obtain ⟨a, ha, rfl⟩ := hI (hs hx)
  exact ⟨f a, by simp [map_eq]⟩

Depends on / 依赖: Submodule, Submodule.sum_smul_mem, le_one_iff_exists_coeIdeal, le_one_iff_exists_coeIdeal.mp, map_eq, mem_extended_iff, mem_span_image_iff_exists_fun, sum_smul_mem
-/
theorem extended_le_one_of_le_one (hI : I <= 1) : extended L hf I <= 1 := by
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp hI
  intro x hx
  simp only [mem_extended_iff, mem_span_image_iff_exists_fun] at hx
  obtain ⟨s, hs, c, rfl⟩ := hx
  refine Submodule.sum_smul_mem _ _ fun ⟨x, hx⟩ h => ?_
  obtain ⟨a, ha, rfl⟩ := hI (hs hx)
  exact ⟨f a, by simp [map_eq]⟩

/--
theorem `one_le_extended_of_one_le` / 定理 `one_le_extended_of_one_le`

English:
theorem one_le_extended_of_one_le
  given: (hI : 1 <= I)
  statement: 1 <= extended L hf I
  proof: by
  rw [one_le] at hI ⊢
exact (mem_extended_iff _ _ _ _).mpr subset_span ⟨1, hI, by rw [map_one]⟩

中文:
定理 one_le_extended_of_one_le
  条件: (hI : 1 <= I)
  结论: 1 <= extended L hf I
  证明: by
  rw [one_le] at hI ⊢
exact (mem_extended_iff _ _ _ _).mpr subset_span ⟨1, hI, by rw [map_one]⟩

Depends on / 依赖: map_one, mem_extended_iff, one_le, subset_span
-/
theorem one_le_extended_of_one_le (hI : 1 <= I) : 1 <= extended L hf I := by
  rw [one_le] at hI ⊢
exact (mem_extended_iff _ _ _ _).mpr subset_span ⟨1, hI, by rw [map_one]⟩

/--
theorem `extended_add` / 定理 `extended_add`

English:
theorem extended_add
  statement: (I + J).extended L hf = (I.extended L hf) + (J.extended L hf)
  proof: by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_add, Submodule.add_eq_sup, ← span_union, ← Set.image_union]
  apply Submodule.span_eq_span
  · rintro _ ⟨y, hy, rfl⟩
obtain ⟨i, hi, j, hj, rfl⟩ := (mem_add I J y).mp SetLike.mem_coe.mp hy
    rw [map_add]
    exact add_mem (S

中文:
定理 extended_add
  结论: (I + J).extended L hf = (I.extended L hf) + (J.extended L hf)
  证明: by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_add, Submodule.add_eq_sup, ← span_union, ← Set.image_union]
  apply Submodule.span_eq_span
  · rintro _ ⟨y, hy, rfl⟩
obtain ⟨i, hi, j, hj, rfl⟩ := (mem_add I J y).mp SetLike.mem_coe.mp hy
    rw [map_add]
    exact add_mem (S

Depends on / 依赖: Set.image_union, Set.mem_union_left, Set.mem_union_right, SetLike, SetLike.mem_coe.mp, SetLike.mem_coe.mpr, Submodule, Submodule.add_eq_sup, Submodule.span_eq_span, Submodule.subset_span, add_eq_sup, add_mem, coeToSubmodule_injective, coe_add, coe_extended_eq_span, image_union, map_add, mem_add, mem_coe, mem_union_left
-/
theorem extended_add : (I + J).extended L hf = (I.extended L hf) + (J.extended L hf) := by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_add, Submodule.add_eq_sup, ← span_union, ← Set.image_union]
  apply Submodule.span_eq_span
  · rintro _ ⟨y, hy, rfl⟩
obtain ⟨i, hi, j, hj, rfl⟩ := (mem_add I J y).mp SetLike.mem_coe.mp hy
    rw [map_add]
    exact add_mem (Submodule.subset_span ⟨i, Set.mem_union_left _ hi, by simp⟩)
      (Submodule.subset_span ⟨j, Set.mem_union_right _ hj, by simp⟩)
  · rintro _ ⟨y, hy, rfl⟩
suffices y in I + J from SetLike.mem_coe.mpr Submodule.subset_span ⟨y, by simp [this]⟩
    exact hy.elim (fun h => (mem_add I J y).mpr ⟨y, h, 0, zero_mem J, add_zero y⟩)
      (fun h => (mem_add I J y).mpr ⟨0, zero_mem I, y, h, zero_add y⟩)

/--
theorem `extended_mul` / 定理 `extended_mul`

English:
theorem extended_mul
  statement: (I * J).extended L hf = (I.extended L hf) * (J.extended L hf)
  proof: by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_mul, span_mul_span]
  refine Submodule.span_eq_span (fun _ h => ?_) (fun _ h => ?_)
  · rcases h with ⟨x, hx, rfl⟩
    replace hx : x in (I : Submodule A K) * (J : Submodule A K) := coe_mul I J ▸ hx
    rw [Submodule.mul_eq_s

中文:
定理 extended_mul
  结论: (I * J).extended L hf = (I.extended L hf) * (J.extended L hf)
  证明: by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_mul, span_mul_span]
  refine Submodule.span_eq_span (fun _ h => ?_) (fun _ h => ?_)
  · rcases h with ⟨x, hx, rfl⟩
    replace hx : x in (I : Submodule A K) * (J : Submodule A K) := coe_mul I J ▸ hx
    rw [Submodule.mul_eq_s

Depends on / 依赖: Set.mem_mul.mp, Set.mem_mul.mpr, Submodule, Submodule.mul_eq_span_mul_set, Submodule.span_eq_span, coeToSubmodule_injective, coe_extended_eq_span, coe_mul, map_f, mem_mul, mul_eq_span_mul_set, replace, span_eq_span, span_induction, span_mul_span, subset_span
-/
theorem extended_mul : (I * J).extended L hf = (I.extended L hf) * (J.extended L hf) := by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_mul, span_mul_span]
  refine Submodule.span_eq_span (fun _ h => ?_) (fun _ h => ?_)
  · rcases h with ⟨x, hx, rfl⟩
    replace hx : x in (I : Submodule A K) * (J : Submodule A K) := coe_mul I J ▸ hx
    rw [Submodule.mul_eq_span_mul_set] at hx
    refine span_induction (fun y hy => ?_) (by simp) (fun y z _ _ hy hz => ?_)
      (fun a y _ hy => ?_) hx
    · rcases Set.mem_mul.mp hy with ⟨i, hi, j, hj, rfl⟩
exact subset_span Set.mem_mul.mpr
        ⟨map_f i, ⟨i, hi, by simp⟩, map_f j, ⟨j, hj, by simp⟩, by simp⟩
    · exact map_add map_f y z ▸ Submodule.add_mem _ hy hz
    · rw [Algebra.smul_def, map_mul, map_eq, ← Algebra.smul_def]
      exact smul_mem _ (f a) hy
  · rcases Set.mem_mul.mp h with ⟨y, ⟨i, hi, rfl⟩, z, ⟨j, hj, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨i * j, mul_mem_mul hi hj, by simp⟩

/--
theorem `extended_extended` / 定理 `extended_extended`

English:
theorem extended_extended
  statement: {C W : Type*} [CommRing C] [CommRing W] [Algebra C W]
  proof: by
  rw [← coeToSubmodule_inj]; rw [coe_extended_eq_span]; rw [coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x in span B (IsLocalization.map L f hf '' (I : Set K)) :=
      (mem_extended_iff L hf I x).1 hx
    refine span_induction (fun y hy => 

中文:
定理 extended_extended
  结论: {C W : 类型} [交换环 C] [交换环 W] [代数 C W]
  证明: by
  rw [← coeToSubmodule_inj]; rw [coe_extended_eq_span]; rw [coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x in span B (IsLocalization.map L f hf '' (I : Set K)) :=
      (mem_extended_iff L hf I x).1 hx
    refine span_induction (fun y hy => 

Depends on / 依赖: IsLocalization, IsLocalization.map, IsLocalization.map_map, Submodule, Submodule.span_eq_span, Submodule.subset_span, Submonoid, Submonoid.monotone_comap, coeToSubmodule_inj, coe_extended_eq_span, g.comp, hf.trans, map_map, mem_extended_iff, monotone_comap, span_eq_span, span_induction, subset_span
-/
theorem extended_extended {C W : Type*} [CommRing C] [CommRing W] [Algebra C W]
    {P : Submonoid C} [IsLocalization P W] {g : B ->+* C} (hg : N <= Submonoid.comap g P) :
      (I.extended L hf).extended W hg =
        I.extended W (f := g.comp f) (hf.trans (Submonoid.monotone_comap hg)) := by
  rw [← coeToSubmodule_inj]; rw [coe_extended_eq_span]; rw [coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x in span B (IsLocalization.map L f hf '' (I : Set K)) :=
      (mem_extended_iff L hf I x).1 hx
    refine span_induction (fun y hy => ?_) (by simp) (fun y z _ _ hy hz => ?_) (fun b y _ hy => ?_) hx'
    · rcases hy with ⟨z, hz, rfl⟩
      exact Submodule.subset_span ⟨z, hz, by rw [IsLocalization.map_map]⟩
    · rw [map_add]
      exact add_mem hy hz
    · rw [IsLocalization.map_smul]
      exact smul_mem _ (g b) hy
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨IsLocalization.map L f hf x, ?_, ?_⟩
· exact (mem_extended_iff L hf I _).2 Submodule.subset_span ⟨x, hx, rfl⟩
    · rw [IsLocalization.map_map]

@[simp]
/--
theorem `extended_coeIdeal_eq_map` / 定理 `extended_coeIdeal_eq_map`

English:
theorem extended_coeIdeal_eq_map
  given: (I₀ : Ideal A)
  proof: by
  rw [Ideal.map]; rw [Ideal.span]; rw [← coeToSubmodule_inj]; rw [Ideal.submodule_span_eq]; rw [coe_coeIdeal]; rw [IsLocalization.coeSubmodule_span]; rw [coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨f a, Set

中文:
定理 extended_coeIdeal_eq_map
  条件: (I₀ : 理想 A)
  证明: by
  rw [Ideal.map]; rw [Ideal.span]; rw [← coeToSubmodule_inj]; rw [Ideal.submodule_span_eq]; rw [coe_coeIdeal]; rw [IsLocalization.coeSubmodule_span]; rw [coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨f a, Set

Depends on / 依赖: Algebra, Algebra.linearMap_apply, Ideal.map, Ideal.span, Ideal.submodule_span_eq, IsLocalization, IsLocalization.coeSubmodule_span, IsLocalization.map_eq, Set.mem_image_of_mem, Submodule, Submodule.span_eq_span, Submodule.subset_span, algebraMap, coeSubmodule_span, coeToSubmodule_inj, coe_coeIdeal, coe_extended_eq_span, linearMap_apply, map_eq, mem_coeIdeal_of_mem
-/
theorem extended_coeIdeal_eq_map (I₀ : Ideal A) :
    (I₀ : FractionalIdeal M K).extended L hf = (I₀.map f : FractionalIdeal N L) := by
  rw [Ideal.map]; rw [Ideal.span]; rw [← coeToSubmodule_inj]; rw [Ideal.submodule_span_eq]; rw [coe_coeIdeal]; rw [IsLocalization.coeSubmodule_span]; rw [coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨f a, Set.mem_image_of_mem f ha, by rw [Algebra.linearMap_apply, IsLocalization.map_eq hf a]⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨algebraMap A K a, mem_coeIdeal_of_mem M ha, IsLocalization.map_eq hf a⟩

/--
theorem `extended_spanSingleton` / 定理 `extended_spanSingleton`

English:
theorem extended_spanSingleton
  given: (x : K)
  proof: by
  ext
  rw [mem_extended_iff]; rw [mem_spanSingleton]; rw [← mem_span_singleton]
  refine ⟨fun hy => span_le.2 ?_ hy, fun hy => span_le.2 (fun _ h => ?_) hy⟩
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_spanSingleton _).1 hw
    rw [SetLike.mem_coe]; rw [Algebra.smul_def]; rw [map_mul]; 

中文:
定理 extended_spanSingleton
  条件: (x : K)
  证明: by
  ext
  rw [mem_extended_iff]; rw [mem_spanSingleton]; rw [← mem_span_singleton]
  refine ⟨fun hy => span_le.2 ?_ hy, fun hy => span_le.2 (fun _ h => ?_) hy⟩
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_spanSingleton _).1 hw
    rw [SetLike.mem_coe]; rw [Algebra.smul_def]; rw [map_mul]; 

Depends on / 依赖: Algebra, Algebra.smul_def, IsLocalization, IsLocalization.map_eq, SetLike, SetLike.mem_coe, SetLike.mem_coe.mpr, h.symm, map_eq, map_mul, mem_coe, mem_extended_iff, mem_spanSingleton, mem_spanSingleton_self, mem_span_singleton, mem_span_singleton_self, smul_def, smul_mem, span_le, subset_span
-/
theorem extended_spanSingleton (x : K) :
    (spanSingleton M x).extended L hf = spanSingleton N (IsLocalization.map L f hf x) := by
  ext
  rw [mem_extended_iff]; rw [mem_spanSingleton]; rw [← mem_span_singleton]
  refine ⟨fun hy => span_le.2 ?_ hy, fun hy => span_le.2 (fun _ h => ?_) hy⟩
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_spanSingleton _).1 hw
    rw [SetLike.mem_coe]; rw [Algebra.smul_def]; rw [map_mul]; rw [IsLocalization.map_eq]; rw [← Algebra.smul_def]
    exact smul_mem _ _ (mem_span_singleton_self _)
  · exact subset_span ⟨x, SetLike.mem_coe.mpr (mem_spanSingleton_self _ x), h.symm⟩

/--
The ring homomorphism version of `FractionalIdeal.extended`.
See `FractionalIdeal.extendedHom` for a more convenient version that is often enough.
-/
@[simps]
/--
Definition of `extendedHom'` / `extendedHom'` 的定义

English:
definition extendedHom'
  signature: : FractionalIdeal M K ->+* FractionalIdeal N L where
  body: extended L hf
  map_one' := extended_one L hf
  map_zero' := extended_zero L hf
  map_mul' := extended_mul L hf
  map_add' := extended_add L hf

中文:
定义 extendedHom'
  签名: : FractionalIdeal M K ->+* FractionalIdeal N L where
  定义体: extended L hf
  map_one' := extended_one L hf
  map_zero' := extended_zero L hf
  map_mul' := extended_mul L hf
  map_add' := extended_add L hf

Depends on / 依赖: extended
-/
def extendedHom' : FractionalIdeal M K ->+* FractionalIdeal N L where
  toFun := extended L hf
  map_one' := extended_one L hf
  map_zero' := extended_zero L hf
  map_mul' := extended_mul L hf
  map_add' := extended_add L hf

/--
theorem `extendedHom'_comp` / 定理 `extendedHom'_comp`

English:
theorem extendedHom'_comp
  statement: {C W : Type*} [CommRing C] [CommRing W] [Algebra C W]
  proof: by
  apply RingHom.ext
  intro I
  exact extended_extended (A := A) (B := B) (f := f) (K := K) (M := M) (L := L)
    (N := N) (hf := hf) (I := I) (C := C) (W := W) (P := P) (g := g) hg

中文:
定理 extendedHom'_comp
  结论: {C W : 类型} [交换环 C] [交换环 W] [代数 C W]
  证明: by
  apply RingHom.ext
  intro I
  exact extended_extended (A := A) (B := B) (f := f) (K := K) (M := M) (L := L)
    (N := N) (hf := hf) (I := I) (C := C) (W := W) (P := P) (g := g) hg
-/
theorem extendedHom'_comp {C W : Type*} [CommRing C] [CommRing W] [Algebra C W]
    {P : Submonoid C} [IsLocalization P W] {g : B ->+* C} (hg : N <= Submonoid.comap g P) :
    (extendedHom' (A := B) (K := L) W hg).comp
      (extendedHom' (A := A) (K := K) L hf) =
        extendedHom' (A := A) (B := C) (f := g.comp f) (K := K) W
          (hf.trans (Submonoid.monotone_comap (f := f) hg)) := by
  apply RingHom.ext
  intro I
  exact extended_extended (A := A) (B := B) (f := f) (K := K) (M := M) (L := L)
    (N := N) (hf := hf) (I := I) (C := C) (W := W) (P := P) (g := g) hg

end RingHom

section Algebra

open scoped nonZeroDivisors

variable {A K : Type*} (L B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [IsTorsionFree A B] [Field K] [Field L] [Algebra A K] [Algebra B L]
  [IsFractionRing A K] [IsFractionRing B L] {I : FractionalIdeal A⁰ K}

/--
Definition of `extendedHom` / `extendedHom` 的定义

English:
abbreviation extendedHom
  signature: : FractionalIdeal A⁰ K ->+* FractionalIdeal B⁰ L
  body: extendedHom' L
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

@[deprecated (since := "2026-04-16")] alias extendedHomₐ := extendedHom

中文:
缩写 extendedHom
  签名: : FractionalIdeal A⁰ K ->+* FractionalIdeal B⁰ L
  定义体: extendedHom' L
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

@[deprecated (since := "2026-04-16")] alias extendedHomₐ := extendedHom

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, extendedHom, nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
-/
abbrev extendedHom : FractionalIdeal A⁰ K ->+* FractionalIdeal B⁰ L :=
extendedHom' L
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

@[deprecated (since := "2026-04-16")] alias extendedHomₐ := extendedHom

/--
theorem `extendedHom_eq_zero_iff` / 定理 `extendedHom_eq_zero_iff`

English:
theorem extendedHom_eq_zero_iff
  given: {I : FractionalIdeal A⁰ K}
  proof: extended_eq_zero_iff _ _ (FaithfulSMul.algebraMap_injective _ _) zero_notMem_nonZeroDivisors

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_eq_zero_iff := extendedHom_eq_zero_iff

中文:
定理 extendedHom_eq_zero_iff
  条件: {I : FractionalIdeal A⁰ K}
  证明: extended_eq_zero_iff _ _ (FaithfulSMul.algebraMap_injective _ _) zero_notMem_nonZeroDivisors

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_eq_zero_iff := extendedHom_eq_zero_iff

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, extended_eq_zero_iff, zero_notMem_nonZeroDivisors
-/
theorem extendedHom_eq_zero_iff {I : FractionalIdeal A⁰ K} :
    extendedHom L B I = 0 ↔ I = 0 :=
  extended_eq_zero_iff _ _ (FaithfulSMul.algebraMap_injective _ _) zero_notMem_nonZeroDivisors

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_eq_zero_iff := extendedHom_eq_zero_iff

/--
theorem `extendedHom_coeIdeal_eq_map` / 定理 `extendedHom_coeIdeal_eq_map`

English:
theorem extendedHom_coeIdeal_eq_map
  given: (I : Ideal A)
  proof: extended_coeIdeal_eq_map L _ I

@[deprecated (since := "2026-04-16")]
alias extendedHomₐ_coeIdeal_eq_map := extendedHom_coeIdeal_eq_map

中文:
定理 extendedHom_coeIdeal_eq_map
  条件: (I : 理想 A)
  证明: extended_coeIdeal_eq_map L _ I

@[deprecated (since := "2026-04-16")]
alias extendedHomₐ_coeIdeal_eq_map := extendedHom_coeIdeal_eq_map

Depends on / 依赖: extended_coeIdeal_eq_map
-/
theorem extendedHom_coeIdeal_eq_map (I : Ideal A) :
    (I : FractionalIdeal A⁰ K).extendedHom L B =
      (I.map (algebraMap A B) : FractionalIdeal B⁰ L) := extended_coeIdeal_eq_map L _ I

@[deprecated (since := "2026-04-16")]
alias extendedHomₐ_coeIdeal_eq_map := extendedHom_coeIdeal_eq_map

/--
theorem `extendedHom_spanSingleton` / 定理 `extendedHom_spanSingleton`

English:
theorem extendedHom_spanSingleton
  given: (x : K)
  statement: extendedHom L B (spanSingleton A⁰ x) =
  proof: extended_spanSingleton L _ x

中文:
定理 extendedHom_spanSingleton
  条件: (x : K)
  结论: extendedHom L B (spanSingleton A⁰ x) =
  证明: extended_spanSingleton L _ x

Depends on / 依赖: extended_spanSingleton
-/
theorem extendedHom_spanSingleton (x : K) : extendedHom L B (spanSingleton A⁰ x) =
    spanSingleton B⁰ (IsFractionRing.map (FaithfulSMul.algebraMap_injective A B) x) :=
  extended_spanSingleton L _ x

variable [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsIntegral A B]

/--
theorem `coe_extendedHom_eq_span` / 定理 `coe_extendedHom_eq_span`

English:
theorem coe_extendedHom_eq_span
  given: (I : FractionalIdeal A⁰ K)
  proof: by
  rw [extendedHom'_apply]; rw [coe_extended_eq_span]; rw [IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
  rfl

@[deprecated (since := "2026-04-16")] alias coe_extendedHomₐ_eq_span := coe_extendedHom_eq_span

中文:
定理 coe_extendedHom_eq_span
  条件: (I : FractionalIdeal A⁰ K)
  证明: by
  rw [extendedHom'_apply]; rw [coe_extended_eq_span]; rw [IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
  rfl

@[deprecated (since := "2026-04-16")] alias coe_extendedHomₐ_eq_span := coe_extendedHom_eq_span

Depends on / 依赖: IsLocalization, IsLocalization.algebraMap_eq_map_map_submonoid, _apply, algebraMap_eq_map_map_submonoid, coe_extended_eq_span, extendedHom
-/
theorem coe_extendedHom_eq_span (I : FractionalIdeal A⁰ K) :
    extendedHom L B I = span B (algebraMap K L '' I) := by
  rw [extendedHom'_apply]; rw [coe_extended_eq_span]; rw [IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
  rfl

@[deprecated (since := "2026-04-16")] alias coe_extendedHomₐ_eq_span := coe_extendedHom_eq_span

/--
theorem `le_one_of_extendedHom_le_one` / 定理 `le_one_of_extendedHom_le_one`

English:
theorem le_one_of_extendedHom_le_one
  statement: [IsIntegrallyClosed A] [IsIntegrallyClosed B]
  proof: by
  contrapose hI
  rw [SetLike.not_le_iff_exists] at hI ⊢
  obtain ⟨x, hx₁, hx₂⟩ := hI
  refine ⟨algebraMap K L x, ?_, ?_⟩
  · simpa [← FractionalIdeal.mem_coe, IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
using! subset_span Set.mem_image_of_mem _ hx₁
  · contrapose hx₂
    rw [mem_one

中文:
定理 le_one_of_extendedHom_le_one
  结论: [是整闭 A] [是整闭 B]
  证明: by
  contrapose hI
  rw [SetLike.not_le_iff_exists] at hI ⊢
  obtain ⟨x, hx₁, hx₂⟩ := hI
  refine ⟨algebraMap K L x, ?_, ?_⟩
  · simpa [← FractionalIdeal.mem_coe, IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
using! subset_span Set.mem_image_of_mem _ hx₁
  · contrapose hx₂
    rw [mem_one

Depends on / 依赖: FractionalIdeal, FractionalIdeal.mem_coe, IsIntegral, IsIntegral.tower_bot_of_field, IsIntegrallyClosed, IsIntegrallyClosed.isIntegral_iff, IsLocalization, IsLocalization.algebraMap_eq_map_map_submonoid, Set.mem_image_of_mem, SetLike, SetLike.not_le_iff_exists, algebraMap, algebraMap_eq_map_map_submonoid, contrapose, isIntegral_iff, isIntegral_trans, mem_coe, mem_image_of_mem, mem_one_iff, not_le_iff_exists
-/
theorem le_one_of_extendedHom_le_one [IsIntegrallyClosed A] [IsIntegrallyClosed B]
    (hI : extendedHom L B I <= 1) : I <= 1 := by
  contrapose hI
  rw [SetLike.not_le_iff_exists] at hI ⊢
  obtain ⟨x, hx₁, hx₂⟩ := hI
  refine ⟨algebraMap K L x, ?_, ?_⟩
  · simpa [← FractionalIdeal.mem_coe, IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
using! subset_span Set.mem_image_of_mem _ hx₁
  · contrapose hx₂
    rw [mem_one_iff]; rw [← IsIntegrallyClosed.isIntegral_iff] at hx₂ ⊢
exact IsIntegral.tower_bot_of_field isIntegral_trans _ hx₂

@[deprecated (since := "2026-04-16")]
alias le_one_of_extendedHomₐ_le_one := le_one_of_extendedHom_le_one

/--
theorem `extendedHom_le_one_iff` / 定理 `extendedHom_le_one_iff`

English:
theorem extendedHom_le_one_iff
  given: [IsIntegrallyClosed A] [IsIntegrallyClosed B]
  proof: ⟨fun h => le_one_of_extendedHom_le_one L B h, fun a => extended_le_one_of_le_one L _ I a⟩

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_le_one_iff := extendedHom_le_one_iff

中文:
定理 extendedHom_le_one_iff
  条件: [是整闭 A] [是整闭 B]
  证明: ⟨fun h => le_one_of_extendedHom_le_one L B h, fun a => extended_le_one_of_le_one L _ I a⟩

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_le_one_iff := extendedHom_le_one_iff

Depends on / 依赖: extended_le_one_of_le_one, le_one_of_extendedHom_le_one
-/
theorem extendedHom_le_one_iff [IsIntegrallyClosed A] [IsIntegrallyClosed B] :
    extendedHom L B I <= 1 ↔ I <= 1 :=
  ⟨fun h => le_one_of_extendedHom_le_one L B h, fun a => extended_le_one_of_le_one L _ I a⟩

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_le_one_iff := extendedHom_le_one_iff

section IsDedekindDomain

set_option linter.overlappingInstances false

variable [IsDedekindDomain A] [IsDedekindDomain B]

/--
theorem `one_le_extendedHom_iff` / 定理 `one_le_extendedHom_iff`

English:
theorem one_le_extendedHom_iff
  given: (hI : I != 0)
  statement: 1 <= extendedHom L B I ↔ 1 <= I
  proof: by
  rw [← inv_le_inv_iff ((extendedHom_eq_zero_iff _ _).not.mpr hI) (by simp)]; rw [inv_one]; rw [← map_inv₀]; rw [extendedHom_le_one_iff]; rw [inv_le_comm hI (by simp)]; rw [inv_one]

@[deprecated (since := "2026-04-16")] alias one_le_extendedHomₐ_iff := one_le_extendedHom_iff

中文:
定理 one_le_extendedHom_iff
  条件: (hI : I != 0)
  结论: 1 <= extendedHom L B I ↔ 1 <= I
  证明: by
  rw [← inv_le_inv_iff ((extendedHom_eq_zero_iff _ _).not.mpr hI) (by simp)]; rw [inv_one]; rw [← map_inv₀]; rw [extendedHom_le_one_iff]; rw [inv_le_comm hI (by simp)]; rw [inv_one]

@[deprecated (since := "2026-04-16")] alias one_le_extendedHomₐ_iff := one_le_extendedHom_iff

Depends on / 依赖: extendedHom_eq_zero_iff, extendedHom_le_one_iff, inv_le_comm, inv_le_inv_iff, inv_one, not.mpr
-/
theorem one_le_extendedHom_iff (hI : I != 0) : 1 <= extendedHom L B I ↔ 1 <= I := by
  rw [← inv_le_inv_iff ((extendedHom_eq_zero_iff _ _).not.mpr hI) (by simp)]; rw [inv_one]; rw [← map_inv₀]; rw [extendedHom_le_one_iff]; rw [inv_le_comm hI (by simp)]; rw [inv_one]

@[deprecated (since := "2026-04-16")] alias one_le_extendedHomₐ_iff := one_le_extendedHom_iff

/--
theorem `extendedHom_eq_one_iff` / 定理 `extendedHom_eq_one_iff`

English:
theorem extendedHom_eq_one_iff
  given: (hI : I != 0)
  statement: extendedHom L B I = 1 ↔ I = 1
  proof: by
  rw [le_antisymm_iff]; rw [extendedHom_le_one_iff]; rw [one_le_extendedHom_iff _ _ hI]; rw [← le_antisymm_iff]

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_eq_one_iff := extendedHom_eq_one_iff

中文:
定理 extendedHom_eq_one_iff
  条件: (hI : I != 0)
  结论: extendedHom L B I = 1 ↔ I = 1
  证明: by
  rw [le_antisymm_iff]; rw [extendedHom_le_one_iff]; rw [one_le_extendedHom_iff _ _ hI]; rw [← le_antisymm_iff]

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_eq_one_iff := extendedHom_eq_one_iff

Depends on / 依赖: extendedHom_le_one_iff, le_antisymm_iff, one_le_extendedHom_iff
-/
theorem extendedHom_eq_one_iff (hI : I != 0) : extendedHom L B I = 1 ↔ I = 1 := by
  rw [le_antisymm_iff]; rw [extendedHom_le_one_iff]; rw [one_le_extendedHom_iff _ _ hI]; rw [← le_antisymm_iff]

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_eq_one_iff := extendedHom_eq_one_iff

variable (A K) in
/--
theorem `extendedHom_injective` / 定理 `extendedHom_injective`

English:
theorem extendedHom_injective
  proof: by
  intro I J h
  dsimp only at h
  by_cases hI : I = 0
  · rwa [hI, map_zero, eq_comm, extendedHom_eq_zero_iff L B, eq_comm, ← hI] at h
  by_cases hJ : J = 0
  · rwa [hJ, map_zero, extendedHom_eq_zero_iff L B, ← hJ] at h
  rwa [← mul_inv_eq_one₀ ((extendedHom_eq_zero_iff _ _).not.mpr hJ), ← map_in

中文:
定理 extendedHom_injective
  证明: by
  intro I J h
  dsimp only at h
  by_cases hI : I = 0
  · rwa [hI, map_zero, eq_comm, extendedHom_eq_zero_iff L B, eq_comm, ← hI] at h
  by_cases hJ : J = 0
  · rwa [hJ, map_zero, extendedHom_eq_zero_iff L B, ← hJ] at h
  rwa [← mul_inv_eq_one₀ ((extendedHom_eq_zero_iff _ _).not.mpr hJ), ← map_in

Depends on / 依赖: eq_comm, extendedHom_eq_one_iff, extendedHom_eq_zero_iff, inv_ne_zero, map_mul, map_zero, mul_ne_zero, not.mpr
-/
theorem extendedHom_injective :
    Function.Injective (fun I : FractionalIdeal A⁰ K => extendedHom L B I) := by
  intro I J h
  dsimp only at h
  by_cases hI : I = 0
  · rwa [hI, map_zero, eq_comm, extendedHom_eq_zero_iff L B, eq_comm, ← hI] at h
  by_cases hJ : J = 0
  · rwa [hJ, map_zero, extendedHom_eq_zero_iff L B, ← hJ] at h
  rwa [← mul_inv_eq_one₀ ((extendedHom_eq_zero_iff _ _).not.mpr hJ), ← map_inv₀, ← map_mul,
    extendedHom_eq_one_iff _ _ (mul_ne_zero hI (inv_ne_zero hJ)), mul_inv_eq_one₀ hJ] at h

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_injective := extendedHom_injective

end IsDedekindDomain

end Algebra

end FractionalIdeal
