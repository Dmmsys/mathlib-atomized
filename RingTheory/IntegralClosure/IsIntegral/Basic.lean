/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.Polynomial.Tower

/-!
# Properties of integral elements.

We prove basic properties of integral elements in a ring extension.
-/

public section

open Polynomial Submodule

section Ring

variable {R S A T : Type*}
variable [CommRing R] [Ring A] [Ring S] [Ring T] (f : R ->+* S) (g : S ->+* T)
variable [Algebra R A]

/--
theorem `RingHom.isIntegralElem_map` / 定理 `RingHom.isIntegralElem_map`

English:
theorem RingHom.isIntegralElem_map
  given: {x : R}
  statement: f.IsIntegralElem (f x)
  proof: ⟨X - C x, monic_X_sub_C _, by simp⟩

中文:
定理 RingHom.isIntegralElem_map
  条件: {x : R}
  结论: f.Is整数egralElem (f x)
  证明: ⟨X - C x, monic_X_sub_C _, by simp⟩

Depends on / 依赖: monic_X_sub_C
-/
theorem RingHom.isIntegralElem_map {x : R} : f.IsIntegralElem (f x) :=
  ⟨X - C x, monic_X_sub_C _, by simp⟩

/--
theorem `isIntegral_algebraMap` / 定理 `isIntegral_algebraMap`

English:
theorem isIntegral_algebraMap
  given: {x : R}
  statement: IsIntegral R (algebraMap R A x)
  proof: (algebraMap R A).isIntegralElem_map

中文:
定理 isIntegral_algebraMap
  条件: {x : R}
  结论: Is整数egral R (algebraMap R A x)
  证明: (algebraMap R A).isIntegralElem_map

Depends on / 依赖: algebraMap, isIntegralElem_map
-/
theorem isIntegral_algebraMap {x : R} : IsIntegral R (algebraMap R A x) :=
  (algebraMap R A).isIntegralElem_map

variable {f} in
/--
lemma `RingHom.IsIntegralElem.map` / 引理 `RingHom.IsIntegralElem.map`

English:
lemma RingHom.IsIntegralElem.map
  given: {x : S} (hx : f.IsIntegralElem x) (g : S ->+* T)
  proof: by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p, hp, by simp_rw [← hom_eval₂, eval₂_eq_eval_map] at hx ⊢; simp [hx]⟩

中文:
引理 RingHom.IsIntegralElem.map
  条件: {x : S} (hx : f.Is整数egralElem x) (g : S ->+* T)
  证明: by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p, hp, by simp_rw [← hom_eval₂, eval₂_eq_eval_map] at hx ⊢; simp [hx]⟩

Depends on / 依赖: simp_rw
-/
lemma RingHom.IsIntegralElem.map {x : S} (hx : f.IsIntegralElem x) (g : S ->+* T) :
    (g.comp f).IsIntegralElem (g x) := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p, hp, by simp_rw [← hom_eval₂, eval₂_eq_eval_map] at hx ⊢; simp [hx]⟩

variable {f g} in
/--
lemma `RingHom.IsIntegralElem.of_map` / 引理 `RingHom.IsIntegralElem.of_map`

English:
lemma RingHom.IsIntegralElem.of_map
  statement: (hg : Function.Injective g) {x : S}
  proof: by
  obtain ⟨p, hp, hx⟩ := hx
exact ⟨p, hp, hg by simp [Polynomial.hom_eval₂, hx]⟩

中文:
引理 RingHom.IsIntegralElem.of_map
  结论: (hg : Function.Injective g) {x : S}
  证明: by
  obtain ⟨p, hp, hx⟩ := hx
exact ⟨p, hp, hg by simp [Polynomial.hom_eval₂, hx]⟩

Depends on / 依赖: Polynomial, Polynomial.hom_eval
-/
lemma RingHom.IsIntegralElem.of_map (hg : Function.Injective g) {x : S}
    (hx : (g.comp f).IsIntegralElem (g x)) :
    f.IsIntegralElem x := by
  obtain ⟨p, hp, hx⟩ := hx
exact ⟨p, hp, hg by simp [Polynomial.hom_eval₂, hx]⟩

variable {f g} in
/--
lemma `RingHom.IsIntegralElem.map_iff` / 引理 `RingHom.IsIntegralElem.map_iff`

English:
lemma RingHom.IsIntegralElem.map_iff
  given: (hg : Function.Injective g) {x : S}
  proof: ⟨of_map hg, (map · g)⟩

中文:
引理 RingHom.IsIntegralElem.map_iff
  条件: (hg : Function.Injective g) {x : S}
  证明: ⟨of_map hg, (map · g)⟩

Depends on / 依赖: of_map
-/
lemma RingHom.IsIntegralElem.map_iff (hg : Function.Injective g) {x : S} :
    (g.comp f).IsIntegralElem (g x) ↔ f.IsIntegralElem x :=
  ⟨of_map hg, (map · g)⟩

end Ring

section

variable {R A B S T : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S] [Ring T]
variable [Algebra R A] (f : R ->+* S)

variable {f} in
/--
lemma `RingHom.IsIntegralElem.of_comp` / 引理 `RingHom.IsIntegralElem.of_comp`

English:
lemma RingHom.IsIntegralElem.of_comp
  given: {g : S ->+* T} {x : T} (hx : (g.comp f).IsIntegralElem x)
  proof: by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p.map f, hp.map _, by simpa only [eval₂_eq_eval_map, map_map] using hx⟩

中文:
引理 RingHom.IsIntegralElem.of_comp
  条件: {g : S ->+* T} {x : T} (hx : (g.comp f).Is整数egralElem x)
  证明: by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p.map f, hp.map _, by simpa only [eval₂_eq_eval_map, map_map] using hx⟩

Depends on / 依赖: hp.map, map_map, p.map
-/
lemma RingHom.IsIntegralElem.of_comp {g : S ->+* T} {x : T} (hx : (g.comp f).IsIntegralElem x) :
    g.IsIntegralElem x := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p.map f, hp.map _, by simpa only [eval₂_eq_eval_map, map_map] using hx⟩

/--
theorem `IsIntegral.map` / 定理 `IsIntegral.map`

English:
theorem IsIntegral.map
  statement: {B C F : Type*} [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C]
  proof: by
  rw [IsIntegral]; rw [← ((AlgHomClass.toAlgHom f).restrictScalars R).comp_algebraMap]
  exact .map hb (RingHomClass.toRingHom f)

中文:
定理 IsIntegral.map
  结论: {B C F : 类型} [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C]
  证明: by
  rw [IsIntegral]; rw [← ((AlgHomClass.toAlgHom f).restrictScalars R).comp_algebraMap]
  exact .map hb (RingHomClass.toRingHom f)

Depends on / 依赖: AlgHomClass, AlgHomClass.toAlgHom, IsIntegral, RingHomClass, RingHomClass.toRingHom, comp_algebraMap, restrictScalars, toAlgHom, toRingHom
-/
theorem IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C]
    [IsScalarTower R A B] [Algebra A C] [IsScalarTower R A C] {b : B}
    [FunLike F B C] [AlgHomClass F A B C] (f : F)
    (hb : IsIntegral R b) : IsIntegral R (f b) := by
  rw [IsIntegral]; rw [← ((AlgHomClass.toAlgHom f).restrictScalars R).comp_algebraMap]
  exact .map hb (RingHomClass.toRingHom f)

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/--
theorem `isIntegral_algHom_iff` / 定理 `isIntegral_algHom_iff`

English:
theorem isIntegral_algHom_iff
  given: (f : A ->ₐ[R] B) (hf : Function.Injective f) {x : A}
  proof: by
  simp [IsIntegral, ← RingHom.IsIntegralElem.map_iff (g := (f : A ->+* B)) hf]

中文:
定理 isIntegral_algHom_iff
  条件: (f : A ->ₐ[R] B) (hf : Function.Injective f) {x : A}
  证明: by
  simp [IsIntegral, ← RingHom.IsIntegralElem.map_iff (g := (f : A ->+* B)) hf]

Depends on / 依赖: IsIntegral, IsIntegralElem, RingHom, RingHom.IsIntegralElem.map_iff, map_iff
-/
theorem isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Function.Injective f) {x : A} :
    IsIntegral R (f x) ↔ IsIntegral R x := by
  simp [IsIntegral, ← RingHom.IsIntegralElem.map_iff (g := (f : A ->+* B)) hf]

end

open scoped Classical in
/--
theorem `Submodule.span_range_natDegree_eq_adjoin` / 定理 `Submodule.span_range_natDegree_eq_adjoin`

English:
theorem Submodule.span_range_natDegree_eq_adjoin
  statement: {R A} [CommRing R] [Semiring A] [Algebra R A]
  proof: by
  nontriviality A
  have hf1 : f != 1 := by rintro rfl; simp [one_ne_zero' A] at hfx
  refine (span_le.mpr fun s hs => ?_).antisymm fun r hr => ?_
  · rcases Finset.mem_image.1 (SetLike.mem_coe.mp hs) with ⟨k, -, rfl⟩
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin rfl) k
  rw [Su

中文:
定理 Submodule.span_range_natDegree_eq_adjoin
  结论: {R A} [CommRing R] [Semiring A] [Algebra R A]
  证明: by
  nontriviality A
  have hf1 : f != 1 := by rintro rfl; simp [one_ne_zero' A] at hfx
  refine (span_le.mpr fun s hs => ?_).antisymm fun r hr => ?_
  · rcases Finset.mem_image.1 (SetLike.mem_coe.mp hs) with ⟨k, -, rfl⟩
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin rfl) k
  rw [Su

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.adjoin_singleton_eq_range_aeval, Algebra.subset_adjoin, Finset, Finset.mem_image, SetLike, SetLike.mem_coe.mp, Subalgebra, Subalgebra.mem_toSubmodule, adjoin, adjoin_singleton_eq_range_aeval, antisymm, map_add, map_mul, mem_coe, mem_image, mem_range, mem_range.mp, mem_toSubmodule
-/
theorem Submodule.span_range_natDegree_eq_adjoin {R A} [CommRing R] [Semiring A] [Algebra R A]
    {x : A} {f : R[X]} (hf : f.Monic) (hfx : aeval x f = 0) :
    span R (Finset.image (x ^ ·) (Finset.range (natDegree f))) =
      Subalgebra.toSubmodule (Algebra.adjoin R {x}) := by
  nontriviality A
  have hf1 : f != 1 := by rintro rfl; simp [one_ne_zero' A] at hfx
  refine (span_le.mpr fun s hs => ?_).antisymm fun r hr => ?_
  · rcases Finset.mem_image.1 (SetLike.mem_coe.mp hs) with ⟨k, -, rfl⟩
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin rfl) k
  rw [Subalgebra.mem_toSubmodule]; rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
  rcases (aeval x).mem_range.mp hr with ⟨p, rfl⟩
  rw [← modByMonic_add_div p f]; rw [map_add]; rw [map_mul]; rw [hfx]; rw [zero_mul]; rw [add_zero]; rw [← sum_C_mul_X_pow_eq (p %ₘ f)]; rw [aeval_def]; rw [eval₂_sum]; rw [sum_def]
  refine sum_mem fun k hkq => ?_
  rw [C_mul_X_pow_eq_monomial]; rw [eval₂_monomial]; rw [← Algebra.smul_def]
  exact smul_mem _ _ (subset_span <| Finset.mem_image_of_mem _ <| Finset.mem_range.mpr <|
(le_natDegree_of_mem_supp _ hkq).trans_lt natDegree_modByMonic_lt p hf hf1)

/--
theorem `IsIntegral.fg_adjoin_singleton` / 定理 `IsIntegral.fg_adjoin_singleton`

English:
theorem IsIntegral.fg_adjoin_singleton
  given: [Algebra R B] {x : B} (hx : IsIntegral R x)
  proof: by
  classical
  rcases hx with ⟨f, hfm, hfx⟩
  use (Finset.range <| f.natDegree).image (x ^ ·)
  exact span_range_natDegree_eq_adjoin hfm (by rwa [aeval_def])

中文:
定理 IsIntegral.fg_adjoin_singleton
  条件: [Algebra R B] {x : B} (hx : Is整数egral R x)
  证明: by
  classical
  rcases hx with ⟨f, hfm, hfx⟩
  use (Finset.range <| f.natDegree).image (x ^ ·)
  exact span_range_natDegree_eq_adjoin hfm (by rwa [aeval_def])

Depends on / 依赖: Finset, Finset.range, aeval_def, classical, f.natDegree, natDegree, span_range_natDegree_eq_adjoin
-/
theorem IsIntegral.fg_adjoin_singleton [Algebra R B] {x : B} (hx : IsIntegral R x) :
    (Algebra.adjoin R {x}).toSubmodule.FG := by
  classical
  rcases hx with ⟨f, hfm, hfx⟩
  use (Finset.range <| f.natDegree).image (x ^ ·)
  exact span_range_natDegree_eq_adjoin hfm (by rwa [aeval_def])

variable (f : R ->+* B)

/--
theorem `RingHom.isIntegralElem_zero` / 定理 `RingHom.isIntegralElem_zero`

English:
theorem RingHom.isIntegralElem_zero
  statement: f.IsIntegralElem 0
  proof: f.map_zero ▸ f.isIntegralElem_map

中文:
定理 RingHom.isIntegralElem_zero
  结论: f.Is整数egralElem 0
  证明: f.map_zero ▸ f.isIntegralElem_map

Depends on / 依赖: f.isIntegralElem_map, f.map_zero, isIntegralElem_map, map_zero
-/
theorem RingHom.isIntegralElem_zero : f.IsIntegralElem 0 :=
  f.map_zero ▸ f.isIntegralElem_map

/--
theorem `isIntegral_zero` / 定理 `isIntegral_zero`

English:
theorem isIntegral_zero
  given: [Algebra R B]
  statement: IsIntegral R (0 : B)
  proof: (algebraMap R B).isIntegralElem_zero

中文:
定理 isIntegral_zero
  条件: [Algebra R B]
  结论: Is整数egral R (0 : B)
  证明: (algebraMap R B).isIntegralElem_zero

Depends on / 依赖: algebraMap, isIntegralElem_zero
-/
theorem isIntegral_zero [Algebra R B] : IsIntegral R (0 : B) :=
  (algebraMap R B).isIntegralElem_zero

/--
theorem `RingHom.isIntegralElem_one` / 定理 `RingHom.isIntegralElem_one`

English:
theorem RingHom.isIntegralElem_one
  statement: f.IsIntegralElem 1
  proof: f.map_one ▸ f.isIntegralElem_map

中文:
定理 RingHom.isIntegralElem_one
  结论: f.Is整数egralElem 1
  证明: f.map_one ▸ f.isIntegralElem_map

Depends on / 依赖: f.isIntegralElem_map, f.map_one, isIntegralElem_map, map_one
-/
theorem RingHom.isIntegralElem_one : f.IsIntegralElem 1 :=
  f.map_one ▸ f.isIntegralElem_map

/--
theorem `isIntegral_one` / 定理 `isIntegral_one`

English:
theorem isIntegral_one
  given: [Algebra R B]
  statement: IsIntegral R (1 : B)
  proof: (algebraMap R B).isIntegralElem_one

中文:
定理 isIntegral_one
  条件: [Algebra R B]
  结论: Is整数egral R (1 : B)
  证明: (algebraMap R B).isIntegralElem_one

Depends on / 依赖: algebraMap, isIntegralElem_one
-/
theorem isIntegral_one [Algebra R B] : IsIntegral R (1 : B) :=
  (algebraMap R B).isIntegralElem_one

variable (f : R ->+* S)

/--
theorem `IsIntegral.of_pow` / 定理 `IsIntegral.of_pow`

English:
theorem IsIntegral.of_pow
  given: [Algebra R B] {x : B} {n : Nat} (hn : 0 < n) (hx : IsIntegral R <| x ^ n)
  proof: have ⟨p, hmonic, heval⟩ := hx
  ⟨expand R n p, hmonic.expand hn, by rwa [← aeval_def, expand_aeval]⟩

中文:
定理 IsIntegral.of_pow
  条件: [Algebra R B] {x : B} {n : 自然数} (hn : 0 < n) (hx : Is整数egral R <| x ^ n)
  证明: have ⟨p, hmonic, heval⟩ := hx
  ⟨expand R n p, hmonic.expand hn, by rwa [← aeval_def, expand_aeval]⟩

Depends on / 依赖: aeval_def, expand, expand_aeval, hmonic, hmonic.expand
-/
theorem IsIntegral.of_pow [Algebra R B] {x : B} {n : Nat} (hn : 0 < n) (hx : IsIntegral R <| x ^ n) :
    IsIntegral R x :=
  have ⟨p, hmonic, heval⟩ := hx
  ⟨expand R n p, hmonic.expand hn, by rwa [← aeval_def, expand_aeval]⟩

/--
theorem `IsIntegral.of_aeval_monic` / 定理 `IsIntegral.of_aeval_monic`

English:
theorem IsIntegral.of_aeval_monic
  statement: {x : A} {p : R[X]} (monic : p.Monic)
  proof: have ⟨p, hmonic, heval⟩ := hx
  ⟨_, hmonic.comp monic deg, by rwa [eval₂_comp, ← aeval_def x]⟩

中文:
定理 IsIntegral.of_aeval_monic
  结论: {x : A} {p : R[X]} (monic : p.Monic)
  证明: have ⟨p, hmonic, heval⟩ := hx
  ⟨_, hmonic.comp monic deg, by rwa [eval₂_comp, ← aeval_def x]⟩

Depends on / 依赖: aeval_def, hmonic, hmonic.comp
-/
theorem IsIntegral.of_aeval_monic {x : A} {p : R[X]} (monic : p.Monic)
    (deg : p.natDegree != 0) (hx : IsIntegral R (aeval x p)) : IsIntegral R x :=
  have ⟨p, hmonic, heval⟩ := hx
  ⟨_, hmonic.comp monic deg, by rwa [eval₂_comp, ← aeval_def x]⟩

end

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] (f : R ->+* S)

/--
theorem `IsIntegral.map_of_comp_eq` / 定理 `IsIntegral.map_of_comp_eq`

English:
theorem IsIntegral.map_of_comp_eq
  statement: {R S T U : Type*} [CommRing R] [Ring S]
  proof: let ⟨p, hp⟩ := ha
  ⟨p.map φ, hp.1.map _, by
    rw [← eval_map]; rw [map_map]; rw [h]; rw [← map_map]; rw [eval_map]; rw [eval₂_at_apply]; rw [eval_map]; rw [hp.2]; rw [ψ.map_zero]⟩

@[simp]

中文:
定理 IsIntegral.map_of_comp_eq
  结论: {R S T U : 类型} [CommRing R] [Ring S]
  证明: let ⟨p, hp⟩ := ha
  ⟨p.map φ, hp.1.map _, by
    rw [← eval_map]; rw [map_map]; rw [h]; rw [← map_map]; rw [eval_map]; rw [eval₂_at_apply]; rw [eval_map]; rw [hp.2]; rw [ψ.map_zero]⟩

@[simp]

Depends on / 依赖: eval_map, map_map, map_zero, p.map
-/
theorem IsIntegral.map_of_comp_eq {R S T U : Type*} [CommRing R] [Ring S]
    [CommRing T] [Ring U] [Algebra R S] [Algebra T U] (φ : R ->+* T) (ψ : S ->+* U)
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) {a : S} (ha : IsIntegral R a) :
    IsIntegral T (ψ a) :=
  let ⟨p, hp⟩ := ha
  ⟨p.map φ, hp.1.map _, by
    rw [← eval_map]; rw [map_map]; rw [h]; rw [← map_map]; rw [eval_map]; rw [eval₂_at_apply]; rw [eval_map]; rw [hp.2]; rw [ψ.map_zero]⟩

@[simp]
/--
theorem `isIntegral_algEquiv` / 定理 `isIntegral_algEquiv`

English:
theorem isIntegral_algEquiv
  statement: {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  proof: ⟨fun h => by simpa using h.map f.symm, IsIntegral.map f⟩

中文:
定理 isIntegral_algEquiv
  结论: {A B : 类型} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  证明: ⟨fun h => by simpa using h.map f.symm, IsIntegral.map f⟩

Depends on / 依赖: IsIntegral, IsIntegral.map, f.symm, h.map
-/
theorem isIntegral_algEquiv {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x :=
  ⟨fun h => by simpa using h.map f.symm, IsIntegral.map f⟩

/--
theorem `IsIntegral.tower_top` / 定理 `IsIntegral.tower_top`

English:
theorem IsIntegral.tower_top
  statement: [Algebra A B] [IsScalarTower R A B] {x : B}
  proof: let ⟨p, hp, hpx⟩ := hx
⟨p.map algebraMap R A, hp.map _, by rw [← aeval_def, aeval_map_algebraMap, aeval_def, hpx]⟩

中文:
定理 IsIntegral.tower_top
  结论: [Algebra A B] [IsScalarTower R A B] {x : B}
  证明: let ⟨p, hp, hpx⟩ := hx
⟨p.map algebraMap R A, hp.map _, by rw [← aeval_def, aeval_map_algebraMap, aeval_def, hpx]⟩

Depends on / 依赖: aeval_def, aeval_map_algebraMap, algebraMap, hp.map, p.map
-/
theorem IsIntegral.tower_top [Algebra A B] [IsScalarTower R A B] {x : B}
    (hx : IsIntegral R x) : IsIntegral A x :=
  let ⟨p, hp, hpx⟩ := hx
⟨p.map algebraMap R A, hp.map _, by rw [← aeval_def, aeval_map_algebraMap, aeval_def, hpx]⟩

/--
theorem `RingEquiv.isIntegral_iff` / 定理 `RingEquiv.isIntegral_iff`

English:
theorem RingEquiv.isIntegral_iff
  statement: {R S T : Type*} [CommRing R] [Ring S] [CommRing T]
  proof: by
  constructor <;> intro ha
  · let : Algebra R T := φ.toRingHom.toAlgebra
    let : IsScalarTower R T S :=
      ⟨fun r t s => by simp only [Algebra.smul_def, map_mul, ← h, mul_assoc]; rfl⟩
    exact IsIntegral.tower_top ha
  · have h' : (algebraMap T S) = (algebraMap R S).comp φ.symm.toRingHom :

中文:
定理 RingEquiv.isIntegral_iff
  结论: {R S T : 类型} [CommRing R] [Ring S] [CommRing T]
  证明: by
  constructor <;> intro ha
  · let : Algebra R T := φ.toRingHom.toAlgebra
    let : IsScalarTower R T S :=
      ⟨fun r t s => by simp only [Algebra.smul_def, map_mul, ← h, mul_assoc]; rfl⟩
    exact IsIntegral.tower_top ha
  · have h' : (algebraMap T S) = (algebraMap R S).comp φ.symm.toRingHom :

Depends on / 依赖: Algebra, Algebra.smul_def, IsIntegral, IsIntegral.tower_top, IsScalarTower, RingEquiv, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.comp_assoc, RingHomCompTriple, RingHomCompTriple.comp_eq, RingHomInvPair, RingHomInvPair.of_ringEquiv, algebraMap, comp_assoc, comp_eq, map_mul, mul_assoc, of_ringEquiv, smul_def
-/
theorem RingEquiv.isIntegral_iff {R S T : Type*} [CommRing R] [Ring S] [CommRing T]
    [Algebra R S] [Algebra T S] (φ : R ≃+* T)
    (h : (algebraMap T S).comp φ.toRingHom = algebraMap R S) (a : S) :
    IsIntegral R a ↔ IsIntegral T a := by
  constructor <;> intro ha
  · let : Algebra R T := φ.toRingHom.toAlgebra
    let : IsScalarTower R T S :=
      ⟨fun r t s => by simp only [Algebra.smul_def, map_mul, ← h, mul_assoc]; rfl⟩
    exact IsIntegral.tower_top ha
  · have h' : (algebraMap T S) = (algebraMap R S).comp φ.symm.toRingHom := by
      have : RingHomInvPair (φ : R ->+* T) φ.symm := RingHomInvPair.of_ringEquiv _
      simp only [← h, RingHom.comp_assoc, RingEquiv.toRingHom_eq_coe, RingHomCompTriple.comp_eq]
    let : Algebra T R := φ.symm.toRingHom.toAlgebra
    let : IsScalarTower T R S :=
      ⟨fun r t s => by simp only [Algebra.smul_def, map_mul, h', mul_assoc]; rfl⟩
    exact IsIntegral.tower_top ha

/--
theorem `map_isIntegral_int` / 定理 `map_isIntegral_int`

English:
theorem map_isIntegral_int
  statement: {B C F : Type*} [Ring B] [Ring C] {b : B}
  proof: hb.map (f : B ->+* C).toIntAlgHom

中文:
定理 map_isIntegral_int
  结论: {B C F : 类型} [Ring B] [Ring C] {b : B}
  证明: hb.map (f : B ->+* C).toIntAlgHom

Depends on / 依赖: hb.map, toIntAlgHom
-/
theorem map_isIntegral_int {B C F : Type*} [Ring B] [Ring C] {b : B}
    [FunLike F B C] [RingHomClass F B C] (f : F)
    (hb : IsIntegral Int b) : IsIntegral Int (f b) :=
  hb.map (f : B ->+* C).toIntAlgHom

/--
theorem `IsIntegral.of_subring` / 定理 `IsIntegral.of_subring`

English:
theorem IsIntegral.of_subring
  given: {x : B} (T : Subring R) (hx : IsIntegral T x)
  statement: IsIntegral R x
  proof: hx.tower_top

中文:
定理 IsIntegral.of_subring
  条件: {x : B} (T : Subring R) (hx : Is整数egral T x)
  结论: Is整数egral R x
  证明: hx.tower_top

Depends on / 依赖: hx.tower_top, tower_top
-/
theorem IsIntegral.of_subring {x : B} (T : Subring R) (hx : IsIntegral T x) : IsIntegral R x :=
  hx.tower_top

/--
theorem `IsIntegral.algebraMap` / 定理 `IsIntegral.algebraMap`

English:
theorem IsIntegral.algebraMap
  statement: [Algebra A B] [IsScalarTower R A B] {x : A}
  proof: by
  rcases h with ⟨f, hf, hx⟩
  use f, hf
  rw [IsScalarTower.algebraMap_eq R A B]; rw [← hom_eval₂]; rw [hx]; rw [map_zero]

中文:
定理 IsIntegral.algebraMap
  结论: [Algebra A B] [IsScalarTower R A B] {x : A}
  证明: by
  rcases h with ⟨f, hf, hx⟩
  use f, hf
  rw [IsScalarTower.algebraMap_eq R A B]; rw [← hom_eval₂]; rw [hx]; rw [map_zero]
-/
protected theorem IsIntegral.algebraMap [Algebra A B] [IsScalarTower R A B] {x : A}
    (h : IsIntegral R x) : IsIntegral R (algebraMap A B x) := by
  rcases h with ⟨f, hf, hx⟩
  use f, hf
  rw [IsScalarTower.algebraMap_eq R A B]; rw [← hom_eval₂]; rw [hx]; rw [map_zero]

/--
theorem `isIntegral_algebraMap_iff` / 定理 `isIntegral_algebraMap_iff`

English:
theorem isIntegral_algebraMap_iff
  statement: [Algebra A B] [IsScalarTower R A B] {x : A}
  proof: isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) hAB

中文:
定理 isIntegral_algebraMap_iff
  结论: [Algebra A B] [IsScalarTower R A B] {x : A}
  证明: isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) hAB

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, isIntegral_algHom_iff, toAlgHom
-/
theorem isIntegral_algebraMap_iff [Algebra A B] [IsScalarTower R A B] {x : A}
    (hAB : Function.Injective (algebraMap A B)) :
    IsIntegral R (algebraMap A B x) ↔ IsIntegral R x :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) hAB

/--
theorem `isIntegral_iff_isIntegral_closure_finite` / 定理 `isIntegral_iff_isIntegral_closure_finite`

English:
theorem isIntegral_iff_isIntegral_closure_finite
  given: {r : B}
  proof: by
  constructor <;> intro hr
  · rcases hr with ⟨p, hmp, hpr⟩
    refine ⟨_, Finset.finite_toSet _, p.restriction, monic_restriction.2 hmp, ?_⟩
    rw [← aeval_def]; rw [← aeval_map_algebraMap R r p.restriction]; rw [map_restriction]; rw [aeval_def]; rw [hpr]
  rcases hr with ⟨s, _, hsr⟩
  exact hs

中文:
定理 isIntegral_iff_isIntegral_closure_finite
  条件: {r : B}
  证明: by
  constructor <;> intro hr
  · rcases hr with ⟨p, hmp, hpr⟩
    refine ⟨_, Finset.finite_toSet _, p.restriction, monic_restriction.2 hmp, ?_⟩
    rw [← aeval_def]; rw [← aeval_map_algebraMap R r p.restriction]; rw [map_restriction]; rw [aeval_def]; rw [hpr]
  rcases hr with ⟨s, _, hsr⟩
  exact hs

Depends on / 依赖: Finset, Finset.finite_toSet, aeval_def, aeval_map_algebraMap, finite_toSet, hsr.of_subring, map_restriction, monic_restriction, of_subring, p.restriction, restriction
-/
theorem isIntegral_iff_isIntegral_closure_finite {r : B} :
    IsIntegral R r ↔ exists s : Set R, s.Finite ∧ IsIntegral (Subring.closure s) r := by
  constructor <;> intro hr
  · rcases hr with ⟨p, hmp, hpr⟩
    refine ⟨_, Finset.finite_toSet _, p.restriction, monic_restriction.2 hmp, ?_⟩
    rw [← aeval_def]; rw [← aeval_map_algebraMap R r p.restriction]; rw [map_restriction]; rw [aeval_def]; rw [hpr]
  rcases hr with ⟨s, _, hsr⟩
  exact hsr.of_subring _

@[stacks 09GH]
/--
theorem `fg_adjoin_of_finite` / 定理 `fg_adjoin_of_finite`

English:
theorem fg_adjoin_of_finite
  given: {s : Set A} (hfs : s.Finite) (his : forall x in s, IsIntegral R x)
  proof: by
  induction s, hfs using Set.Finite.induction_on with
  | empty =>
    refine ⟨{1}, Submodule.ext fun x => ?_⟩
    rw [Algebra.adjoin_empty]; rw [Finset.coe_singleton]; rw [← one_eq_span]; rw [Algebra.toSubmodule_bot]
  | @insert a s _ _ ih =>
    rw [← Set.union_singleton]; rw [Algebra.adjoin_un

中文:
定理 fg_adjoin_of_finite
  条件: {s : Set A} (hfs : s.Finite) (his : 对任意 x in s, Is整数egral R x)
  证明: by
  induction s, hfs using Set.Finite.induction_on with
  | empty =>
    refine ⟨{1}, Submodule.ext fun x => ?_⟩
    rw [Algebra.adjoin_empty]; rw [Finset.coe_singleton]; rw [← one_eq_span]; rw [Algebra.toSubmodule_bot]
  | @insert a s _ _ ih =>
    rw [← Set.union_singleton]; rw [Algebra.adjoin_un

Depends on / 依赖: Algebra, Algebra.adjoin_empty, Algebra.adjoin_union_coe_submodule, Algebra.toSubmodule_bot, FG.mul, Finite, Finset, Finset.coe_singleton, Set.Finite.induction_on, Set.mem_insert, Set.mem_insert_of_mem, Set.union_singleton, Submodule, Submodule.ext, adjoin_empty, adjoin_union_coe_submodule, coe_singleton, fg_adjoin_singleton, induction_on, insert
-/
theorem fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (his : forall x in s, IsIntegral R x) :
    (Algebra.adjoin R s).toSubmodule.FG := by
  induction s, hfs using Set.Finite.induction_on with
  | empty =>
    refine ⟨{1}, Submodule.ext fun x => ?_⟩
    rw [Algebra.adjoin_empty]; rw [Finset.coe_singleton]; rw [← one_eq_span]; rw [Algebra.toSubmodule_bot]
  | @insert a s _ _ ih =>
    rw [← Set.union_singleton]; rw [Algebra.adjoin_union_coe_submodule]
    exact FG.mul
      (ih fun i hi => his i <| Set.mem_insert_of_mem a hi)
      (his a <| Set.mem_insert a s).fg_adjoin_singleton

/--
theorem `Algebra.finite_adjoin_of_finite_of_isIntegral` / 定理 `Algebra.finite_adjoin_of_finite_of_isIntegral`

English:
theorem Algebra.finite_adjoin_of_finite_of_isIntegral
  statement: {s : Set A} (hf : s.Finite)
  proof: .of_fg fg_adjoin_of_finite hf hi

中文:
定理 Algebra.finite_adjoin_of_finite_of_isIntegral
  结论: {s : Set A} (hf : s.Finite)
  证明: .of_fg fg_adjoin_of_finite hf hi

Depends on / 依赖: fg_adjoin_of_finite, of_fg
-/
theorem Algebra.finite_adjoin_of_finite_of_isIntegral {s : Set A} (hf : s.Finite)
    (hi : forall x in s, IsIntegral R x) : Module.Finite R (adjoin R s) :=
.of_fg fg_adjoin_of_finite hf hi

/--
theorem `Algebra.finite_adjoin_simple_of_isIntegral` / 定理 `Algebra.finite_adjoin_simple_of_isIntegral`

English:
theorem Algebra.finite_adjoin_simple_of_isIntegral
  given: {x : B} (hi : IsIntegral R x)
  proof: .of_fg hi.fg_adjoin_singleton

中文:
定理 Algebra.finite_adjoin_simple_of_isIntegral
  条件: {x : B} (hi : Is整数egral R x)
  证明: .of_fg hi.fg_adjoin_singleton

Depends on / 依赖: fg_adjoin_singleton, hi.fg_adjoin_singleton, of_fg
-/
theorem Algebra.finite_adjoin_simple_of_isIntegral {x : B} (hi : IsIntegral R x) :
    Module.Finite R (adjoin R {x}) :=
  .of_fg hi.fg_adjoin_singleton

/--
theorem `isNoetherian_adjoin_finset` / 定理 `isNoetherian_adjoin_finset`

English:
theorem isNoetherian_adjoin_finset
  statement: [IsNoetherianRing R] (s : Finset A)
  proof: isNoetherian_of_fg_of_noetherian _ (fg_adjoin_of_finite s.finite_toSet hs)

中文:
定理 isNoetherian_adjoin_finset
  结论: [IsNoetherianRing R] (s : Finset A)
  证明: isNoetherian_of_fg_of_noetherian _ (fg_adjoin_of_finite s.finite_toSet hs)

Depends on / 依赖: fg_adjoin_of_finite, finite_toSet, isNoetherian_of_fg_of_noetherian, s.finite_toSet
-/
theorem isNoetherian_adjoin_finset [IsNoetherianRing R] (s : Finset A)
    (hs : forall x in s, IsIntegral R x) : IsNoetherian R (Algebra.adjoin R (s : Set A)) :=
  isNoetherian_of_fg_of_noetherian _ (fg_adjoin_of_finite s.finite_toSet hs)

end

section Prod

variable {R A B : Type*}
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/--
theorem `IsIntegral.pair` / 定理 `IsIntegral.pair`

English:
theorem IsIntegral.pair
  given: {x : A × B} (hx₁ : IsIntegral R x.1) (hx₂ : IsIntegral R x.2)
  proof: by
  obtain ⟨p₁, ⟨hp₁Monic, hp₁Eval⟩⟩ := hx₁
  obtain ⟨p₂, ⟨hp₂Monic, hp₂Eval⟩⟩ := hx₂
  refine ⟨p₁ * p₂, ⟨hp₁Monic.mul hp₂Monic, ?_⟩⟩
  rw [← aeval_def] at *
  rw [aeval_prod_apply]; rw [aeval_mul]; rw [hp₁Eval]; rw [zero_mul]; rw [aeval_mul]; rw [hp₂Eval]; rw [mul_zero]; rw [Prod.zero_eq_mk]

中文:
定理 IsIntegral.pair
  条件: {x : A × B} (hx₁ : Is整数egral R x.1) (hx₂ : Is整数egral R x.2)
  证明: by
  obtain ⟨p₁, ⟨hp₁Monic, hp₁Eval⟩⟩ := hx₁
  obtain ⟨p₂, ⟨hp₂Monic, hp₂Eval⟩⟩ := hx₂
  refine ⟨p₁ * p₂, ⟨hp₁Monic.mul hp₂Monic, ?_⟩⟩
  rw [← aeval_def] at *
  rw [aeval_prod_apply]; rw [aeval_mul]; rw [hp₁Eval]; rw [zero_mul]; rw [aeval_mul]; rw [hp₂Eval]; rw [mul_zero]; rw [Prod.zero_eq_mk]

Depends on / 依赖: Monic.mul, Prod.zero_eq_mk, aeval_def, aeval_mul, aeval_prod_apply, mul_zero, zero_eq_mk, zero_mul
-/
theorem IsIntegral.pair {x : A × B} (hx₁ : IsIntegral R x.1) (hx₂ : IsIntegral R x.2) :
    IsIntegral R x := by
  obtain ⟨p₁, ⟨hp₁Monic, hp₁Eval⟩⟩ := hx₁
  obtain ⟨p₂, ⟨hp₂Monic, hp₂Eval⟩⟩ := hx₂
  refine ⟨p₁ * p₂, ⟨hp₁Monic.mul hp₂Monic, ?_⟩⟩
  rw [← aeval_def] at *
  rw [aeval_prod_apply]; rw [aeval_mul]; rw [hp₁Eval]; rw [zero_mul]; rw [aeval_mul]; rw [hp₂Eval]; rw [mul_zero]; rw [Prod.zero_eq_mk]

/--
theorem `IsIntegral.pair_iff` / 定理 `IsIntegral.pair_iff`

English:
theorem IsIntegral.pair_iff
  given: {x : A × B}
  statement: IsIntegral R x ↔ IsIntegral R x.1 ∧ IsIntegral R x.2
  proof: ⟨fun h => ⟨h.map (AlgHom.fst R A B), h.map (AlgHom.snd R A B)⟩, fun h => h.1.pair h.2⟩

中文:
定理 IsIntegral.pair_iff
  条件: {x : A × B}
  结论: Is整数egral R x ↔ Is整数egral R x.1 ∧ Is整数egral R x.2
  证明: ⟨fun h => ⟨h.map (AlgHom.fst R A B), h.map (AlgHom.snd R A B)⟩, fun h => h.1.pair h.2⟩

Depends on / 依赖: AlgHom, AlgHom.fst, AlgHom.snd, h.map
-/
theorem IsIntegral.pair_iff {x : A × B} : IsIntegral R x ↔ IsIntegral R x.1 ∧ IsIntegral R x.2 :=
  ⟨fun h => ⟨h.map (AlgHom.fst R A B), h.map (AlgHom.snd R A B)⟩, fun h => h.1.pair h.2⟩

end Prod
