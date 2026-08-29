/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yongle Hu
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Integral

/-!
# Ideals over/under ideals in integral extensions

This file proves some going-up results for integral algebras.

## Implementation notes

The proofs of the `comap_ne_bot` and `comap_lt_comap` families use an approach
specific for their situation: we construct an element in `I.comap f` from the
coefficients of a minimal polynomial.
Once mathlib has more material on the localization at a prime ideal, the results
can be proven using more general going-up/going-down theory.
-/

@[expose] public section

open Polynomial Submodule

open scoped Pointwise

namespace Ideal

section

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S] {f : R ->+* S} {I J : Ideal S}

/--
theorem `coeff_zero_mem_comap_of_root_mem_of_eval_mem` / 定理 `coeff_zero_mem_comap_of_root_mem_of_eval_mem`

English:
theorem coeff_zero_mem_comap_of_root_mem_of_eval_mem
  statement: {r : S} (hr : r in I) {p : R[X]}
  proof: by
  rw [← p.divX_mul_X_add]; rw [eval₂_add]; rw [eval₂_C]; rw [eval₂_mul]; rw [eval₂_X] at hp
  refine mem_comap.mpr ((I.add_mem_iff_right ?_).mp hp)
  exact I.mul_mem_left _ hr

中文:
定理 coeff_zero_mem_comap_of_root_mem_of_eval_mem
  结论: {r : S} (hr : r in I) {p : R[X]}
  证明: by
  rw [← p.divX_mul_X_add]; rw [eval₂_add]; rw [eval₂_C]; rw [eval₂_mul]; rw [eval₂_X] at hp
  refine mem_comap.mpr ((I.add_mem_iff_right ?_).mp hp)
  exact I.mul_mem_left _ hr

Depends on / 依赖: I.add_mem_iff_right, I.mul_mem_left, add_mem_iff_right, divX_mul_X_add, mem_comap, mem_comap.mpr, mul_mem_left, p.divX_mul_X_add
-/
theorem coeff_zero_mem_comap_of_root_mem_of_eval_mem {r : S} (hr : r in I) {p : R[X]}
    (hp : p.eval₂ f r in I) : p.coeff 0 in I.comap f := by
  rw [← p.divX_mul_X_add]; rw [eval₂_add]; rw [eval₂_C]; rw [eval₂_mul]; rw [eval₂_X] at hp
  refine mem_comap.mpr ((I.add_mem_iff_right ?_).mp hp)
  exact I.mul_mem_left _ hr

/--
theorem `coeff_zero_mem_comap_of_root_mem` / 定理 `coeff_zero_mem_comap_of_root_mem`

English:
theorem coeff_zero_mem_comap_of_root_mem
  given: {r : S} (hr : r in I) {p : R[X]} (hp : p.eval₂ f r = 0)
  proof: coeff_zero_mem_comap_of_root_mem_of_eval_mem hr (hp.symm ▸ I.zero_mem)

中文:
定理 coeff_zero_mem_comap_of_root_mem
  条件: {r : S} (hr : r in I) {p : R[X]} (hp : p.eval₂ f r = 0)
  证明: coeff_zero_mem_comap_of_root_mem_of_eval_mem hr (hp.symm ▸ I.zero_mem)

Depends on / 依赖: I.zero_mem, coeff_zero_mem_comap_of_root_mem_of_eval_mem, hp.symm, zero_mem
-/
theorem coeff_zero_mem_comap_of_root_mem {r : S} (hr : r in I) {p : R[X]} (hp : p.eval₂ f r = 0) :
    p.coeff 0 in I.comap f :=
  coeff_zero_mem_comap_of_root_mem_of_eval_mem hr (hp.symm ▸ I.zero_mem)

/--
theorem `exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem` / 定理 `exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem`

English:
theorem exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
  statement: {r : S}
  proof: by
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a coeff_eq_zero a_ne_zero _ _ hp
    refine ⟨0, ?_, coeff_zero_mem_comap_of_root_mem hr hp⟩
    simp [coeff_eq_zero, a_ne_zero]
  · intro p p_nonzero ih _ hp
    rw [eval₂_mul]; rw [eval₂_X] at hp
    obtain ⟨i, hi, mem⟩ := ih p_nonzero (r_non_zero_divisor hp)
    refine ⟨i + 1, ?_, ?_⟩
    · simp [hi]
    · simpa [hi] using mem

中文:
定理 存在_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
  结论: {r : S}
  证明: by
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a coeff_eq_zero a_ne_zero _ _ hp
    refine ⟨0, ?_, coeff_zero_mem_comap_of_root_mem hr hp⟩
    simp [coeff_eq_zero, a_ne_zero]
  · intro p p_nonzero ih _ hp
    rw [eval₂_mul]; rw [eval₂_X] at hp
    obtain ⟨i, hi, mem⟩ := ih p_nonzero (r_non_zero_divisor hp)
    refine ⟨i + 1, ?_, ?_⟩
    · simp [hi]
    · simpa [hi] using mem

Depends on / 依赖: a_ne_zero, coeff_eq_zero, coeff_zero_mem_comap_of_root_mem, p.recOnHorner, p_nonzero, r_non_zero_divisor, recOnHorner
-/
theorem exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem {r : S}
    (r_non_zero_divisor : forall {x}, x * r = 0 -> x = 0) (hr : r in I) {p : R[X]} :
    p != 0 -> p.eval₂ f r = 0 -> exists i, p.coeff i != 0 ∧ p.coeff i in I.comap f := by
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a coeff_eq_zero a_ne_zero _ _ hp
    refine ⟨0, ?_, coeff_zero_mem_comap_of_root_mem hr hp⟩
    simp [coeff_eq_zero, a_ne_zero]
  · intro p p_nonzero ih _ hp
    rw [eval₂_mul]; rw [eval₂_X] at hp
    obtain ⟨i, hi, mem⟩ := ih p_nonzero (r_non_zero_divisor hp)
    refine ⟨i + 1, ?_, ?_⟩
    · simp [hi]
    · simpa [hi] using mem

/--
theorem `injective_quotient_le_comap_map` / 定理 `injective_quotient_le_comap_map`

English:
theorem injective_quotient_le_comap_map
  given: (P : Ideal R[X])
  proof: by
  refine quotientMap_injective' (le_of_eq ?_)
  rw [comap_map_of_surjective (mapRingHom (Ideal.Quotient.mk (P.comap (C : R ->+* R[X]))))
      (map_surjective (Ideal.Quotient.mk (P.comap (C : R ->+* R[X]))) Ideal.Quotient.mk_surjective)]
  refine le_antisymm (sup_le le_rfl ?_) (le_sup_of_le_left le_rfl)
  refine fun p hp =>
    polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => Ideal.Quotient.eq_zero_iff_mem.mp ?_
  simpa only [coeff_map, coe_mapRingHom] using! ext_iff.mp (Ideal.mem_bot.mp (mem_comap.mp hp)) n

中文:
定理 injective_quotient_le_comap_map
  条件: (P : 理想 R[X])
  证明: by
  refine quotientMap_injective' (le_of_eq ?_)
  rw [comap_map_of_surjective (mapRingHom (Ideal.Quotient.mk (P.comap (C : R ->+* R[X]))))
      (map_surjective (Ideal.Quotient.mk (P.comap (C : R ->+* R[X]))) Ideal.Quotient.mk_surjective)]
  refine le_antisymm (sup_le le_rfl ?_) (le_sup_of_le_left le_rfl)
  refine fun p hp =>
    polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => Ideal.Quotient.eq_zero_iff_mem.mp ?_
  simpa only [coeff_map, coe_mapRingHom] using! ext_iff.mp (Ideal.mem_bot.mp (mem_comap.mp hp)) n

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem.mp, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.mem_bot.mp, P.comap, Quotient, coe_mapRingHom, coeff_map, comap_map_of_surjective, eq_zero_iff_mem, ext_iff, ext_iff.mp, le_antisymm, le_of_eq, le_rfl, le_sup_of_le_left, mapRingHom, map_surjective, mem_bot, mem_comap
-/
theorem injective_quotient_le_comap_map (P : Ideal R[X]) :
Function.Injective
      Ideal.quotientMap
        (Ideal.map (Polynomial.mapRingHom (Quotient.mk (P.comap (C : R ->+* R[X])))) P)
        (Polynomial.mapRingHom (Ideal.Quotient.mk (P.comap (C : R ->+* R[X]))))
        le_comap_map := by
  refine quotientMap_injective' (le_of_eq ?_)
  rw [comap_map_of_surjective (mapRingHom (Ideal.Quotient.mk (P.comap (C : R ->+* R[X]))))
      (map_surjective (Ideal.Quotient.mk (P.comap (C : R ->+* R[X]))) Ideal.Quotient.mk_surjective)]
  refine le_antisymm (sup_le le_rfl ?_) (le_sup_of_le_left le_rfl)
  refine fun p hp =>
    polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => Ideal.Quotient.eq_zero_iff_mem.mp ?_
  simpa only [coeff_map, coe_mapRingHom] using! ext_iff.mp (Ideal.mem_bot.mp (mem_comap.mp hp)) n

/--
theorem `quotient_mk_maps_eq` / 定理 `quotient_mk_maps_eq`

English:
theorem quotient_mk_maps_eq
  given: (P : Ideal R[X])
  proof: by
  ext
  simp

中文:
定理 quotient_mk_maps_eq
  条件: (P : 理想 R[X])
  证明: by
  ext
  simp
-/
theorem quotient_mk_maps_eq (P : Ideal R[X]) :
    ((Quotient.mk (map (mapRingHom (Quotient.mk (P.comap (C : R ->+* R[X])))) P)).comp C).comp
        (Quotient.mk (P.comap (C : R ->+* R[X]))) =
      (Ideal.quotientMap (map (mapRingHom (Quotient.mk (P.comap (C : R ->+* R[X])))) P)
            (mapRingHom (Quotient.mk (P.comap (C : R ->+* R[X])))) le_comap_map).comp
        ((Quotient.mk P).comp C) := by
  ext
  simp

/--
theorem `exists_nonzero_mem_of_ne_bot` / 定理 `exists_nonzero_mem_of_ne_bot`

English:
theorem exists_nonzero_mem_of_ne_bot
  given: {P : Ideal R[X]} (Pb : P != ⊥) (hP : forall x : R, C x in P -> x = 0)
  proof: by
  obtain ⟨m, hm⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr Pb)
  refine ⟨m, Submodule.coe_mem m, fun pp0 => hm (Submodule.coe_eq_zero.mp ?_)⟩
  refine
    (injective_iff_map_eq_zero (Polynomial.mapRingHom (Ideal.Quotient.mk
      (P.comap (C : R ->+* R[X]))))).mp
      ?_ _ pp0
  refine map_injective _ ((RingHom.injective_iff_ker_eq_bot (Ideal.Quotient.mk (P.comap C))).mpr ?_)
  rw [mk_ker]
  exact (Submodule.eq_bot_iff _).mpr fun x hx => hP x (mem_comap.mp hx)

中文:
定理 存在_nonzero_mem_of_ne_bot
  条件: {P : 理想 R[X]} (Pb : P != ⊥) (hP : 对任意 x : R, C x in P -> x = 0)
  证明: by
  obtain ⟨m, hm⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr Pb)
  refine ⟨m, Submodule.coe_mem m, fun pp0 => hm (Submodule.coe_eq_zero.mp ?_)⟩
  refine
    (injective_iff_map_eq_zero (Polynomial.mapRingHom (Ideal.Quotient.mk
      (P.comap (C : R ->+* R[X]))))).mp
      ?_ _ pp0
  refine map_injective _ ((RingHom.injective_iff_ker_eq_bot (Ideal.Quotient.mk (P.comap C))).mpr ?_)
  rw [mk_ker]
  exact (Submodule.eq_bot_iff _).mpr fun x hx => hP x (mem_comap.mp hx)

Depends on / 依赖: Ideal.Quotient.mk, P.comap, Polynomial, Polynomial.mapRingHom, Quotient, RingHom, RingHom.injective_iff_ker_eq_bot, Submodule, Submodule.coe_eq_zero.mp, Submodule.coe_mem, Submodule.eq_bot_iff, Submodule.nonzero_mem_of_bot_lt, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, coe_eq_zero, coe_mem, eq_bot_iff, injective_iff_ker_eq_bot, injective_iff_map_eq_zero, mapRingHom
-/
theorem exists_nonzero_mem_of_ne_bot {P : Ideal R[X]} (Pb : P != ⊥) (hP : forall x : R, C x in P -> x = 0) :
    exists p : R[X], p in P ∧ Polynomial.map (Quotient.mk (P.comap (C : R ->+* R[X]))) p != 0 := by
  obtain ⟨m, hm⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr Pb)
  refine ⟨m, Submodule.coe_mem m, fun pp0 => hm (Submodule.coe_eq_zero.mp ?_)⟩
  refine
    (injective_iff_map_eq_zero (Polynomial.mapRingHom (Ideal.Quotient.mk
      (P.comap (C : R ->+* R[X]))))).mp
      ?_ _ pp0
  refine map_injective _ ((RingHom.injective_iff_ker_eq_bot (Ideal.Quotient.mk (P.comap C))).mpr ?_)
  rw [mk_ker]
  exact (Submodule.eq_bot_iff _).mpr fun x hx => hP x (mem_comap.mp hx)

end

section IsDomain

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S] {f : R ->+* S} {I J : Ideal S}

/--
theorem `exists_coeff_ne_zero_mem_comap_of_root_mem` / 定理 `exists_coeff_ne_zero_mem_comap_of_root_mem`

English:
theorem exists_coeff_ne_zero_mem_comap_of_root_mem
  statement: [IsDomain S] {r : S} (r_ne_zero : r != 0)
  proof: exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
    (fun {_} h => Or.resolve_right (mul_eq_zero.mp h) r_ne_zero) hr

中文:
定理 存在_coeff_ne_zero_mem_comap_of_root_mem
  结论: [是整环 S] {r : S} (r_ne_zero : r != 0)
  证明: exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
    (fun {_} h => Or.resolve_right (mul_eq_zero.mp h) r_ne_zero) hr

Depends on / 依赖: Or.resolve_right, exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem, mul_eq_zero, mul_eq_zero.mp, r_ne_zero, resolve_right
-/
theorem exists_coeff_ne_zero_mem_comap_of_root_mem [IsDomain S] {r : S} (r_ne_zero : r != 0)
    (hr : r in I) {p : R[X]} :
    p != 0 -> p.eval₂ f r = 0 -> exists i, p.coeff i != 0 ∧ p.coeff i in I.comap f :=
  exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
    (fun {_} h => Or.resolve_right (mul_eq_zero.mp h) r_ne_zero) hr

/--
theorem `exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff` / 定理 `exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff`

English:
theorem exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff
  statement: [IsPrime I] (hIJ : I <= J) {r : S}
  proof: by
  obtain ⟨hrJ, hrI⟩ := hr
  have rbar_ne_zero : Ideal.Quotient.mk I r != 0 := mt (Quotient.mk_eq_zero I).mp hrI
  have rbar_mem_J : Ideal.Quotient.mk I r in J.map (Ideal.Quotient.mk I) := mem_map_of_mem _ hrJ
  have quotient_f : forall x in I.comap f, (Ideal.Quotient.mk I).comp f x = 0 := by
    simp [Quotient.eq_zero_iff_mem]
  have rbar_root :
    (p.map (Ideal.Quotient.mk (I.comap f))).eval₂ (Quotient.lift (I.comap f) _ quotient_f)
        (Ideal.Quotient.mk I r) =
      0 := by
    convert! Quotient.eq_zero_iff_mem.mpr hpI
    exact _root_.trans (eval₂_map _ _ _) (hom_eval₂ p f (Ideal.Quotient.mk I) r).symm
  obtain ⟨i, ne_zero, mem⟩ :=
    exists_coeff_ne_zero_mem_comap_of_root_mem rbar_ne_zero rbar_mem_J p_ne_zero rbar_root
  rw [coeff_map] at ne_zero mem
  refine ⟨i, (mem_quotient_iff_mem hIJ).mp ?_, mt ?_ ne_zero⟩
  · simpa using mem
  simp [Quotient.eq_zero_iff_mem]

中文:
定理 存在_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff
  结论: [是素 I] (hIJ : I <= J) {r : S}
  证明: by
  obtain ⟨hrJ, hrI⟩ := hr
  have rbar_ne_zero : Ideal.Quotient.mk I r != 0 := mt (Quotient.mk_eq_zero I).mp hrI
  have rbar_mem_J : Ideal.Quotient.mk I r in J.map (Ideal.Quotient.mk I) := mem_map_of_mem _ hrJ
  have quotient_f : forall x in I.comap f, (Ideal.Quotient.mk I).comp f x = 0 := by
    simp [Quotient.eq_zero_iff_mem]
  have rbar_root :
    (p.map (Ideal.Quotient.mk (I.comap f))).eval₂ (Quotient.lift (I.comap f) _ quotient_f)
        (Ideal.Quotient.mk I r) =
      0 := by
    convert! Quotient.eq_zero_iff_mem.mpr hpI
    exact _root_.trans (eval₂_map _ _ _) (hom_eval₂ p f (Ideal.Quotient.mk I) r).symm
  obtain ⟨i, ne_zero, mem⟩ :=
    exists_coeff_ne_zero_mem_comap_of_root_mem rbar_ne_zero rbar_mem_J p_ne_zero rbar_root
  rw [coeff_map] at ne_zero mem
  refine ⟨i, (mem_quotient_iff_mem hIJ).mp ?_, mt ?_ ne_zero⟩
  · simpa using mem
  simp [Quotient.eq_zero_iff_mem]

Depends on / 依赖: I.comap, Ideal.Quotient.mk, J.map, Quotient, Quotient.eq_zero_iff_mem, Quotient.eq_zero_iff_mem.mpr, Quotient.lift, Quotient.mk_eq_zero, convert, eq_zero_iff_mem, mem_map_of_mem, mk_eq_zero, p.map, quotient_f, rbar_mem_J, rbar_ne_zero, rbar_root
-/
theorem exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff [IsPrime I] (hIJ : I <= J) {r : S}
    (hr : r in (J : Set S) \ I) {p : R[X]} (p_ne_zero : p.map (Quotient.mk (I.comap f)) != 0)
    (hpI : p.eval₂ f r in I) : exists i, p.coeff i in (J.comap f : Set R) \ I.comap f := by
  obtain ⟨hrJ, hrI⟩ := hr
  have rbar_ne_zero : Ideal.Quotient.mk I r != 0 := mt (Quotient.mk_eq_zero I).mp hrI
  have rbar_mem_J : Ideal.Quotient.mk I r in J.map (Ideal.Quotient.mk I) := mem_map_of_mem _ hrJ
  have quotient_f : forall x in I.comap f, (Ideal.Quotient.mk I).comp f x = 0 := by
    simp [Quotient.eq_zero_iff_mem]
  have rbar_root :
    (p.map (Ideal.Quotient.mk (I.comap f))).eval₂ (Quotient.lift (I.comap f) _ quotient_f)
        (Ideal.Quotient.mk I r) =
      0 := by
    convert! Quotient.eq_zero_iff_mem.mpr hpI
    exact _root_.trans (eval₂_map _ _ _) (hom_eval₂ p f (Ideal.Quotient.mk I) r).symm
  obtain ⟨i, ne_zero, mem⟩ :=
    exists_coeff_ne_zero_mem_comap_of_root_mem rbar_ne_zero rbar_mem_J p_ne_zero rbar_root
  rw [coeff_map] at ne_zero mem
  refine ⟨i, (mem_quotient_iff_mem hIJ).mp ?_, mt ?_ ne_zero⟩
  · simpa using mem
  simp [Quotient.eq_zero_iff_mem]

/--
theorem `comap_lt_comap_of_root_mem_sdiff` / 定理 `comap_lt_comap_of_root_mem_sdiff`

English:
theorem comap_lt_comap_of_root_mem_sdiff
  statement: [I.IsPrime] (hIJ : I <= J) {r : S}
  proof: let ⟨i, hJ, hI⟩ := exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff hIJ hr p_ne_zero hp
  SetLike.lt_iff_le_and_exists.mpr ⟨comap_mono hIJ, p.coeff i, hJ, hI⟩

中文:
定理 comap_lt_comap_of_root_mem_sdiff
  结论: [I.是素] (hIJ : I <= J) {r : S}
  证明: let ⟨i, hJ, hI⟩ := exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff hIJ hr p_ne_zero hp
  SetLike.lt_iff_le_and_exists.mpr ⟨comap_mono hIJ, p.coeff i, hJ, hI⟩

Depends on / 依赖: SetLike, SetLike.lt_iff_le_and_exists.mpr, comap_mono, exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff, lt_iff_le_and_exists, p.coeff, p_ne_zero
-/
theorem comap_lt_comap_of_root_mem_sdiff [I.IsPrime] (hIJ : I <= J) {r : S}
    (hr : r in (J : Set S) \ I) {p : R[X]} (p_ne_zero : p.map (Quotient.mk (I.comap f)) != 0)
    (hp : p.eval₂ f r in I) : I.comap f < J.comap f :=
  let ⟨i, hJ, hI⟩ := exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff hIJ hr p_ne_zero hp
  SetLike.lt_iff_le_and_exists.mpr ⟨comap_mono hIJ, p.coeff i, hJ, hI⟩

/--
theorem `mem_of_one_mem` / 定理 `mem_of_one_mem`

English:
theorem mem_of_one_mem
  given: (h : (1 : S) in I) (x)
  statement: x in I
  proof: (I.eq_top_iff_one.mpr h).symm ▸ mem_top

中文:
定理 mem_of_one_mem
  条件: (h : (1 : S) in I) (x)
  结论: x in I
  证明: (I.eq_top_iff_one.mpr h).symm ▸ mem_top

Depends on / 依赖: I.eq_top_iff_one.mpr, eq_top_iff_one, mem_top
-/
theorem mem_of_one_mem (h : (1 : S) in I) (x) : x in I :=
  (I.eq_top_iff_one.mpr h).symm ▸ mem_top

/--
theorem `comap_lt_comap_of_integral_mem_sdiff` / 定理 `comap_lt_comap_of_integral_mem_sdiff`

English:
theorem comap_lt_comap_of_integral_mem_sdiff
  statement: [Algebra R S] [hI : I.IsPrime] (hIJ : I <= J) {x : S}
  proof: by
  obtain ⟨p, p_monic, hpx⟩ := integral
  refine comap_lt_comap_of_root_mem_sdiff hIJ mem (map_monic_ne_zero p_monic) ?_
  convert! I.zero_mem

中文:
定理 comap_lt_comap_of_integral_mem_sdiff
  结论: [代数 R S] [hI : I.是素] (hIJ : I <= J) {x : S}
  证明: by
  obtain ⟨p, p_monic, hpx⟩ := integral
  refine comap_lt_comap_of_root_mem_sdiff hIJ mem (map_monic_ne_zero p_monic) ?_
  convert! I.zero_mem

Depends on / 依赖: I.zero_mem, comap_lt_comap_of_root_mem_sdiff, convert, integral, map_monic_ne_zero, p_monic, zero_mem
-/
theorem comap_lt_comap_of_integral_mem_sdiff [Algebra R S] [hI : I.IsPrime] (hIJ : I <= J) {x : S}
    (mem : x in (J : Set S) \ I) (integral : IsIntegral R x) :
    I.comap (algebraMap R S) < J.comap (algebraMap R S) := by
  obtain ⟨p, p_monic, hpx⟩ := integral
  refine comap_lt_comap_of_root_mem_sdiff hIJ mem (map_monic_ne_zero p_monic) ?_
  convert! I.zero_mem

/--
theorem `comap_ne_bot_of_root_mem` / 定理 `comap_ne_bot_of_root_mem`

English:
theorem comap_ne_bot_of_root_mem
  statement: [IsDomain S] {r : S} (r_ne_zero : r != 0) (hr : r in I) {p : R[X]}
  proof: fun h =>
  let ⟨_, hi, mem⟩ := exists_coeff_ne_zero_mem_comap_of_root_mem r_ne_zero hr p_ne_zero hp
  absurd (mem_bot.mp (eq_bot_iff.mp h mem)) hi

中文:
定理 comap_ne_bot_of_root_mem
  结论: [是整环 S] {r : S} (r_ne_zero : r != 0) (hr : r in I) {p : R[X]}
  证明: fun h =>
  let ⟨_, hi, mem⟩ := exists_coeff_ne_zero_mem_comap_of_root_mem r_ne_zero hr p_ne_zero hp
  absurd (mem_bot.mp (eq_bot_iff.mp h mem)) hi
-/
theorem comap_ne_bot_of_root_mem [IsDomain S] {r : S} (r_ne_zero : r != 0) (hr : r in I) {p : R[X]}
    (p_ne_zero : p != 0) (hp : p.eval₂ f r = 0) : I.comap f != ⊥ := fun h =>
  let ⟨_, hi, mem⟩ := exists_coeff_ne_zero_mem_comap_of_root_mem r_ne_zero hr p_ne_zero hp
  absurd (mem_bot.mp (eq_bot_iff.mp h mem)) hi

/--
theorem `isMaximal_of_isIntegral_of_isMaximal_comap` / 定理 `isMaximal_of_isIntegral_of_isMaximal_comap`

English:
theorem isMaximal_of_isIntegral_of_isMaximal_comap
  statement: [Algebra R S] [Algebra.IsIntegral R S]
  proof: ⟨⟨mt comap_eq_top_iff.mpr hI.1.1, fun _ I_lt_J =>
      let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
comap_eq_top_iff.1
        hI.1.2 _ (comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩
          (Algebra.IsIntegral.isIntegral x))⟩⟩

中文:
定理 isMaximal_of_is整数egral_of_isMaximal_comap
  结论: [代数 R S] [代数.是整 R S]
  证明: ⟨⟨mt comap_eq_top_iff.mpr hI.1.1, fun _ I_lt_J =>
      let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
comap_eq_top_iff.1
        hI.1.2 _ (comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩
          (Algebra.IsIntegral.isIntegral x))⟩⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, I_le_J, I_lt_J, IsIntegral, SetLike, SetLike.lt_iff_le_and_exists.mp, comap_eq_top_iff, comap_eq_top_iff.mpr, comap_lt_comap_of_integral_mem_sdiff, isIntegral, lt_iff_le_and_exists
-/
theorem isMaximal_of_isIntegral_of_isMaximal_comap [Algebra R S] [Algebra.IsIntegral R S]
    (I : Ideal S) [I.IsPrime] (hI : IsMaximal (I.comap (algebraMap R S))) : IsMaximal I :=
  ⟨⟨mt comap_eq_top_iff.mpr hI.1.1, fun _ I_lt_J =>
      let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
comap_eq_top_iff.1
        hI.1.2 _ (comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩
          (Algebra.IsIntegral.isIntegral x))⟩⟩

/--
theorem `isMaximal_of_isIntegral_of_isMaximal_comap'` / 定理 `isMaximal_of_isIntegral_of_isMaximal_comap'`

English:
theorem isMaximal_of_isIntegral_of_isMaximal_comap'
  statement: (f : R ->+* S) (hf : f.IsIntegral) (I : Ideal S)
  proof: let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_of_isIntegral_of_isMaximal_comap (R := R) (S := S) I hI

中文:
定理 isMaximal_of_is整数egral_of_isMaximal_comap'
  结论: (f : R ->+* S) (hf : f.是整) (I : 理想 S)
  证明: let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_of_isIntegral_of_isMaximal_comap (R := R) (S := S) I hI

Depends on / 依赖: Algebra, Algebra.IsIntegral, IsIntegral, f.toAlgebra, isMaximal_of_isIntegral_of_isMaximal_comap, toAlgebra
-/
theorem isMaximal_of_isIntegral_of_isMaximal_comap' (f : R ->+* S) (hf : f.IsIntegral) (I : Ideal S)
    [I.IsPrime] (hI : IsMaximal (I.comap f)) : IsMaximal I :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_of_isIntegral_of_isMaximal_comap (R := R) (S := S) I hI

variable [Algebra R S]

/--
theorem `comap_ne_bot_of_algebraic_mem` / 定理 `comap_ne_bot_of_algebraic_mem`

English:
theorem comap_ne_bot_of_algebraic_mem
  statement: [IsDomain S] {x : S} (x_ne_zero : x != 0) (x_mem : x in I)
  proof: let ⟨_, p_ne_zero, hp⟩ := hx
  comap_ne_bot_of_root_mem x_ne_zero x_mem p_ne_zero hp

中文:
定理 comap_ne_bot_of_algebraic_mem
  结论: [是整环 S] {x : S} (x_ne_zero : x != 0) (x_mem : x in I)
  证明: let ⟨_, p_ne_zero, hp⟩ := hx
  comap_ne_bot_of_root_mem x_ne_zero x_mem p_ne_zero hp

Depends on / 依赖: comap_ne_bot_of_root_mem, p_ne_zero, x_mem, x_ne_zero
-/
theorem comap_ne_bot_of_algebraic_mem [IsDomain S] {x : S} (x_ne_zero : x != 0) (x_mem : x in I)
    (hx : IsAlgebraic R x) : I.comap (algebraMap R S) != ⊥ :=
  let ⟨_, p_ne_zero, hp⟩ := hx
  comap_ne_bot_of_root_mem x_ne_zero x_mem p_ne_zero hp

/--
theorem `comap_ne_bot_of_integral_mem` / 定理 `comap_ne_bot_of_integral_mem`

English:
theorem comap_ne_bot_of_integral_mem
  statement: [Nontrivial R] [IsDomain S] {x : S} (x_ne_zero : x != 0)
  proof: comap_ne_bot_of_algebraic_mem x_ne_zero x_mem hx.isAlgebraic

中文:
定理 comap_ne_bot_of_integral_mem
  结论: [非平凡 R] [是整环 S] {x : S} (x_ne_zero : x != 0)
  证明: comap_ne_bot_of_algebraic_mem x_ne_zero x_mem hx.isAlgebraic

Depends on / 依赖: comap_ne_bot_of_algebraic_mem, hx.isAlgebraic, isAlgebraic, x_mem, x_ne_zero
-/
theorem comap_ne_bot_of_integral_mem [Nontrivial R] [IsDomain S] {x : S} (x_ne_zero : x != 0)
    (x_mem : x in I) (hx : IsIntegral R x) : I.comap (algebraMap R S) != ⊥ :=
  comap_ne_bot_of_algebraic_mem x_ne_zero x_mem hx.isAlgebraic

/--
theorem `eq_bot_of_comap_eq_bot` / 定理 `eq_bot_of_comap_eq_bot`

English:
theorem eq_bot_of_comap_eq_bot
  statement: [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
  proof: by
  refine eq_bot_iff.2 fun x hx => ?_
  by_cases hx0 : x = 0
  · exact hx0.symm ▸ Ideal.zero_mem ⊥
  · exact absurd hI (comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x))

中文:
定理 eq_bot_of_comap_eq_bot
  结论: [非平凡 R] [是整环 S] [代数.是整 R S]
  证明: by
  refine eq_bot_iff.2 fun x hx => ?_
  by_cases hx0 : x = 0
  · exact hx0.symm ▸ Ideal.zero_mem ⊥
  · exact absurd hI (comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x))

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, Ideal.zero_mem, IsIntegral, absurd, comap_ne_bot_of_integral_mem, eq_bot_iff, hx0.symm, isIntegral, zero_mem
-/
theorem eq_bot_of_comap_eq_bot [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
    (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  by_cases hx0 : x = 0
  · exact hx0.symm ▸ Ideal.zero_mem ⊥
  · exact absurd hI (comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x))

/--
theorem `isMaximal_comap_of_isIntegral_of_isMaximal` / 定理 `isMaximal_comap_of_isIntegral_of_isMaximal`

English:
theorem isMaximal_comap_of_isIntegral_of_isMaximal
  statement: [Algebra.IsIntegral R S] (I : Ideal S)
  proof: by
  refine Ideal.Quotient.maximal_of_isField _ ?_
  have : IsPrime (I.comap (algebraMap R S)) := comap_isPrime _ _
  exact isField_of_isIntegral_of_isField
    algebraMap_quotient_injective (by rwa [← Quotient.maximal_ideal_iff_isField_quotient])

中文:
定理 isMaximal_comap_of_is整数egral_of_isMaximal
  结论: [代数.是整 R S] (I : 理想 S)
  证明: by
  refine Ideal.Quotient.maximal_of_isField _ ?_
  have : IsPrime (I.comap (algebraMap R S)) := comap_isPrime _ _
  exact isField_of_isIntegral_of_isField
    algebraMap_quotient_injective (by rwa [← Quotient.maximal_ideal_iff_isField_quotient])

Depends on / 依赖: I.comap, Ideal.Quotient.maximal_of_isField, IsPrime, Quotient, Quotient.maximal_ideal_iff_isField_quotient, algebraMap, algebraMap_quotient_injective, comap_isPrime, isField_of_isIntegral_of_isField, maximal_ideal_iff_isField_quotient, maximal_of_isField
-/
theorem isMaximal_comap_of_isIntegral_of_isMaximal [Algebra.IsIntegral R S] (I : Ideal S)
    [hI : I.IsMaximal] : IsMaximal (I.comap (algebraMap R S)) := by
  refine Ideal.Quotient.maximal_of_isField _ ?_
  have : IsPrime (I.comap (algebraMap R S)) := comap_isPrime _ _
  exact isField_of_isIntegral_of_isField
    algebraMap_quotient_injective (by rwa [← Quotient.maximal_ideal_iff_isField_quotient])

/--
theorem `isMaximal_comap_of_isIntegral_of_isMaximal'` / 定理 `isMaximal_comap_of_isIntegral_of_isMaximal'`

English:
theorem isMaximal_comap_of_isIntegral_of_isMaximal'
  statement: {R S : Type*} [CommRing R] [CommRing S]
  proof: let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := S) I

中文:
定理 isMaximal_comap_of_is整数egral_of_isMaximal'
  结论: {R S : 类型} [交换环 R] [交换环 S]
  证明: let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := S) I

Depends on / 依赖: Algebra, Algebra.IsIntegral, IsIntegral, f.toAlgebra, isMaximal_comap_of_isIntegral_of_isMaximal, toAlgebra
-/
theorem isMaximal_comap_of_isIntegral_of_isMaximal' {R S : Type*} [CommRing R] [CommRing S]
    (f : R ->+* S) (hf : f.IsIntegral) (I : Ideal S) [I.IsMaximal] : IsMaximal (I.comap f) :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := S) I

section IsIntegral

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]

/--
theorem `IsIntegral.comap_lt_comap` / 定理 `IsIntegral.comap_lt_comap`

English:
theorem IsIntegral.comap_lt_comap
  given: {I J : Ideal A} [I.IsPrime] (I_lt_J : I < J)
  proof: let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
  comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (Algebra.IsIntegral.isIntegral x)

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.comap_le_comap :=
  IsIntegral.comap_lt_comap

中文:
定理 是整.comap_lt_comap
  条件: {I J : 理想 A} [I.是素] (I_lt_J : I < J)
  证明: let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
  comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (Algebra.IsIntegral.isIntegral x)

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.comap_le_comap :=
  IsIntegral.comap_lt_comap

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, I_le_J, I_lt_J, IsIntegral, SetLike, SetLike.lt_iff_le_and_exists.mp, comap_lt_comap_of_integral_mem_sdiff, isIntegral, lt_iff_le_and_exists
-/
theorem IsIntegral.comap_lt_comap {I J : Ideal A} [I.IsPrime] (I_lt_J : I < J) :
    I.comap (algebraMap R A) < J.comap (algebraMap R A) :=
  let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
  comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (Algebra.IsIntegral.isIntegral x)

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.comap_le_comap :=
  IsIntegral.comap_lt_comap

/--
theorem `IsIntegral.isMaximal_of_isMaximal_comap` / 定理 `IsIntegral.isMaximal_of_isMaximal_comap`

English:
theorem IsIntegral.isMaximal_of_isMaximal_comap
  statement: (I : Ideal A) [I.IsPrime]
  proof: isMaximal_of_isIntegral_of_isMaximal_comap I hI

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.isMaximal_of_isMaximal_comap :=
  IsIntegral.isMaximal_of_isMaximal_comap

中文:
定理 是整.isMaximal_of_isMaximal_comap
  结论: (I : 理想 A) [I.是素]
  证明: isMaximal_of_isIntegral_of_isMaximal_comap I hI

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.isMaximal_of_isMaximal_comap :=
  IsIntegral.isMaximal_of_isMaximal_comap

Depends on / 依赖: isMaximal_of_isIntegral_of_isMaximal_comap
-/
theorem IsIntegral.isMaximal_of_isMaximal_comap (I : Ideal A) [I.IsPrime]
    (hI : IsMaximal (I.comap (algebraMap R A))) : IsMaximal I :=
  isMaximal_of_isIntegral_of_isMaximal_comap I hI

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.isMaximal_of_isMaximal_comap :=
  IsIntegral.isMaximal_of_isMaximal_comap

/--
theorem `IsIntegral.mem_minimalPrimes_map_under` / 定理 `IsIntegral.mem_minimalPrimes_map_under`

English:
theorem IsIntegral.mem_minimalPrimes_map_under
  given: (I : Ideal A) [I.IsPrime]
  proof: by
  refine ⟨⟨inferInstance, map_comap_le⟩, fun r ⟨hr, hpr⟩ hrq => ?_⟩
  contrapose! hpr
  exact mt map_le_iff_le_comap.mp (not_le_of_gt (IsIntegral.comap_lt_comap (hrq.lt_of_not_ge hpr)))

中文:
定理 是整.mem_minimalPrimes_map_under
  条件: (I : 理想 A) [I.是素]
  证明: by
  refine ⟨⟨inferInstance, map_comap_le⟩, fun r ⟨hr, hpr⟩ hrq => ?_⟩
  contrapose! hpr
  exact mt map_le_iff_le_comap.mp (not_le_of_gt (IsIntegral.comap_lt_comap (hrq.lt_of_not_ge hpr)))

Depends on / 依赖: IsIntegral, IsIntegral.comap_lt_comap, comap_lt_comap, contrapose, hrq.lt_of_not_ge, lt_of_not_ge, map_comap_le, map_le_iff_le_comap, map_le_iff_le_comap.mp, not_le_of_gt
-/
theorem IsIntegral.mem_minimalPrimes_map_under (I : Ideal A) [I.IsPrime] :
    I in ((I.under R).map (algebraMap R A)).minimalPrimes := by
  refine ⟨⟨inferInstance, map_comap_le⟩, fun r ⟨hr, hpr⟩ hrq => ?_⟩
  contrapose! hpr
  exact mt map_le_iff_le_comap.mp (not_le_of_gt (IsIntegral.comap_lt_comap (hrq.lt_of_not_ge hpr)))

variable [IsDomain A]

variable (R) in
/--
theorem `IsIntegral.comap_ne_bot` / 定理 `IsIntegral.comap_ne_bot`

English:
theorem IsIntegral.comap_ne_bot
  given: [Nontrivial R] {I : Ideal A} (I_ne_bot : I != ⊥)
  proof: let ⟨x, x_mem, x_ne_zero⟩ := I.ne_bot_iff.mp I_ne_bot
  comap_ne_bot_of_integral_mem x_ne_zero x_mem (Algebra.IsIntegral.isIntegral x)

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.comap_ne_bot :=
  IsIntegral.comap_ne_bot

中文:
定理 是整.comap_ne_bot
  条件: [非平凡 R] {I : 理想 A} (I_ne_bot : I != ⊥)
  证明: let ⟨x, x_mem, x_ne_zero⟩ := I.ne_bot_iff.mp I_ne_bot
  comap_ne_bot_of_integral_mem x_ne_zero x_mem (Algebra.IsIntegral.isIntegral x)

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.comap_ne_bot :=
  IsIntegral.comap_ne_bot

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, I.ne_bot_iff.mp, I_ne_bot, IsIntegral, comap_ne_bot_of_integral_mem, isIntegral, ne_bot_iff, x_mem, x_ne_zero
-/
theorem IsIntegral.comap_ne_bot [Nontrivial R] {I : Ideal A} (I_ne_bot : I != ⊥) :
    I.comap (algebraMap R A) != ⊥ :=
  let ⟨x, x_mem, x_ne_zero⟩ := I.ne_bot_iff.mp I_ne_bot
  comap_ne_bot_of_integral_mem x_ne_zero x_mem (Algebra.IsIntegral.isIntegral x)

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.comap_ne_bot :=
  IsIntegral.comap_ne_bot

variable (R) in
/--
theorem `IsIntegral.eq_bot_of_comap_eq_bot` / 定理 `IsIntegral.eq_bot_of_comap_eq_bot`

English:
theorem IsIntegral.eq_bot_of_comap_eq_bot
  given: [Nontrivial R] {I : Ideal A}
  proof: by
  contrapose
  exact IsIntegral.comap_ne_bot R

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.eq_bot_of_comap_eq_bot :=
    IsIntegral.eq_bot_of_comap_eq_bot

中文:
定理 是整.eq_bot_of_comap_eq_bot
  条件: [非平凡 R] {I : 理想 A}
  证明: by
  contrapose
  exact IsIntegral.comap_ne_bot R

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.eq_bot_of_comap_eq_bot :=
    IsIntegral.eq_bot_of_comap_eq_bot

Depends on / 依赖: IsIntegral, IsIntegral.comap_ne_bot, comap_ne_bot, contrapose
-/
theorem IsIntegral.eq_bot_of_comap_eq_bot [Nontrivial R] {I : Ideal A} :
    I.comap (algebraMap R A) = ⊥ -> I = ⊥ := by
  contrapose
  exact IsIntegral.comap_ne_bot R

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.eq_bot_of_comap_eq_bot :=
    IsIntegral.eq_bot_of_comap_eq_bot

end IsIntegral

@[deprecated (since := "2026-05-08")] alias IntegralClosure.comap_lt_comap :=
  IsIntegral.comap_lt_comap

@[deprecated (since := "2026-05-08")] alias IntegralClosure.isMaximal_of_isMaximal_comap :=
  IsIntegral.isMaximal_of_isMaximal_comap

section

variable [IsDomain S]

@[deprecated (since := "2026-05-08")] alias IntegralClosure.comap_ne_bot := IsIntegral.comap_ne_bot

@[deprecated (since := "2026-05-08")] alias IntegralClosure.eq_bot_of_comap_eq_bot :=
  IsIntegral.eq_bot_of_comap_eq_bot

/--
theorem `exists_ideal_over_prime_of_isIntegral_of_isDomain` / 定理 `exists_ideal_over_prime_of_isIntegral_of_isDomain`

English:
theorem exists_ideal_over_prime_of_isIntegral_of_isDomain
  statement: [Algebra.IsIntegral R S] (P : Ideal R)
  proof: by
  have hP0 : (0 : S) ∉ Algebra.algebraMapSubmonoid S P.primeCompl := by
    rintro ⟨x, ⟨hx, x0⟩⟩
    exact absurd (hP x0) hx
  let Rₚ := Localization P.primeCompl
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  let : IsDomain (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors hP0)
  obtain ⟨Qₚ : Ideal Sₚ, Qₚ_maximal⟩ := exists_maximal Sₚ
  have : Algebra.IsIntegral Rₚ Sₚ := ⟨isIntegral_localization⟩
  have Qₚ_max : IsMaximal (comap _ Qₚ) :=
    isMaximal_comap_of_isIntegral_of_isMaximal (R := Rₚ) (S := Sₚ) Qₚ
  refine ⟨comap (algebraMap S Sₚ) Qₚ, ⟨comap_isPrime _ Qₚ, ?_⟩⟩
  convert! Localization.AtPrime.under_maximalIdeal (I := P)
  rw [comap_comap]; rw [← IsLocalRing.eq_maximalIdeal Qₚ_max]; rw [← IsLocalization.map_comp (P := S) (Q := Sₚ) (g := algebraMap R S)
    (M := P.primeCompl) (T := Algebra.algebraMapSubmonoid S P.primeCompl) (S := Rₚ)
    (fun p hp => Algebra.mem_algebraMapSubmonoid_of_mem ⟨p]; rw [hp⟩)]
  rfl

中文:
定理 存在_ideal_over_prime_of_is整数egral_of_isDomain
  结论: [代数.是整 R S] (P : 理想 R)
  证明: by
  have hP0 : (0 : S) ∉ Algebra.algebraMapSubmonoid S P.primeCompl := by
    rintro ⟨x, ⟨hx, x0⟩⟩
    exact absurd (hP x0) hx
  let Rₚ := Localization P.primeCompl
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  let : IsDomain (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors hP0)
  obtain ⟨Qₚ : Ideal Sₚ, Qₚ_maximal⟩ := exists_maximal Sₚ
  have : Algebra.IsIntegral Rₚ Sₚ := ⟨isIntegral_localization⟩
  have Qₚ_max : IsMaximal (comap _ Qₚ) :=
    isMaximal_comap_of_isIntegral_of_isMaximal (R := Rₚ) (S := Sₚ) Qₚ
  refine ⟨comap (algebraMap S Sₚ) Qₚ, ⟨comap_isPrime _ Qₚ, ?_⟩⟩
  convert! Localization.AtPrime.under_maximalIdeal (I := P)
  rw [comap_comap]; rw [← IsLocalRing.eq_maximalIdeal Qₚ_max]; rw [← IsLocalization.map_comp (P := S) (Q := Sₚ) (g := algebraMap R S)
    (M := P.primeCompl) (T := Algebra.algebraMapSubmonoid S P.primeCompl) (S := Rₚ)
    (fun p hp => Algebra.mem_algebraMapSubmonoid_of_mem ⟨p]; rw [hp⟩)]
  rfl

Depends on / 依赖: Algebra, Algebra.IsIntegral, Algebra.algebraMapSubmonoid, IsDomain, IsIntegral, IsLocalization, IsLocalization.isDomain_localization, Localization, P.primeCompl, absurd, algebraMapSubmonoid, exists_maximal, isDomain_localization, isIntegral_localization, le_nonZeroDivisors_of_noZeroDivisors, primeCompl
-/
theorem exists_ideal_over_prime_of_isIntegral_of_isDomain [Algebra.IsIntegral R S] (P : Ideal R)
    [IsPrime P] (hP : RingHom.ker (algebraMap R S) <= P) :
    exists Q : Ideal S, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  have hP0 : (0 : S) ∉ Algebra.algebraMapSubmonoid S P.primeCompl := by
    rintro ⟨x, ⟨hx, x0⟩⟩
    exact absurd (hP x0) hx
  let Rₚ := Localization P.primeCompl
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  let : IsDomain (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors hP0)
  obtain ⟨Qₚ : Ideal Sₚ, Qₚ_maximal⟩ := exists_maximal Sₚ
  have : Algebra.IsIntegral Rₚ Sₚ := ⟨isIntegral_localization⟩
  have Qₚ_max : IsMaximal (comap _ Qₚ) :=
    isMaximal_comap_of_isIntegral_of_isMaximal (R := Rₚ) (S := Sₚ) Qₚ
  refine ⟨comap (algebraMap S Sₚ) Qₚ, ⟨comap_isPrime _ Qₚ, ?_⟩⟩
  convert! Localization.AtPrime.under_maximalIdeal (I := P)
  rw [comap_comap]; rw [← IsLocalRing.eq_maximalIdeal Qₚ_max]; rw [← IsLocalization.map_comp (P := S) (Q := Sₚ) (g := algebraMap R S)
    (M := P.primeCompl) (T := Algebra.algebraMapSubmonoid S P.primeCompl) (S := Rₚ)
    (fun p hp => Algebra.mem_algebraMapSubmonoid_of_mem ⟨p]; rw [hp⟩)]
  rfl

end

/--
theorem `exists_ideal_over_prime_of_isIntegral_of_isPrime` / 定理 `exists_ideal_over_prime_of_isIntegral_of_isPrime`

English:
theorem exists_ideal_over_prime_of_isIntegral_of_isPrime
  proof: by
  obtain ⟨Q' : Ideal (S ⧸ I), ⟨Q'_prime, hQ'⟩⟩ :=
    @exists_ideal_over_prime_of_isIntegral_of_isDomain (R ⧸ I.comap (algebraMap R S)) _ (S ⧸ I) _
      Ideal.quotientAlgebra _ _
      (map (Ideal.Quotient.mk (I.comap (algebraMap R S))) P)
      (map_isPrime_of_surjective Quotient.mk_surjective (by simp [hIP]))
      (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot _).1 algebraMap_quotient_injective))
        bot_le)
  refine ⟨Q'.comap _, le_trans (le_of_eq mk_ker.symm) (ker_le_comap _), ⟨comap_isPrime _ Q', ?_⟩⟩
  rw [comap_comap]
  refine _root_.trans ?_ (_root_.trans (congr_arg (comap (Ideal.Quotient.mk
    (comap (algebraMap R S) I))) hQ') ?_)
  · rw [comap_comap]
    exact congr_arg (comap · Q') (RingHom.ext fun r => rfl)
  · refine _root_.trans (comap_map_of_surjective _ Quotient.mk_surjective _) (sup_eq_left.2 ?_)
    simpa [← RingHom.ker_eq_comap_bot] using hIP

中文:
定理 存在_ideal_over_prime_of_is整数egral_of_isPrime
  证明: by
  obtain ⟨Q' : Ideal (S ⧸ I), ⟨Q'_prime, hQ'⟩⟩ :=
    @exists_ideal_over_prime_of_isIntegral_of_isDomain (R ⧸ I.comap (algebraMap R S)) _ (S ⧸ I) _
      Ideal.quotientAlgebra _ _
      (map (Ideal.Quotient.mk (I.comap (algebraMap R S))) P)
      (map_isPrime_of_surjective Quotient.mk_surjective (by simp [hIP]))
      (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot _).1 algebraMap_quotient_injective))
        bot_le)
  refine ⟨Q'.comap _, le_trans (le_of_eq mk_ker.symm) (ker_le_comap _), ⟨comap_isPrime _ Q', ?_⟩⟩
  rw [comap_comap]
  refine _root_.trans ?_ (_root_.trans (congr_arg (comap (Ideal.Quotient.mk
    (comap (algebraMap R S) I))) hQ') ?_)
  · rw [comap_comap]
    exact congr_arg (comap · Q') (RingHom.ext fun r => rfl)
  · refine _root_.trans (comap_map_of_surjective _ Quotient.mk_surjective _) (sup_eq_left.2 ?_)
    simpa [← RingHom.ker_eq_comap_bot] using hIP

Depends on / 依赖: I.comap, Ideal.Quotient.mk, Ideal.quotientAlgebra, Quotient, Quotient.mk_surjective, RingHom, RingHom.injective_iff_ker_eq_bot, _prime, algebraMap, algebraMap_quotient_injective, bot_le, comap_c, comap_isPrime, exists_ideal_over_prime_of_isIntegral_of_isDomain, injective_iff_ker_eq_bot, ker_le_comap, le_of_eq, le_trans, map_isPrime_of_surjective, mk_ker
-/
theorem exists_ideal_over_prime_of_isIntegral_of_isPrime
    [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P]
    (I : Ideal S) [IsPrime I] (hIP : I.comap (algebraMap R S) <= P) :
    exists Q >= I, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  obtain ⟨Q' : Ideal (S ⧸ I), ⟨Q'_prime, hQ'⟩⟩ :=
    @exists_ideal_over_prime_of_isIntegral_of_isDomain (R ⧸ I.comap (algebraMap R S)) _ (S ⧸ I) _
      Ideal.quotientAlgebra _ _
      (map (Ideal.Quotient.mk (I.comap (algebraMap R S))) P)
      (map_isPrime_of_surjective Quotient.mk_surjective (by simp [hIP]))
      (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot _).1 algebraMap_quotient_injective))
        bot_le)
  refine ⟨Q'.comap _, le_trans (le_of_eq mk_ker.symm) (ker_le_comap _), ⟨comap_isPrime _ Q', ?_⟩⟩
  rw [comap_comap]
  refine _root_.trans ?_ (_root_.trans (congr_arg (comap (Ideal.Quotient.mk
    (comap (algebraMap R S) I))) hQ') ?_)
  · rw [comap_comap]
    exact congr_arg (comap · Q') (RingHom.ext fun r => rfl)
  · refine _root_.trans (comap_map_of_surjective _ Quotient.mk_surjective _) (sup_eq_left.2 ?_)
    simpa [← RingHom.ker_eq_comap_bot] using hIP

/--
theorem `exists_ideal_over_prime_of_isIntegral` / 定理 `exists_ideal_over_prime_of_isIntegral`

English:
theorem exists_ideal_over_prime_of_isIntegral
  statement: [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P]
  proof: by
  have ⟨P', hP, hP', hP''⟩ := exists_ideal_comap_le_prime P I hIP
  obtain ⟨Q, hQ, hQ', hQ''⟩ := exists_ideal_over_prime_of_isIntegral_of_isPrime P P' hP''
  exact ⟨Q, hP.trans hQ, hQ', hQ''⟩

中文:
定理 存在_ideal_over_prime_of_is整数egral
  结论: [代数.是整 R S] (P : 理想 R) [是素 P]
  证明: by
  have ⟨P', hP, hP', hP''⟩ := exists_ideal_comap_le_prime P I hIP
  obtain ⟨Q, hQ, hQ', hQ''⟩ := exists_ideal_over_prime_of_isIntegral_of_isPrime P P' hP''
  exact ⟨Q, hP.trans hQ, hQ', hQ''⟩

Depends on / 依赖: exists_ideal_comap_le_prime, exists_ideal_over_prime_of_isIntegral_of_isPrime, hP.trans
-/
theorem exists_ideal_over_prime_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P]
    (I : Ideal S) (hIP : I.comap (algebraMap R S) <= P) :
    exists Q >= I, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  have ⟨P', hP, hP', hP''⟩ := exists_ideal_comap_le_prime P I hIP
  obtain ⟨Q, hQ, hQ', hQ''⟩ := exists_ideal_over_prime_of_isIntegral_of_isPrime P P' hP''
  exact ⟨Q, hP.trans hQ, hQ', hQ''⟩

/--
Instance `nonempty_primesOver` / 实例 `nonempty_primesOver`

English:
instance nonempty_primesOver
  signature: [Algebra.IsIntegral R S] [FaithfulSMul R S] (P : Ideal R) [P.IsPrime]
  body: by
  obtain ⟨Q, _, hQ₁, hQ₂⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal S)
    (by simp [← RingHom.ker_eq_comap_bot])
  exact ⟨Q, ⟨hQ₁, (liesOver_iff _ _).mpr hQ₂.symm⟩⟩

中文:
实例 nonempty_primesOver
  签名: [代数.是整 R S] [忠实标量乘法 R S] (P : 理想 R) [P.是素]
  定义体: by
  obtain ⟨Q, _, hQ₁, hQ₂⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal S)
    (by simp [← RingHom.ker_eq_comap_bot])
  exact ⟨Q, ⟨hQ₁, (liesOver_iff _ _).mpr hQ₂.symm⟩⟩

Depends on / 依赖: RingHom, RingHom.ker_eq_comap_bot, exists_ideal_over_prime_of_isIntegral, ker_eq_comap_bot, liesOver_iff
-/
instance nonempty_primesOver [Algebra.IsIntegral R S] [FaithfulSMul R S] (P : Ideal R) [P.IsPrime] :
    Nonempty (primesOver P S) := by
  obtain ⟨Q, _, hQ₁, hQ₂⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal S)
    (by simp [← RingHom.ker_eq_comap_bot])
  exact ⟨Q, ⟨hQ₁, (liesOver_iff _ _).mpr hQ₂.symm⟩⟩

/--
theorem `exists_ideal_over_maximal_of_isIntegral` / 定理 `exists_ideal_over_maximal_of_isIntegral`

English:
theorem exists_ideal_over_maximal_of_isIntegral
  statement: [Algebra.IsIntegral R S]
  proof: by
  obtain ⟨Q, -, Q_prime, hQ⟩ := exists_ideal_over_prime_of_isIntegral P ⊥ hP
  exact ⟨Q, isMaximal_of_isIntegral_of_isMaximal_comap _ (hQ.symm ▸ P_max), hQ⟩

中文:
定理 存在_ideal_over_maximal_of_is整数egral
  结论: [代数.是整 R S]
  证明: by
  obtain ⟨Q, -, Q_prime, hQ⟩ := exists_ideal_over_prime_of_isIntegral P ⊥ hP
  exact ⟨Q, isMaximal_of_isIntegral_of_isMaximal_comap _ (hQ.symm ▸ P_max), hQ⟩

Depends on / 依赖: P_max, Q_prime, exists_ideal_over_prime_of_isIntegral, hQ.symm, isMaximal_of_isIntegral_of_isMaximal_comap
-/
theorem exists_ideal_over_maximal_of_isIntegral [Algebra.IsIntegral R S]
    (P : Ideal R) [P_max : IsMaximal P] (hP : RingHom.ker (algebraMap R S) <= P) :
    exists Q : Ideal S, IsMaximal Q ∧ Q.comap (algebraMap R S) = P := by
  obtain ⟨Q, -, Q_prime, hQ⟩ := exists_ideal_over_prime_of_isIntegral P ⊥ hP
  exact ⟨Q, isMaximal_of_isIntegral_of_isMaximal_comap _ (hQ.symm ▸ P_max), hQ⟩

/--
theorem `exists_maximal_ideal_liesOver_of_isIntegral` / 定理 `exists_maximal_ideal_liesOver_of_isIntegral`

English:
theorem exists_maximal_ideal_liesOver_of_isIntegral
  statement: [Algebra.IsIntegral R S] [FaithfulSMul R S]
  proof: by
  simp_rw [liesOver_iff, eq_comm (a := P)]
  exact exists_ideal_over_maximal_of_isIntegral P (by
    simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)])

中文:
定理 存在_maximal_ideal_liesOver_of_is整数egral
  结论: [代数.是整 R S] [忠实标量乘法 R S]
  证明: by
  simp_rw [liesOver_iff, eq_comm (a := P)]
  exact exists_ideal_over_maximal_of_isIntegral P (by
    simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)])

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, RingHom, RingHom.injective_iff_ker_eq_bot, algebraMap_injective, eq_comm, exists_ideal_over_maximal_of_isIntegral, injective_iff_ker_eq_bot, liesOver_iff, simp_rw
-/
theorem exists_maximal_ideal_liesOver_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (P : Ideal R) [P.IsMaximal] :
    exists (Q : Ideal S), Q.IsMaximal ∧ Q.LiesOver P := by
  simp_rw [liesOver_iff, eq_comm (a := P)]
  exact exists_ideal_over_maximal_of_isIntegral P (by
    simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)])

/--
lemma `map_eq_top_iff_of_ker_le` / 引理 `map_eq_top_iff_of_ker_le`

English:
lemma map_eq_top_iff_of_ker_le
  statement: {R S} [CommRing R] [CommRing S]
  proof: by
  constructor; swap
  · rintro rfl; exact Ideal.map_top _
  contrapose
  intro h
  obtain ⟨m, _, hm⟩ := Ideal.exists_le_maximal I h
  let _ := f.toAlgebra
  have : Algebra.IsIntegral _ _ := ⟨hf₂⟩
  obtain ⟨m', _, rfl⟩ := exists_ideal_over_maximal_of_isIntegral m (hf₁.trans hm)
  rw [← map_le_iff_le_comap] at hm
  exact (hm.trans_lt (lt_top_iff_ne_top.mpr (IsMaximal.ne_top ‹_›))).ne

中文:
引理 map_eq_top_iff_of_ker_le
  结论: {R S} [交换环 R] [交换环 S]
  证明: by
  constructor; swap
  · rintro rfl; exact Ideal.map_top _
  contrapose
  intro h
  obtain ⟨m, _, hm⟩ := Ideal.exists_le_maximal I h
  let _ := f.toAlgebra
  have : Algebra.IsIntegral _ _ := ⟨hf₂⟩
  obtain ⟨m', _, rfl⟩ := exists_ideal_over_maximal_of_isIntegral m (hf₁.trans hm)
  rw [← map_le_iff_le_comap] at hm
  exact (hm.trans_lt (lt_top_iff_ne_top.mpr (IsMaximal.ne_top ‹_›))).ne

Depends on / 依赖: Algebra, Algebra.IsIntegral, Ideal.exists_le_maximal, Ideal.map_top, IsIntegral, IsMaximal, IsMaximal.ne_top, contrapose, exists_ideal_over_maximal_of_isIntegral, exists_le_maximal, f.toAlgebra, hm.trans_lt, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, map_le_iff_le_comap, map_top, ne_top, toAlgebra, trans_lt
-/
lemma map_eq_top_iff_of_ker_le {R S} [CommRing R] [CommRing S]
    (f : R ->+* S) {I : Ideal R} (hf₁ : RingHom.ker f <= I) (hf₂ : f.IsIntegral) :
    I.map f = ⊤ ↔ I = ⊤ := by
  constructor; swap
  · rintro rfl; exact Ideal.map_top _
  contrapose
  intro h
  obtain ⟨m, _, hm⟩ := Ideal.exists_le_maximal I h
  let _ := f.toAlgebra
  have : Algebra.IsIntegral _ _ := ⟨hf₂⟩
  obtain ⟨m', _, rfl⟩ := exists_ideal_over_maximal_of_isIntegral m (hf₁.trans hm)
  rw [← map_le_iff_le_comap] at hm
  exact (hm.trans_lt (lt_top_iff_ne_top.mpr (IsMaximal.ne_top ‹_›))).ne

/--
lemma `map_eq_top_iff` / 引理 `map_eq_top_iff`

English:
lemma map_eq_top_iff
  statement: {R S} [CommRing R] [CommRing S]
  proof: map_eq_top_iff_of_ker_le f (by simp [(RingHom.injective_iff_ker_eq_bot f).mp hf₁]) hf₂

中文:
引理 map_eq_top_iff
  结论: {R S} [交换环 R] [交换环 S]
  证明: map_eq_top_iff_of_ker_le f (by simp [(RingHom.injective_iff_ker_eq_bot f).mp hf₁]) hf₂

Depends on / 依赖: RingHom, RingHom.injective_iff_ker_eq_bot, _interior, _interior.ge_iff, _interior_le, ge_iff, h.lift, h.mem_of_mem, injective_iff_ker_eq_bot, interior_eq, l.lift, le_antisymm, map_eq_top_iff_of_ker_le, mem_of_mem
-/
lemma map_eq_top_iff {R S} [CommRing R] [CommRing S]
    (f : R ->+* S) {I : Ideal R} (hf₁ : Function.Injective f) (hf₂ : f.IsIntegral) :
    I.map f = ⊤ ↔ I = ⊤ :=
  map_eq_top_iff_of_ker_le f (by simp [(RingHom.injective_iff_ker_eq_bot f).mp hf₁]) hf₂

/--
lemma `exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton` / 引理 `exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton`

English:
lemma exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton
  proof: by
  simp only [dvd_def, eq_comm, mul_comm x]
  by_contra!
  obtain ⟨Q, hQ, hxQ, hQp⟩ := Ideal.exists_le_prime_disjoint (.span {x})
    (Algebra.algebraMapSubmonoid _ p.primeCompl)
    (by simpa [Set.disjoint_iff_forall_ne, Ideal.mem_span_singleton',
      Algebra.algebraMapSubmonoid, @forall_comm S])
  have hQp' : Q.under _ <= p := by
    intro x hxQ
    by_contra hxp
    exact Set.subset_compl_iff_disjoint_right.mpr hQp hxQ ⟨x, hxp, rfl⟩
  obtain ⟨Q', hQ'Q, hQ', hQ'p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime _ _ hQp'
  obtain rfl : Q' = q := hq.le ⟨hQ', ⟨hQ'p.symm⟩⟩
  exact hx (hQ'Q (hxQ (Ideal.mem_span_singleton_self _)))

中文:
引理 存在_notMem_dvd_algebraMap_of_primesOver_eq_singleton
  证明: by
  simp only [dvd_def, eq_comm, mul_comm x]
  by_contra!
  obtain ⟨Q, hQ, hxQ, hQp⟩ := Ideal.exists_le_prime_disjoint (.span {x})
    (Algebra.algebraMapSubmonoid _ p.primeCompl)
    (by simpa [Set.disjoint_iff_forall_ne, Ideal.mem_span_singleton',
      Algebra.algebraMapSubmonoid, @forall_comm S])
  have hQp' : Q.under _ <= p := by
    intro x hxQ
    by_contra hxp
    exact Set.subset_compl_iff_disjoint_right.mpr hQp hxQ ⟨x, hxp, rfl⟩
  obtain ⟨Q', hQ'Q, hQ', hQ'p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime _ _ hQp'
  obtain rfl : Q' = q := hq.le ⟨hQ', ⟨hQ'p.symm⟩⟩
  exact hx (hQ'Q (hxQ (Ideal.mem_span_singleton_self _)))

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime, Ideal.exists_le_prime_disjoint, Ideal.mem_span_singleton, Q.under, Set.disjoint_iff_forall_ne, Set.subset_compl_iff_disjoint_right.mpr, algebraMapSubmonoid, disjoint_iff_forall_ne, dvd_def, eq_comm, exists_ideal_over_prime_of_isIntegral_of_isPrime, exists_le_prime_disjoint, forall_comm, mem_span_singleton, mul_comm, p.primeCompl, primeCompl, subset_compl_iff_disjoint_right
-/
lemma exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton
    {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] (hq : p.primesOver S = {q})
    [Algebra.IsIntegral R S] (x : S) (hx : x ∉ q) : exists r ∉ p, x ∣ algebraMap _ _ r := by
  simp only [dvd_def, eq_comm, mul_comm x]
  by_contra!
  obtain ⟨Q, hQ, hxQ, hQp⟩ := Ideal.exists_le_prime_disjoint (.span {x})
    (Algebra.algebraMapSubmonoid _ p.primeCompl)
    (by simpa [Set.disjoint_iff_forall_ne, Ideal.mem_span_singleton',
      Algebra.algebraMapSubmonoid, @forall_comm S])
  have hQp' : Q.under _ <= p := by
    intro x hxQ
    by_contra hxp
    exact Set.subset_compl_iff_disjoint_right.mpr hQp hxQ ⟨x, hxp, rfl⟩
  obtain ⟨Q', hQ'Q, hQ', hQ'p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime _ _ hQp'
  obtain rfl : Q' = q := hq.le ⟨hQ', ⟨hQ'p.symm⟩⟩
  exact hx (hQ'Q (hxQ (Ideal.mem_span_singleton_self _)))

end IsDomain

section IsIntegral

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
  (P : Ideal B) (p : Ideal A) [P.LiesOver p]

variable (A) in
/--
Instance `IsMaximal.under` / 实例 `IsMaximal.under`

English:
instance IsMaximal.under
  signature: [P.IsMaximal]
  body: isMaximal_comap_of_isIntegral_of_isMaximal P

中文:
实例 是极大.under
  签名: [P.是极大]
  定义体: isMaximal_comap_of_isIntegral_of_isMaximal P

Depends on / 依赖: isMaximal_comap_of_isIntegral_of_isMaximal
-/
instance IsMaximal.under [P.IsMaximal] : (P.under A).IsMaximal :=
  isMaximal_comap_of_isIntegral_of_isMaximal P

/--
theorem `IsMaximal.of_liesOver_isMaximal` / 定理 `IsMaximal.of_liesOver_isMaximal`

English:
theorem IsMaximal.of_liesOver_isMaximal
  given: [hpm : p.IsMaximal] [P.IsPrime]
  statement: P.IsMaximal
  proof: by
  rw [P.over_def p] at hpm
  exact isMaximal_of_isIntegral_of_isMaximal_comap P hpm

中文:
定理 是极大.of_liesOver_isMaximal
  条件: [hpm : p.是极大] [P.是素]
  结论: P.是极大
  证明: by
  rw [P.over_def p] at hpm
  exact isMaximal_of_isIntegral_of_isMaximal_comap P hpm

Depends on / 依赖: P.over_def, isMaximal_of_isIntegral_of_isMaximal_comap, over_def
-/
theorem IsMaximal.of_liesOver_isMaximal [hpm : p.IsMaximal] [P.IsPrime] : P.IsMaximal := by
  rw [P.over_def p] at hpm
  exact isMaximal_of_isIntegral_of_isMaximal_comap P hpm

/--
theorem `IsMaximal.of_isMaximal_liesOver` / 定理 `IsMaximal.of_isMaximal_liesOver`

English:
theorem IsMaximal.of_isMaximal_liesOver
  given: [P.IsMaximal]
  statement: p.IsMaximal
  proof: by
  rw [P.over_def p]
  exact isMaximal_comap_of_isIntegral_of_isMaximal P

中文:
定理 是极大.of_isMaximal_liesOver
  条件: [P.是极大]
  结论: p.是极大
  证明: by
  rw [P.over_def p]
  exact isMaximal_comap_of_isIntegral_of_isMaximal P

Depends on / 依赖: P.over_def, isMaximal_comap_of_isIntegral_of_isMaximal, over_def
-/
theorem IsMaximal.of_isMaximal_liesOver [P.IsMaximal] : p.IsMaximal := by
  rw [P.over_def p]
  exact isMaximal_comap_of_isIntegral_of_isMaximal P

variable (A) in
/--
theorem `eq_bot_of_liesOver_bot` / 定理 `eq_bot_of_liesOver_bot`

English:
theorem eq_bot_of_liesOver_bot
  given: [Nontrivial A] [IsDomain B] [h : P.LiesOver (⊥ : Ideal A)]
  proof: eq_bot_of_comap_eq_bot ((liesOver_iff _ _).mp h).symm

中文:
定理 eq_bot_of_liesOver_bot
  条件: [非平凡 A] [是整环 B] [h : P.LiesOver (⊥ : 理想 A)]
  证明: eq_bot_of_comap_eq_bot ((liesOver_iff _ _).mp h).symm

Depends on / 依赖: eq_bot_of_comap_eq_bot, liesOver_iff
-/
theorem eq_bot_of_liesOver_bot [Nontrivial A] [IsDomain B] [h : P.LiesOver (⊥ : Ideal A)] :
    P = ⊥ :=
eq_bot_of_comap_eq_bot ((liesOver_iff _ _).mp h).symm

variable (A) {P} in
/--
theorem `under_ne_bot` / 定理 `under_ne_bot`

English:
theorem under_ne_bot
  given: [Nontrivial A] [IsDomain B] (hP : P != ⊥)
  statement: under A P != ⊥
  proof: fun h => hP eq_bot_of_comap_eq_bot h

中文:
定理 under_ne_bot
  条件: [非平凡 A] [是整环 B] (hP : P != ⊥)
  结论: under A P != ⊥
  证明: fun h => hP eq_bot_of_comap_eq_bot h

Depends on / 依赖: eq_bot_of_comap_eq_bot
-/
theorem under_ne_bot [Nontrivial A] [IsDomain B] (hP : P != ⊥) : under A P != ⊥ :=
fun h => hP eq_bot_of_comap_eq_bot h

/--
Instance `Quotient.algebra_isIntegral_of_liesOver` / 实例 `Quotient.algebra_isIntegral_of_liesOver`

English:
instance Quotient.algebra_isIntegral_of_liesOver
  signature: : Algebra.IsIntegral (A ⧸ p) (B ⧸ P)
  body: Algebra.IsIntegral.tower_top A

中文:
实例 商.algebra_is整数egral_of_liesOver
  签名: : 代数.是整 (A ⧸ p) (B ⧸ P)
  定义体: Algebra.IsIntegral.tower_top A

Depends on / 依赖: Algebra, Algebra.IsIntegral.tower_top, IsIntegral, Subset, Subset.antisymm, Subset.refl, antisymm, closure_minimal, subset_closure, tower_top
-/
instance Quotient.algebra_isIntegral_of_liesOver : Algebra.IsIntegral (A ⧸ p) (B ⧸ P) :=
  Algebra.IsIntegral.tower_top A

end IsIntegral

section IsIntegral

variable {A : Type*} [CommRing A] {p : Ideal A} [p.IsMaximal] {B : Type*} [CommRing B]
  [Algebra A B] [Algebra.IsIntegral A B] (Q : primesOver p B)

/--
Instance `primesOver.isMaximal` / 实例 `primesOver.isMaximal`

English:
instance primesOver.isMaximal
  signature: : Q.1.IsMaximal
  body: Ideal.IsMaximal.of_liesOver_isMaximal Q.1 p

中文:
实例 primesOver.isMaximal
  签名: : Q.1.是极大
  定义体: Ideal.IsMaximal.of_liesOver_isMaximal Q.1 p

Depends on / 依赖: Ideal.IsMaximal.of_liesOver_isMaximal, IsMaximal, of_liesOver_isMaximal
-/
instance primesOver.isMaximal : Q.1.IsMaximal :=
  Ideal.IsMaximal.of_liesOver_isMaximal Q.1 p

/--
theorem `isMaximal_of_mem_primesOver` / 定理 `isMaximal_of_mem_primesOver`

English:
theorem isMaximal_of_mem_primesOver
  given: {P : Ideal B} (hP : P in primesOver p B)
  statement: P.IsMaximal
  proof: primesOver.isMaximal ⟨P, hP⟩

中文:
定理 isMaximal_of_mem_primesOver
  条件: {P : 理想 B} (hP : P in primesOver p B)
  结论: P.是极大
  证明: primesOver.isMaximal ⟨P, hP⟩

Depends on / 依赖: isMaximal, primesOver, primesOver.isMaximal
-/
theorem isMaximal_of_mem_primesOver {P : Ideal B} (hP : P in primesOver p B) : P.IsMaximal :=
  primesOver.isMaximal ⟨P, hP⟩

variable (A B) in
/--
lemma `primesOver_bot` / 引理 `primesOver_bot`

English:
lemma primesOver_bot
  given: [Module.IsTorsionFree A B] [IsDomain A] [IsDomain B]
  proof: by
  ext p
  refine ⟨fun ⟨_, ⟨h⟩⟩ => p.eq_bot_of_comap_eq_bot h.symm, ?_⟩
  rintro rfl
  exact ⟨Ideal.isPrime_bot, Ideal.bot_liesOver_bot A B⟩

中文:
引理 primesOver_bot
  条件: [模.是无挠 A B] [是整环 A] [是整环 B]
  证明: by
  ext p
  refine ⟨fun ⟨_, ⟨h⟩⟩ => p.eq_bot_of_comap_eq_bot h.symm, ?_⟩
  rintro rfl
  exact ⟨Ideal.isPrime_bot, Ideal.bot_liesOver_bot A B⟩

Depends on / 依赖: Ideal.bot_liesOver_bot, Ideal.isPrime_bot, bot_liesOver_bot, eq_bot_of_comap_eq_bot, h.symm, isPrime_bot, p.eq_bot_of_comap_eq_bot
-/
lemma primesOver_bot [Module.IsTorsionFree A B] [IsDomain A] [IsDomain B] :
    primesOver (⊥ : Ideal A) B = {⊥} := by
  ext p
  refine ⟨fun ⟨_, ⟨h⟩⟩ => p.eq_bot_of_comap_eq_bot h.symm, ?_⟩
  rintro rfl
  exact ⟨Ideal.isPrime_bot, Ideal.bot_liesOver_bot A B⟩

end IsIntegral

end Ideal
