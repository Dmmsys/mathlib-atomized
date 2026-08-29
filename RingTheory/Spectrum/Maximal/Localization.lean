/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Maximal spectrum of a commutative (semi)ring

Localization results.
-/

@[expose] public section

noncomputable section

variable (R S P : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]

namespace MaximalSpectrum

variable {R}

open PrimeSpectrum Set

variable (R : Type*)
variable [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/--
theorem `iInf_localization_eq_bot` / 定理 `iInf_localization_eq_bot`

English:
theorem iInf_localization_eq_bot
  statement: (⨅ v : MaximalSpectrum R,
  proof: by
  ext x
  rw [Algebra.mem_bot]; rw [Algebra.mem_iInf]
  constructor
  · contrapose
    intro hrange hlocal
    let denom : Ideal R := (1 : Submodule R K).comap (LinearMap.toSpanSingleton R K x)
    have hdenom : (1 : R) ∉ denom := by simpa [denom] using hrange
    rcases denom.exists_le_maximal (

中文:
定理 iInf_localization_eq_bot
  结论: (⨅ v : MaximalSpectrum R,
  证明: by
  ext x
  rw [Algebra.mem_bot]; rw [Algebra.mem_iInf]
  constructor
  · contrapose
    intro hrange hlocal
    let denom : Ideal R := (1 : Submodule R K).comap (LinearMap.toSpanSingleton R K x)
    have hdenom : (1 : R) ∉ denom := by simpa [denom] using hrange
    rcases denom.exists_le_maximal (

Depends on / 依赖: Algebra, Algebra.mem_bot, Algebra.mem_iInf, Algebra.smul_def, IsFractionRing, IsFractionRing.inject, LinearMap, LinearMap.toSpanSingleton, Submodule, contrapose, denom.exists_le_maximal, denom.ne_top_iff_one.mpr, exists_le_maximal, hdenom, hlocal, hrange, inject, map_ne_zero_iff, mem_bot, mem_iInf
-/
theorem iInf_localization_eq_bot : (⨅ v : MaximalSpectrum R,
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_bot]; rw [Algebra.mem_iInf]
  constructor
  · contrapose
    intro hrange hlocal
    let denom : Ideal R := (1 : Submodule R K).comap (LinearMap.toSpanSingleton R K x)
    have hdenom : (1 : R) ∉ denom := by simpa [denom] using hrange
    rcases denom.exists_le_maximal (denom.ne_top_iff_one.mpr hdenom) with ⟨max, hmax, hle⟩
    rcases hlocal ⟨max, hmax⟩ with ⟨n, d, hd, rfl⟩
    exact hd (hle ⟨n, by simp [Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ <|
      (map_ne_zero_iff _ <| IsFractionRing.injective R K).mpr fun h => hd (h ▸ max.zero_mem :)]⟩)
  · rintro ⟨y, rfl⟩ ⟨v, hv⟩
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩

end MaximalSpectrum

namespace PrimeSpectrum

variable (R : Type*)
variable [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/--
theorem `iInf_localization_eq_bot` / 定理 `iInf_localization_eq_bot`

English:
theorem iInf_localization_eq_bot
  statement: ⨅ v : PrimeSpectrum R,
  proof: by
  refine bot_unique (.trans (fun _ => ?_) (MaximalSpectrum.iInf_localization_eq_bot R K).le)
  simpa only [Algebra.mem_iInf] using fun hx ⟨v, hv⟩ => hx ⟨v, hv.isPrime⟩

中文:
定理 iInf_localization_eq_bot
  结论: ⨅ v : PrimeSpectrum R,
  证明: by
  refine bot_unique (.trans (fun _ => ?_) (MaximalSpectrum.iInf_localization_eq_bot R K).le)
  simpa only [Algebra.mem_iInf] using fun hx ⟨v, hv⟩ => hx ⟨v, hv.isPrime⟩

Depends on / 依赖: Algebra, Algebra.mem_iInf, MaximalSpectrum, MaximalSpectrum.iInf_localization_eq_bot, bot_unique, hv.isPrime, iInf_localization_eq_bot, isPrime, mem_iInf
-/
theorem iInf_localization_eq_bot : ⨅ v : PrimeSpectrum R,
    Localization.subalgebra.ofField K _ (v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  refine bot_unique (.trans (fun _ => ?_) (MaximalSpectrum.iInf_localization_eq_bot R K).le)
  simpa only [Algebra.mem_iInf] using fun hx ⟨v, hv⟩ => hx ⟨v, hv.isPrime⟩

end PrimeSpectrum

namespace MaximalSpectrum

/--
Definition of `PiLocalization` / `PiLocalization` 的定义

English:
abbreviation PiLocalization
  signature: : Type _
  body: Π I : MaximalSpectrum R, Localization.AtPrime I.1

中文:
缩写 PiLocalization
  签名: : Type _
  定义体: Π I : MaximalSpectrum R, Localization.AtPrime I.1

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, MaximalSpectrum
-/
abbrev PiLocalization : Type _ := Π I : MaximalSpectrum R, Localization.AtPrime I.1

/--
Definition of `toPiLocalization` / `toPiLocalization` 的定义

English:
definition toPiLocalization
  signature: : R ->ₐ[R] PiLocalization R
  body: Algebra.ofId R (PiLocalization R)

中文:
定义 toPiLocalization
  签名: : R ->ₐ[R] PiLocalization R
  定义体: Algebra.ofId R (PiLocalization R)

Depends on / 依赖: Algebra, Algebra.ofId, PiLocalization
-/
def toPiLocalization : R ->ₐ[R] PiLocalization R := Algebra.ofId R (PiLocalization R)

/--
theorem `toPiLocalization_injective` / 定理 `toPiLocalization_injective`

English:
theorem toPiLocalization_injective
  statement: Function.Injective (toPiLocalization R)
  proof: fun r r' eq => by
  rw [← one_mul r]; rw [← one_mul r']
  by_contra ne
  have ⟨I, mI, hI⟩ := (Module.eqIdeal R r r').exists_le_maximal ((Ideal.ne_top_iff_one _).mpr ne)
  have ⟨s, hs⟩ := (IsLocalization.eq_iff_exists I.primeCompl _).mp (congr_fun eq ⟨I, mI⟩)
  exact s.2 (hI hs)

中文:
定理 toPiLocalization_injective
  结论: Function.Injective (toPiLocalization R)
  证明: fun r r' eq => by
  rw [← one_mul r]; rw [← one_mul r']
  by_contra ne
  have ⟨I, mI, hI⟩ := (Module.eqIdeal R r r').exists_le_maximal ((Ideal.ne_top_iff_one _).mpr ne)
  have ⟨s, hs⟩ := (IsLocalization.eq_iff_exists I.primeCompl _).mp (congr_fun eq ⟨I, mI⟩)
  exact s.2 (hI hs)

Depends on / 依赖: I.primeCompl, Ideal.ne_top_iff_one, IsLocalization, IsLocalization.eq_iff_exists, Module, Module.eqIdeal, congr_fun, eqIdeal, eq_iff_exists, exists_le_maximal, ne_top_iff_one, one_mul, primeCompl
-/
theorem toPiLocalization_injective : Function.Injective (toPiLocalization R) := fun r r' eq => by
  rw [← one_mul r]; rw [← one_mul r']
  by_contra ne
  have ⟨I, mI, hI⟩ := (Module.eqIdeal R r r').exists_le_maximal ((Ideal.ne_top_iff_one _).mpr ne)
  have ⟨s, hs⟩ := (IsLocalization.eq_iff_exists I.primeCompl _).mp (congr_fun eq ⟨I, mI⟩)
  exact s.2 (hI hs)

/--
theorem `toPiLocalization_apply_apply` / 定理 `toPiLocalization_apply_apply`

English:
theorem toPiLocalization_apply_apply
  given: {r I}
  statement: toPiLocalization R r I = algebraMap R _ r
  proof: rfl

中文:
定理 toPiLocalization_apply_apply
  条件: {r I}
  结论: toPiLocalization R r I = algebraMap R _ r
  证明: rfl
-/
theorem toPiLocalization_apply_apply {r I} : toPiLocalization R r I = algebraMap R _ r := rfl

variable {R S} (f : R ->+* S) (g : S ->+* P) (hf : Function.Bijective f) (hg : Function.Bijective g)

/--
Definition of `mapPiLocalization` / `mapPiLocalization` 的定义

English:
definition mapPiLocalization
  signature: : PiLocalization R ->+* PiLocalization S
  body: RingHom.pi fun I => (Localization.localRingHom _ _ f rfl).comp
    Pi.evalRingHom _ (⟨_, I.2.comap_bijective f hf⟩ : MaximalSpectrum R)

中文:
定义 mapPiLocalization
  签名: : PiLocalization R ->+* PiLocalization S
  定义体: RingHom.pi fun I => (Localization.localRingHom _ _ f rfl).comp
    Pi.evalRingHom _ (⟨_, I.2.comap_bijective f hf⟩ : MaximalSpectrum R)

Depends on / 依赖: Localization, Localization.localRingHom, MaximalSpectrum, Pi.evalRingHom, RingHom, RingHom.pi, comap_bijective, evalRingHom, localRingHom
-/
noncomputable def mapPiLocalization : PiLocalization R ->+* PiLocalization S :=
RingHom.pi fun I => (Localization.localRingHom _ _ f rfl).comp
    Pi.evalRingHom _ (⟨_, I.2.comap_bijective f hf⟩ : MaximalSpectrum R)

/--
theorem `mapPiLocalization_naturality` / 定理 `mapPiLocalization_naturality`

English:
theorem mapPiLocalization_naturality
  proof: by
  ext r I
  change Localization.localRingHom _ _ _ rfl (algebraMap _ _ r) = algebraMap _ _ (f r)
  simp_rw [← IsLocalization.mk'_one (M := (I.1.comap f).primeCompl), Localization.localRingHom_mk',
    ← IsLocalization.mk'_one (M := I.1.primeCompl), Submonoid.coe_one, map_one f]
  rfl

中文:
定理 mapPiLocalization_naturality
  证明: by
  ext r I
  change Localization.localRingHom _ _ _ rfl (algebraMap _ _ r) = algebraMap _ _ (f r)
  simp_rw [← IsLocalization.mk'_one (M := (I.1.comap f).primeCompl), Localization.localRingHom_mk',
    ← IsLocalization.mk'_one (M := I.1.primeCompl), Submonoid.coe_one, map_one f]
  rfl

Depends on / 依赖: IsLocalization, IsLocalization.mk, Localization, Localization.localRingHom, Localization.localRingHom_mk, Submonoid, Submonoid.coe_one, _one, algebraMap, coe_one, localRingHom, localRingHom_mk, map_one, primeCompl, simp_rw
-/
theorem mapPiLocalization_naturality :
    (mapPiLocalization f hf).comp (toPiLocalization R) =
      (toPiLocalization S).toRingHom.comp f := by
  ext r I
  change Localization.localRingHom _ _ _ rfl (algebraMap _ _ r) = algebraMap _ _ (f r)
  simp_rw [← IsLocalization.mk'_one (M := (I.1.comap f).primeCompl), Localization.localRingHom_mk',
    ← IsLocalization.mk'_one (M := I.1.primeCompl), Submonoid.coe_one, map_one f]
  rfl

/--
theorem `mapPiLocalization_id` / 定理 `mapPiLocalization_id`

English:
theorem mapPiLocalization_id
  statement: mapPiLocalization (.id R) Function.bijective_id = .id _
  proof: RingHom.ext fun _ => funext fun _ => congr($(Localization.localRingHom_id _) _)

中文:
定理 mapPiLocalization_id
  结论: mapPiLocalization (.id R) Function.bijective_id = .id _
  证明: RingHom.ext fun _ => funext fun _ => congr($(Localization.localRingHom_id _) _)

Depends on / 依赖: Localization, Localization.localRingHom_id, RingHom, RingHom.ext, localRingHom_id
-/
theorem mapPiLocalization_id : mapPiLocalization (.id R) Function.bijective_id = .id _ :=
  RingHom.ext fun _ => funext fun _ => congr($(Localization.localRingHom_id _) _)

/--
theorem `mapPiLocalization_comp` / 定理 `mapPiLocalization_comp`

English:
theorem mapPiLocalization_comp
  proof: RingHom.ext fun _ => funext fun _ => congr($(Localization.localRingHom_comp _ _ _ _ rfl _ rfl) _)

中文:
定理 mapPiLocalization_comp
  证明: RingHom.ext fun _ => funext fun _ => congr($(Localization.localRingHom_comp _ _ _ _ rfl _ rfl) _)

Depends on / 依赖: Localization, Localization.localRingHom_comp, RingHom, RingHom.ext, localRingHom_comp
-/
theorem mapPiLocalization_comp :
    mapPiLocalization (g.comp f) (hg.comp hf) =
      (mapPiLocalization g hg).comp (mapPiLocalization f hf) :=
  RingHom.ext fun _ => funext fun _ => congr($(Localization.localRingHom_comp _ _ _ _ rfl _ rfl) _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mapPiLocalization_bijective` / 定理 `mapPiLocalization_bijective`

English:
theorem mapPiLocalization_bijective
  statement: Function.Bijective (mapPiLocalization f hf)
  proof: by
  let f := RingEquiv.ofBijective f hf
  let e := RingEquiv.ofRingHom (mapPiLocalization f hf)
    (mapPiLocalization (f.symm : S ->+* R) f.symm.bijective) ?_ ?_
  · exact e.bijective
  · rw [← mapPiLocalization_comp]
    simp_rw [RingEquiv.comp_symm, mapPiLocalization_id]
  · rw [← mapPiLocalizat

中文:
定理 mapPiLocalization_bijective
  结论: Function.Bijective (mapPiLocalization f hf)
  证明: by
  let f := RingEquiv.ofBijective f hf
  let e := RingEquiv.ofRingHom (mapPiLocalization f hf)
    (mapPiLocalization (f.symm : S ->+* R) f.symm.bijective) ?_ ?_
  · exact e.bijective
  · rw [← mapPiLocalization_comp]
    simp_rw [RingEquiv.comp_symm, mapPiLocalization_id]
  · rw [← mapPiLocalizat

Depends on / 依赖: RingEquiv, RingEquiv.comp_symm, RingEquiv.ofBijective, RingEquiv.ofRingHom, RingEquiv.symm_comp, bijective, comp_symm, e.bijective, f.symm, f.symm.bijective, mapPiLocalization, mapPiLocalization_comp, mapPiLocalization_id, ofBijective, ofRingHom, simp_rw, symm_comp
-/
theorem mapPiLocalization_bijective : Function.Bijective (mapPiLocalization f hf) := by
  let f := RingEquiv.ofBijective f hf
  let e := RingEquiv.ofRingHom (mapPiLocalization f hf)
    (mapPiLocalization (f.symm : S ->+* R) f.symm.bijective) ?_ ?_
  · exact e.bijective
  · rw [← mapPiLocalization_comp]
    simp_rw [RingEquiv.comp_symm, mapPiLocalization_id]
  · rw [← mapPiLocalization_comp]
    simp_rw [RingEquiv.symm_comp, mapPiLocalization_id]

section Pi

variable {ι} (R : ι -> Type*) [forall i, CommSemiring (R i)] [forall i, Nontrivial (R i)]

/--
theorem `toPiLocalization_not_surjective_of_infinite` / 定理 `toPiLocalization_not_surjective_of_infinite`

English:
theorem toPiLocalization_not_surjective_of_infinite
  given: [Infinite ι]
  proof: fun surj => by
  classical
  have ⟨J, max, notMem⟩ := PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite R
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max⟩ 1)
have : r = 0 := funext fun i => toPiLocalization_injective _ funext fun I => by
    replace hr := congr_fun hr ⟨_, I.2.comap

中文:
定理 toPiLocalization_not_surjective_of_infinite
  条件: [Infinite ι]
  证明: fun surj => by
  classical
  have ⟨J, max, notMem⟩ := PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite R
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max⟩ 1)
have : r = 0 := funext fun i => toPiLocalization_injective _ funext fun I => by
    replace hr := congr_fun hr ⟨_, I.2.comap

Depends on / 依赖: AtPrime, Function, Function.update, Function.update_of_ne, Localization, Localization.AtPrime.mapPiEvalRingHom_algebraMap_apply, PrimeSpectrum, PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite, Subtype, Subtype.coe_mk, classical, coe_mk, comap_piEvalRingHom, congr_fun, exists_maximal_notMem_range_sigmaToPi_of_infinite, mapPiEvalRingHom_algebraMap_apply, notMem, replace, simp_rw, toPiLocalization_apply_apply
-/
theorem toPiLocalization_not_surjective_of_infinite [Infinite ι] :
    ¬ Function.Surjective (toPiLocalization (Π i, R i)) := fun surj => by
  classical
  have ⟨J, max, notMem⟩ := PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite R
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max⟩ 1)
have : r = 0 := funext fun i => toPiLocalization_injective _ funext fun I => by
    replace hr := congr_fun hr ⟨_, I.2.comap_piEvalRingHom⟩
    dsimp only [toPiLocalization_apply_apply, Subtype.coe_mk] at hr
    simp_rw [toPiLocalization_apply_apply,
      ← Localization.AtPrime.mapPiEvalRingHom_algebraMap_apply, hr]
    rw [Function.update_of_ne]; · simp_rw [Pi.zero_apply, map_zero]
    exact fun h => notMem ⟨⟨i, I.1, I.2.isPrime⟩, PrimeSpectrum.ext congr($h.1)⟩
  replace hr := congr_fun hr ⟨J, max⟩
  rw [this]; rw [map_zero]; rw [Function.update_self] at hr
  exact zero_ne_one hr

variable {R}

/--
theorem `finite_of_toPiLocalization_pi_surjective` / 定理 `finite_of_toPiLocalization_pi_surjective`

English:
theorem finite_of_toPiLocalization_pi_surjective
  proof: by
  contrapose! h
  exact toPiLocalization_not_surjective_of_infinite _

中文:
定理 finite_of_toPiLocalization_pi_surjective
  证明: by
  contrapose! h
  exact toPiLocalization_not_surjective_of_infinite _

Depends on / 依赖: contrapose, toPiLocalization_not_surjective_of_infinite
-/
theorem finite_of_toPiLocalization_pi_surjective
    (h : Function.Surjective (toPiLocalization (Π i, R i))) :
    Finite ι := by
  contrapose! h
  exact toPiLocalization_not_surjective_of_infinite _

end Pi

set_option backward.isDefEq.respectTransparency false in
/--
theorem `finite_of_toPiLocalization_surjective` / 定理 `finite_of_toPiLocalization_surjective`

English:
theorem finite_of_toPiLocalization_surjective
  proof: by
  replace surj := mapPiLocalization_bijective _ ⟨toPiLocalization_injective R, surj⟩
.2.comp surj
  rw [← AlgHom.coe_toRingHom]; rw [← RingHom.coe_comp]; rw [mapPiLocalization_naturality]; rw [RingHom.coe_comp] at surj
  exact finite_of_toPiLocalization_pi_surjective surj.of_comp

中文:
定理 finite_of_toPiLocalization_surjective
  证明: by
  replace surj := mapPiLocalization_bijective _ ⟨toPiLocalization_injective R, surj⟩
.2.comp surj
  rw [← AlgHom.coe_toRingHom]; rw [← RingHom.coe_comp]; rw [mapPiLocalization_naturality]; rw [RingHom.coe_comp] at surj
  exact finite_of_toPiLocalization_pi_surjective surj.of_comp

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, RingHom, RingHom.coe_comp, coe_comp, coe_toRingHom, finite_of_toPiLocalization_pi_surjective, mapPiLocalization_bijective, mapPiLocalization_naturality, of_comp, replace, surj.of_comp, toPiLocalization_injective
-/
theorem finite_of_toPiLocalization_surjective
    (surj : Function.Surjective (toPiLocalization R)) :
    Finite (MaximalSpectrum R) := by
  replace surj := mapPiLocalization_bijective _ ⟨toPiLocalization_injective R, surj⟩
.2.comp surj
  rw [← AlgHom.coe_toRingHom]; rw [← RingHom.coe_comp]; rw [mapPiLocalization_naturality]; rw [RingHom.coe_comp] at surj
  exact finite_of_toPiLocalization_pi_surjective surj.of_comp

end MaximalSpectrum

namespace PrimeSpectrum

/--
Definition of `PiLocalization` / `PiLocalization` 的定义

English:
abbreviation PiLocalization
  signature: : Type _
  body: Π p : PrimeSpectrum R, Localization p.asIdeal.primeCompl

中文:
缩写 PiLocalization
  签名: : Type _
  定义体: Π p : PrimeSpectrum R, Localization p.asIdeal.primeCompl

Depends on / 依赖: Localization, PrimeSpectrum, asIdeal, p.asIdeal.primeCompl, primeCompl
-/
abbrev PiLocalization : Type _ := Π p : PrimeSpectrum R, Localization p.asIdeal.primeCompl

/--
Definition of `toPiLocalization` / `toPiLocalization` 的定义

English:
definition toPiLocalization
  signature: : R ->ₐ[R] PiLocalization R
  body: Algebra.ofId R (PiLocalization R)

中文:
定义 toPiLocalization
  签名: : R ->ₐ[R] PiLocalization R
  定义体: Algebra.ofId R (PiLocalization R)

Depends on / 依赖: Algebra, Algebra.ofId, PiLocalization
-/
def toPiLocalization : R ->ₐ[R] PiLocalization R := Algebra.ofId R (PiLocalization R)

/--
theorem `toPiLocalization_injective` / 定理 `toPiLocalization_injective`

English:
theorem toPiLocalization_injective
  statement: Function.Injective (toPiLocalization R)
  proof: fun _ _ eq => MaximalSpectrum.toPiLocalization_injective R
    funext fun I => congr_fun eq I.toPrimeSpectrum

中文:
定理 toPiLocalization_injective
  结论: Function.Injective (toPiLocalization R)
  证明: fun _ _ eq => MaximalSpectrum.toPiLocalization_injective R
    funext fun I => congr_fun eq I.toPrimeSpectrum

Depends on / 依赖: I.toPrimeSpectrum, MaximalSpectrum, MaximalSpectrum.toPiLocalization_injective, congr_fun, toPiLocalization_injective, toPrimeSpectrum
-/
theorem toPiLocalization_injective : Function.Injective (toPiLocalization R) :=
fun _ _ eq => MaximalSpectrum.toPiLocalization_injective R
    funext fun I => congr_fun eq I.toPrimeSpectrum

/--
Definition of `piLocalizationToMaximal` / `piLocalizationToMaximal` 的定义

English:
definition piLocalizationToMaximal
  signature: : PiLocalization R ->ₐ[R] MaximalSpectrum.PiLocalization R
  body: AlgHom.pi fun I => Pi.evalAlgHom _ _ I.toPrimeSpectrum

中文:
定义 piLocalizationToMaximal
  签名: : PiLocalization R ->ₐ[R] MaximalSpectrum.PiLocalization R
  定义体: AlgHom.pi fun I => Pi.evalAlgHom _ _ I.toPrimeSpectrum

Depends on / 依赖: AlgHom, AlgHom.pi, I.toPrimeSpectrum, Pi.evalAlgHom, evalAlgHom, toPrimeSpectrum
-/
def piLocalizationToMaximal : PiLocalization R ->ₐ[R] MaximalSpectrum.PiLocalization R :=
  AlgHom.pi fun I => Pi.evalAlgHom _ _ I.toPrimeSpectrum

/--
theorem `piLocalizationToMaximal_surjective` / 定理 `piLocalizationToMaximal_surjective`

English:
theorem piLocalizationToMaximal_surjective
  statement: Function.Surjective (piLocalizationToMaximal R)
  proof: by
  classical
  exact fun r => ⟨fun I => if h : I.1.IsMaximal then r ⟨_, h⟩ else 0, funext fun _ => dif_pos _⟩

中文:
定理 piLocalizationToMaximal_surjective
  结论: Function.Surjective (piLocalizationToMaximal R)
  证明: by
  classical
  exact fun r => ⟨fun I => if h : I.1.IsMaximal then r ⟨_, h⟩ else 0, funext fun _ => dif_pos _⟩

Depends on / 依赖: IsMaximal, classical, dif_pos
-/
theorem piLocalizationToMaximal_surjective : Function.Surjective (piLocalizationToMaximal R) := by
  classical
  exact fun r => ⟨fun I => if h : I.1.IsMaximal then r ⟨_, h⟩ else 0, funext fun _ => dif_pos _⟩

variable {R}

/--
Definition of `piLocalizationToMaximalEquiv` / `piLocalizationToMaximalEquiv` 的定义

English:
definition piLocalizationToMaximalEquiv
  signature: (h : forall I : Ideal R, I.IsPrime -> I.IsMaximal)
  body: piLocalizationToMaximal R
  invFun := RingHom.pi fun I => Pi.evalRingHom _ (⟨_, h _ I.2⟩ : MaximalSpectrum R)

中文:
定义 piLocalizationToMaximalEquiv
  签名: (h : 对任意 I : Ideal R, I.IsPrime -> I.IsMaximal)
  定义体: piLocalizationToMaximal R
  invFun := RingHom.pi fun I => Pi.evalRingHom _ (⟨_, h _ I.2⟩ : MaximalSpectrum R)

Depends on / 依赖: piLocalizationToMaximal
-/
def piLocalizationToMaximalEquiv (h : forall I : Ideal R, I.IsPrime -> I.IsMaximal) :
    PiLocalization R ≃+* MaximalSpectrum.PiLocalization R where
  __ := piLocalizationToMaximal R
  invFun := RingHom.pi fun I => Pi.evalRingHom _ (⟨_, h _ I.2⟩ : MaximalSpectrum R)

/--
theorem `piLocalizationToMaximal_bijective` / 定理 `piLocalizationToMaximal_bijective`

English:
theorem piLocalizationToMaximal_bijective
  given: (h : forall I : Ideal R, I.IsPrime -> I.IsMaximal)
  proof: (piLocalizationToMaximalEquiv h).bijective

中文:
定理 piLocalizationToMaximal_bijective
  条件: (h : 对任意 I : Ideal R, I.IsPrime -> I.IsMaximal)
  证明: (piLocalizationToMaximalEquiv h).bijective

Depends on / 依赖: bijective, piLocalizationToMaximalEquiv
-/
theorem piLocalizationToMaximal_bijective (h : forall I : Ideal R, I.IsPrime -> I.IsMaximal) :
    Function.Bijective (piLocalizationToMaximal R) :=
  (piLocalizationToMaximalEquiv h).bijective

/--
theorem `piLocalizationToMaximal_comp_toPiLocalization` / 定理 `piLocalizationToMaximal_comp_toPiLocalization`

English:
theorem piLocalizationToMaximal_comp_toPiLocalization
  proof: rfl

中文:
定理 piLocalizationToMaximal_comp_toPiLocalization
  证明: rfl

Depends on / 依赖: PreirreducibleSpace, PreirreducibleSpace.preconnectedSpace, TopologicalSpace, preconnectedSpace
-/
theorem piLocalizationToMaximal_comp_toPiLocalization :
    (piLocalizationToMaximal R).comp (toPiLocalization R) = MaximalSpectrum.toPiLocalization R :=
  rfl

variable {S}

/--
theorem `isMaximal_of_toPiLocalization_surjective` / 定理 `isMaximal_of_toPiLocalization_surjective`

English:
theorem isMaximal_of_toPiLocalization_surjective
  statement: (surj : Function.Surjective (toPiLocalization R))
  proof: by
  classical
  have ⟨J, max, le⟩ := I.1.exists_le_maximal I.2.ne_top
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max.isPrime⟩ 1)
  by_contra h
  have hJ : algebraMap _ _ r = _ := (congr_fun hr _).trans (Function.update_self ..)
  have hI : algebraMap _ _ r = _ := congr_fun hr I
  rw [← IsLocal

中文:
定理 isMaximal_of_toPiLocalization_surjective
  结论: (surj : Function.Surjective (toPiLocalization R))
  证明: by
  classical
  have ⟨J, max, le⟩ := I.1.exists_le_maximal I.2.ne_top
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max.isPrime⟩ 1)
  by_contra h
  have hJ : algebraMap _ _ r = _ := (congr_fun hr _).trans (Function.update_self ..)
  have hI : algebraMap _ _ r = _ := congr_fun hr I
  rw [← IsLocal

Depends on / 依赖: Function, Function.update, Function.update_of_ne, Function.update_self, IrreducibleSpace, IrreducibleSpace.connectedSpace, IsLocalization, IsLocalization.lift_eq, J.primeCompl, Localization, TopologicalSpace, algebraMap, classical, congr_arg, congr_fun, connectedSpace, exists_le_maximal, isPrime, lift_eq, map_one
-/
theorem isMaximal_of_toPiLocalization_surjective (surj : Function.Surjective (toPiLocalization R))
    (I : PrimeSpectrum R) : I.1.IsMaximal := by
  classical
  have ⟨J, max, le⟩ := I.1.exists_le_maximal I.2.ne_top
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max.isPrime⟩ 1)
  by_contra h
  have hJ : algebraMap _ _ r = _ := (congr_fun hr _).trans (Function.update_self ..)
  have hI : algebraMap _ _ r = _ := congr_fun hr I
  rw [← IsLocalization.lift_eq (M := J.primeCompl) (S := Localization J.primeCompl)]; rw [hJ]; rw [map_one]; rw [Function.update_of_ne] at hI
  · exact one_ne_zero hI
  · intro eq; have : I.1 = J := congr_arg (·.1) eq; exact h (this ▸ max)
  · exact fun ⟨s, hs⟩ => IsLocalization.map_units (M := I.1.primeCompl) _ ⟨s, fun h => hs (le h)⟩

variable (f : R ->+* S)

/--
Definition of `mapPiLocalization` / `mapPiLocalization` 的定义

English:
definition mapPiLocalization
  signature: : PiLocalization R ->+* PiLocalization S
  body: RingHom.pi fun I => (Localization.localRingHom _ I.1 f rfl).comp (Pi.evalRingHom _ (comap f I))

中文:
定义 mapPiLocalization
  签名: : PiLocalization R ->+* PiLocalization S
  定义体: RingHom.pi fun I => (Localization.localRingHom _ I.1 f rfl).comp (Pi.evalRingHom _ (comap f I))

Depends on / 依赖: Localization, Localization.localRingHom, Pi.evalRingHom, RingHom, RingHom.pi, evalRingHom, localRingHom
-/
noncomputable def mapPiLocalization : PiLocalization R ->+* PiLocalization S :=
  RingHom.pi fun I => (Localization.localRingHom _ I.1 f rfl).comp (Pi.evalRingHom _ (comap f I))

/--
theorem `mapPiLocalization_naturality` / 定理 `mapPiLocalization_naturality`

English:
theorem mapPiLocalization_naturality
  proof: by
  ext r I
  change Localization.localRingHom _ _ _ rfl (algebraMap _ _ r) = algebraMap _ _ (f r)
  simp_rw [← IsLocalization.mk'_one (M := (I.1.comap f).primeCompl), Localization.localRingHom_mk',
    ← IsLocalization.mk'_one (M := I.1.primeCompl), Submonoid.coe_one, map_one f]
  rfl

中文:
定理 mapPiLocalization_naturality
  证明: by
  ext r I
  change Localization.localRingHom _ _ _ rfl (algebraMap _ _ r) = algebraMap _ _ (f r)
  simp_rw [← IsLocalization.mk'_one (M := (I.1.comap f).primeCompl), Localization.localRingHom_mk',
    ← IsLocalization.mk'_one (M := I.1.primeCompl), Submonoid.coe_one, map_one f]
  rfl

Depends on / 依赖: IsLocalization, IsLocalization.mk, Localization, Localization.localRingHom, Localization.localRingHom_mk, Submonoid, Submonoid.coe_one, _one, algebraMap, coe_one, localRingHom, localRingHom_mk, map_one, primeCompl, simp_rw
-/
theorem mapPiLocalization_naturality :
    (mapPiLocalization f).comp (toPiLocalization R) = (toPiLocalization S).toRingHom.comp f := by
  ext r I
  change Localization.localRingHom _ _ _ rfl (algebraMap _ _ r) = algebraMap _ _ (f r)
  simp_rw [← IsLocalization.mk'_one (M := (I.1.comap f).primeCompl), Localization.localRingHom_mk',
    ← IsLocalization.mk'_one (M := I.1.primeCompl), Submonoid.coe_one, map_one f]
  rfl

/--
theorem `mapPiLocalization_id` / 定理 `mapPiLocalization_id`

English:
theorem mapPiLocalization_id
  statement: mapPiLocalization (.id R) = .id _
  proof: by
  ext; exact congr($(Localization.localRingHom_id _) _)

中文:
定理 mapPiLocalization_id
  结论: mapPiLocalization (.id R) = .id _
  证明: by
  ext; exact congr($(Localization.localRingHom_id _) _)

Depends on / 依赖: Localization, Localization.localRingHom_id, localRingHom_id
-/
theorem mapPiLocalization_id : mapPiLocalization (.id R) = .id _ := by
  ext; exact congr($(Localization.localRingHom_id _) _)

/--
theorem `mapPiLocalization_comp` / 定理 `mapPiLocalization_comp`

English:
theorem mapPiLocalization_comp
  given: (g : S ->+* P)
  proof: by
  ext; exact congr($(Localization.localRingHom_comp _ _ _ _ rfl _ rfl) _)

中文:
定理 mapPiLocalization_comp
  条件: (g : S ->+* P)
  证明: by
  ext; exact congr($(Localization.localRingHom_comp _ _ _ _ rfl _ rfl) _)

Depends on / 依赖: Localization, Localization.localRingHom_comp, localRingHom_comp
-/
theorem mapPiLocalization_comp (g : S ->+* P) :
    mapPiLocalization (g.comp f) = (mapPiLocalization g).comp (mapPiLocalization f) := by
  ext; exact congr($(Localization.localRingHom_comp _ _ _ _ rfl _ rfl) _)

/--
theorem `mapPiLocalization_bijective` / 定理 `mapPiLocalization_bijective`

English:
theorem mapPiLocalization_bijective
  given: (hf : Function.Bijective f)
  proof: by
  let f := RingEquiv.ofBijective f hf
  let e := RingEquiv.ofRingHom (mapPiLocalization (f : R ->+* S)) (mapPiLocalization f.symm) ?_ ?_
  · exact e.bijective
  · rw [← mapPiLocalization_comp, RingEquiv.comp_symm, mapPiLocalization_id]
  · rw [← mapPiLocalization_comp, RingEquiv.symm_comp, mapPiL

中文:
定理 mapPiLocalization_bijective
  条件: (hf : Function.Bijective f)
  证明: by
  let f := RingEquiv.ofBijective f hf
  let e := RingEquiv.ofRingHom (mapPiLocalization (f : R ->+* S)) (mapPiLocalization f.symm) ?_ ?_
  · exact e.bijective
  · rw [← mapPiLocalization_comp, RingEquiv.comp_symm, mapPiLocalization_id]
  · rw [← mapPiLocalization_comp, RingEquiv.symm_comp, mapPiL

Depends on / 依赖: RingEquiv, RingEquiv.comp_symm, RingEquiv.ofBijective, RingEquiv.ofRingHom, RingEquiv.symm_comp, bijective, comp_symm, e.bijective, f.symm, mapPiLocalization, mapPiLocalization_comp, mapPiLocalization_id, ofBijective, ofRingHom, symm_comp
-/
theorem mapPiLocalization_bijective (hf : Function.Bijective f) :
    Function.Bijective (mapPiLocalization f) := by
  let f := RingEquiv.ofBijective f hf
  let e := RingEquiv.ofRingHom (mapPiLocalization (f : R ->+* S)) (mapPiLocalization f.symm) ?_ ?_
  · exact e.bijective
  · rw [← mapPiLocalization_comp, RingEquiv.comp_symm, mapPiLocalization_id]
  · rw [← mapPiLocalization_comp, RingEquiv.symm_comp, mapPiLocalization_id]

section Pi

variable {ι} (R : ι -> Type*) [forall i, CommSemiring (R i)] [forall i, Nontrivial (R i)]

/--
theorem `toPiLocalization_not_surjective_of_infinite` / 定理 `toPiLocalization_not_surjective_of_infinite`

English:
theorem toPiLocalization_not_surjective_of_infinite
  given: [Infinite ι]
  proof: fun surj => MaximalSpectrum.toPiLocalization_not_surjective_of_infinite R by
    rw [← AlgHom.coe_toRingHom]; rw [← piLocalizationToMaximal_comp_toPiLocalization]
    exact (piLocalizationToMaximal_surjective _).comp surj

中文:
定理 toPiLocalization_not_surjective_of_infinite
  条件: [Infinite ι]
  证明: fun surj => MaximalSpectrum.toPiLocalization_not_surjective_of_infinite R by
    rw [← AlgHom.coe_toRingHom]; rw [← piLocalizationToMaximal_comp_toPiLocalization]
    exact (piLocalizationToMaximal_surjective _).comp surj

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, MaximalSpectrum, MaximalSpectrum.toPiLocalization_not_surjective_of_infinite, coe_toRingHom, piLocalizationToMaximal_comp_toPiLocalization, piLocalizationToMaximal_surjective, toPiLocalization_not_surjective_of_infinite
-/
theorem toPiLocalization_not_surjective_of_infinite [Infinite ι] :
    ¬ Function.Surjective (toPiLocalization (Π i, R i)) :=
fun surj => MaximalSpectrum.toPiLocalization_not_surjective_of_infinite R by
    rw [← AlgHom.coe_toRingHom]; rw [← piLocalizationToMaximal_comp_toPiLocalization]
    exact (piLocalizationToMaximal_surjective _).comp surj

variable {R}

/--
theorem `finite_of_toPiLocalization_pi_surjective` / 定理 `finite_of_toPiLocalization_pi_surjective`

English:
theorem finite_of_toPiLocalization_pi_surjective
  proof: by
  contrapose! h
  exact toPiLocalization_not_surjective_of_infinite _

中文:
定理 finite_of_toPiLocalization_pi_surjective
  证明: by
  contrapose! h
  exact toPiLocalization_not_surjective_of_infinite _

Depends on / 依赖: contrapose, toPiLocalization_not_surjective_of_infinite
-/
theorem finite_of_toPiLocalization_pi_surjective
    (h : Function.Surjective (toPiLocalization (Π i, R i))) :
    Finite ι := by
  contrapose! h
  exact toPiLocalization_not_surjective_of_infinite _

end Pi

/--
theorem `finite_of_toPiLocalization_surjective` / 定理 `finite_of_toPiLocalization_surjective`

English:
theorem finite_of_toPiLocalization_surjective
  proof: by
  replace surj := (mapPiLocalization_bijective _ ⟨toPiLocalization_injective R, surj⟩).2.comp surj
  rw [← AlgHom.coe_toRingHom]; rw [← RingHom.coe_comp]; rw [mapPiLocalization_naturality]; rw [RingHom.coe_comp] at surj
  exact finite_of_toPiLocalization_pi_surjective surj.of_comp

中文:
定理 finite_of_toPiLocalization_surjective
  证明: by
  replace surj := (mapPiLocalization_bijective _ ⟨toPiLocalization_injective R, surj⟩).2.comp surj
  rw [← AlgHom.coe_toRingHom]; rw [← RingHom.coe_comp]; rw [mapPiLocalization_naturality]; rw [RingHom.coe_comp] at surj
  exact finite_of_toPiLocalization_pi_surjective surj.of_comp

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, RingHom, RingHom.coe_comp, coe_comp, coe_toRingHom, finite_of_toPiLocalization_pi_surjective, mapPiLocalization_bijective, mapPiLocalization_naturality, of_comp, replace, surj.of_comp, toPiLocalization_injective
-/
theorem finite_of_toPiLocalization_surjective
    (surj : Function.Surjective (toPiLocalization R)) :
    Finite (PrimeSpectrum R) := by
  replace surj := (mapPiLocalization_bijective _ ⟨toPiLocalization_injective R, surj⟩).2.comp surj
  rw [← AlgHom.coe_toRingHom]; rw [← RingHom.coe_comp]; rw [mapPiLocalization_naturality]; rw [RingHom.coe_comp] at surj
  exact finite_of_toPiLocalization_pi_surjective surj.of_comp

end PrimeSpectrum
