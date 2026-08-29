/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth

/-!

# Some lemmas about formally smooth under quotient

In this file, we formalize the result [Stacks 031L] : For flat ring homomorphism `f : R →+* S`,
`I` an ideal of `R` which is square zero, if `R ⧸ I →+* S ⧸ IS` is formally smooth, so is `f`.

-/

public section

open IsLocalRing

variable {R : Type*} [CommRing R]

/--
lemma `LinearMap.ker_inf_smul_top_eq_smul_of_flat` / 引理 `LinearMap.ker_inf_smul_top_eq_smul_of_flat`

English:
lemma LinearMap.ker_inf_smul_top_eq_smul_of_flat
  statement: {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  proof: by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rcases (Submodule.ext_iff.mp (I.subtype_rTensor_range M) x).mpr hx.2 with ⟨y, hy⟩
    have inj : Function.Injective ((TensorProduct.lid R N).comp (I.subtype.rTensor N)) := by
      simpa using Module.Flat.iff_rTensor_injective'.mp ‹_› I
    have comm1 : ((TensorProduct.lid R N).comp (I.subtype.rTensor N)).comp (f.lTensor I) =
      f.comp ((TensorProduct.lid R M).comp (I.subtype.rTensor M)) := by
      ext
      simp
    have eq0 : f.lTensor I y = 0 := by
      apply inj
      rw [map_zero]; rw [← LinearMap.comp_apply]; rw [comm1]; rw [LinearMap.comp_apply]; rw [hy]; rw [f.mem_ker.mp hx.1]
    rcases ((lTensor_exact I (f.exact_subtype_ker_map) surj) y).mp eq0 with ⟨z, hz⟩
    have comm2 : ((TensorProduct.lid R M).comp (I.subtype.rTensor M)).comp
      (f.ker.subtype.lTensor I) = f.ker.subtype.comp
      ((TensorProduct.lid R f.ker).comp (I.subtype.rTensor f.ker)) := by
      ext
      simp
    apply (Submodule.mem_smul_top_iff I f.ker ⟨x, hx.1⟩).mp
    rw [← Ideal.subtype_rTensor_range]
    use z
    apply f.ker.subtype_injective
    rw [← LinearMap.comp_apply]; rw [← comm2]; rw [LinearMap.comp_apply]; rw [hz]; rw [hy]; rw [Submodule.subtype_apply]
  · induction hx using Submodule.smul_induction_on' with
    | smul r hr m hm =>
      simpa [LinearMap.mem_ker.mp hm] using Submodule.smul_mem_smul hr Submodule.mem_top
    | add y ymem z zmem hy hz => exact add_mem hy hz

中文:
引理 线性映射.ker_inf_smul_top_eq_smul_of_flat
  结论: {M N : 类型} [加法交换群 M] [加法交换群 N]
  证明: by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rcases (Submodule.ext_iff.mp (I.subtype_rTensor_range M) x).mpr hx.2 with ⟨y, hy⟩
    have inj : Function.Injective ((TensorProduct.lid R N).comp (I.subtype.rTensor N)) := by
      simpa using Module.Flat.iff_rTensor_injective'.mp ‹_› I
    have comm1 : ((TensorProduct.lid R N).comp (I.subtype.rTensor N)).comp (f.lTensor I) =
      f.comp ((TensorProduct.lid R M).comp (I.subtype.rTensor M)) := by
      ext
      simp
    have eq0 : f.lTensor I y = 0 := by
      apply inj
      rw [map_zero]; rw [← LinearMap.comp_apply]; rw [comm1]; rw [LinearMap.comp_apply]; rw [hy]; rw [f.mem_ker.mp hx.1]
    rcases ((lTensor_exact I (f.exact_subtype_ker_map) surj) y).mp eq0 with ⟨z, hz⟩
    have comm2 : ((TensorProduct.lid R M).comp (I.subtype.rTensor M)).comp
      (f.ker.subtype.lTensor I) = f.ker.subtype.comp
      ((TensorProduct.lid R f.ker).comp (I.subtype.rTensor f.ker)) := by
      ext
      simp
    apply (Submodule.mem_smul_top_iff I f.ker ⟨x, hx.1⟩).mp
    rw [← Ideal.subtype_rTensor_range]
    use z
    apply f.ker.subtype_injective
    rw [← LinearMap.comp_apply]; rw [← comm2]; rw [LinearMap.comp_apply]; rw [hz]; rw [hy]; rw [Submodule.subtype_apply]
  · induction hx using Submodule.smul_induction_on' with
    | smul r hr m hm =>
      simpa [LinearMap.mem_ker.mp hm] using Submodule.smul_mem_smul hr Submodule.mem_top
    | add y ymem z zmem hy hz => exact add_mem hy hz

Depends on / 依赖: Function, Function.Injective, I.subtype.rTensor, I.subtype_rTensor_range, Injective, Module, Module.Flat.iff_rTensor_injective, Submodule, Submodule.ext_iff.mp, TensorProduct, TensorProduct.lid, ext_iff, f.comp, f.lTensor, iff_rTensor_injective, lTensor, le_antisymm, map_, rTensor, subtype
-/
lemma LinearMap.ker_inf_smul_top_eq_smul_of_flat {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (I : Ideal R) (f : M ->ₗ[R] N) (surj : Function.Surjective f)
    [Module.Flat R N] : f.ker ⊓ (I • (⊤ : Submodule R M)) = I • f.ker := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rcases (Submodule.ext_iff.mp (I.subtype_rTensor_range M) x).mpr hx.2 with ⟨y, hy⟩
    have inj : Function.Injective ((TensorProduct.lid R N).comp (I.subtype.rTensor N)) := by
      simpa using Module.Flat.iff_rTensor_injective'.mp ‹_› I
    have comm1 : ((TensorProduct.lid R N).comp (I.subtype.rTensor N)).comp (f.lTensor I) =
      f.comp ((TensorProduct.lid R M).comp (I.subtype.rTensor M)) := by
      ext
      simp
    have eq0 : f.lTensor I y = 0 := by
      apply inj
      rw [map_zero]; rw [← LinearMap.comp_apply]; rw [comm1]; rw [LinearMap.comp_apply]; rw [hy]; rw [f.mem_ker.mp hx.1]
    rcases ((lTensor_exact I (f.exact_subtype_ker_map) surj) y).mp eq0 with ⟨z, hz⟩
    have comm2 : ((TensorProduct.lid R M).comp (I.subtype.rTensor M)).comp
      (f.ker.subtype.lTensor I) = f.ker.subtype.comp
      ((TensorProduct.lid R f.ker).comp (I.subtype.rTensor f.ker)) := by
      ext
      simp
    apply (Submodule.mem_smul_top_iff I f.ker ⟨x, hx.1⟩).mp
    rw [← Ideal.subtype_rTensor_range]
    use z
    apply f.ker.subtype_injective
    rw [← LinearMap.comp_apply]; rw [← comm2]; rw [LinearMap.comp_apply]; rw [hz]; rw [hy]; rw [Submodule.subtype_apply]
  · induction hx using Submodule.smul_induction_on' with
    | smul r hr m hm =>
      simpa [LinearMap.mem_ker.mp hm] using Submodule.smul_mem_smul hr Submodule.mem_top
    | add y ymem z zmem hy hz => exact add_mem hy hz

variable {S : Type*} [CommRing S] {R' S' : Type*} [CommRing R'] [CommRing S']

section

variable [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']

/--
lemma `comap_ker_eq_sup_of_ker_eq_map` / 引理 `comap_ker_eq_sup_of_ker_eq_map`

English:
lemma comap_ker_eq_sup_of_ker_eq_map
  statement: (surjRS : Function.Surjective (algebraMap R S))
  proof: by
  rw [RingHom.comap_ker]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq _ S]; rw [← RingHom.comap_ker]
  simp [eqmap, Ideal.comap_map_of_surjective' _ surjRS]

中文:
引理 comap_ker_eq_sup_of_ker_eq_map
  结论: (surjRS : 函数.满射 (algebraMap R S))
  证明: by
  rw [RingHom.comap_ker]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq _ S]; rw [← RingHom.comap_ker]
  simp [eqmap, Ideal.comap_map_of_surjective' _ surjRS]
-/
private lemma comap_ker_eq_sup_of_ker_eq_map (surjRS : Function.Surjective (algebraMap R S))
    (eqmap : RingHom.ker (algebraMap S S') = (RingHom.ker (algebraMap R R')).map (algebraMap R S)) :
    (RingHom.ker (algebraMap R' S')).comap (algebraMap R R') =
      RingHom.ker (algebraMap R R') ⊔ RingHom.ker (algebraMap R S) := by
  rw [RingHom.comap_ker]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq _ S]; rw [← RingHom.comap_ker]
  simp [eqmap, Ideal.comap_map_of_surjective' _ surjRS]

/--
lemma `mul_le_ker_of_range_le_mul_of_sq_zero` / 引理 `mul_le_ker_of_range_le_mul_of_sq_zero`

English:
lemma mul_le_ker_of_range_le_mul_of_sq_zero
  statement: {J I : Ideal R} (sq : I ^ 2 = ⊥)
  proof: by
  rw [pow_two] at sq
  have {x : R} (h : x in I * J) : f (J.toCotangent ⟨x, Ideal.mul_le_right h⟩) = 0 := by
    induction h using Submodule.mul_induction_on' with
    | mem_mul_mem y hy z hz =>
      rcases Submodule.mem_map.mp (le (f.mem_range_self (J.toCotangent ⟨z, hz⟩))) with ⟨w, hw, eqz⟩
      have mem_bot := Ideal.mul_mem_mul hy (Submodule.mem_comap.mp hw)
      simp only [← mul_assoc, sq, Submodule.bot_mul, Submodule.mem_bot] at mem_bot
      have eq0 : y • w = 0 := SetCoe.ext mem_bot
      have : ⟨y * z, Ideal.mul_le_right (Submodule.mul_mem_mul hy hz)⟩ = y • (⟨z, hz⟩ : J) := rfl
      rw [this]; rw [map_smul]; rw [map_smul]; rw [← eqz]; rw [← map_smul]; rw [eq0]; rw [map_zero]
    | add y ymem z zmem hy hz =>
      have : (⟨y + z, Ideal.mul_le_right (add_mem ymem zmem)⟩ : J) =
        ⟨y, Ideal.mul_le_right ymem⟩ + ⟨z, Ideal.mul_le_right zmem⟩ := rfl
      rw [this]; rw [map_add]; rw [map_add]; rw [hy]; rw [hz]; rw [add_zero]
  intro x hx
  rcases Submodule.mem_map.mp hx with ⟨x', hx', eq⟩
  simpa [← eq] using this hx'

中文:
引理 mul_le_ker_of_range_le_mul_of_sq_zero
  结论: {J I : 理想 R} (sq : I ^ 2 = ⊥)
  证明: by
  rw [pow_two] at sq
  have {x : R} (h : x in I * J) : f (J.toCotangent ⟨x, Ideal.mul_le_right h⟩) = 0 := by
    induction h using Submodule.mul_induction_on' with
    | mem_mul_mem y hy z hz =>
      rcases Submodule.mem_map.mp (le (f.mem_range_self (J.toCotangent ⟨z, hz⟩))) with ⟨w, hw, eqz⟩
      have mem_bot := Ideal.mul_mem_mul hy (Submodule.mem_comap.mp hw)
      simp only [← mul_assoc, sq, Submodule.bot_mul, Submodule.mem_bot] at mem_bot
      have eq0 : y • w = 0 := SetCoe.ext mem_bot
      have : ⟨y * z, Ideal.mul_le_right (Submodule.mul_mem_mul hy hz)⟩ = y • (⟨z, hz⟩ : J) := rfl
      rw [this]; rw [map_smul]; rw [map_smul]; rw [← eqz]; rw [← map_smul]; rw [eq0]; rw [map_zero]
    | add y ymem z zmem hy hz =>
      have : (⟨y + z, Ideal.mul_le_right (add_mem ymem zmem)⟩ : J) =
        ⟨y, Ideal.mul_le_right ymem⟩ + ⟨z, Ideal.mul_le_right zmem⟩ := rfl
      rw [this]; rw [map_add]; rw [map_add]; rw [hy]; rw [hz]; rw [add_zero]
  intro x hx
  rcases Submodule.mem_map.mp hx with ⟨x', hx', eq⟩
  simpa [← eq] using this hx'
-/
private lemma mul_le_ker_of_range_le_mul_of_sq_zero {J I : Ideal R} (sq : I ^ 2 = ⊥)
    (f : J.Cotangent ->ₗ[R] J.Cotangent)
    (le : f.range <= (Submodule.comap J.subtype (I * J)).map J.toCotangent) :
    (Submodule.comap J.subtype (I * J)).map J.toCotangent <= f.ker := by
  rw [pow_two] at sq
  have {x : R} (h : x in I * J) : f (J.toCotangent ⟨x, Ideal.mul_le_right h⟩) = 0 := by
    induction h using Submodule.mul_induction_on' with
    | mem_mul_mem y hy z hz =>
      rcases Submodule.mem_map.mp (le (f.mem_range_self (J.toCotangent ⟨z, hz⟩))) with ⟨w, hw, eqz⟩
      have mem_bot := Ideal.mul_mem_mul hy (Submodule.mem_comap.mp hw)
      simp only [← mul_assoc, sq, Submodule.bot_mul, Submodule.mem_bot] at mem_bot
      have eq0 : y • w = 0 := SetCoe.ext mem_bot
      have : ⟨y * z, Ideal.mul_le_right (Submodule.mul_mem_mul hy hz)⟩ = y • (⟨z, hz⟩ : J) := rfl
      rw [this]; rw [map_smul]; rw [map_smul]; rw [← eqz]; rw [← map_smul]; rw [eq0]; rw [map_zero]
    | add y ymem z zmem hy hz =>
      have : (⟨y + z, Ideal.mul_le_right (add_mem ymem zmem)⟩ : J) =
        ⟨y, Ideal.mul_le_right ymem⟩ + ⟨z, Ideal.mul_le_right zmem⟩ := rfl
      rw [this]; rw [map_add]; rw [map_add]; rw [hy]; rw [hz]; rw [add_zero]
  intro x hx
  rcases Submodule.mem_map.mp hx with ⟨x', hx', eq⟩
  simpa [← eq] using this hx'

set_option backward.isDefEq.respectTransparency.types false in
/-- For flat ring homomorphism `f : R →+* S`, `I` an ideal of `R` which is square zero,
if `R ⧸ I →+* S ⧸ IS` is formally smooth, so is `f`. -/
@[stacks 031L]
/--
lemma `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat` / 引理 `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat`

English:
lemma Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat
  statement: [Module.Flat R S]
  proof: by
  let P := (Algebra.Generators.self R S).toExtension
  let : Algebra.FormallySmooth R P.Ring := instFormallySmoothMvPolynomial S
  let IP := (RingHom.ker (algebraMap R R')).map (algebraMap R P.Ring)
  let Gen : Algebra.Generators R' S' S := {
    val := algebraMap S S'
    σ' := fun s' => MvPolynomial.X (Classical.choose (surjS s'))
    aeval_val_σ' s' := by simp [Classical.choose_spec (surjS s')] }
  let P' := Gen.toExtension
  let : Algebra.FormallySmooth R' P'.Ring := instFormallySmoothMvPolynomial S
  let : Algebra P.Ring P'.Ring := MvPolynomial.algebraMvPolynomial
  let : IsScalarTower R P.Ring P'.Ring :=
    IsScalarTower.of_algebraMap_eq (fun x => (MvPolynomial.map_C _ x).symm)
  algebraize [(algebraMap S S').comp (algebraMap P.Ring S)]
  have : IsScalarTower P.Ring P'.Ring S' := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    change (algebraMap S S') (MvPolynomial.aeval _root_.id x) =
      MvPolynomial.aeval Gen.val (MvPolynomial.map (algebraMap R R') x)
    rw [← MvPolynomial.aeval_algebraMap_apply]
    simp [MvPolynomial.aeval_map_algebraMap, Gen]
  let J := RingHom.ker (algebraMap P.Ring S)
  let J' := RingHom.ker (algebraMap P'.Ring S')
  let I := RingHom.ker (algebraMap R R')
  let IS := I.map (algebraMap R S)
  have kerS : RingHom.ker (algebraMap S S') = IS := eqmap
  let IP := I.map (algebraMap R P.Ring)
  have kerP : RingHom.ker (algebraMap P.Ring P'.Ring) = IP := MvPolynomial.ker_map _
  have surjPP' : Function.Surjective (algebraMap P.Ring P'.Ring) :=
    MvPolynomial.map_surjective _ surj
  have ISeq : IS = IP.map (algebraMap P.Ring S) := by
    simp [IP, IS, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  classical
  have surjP : Function.Surjective (algebraMap P.Ring S) := fun x => ⟨P.σ x, P.algebraMap_σ x⟩
  apply (Algebra.FormallySmooth.iff_split_injection surjP).mpr
  have surjP' : Function.Surjective (algebraMap P'.Ring S') := fun x => ⟨P'.σ x, P'.algebraMap_σ x⟩
  rcases (Algebra.FormallySmooth.iff_split_injection surjP').mp smoothq with ⟨σ, hσ⟩
  have infeq : IP ⊓ J = IP * J := by
    refine le_antisymm (fun x hx => ?_) Ideal.mul_le_inf
    have : x in I • (J.restrictScalars R) := by
      change x in I • (IsScalarTower.toAlgHom R P.Ring S).toLinearMap.ker
      rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat I _ surjP]
      simpa using! ⟨hx.2, hx.1⟩
    simpa [← Ideal.smul_restrictScalars I J, Submodule.restrictScalars_mem] using! this
  have h : J'.comap (algebraMap P.Ring P'.Ring) = RingHom.ker (algebraMap P.Ring P'.Ring) ⊔ J :=
    comap_ker_eq_sup_of_ker_eq_map surjP (by simp [kerP, ← ISeq, eqmap, IS, I])
  have Jle : J <= J'.comap (algebraMap P.Ring P'.Ring) := le_of_le_of_eq le_sup_right h.symm
  let mapcot := Ideal.mapCotangent J J' (Algebra.ofId P.Ring P'.Ring) Jle
  have cotsurj : Function.Surjective mapcot := Ideal.mapCotangent_surjective_of_comap_eq surjPP' h
  have cotker : LinearMap.ker mapcot = (Submodule.comap J.subtype (_ ⊓ J)).map J.toCotangent :=
    Ideal.mapCotangent_ker_of_surjective surjPP' h
  rw [kerP]; rw [infeq] at cotker
  let cottoTen := KaehlerDifferential.kerCotangentToTensor R P.Ring S
  let cottoTen' := KaehlerDifferential.kerCotangentToTensor R' P'.Ring S'
  let mapTen : TensorProduct P.Ring S Ω[P.Ring⁄R] ->ₗ[P.Ring]
    TensorProduct P'.Ring S' Ω[P'.Ring⁄R'] :=
    _root_.TensorProduct.lift ((((TensorProduct.mk P'.Ring S' Ω[P'.Ring⁄R']).restrictScalars₁₂
      P.Ring P.Ring).compl₂ (KaehlerDifferential.map R R' P.Ring P'.Ring)).comp
      (IsScalarTower.toAlgHom P.Ring S S').toLinearMap)
  have comm : (cottoTen'.restrictScalars P.Ring).comp mapcot = mapTen.comp cottoTen := by
    ext x
    rcases Ideal.toCotangent_surjective _ x with ⟨y, rfl⟩
    have : (KaehlerDifferential.kerToTensor R' P'.Ring S')
      ⟨(algebraMap P.Ring P'.Ring) y.1, Jle y.2⟩ =
      mapTen ((KaehlerDifferential.kerToTensor R P.Ring S) y) := by
      simp [KaehlerDifferential.kerToTensor, mapTen]
    simpa [mapcot] using! this
  let ediff : Ω[P.Ring⁄R] ≃ₗ[P.Ring] S ->₀ P.Ring := KaehlerDifferential.mvPolynomialEquiv R S
  let eTen : TensorProduct P.Ring S Ω[P.Ring⁄R] ≃ₗ[P.Ring] (S ->₀ S) :=
    ((ediff.lTensor S).trans (TensorProduct.finsuppRight P.Ring P.Ring _ _ S)).trans
    (Finsupp.mapRange.linearEquiv (_root_.TensorProduct.rid P.Ring _))
  let toJ'cot : (S ->₀ S) ->ₗ[P.Ring] J'.Cotangent :=
    ((σ.restrictScalars P.Ring).comp mapTen).comp eTen.symm.toLinearMap
  let eS : (P.Ring ⧸ J) ≃ₗ[P.Ring] S :=
    (Submodule.quotEquivOfEq _ _ rfl).trans
    ((Algebra.linearMap P.Ring S).quotKerEquivOfSurjective surjP)
  let toJcot : (S ->₀ S) ->ₗ[P.Ring] J.Cotangent :=
    Finsupp.lsum P.Ring (fun s => ((LinearMap.toSpanSingleton (P.Ring ⧸ J) J.Cotangent
      (Classical.choose (cotsurj (toJ'cot (Finsupp.single s 1))))).restrictScalars P.Ring).comp
        eS.symm.toLinearMap)
  have toJcot_spec : mapcot.comp toJcot = toJ'cot := by
    ext i s
    simp only [LinearMap.comp_assoc, toJcot, Finsupp.lsum_comp_lsingle]
    rcases Ideal.Quotient.mk_surjective (eS.symm s) with ⟨p, hp⟩
    have (x : J.Cotangent) : mapcot (eS.symm s • x) = p • mapcot x := hp ▸ map_smul mapcot p x
    have psmul : p • 1 = s := by simpa [Algebra.smul_def, eS] using! eS.eq_symm_apply.mp hp
    simp [this, Classical.choose_spec (cotsurj (toJ'cot (Finsupp.single i 1))), ← map_smul, psmul]
  let σ' := toJcot.comp eTen.toLinearMap
  have σ'_spec' : mapcot.comp σ' = (σ.restrictScalars P.Ring).comp mapTen := by
    simp only [← LinearMap.comp_assoc, toJcot_spec, σ']
    apply LinearMap.ext (fun x => ?_)
    exact ((σ.restrictScalars P.Ring).comp mapTen).congr_arg (eTen.symm_apply_apply x)
  have σ'_spec : mapcot.comp (σ'.comp cottoTen) = mapcot := by
    rw [← LinearMap.comp_assoc]; rw [σ'_spec']; rw [LinearMap.comp_assoc]; rw [← comm]; rw [← LinearMap.comp_assoc]; rw [← LinearMap.restrictScalars_comp]; rw [hσ]
    rfl
  let Δ : J.Cotangent ->ₗ[P.Ring] J.Cotangent := LinearMap.id - (σ'.comp cottoTen)
  have rΔle : Δ.range <= (Submodule.comap J.subtype (IP * J)).map J.toCotangent := by
    rintro x ⟨y, hy⟩
    simp only [← cotker, ← hy, LinearMap.mem_ker, Δ]
    rw [LinearMap.sub_apply]; rw [map_sub]; rw [LinearMap.id_apply]; rw [← LinearMap.comp_apply]; rw [σ'_spec]; rw [sub_self]
  have leΔk := mul_le_ker_of_range_le_mul_of_sq_zero (by simp [IP, ← Ideal.map_pow, I, sq0]) Δ rΔle
  let δ := (Submodule.liftQ _ Δ (le_of_eq_of_le cotker leΔk)).comp
    (mapcot.quotKerEquivOfSurjective cotsurj).symm.toLinearMap
  have δ_spec : δ.comp mapcot = Δ := by
    ext
    simp [δ]
  have : σ'.comp cottoTen + δ.comp ((σ.restrictScalars P.Ring).comp (mapTen.comp cottoTen)) =
    LinearMap.id := by
    rw [← comm]; rw [← LinearMap.comp_assoc mapcot]; rw [← LinearMap.restrictScalars_comp]; rw [hσ]
    exact add_eq_of_eq_sub' δ_spec
  exact ⟨σ' + (δ.comp (σ.restrictScalars P.Ring)).comp mapTen, this⟩

中文:
引理 代数.形式光滑.of_surjective_of_ker_eq_map_of_flat
  结论: [模.平坦 R S]
  证明: by
  let P := (Algebra.Generators.self R S).toExtension
  let : Algebra.FormallySmooth R P.Ring := instFormallySmoothMvPolynomial S
  let IP := (RingHom.ker (algebraMap R R')).map (algebraMap R P.Ring)
  let Gen : Algebra.Generators R' S' S := {
    val := algebraMap S S'
    σ' := fun s' => MvPolynomial.X (Classical.choose (surjS s'))
    aeval_val_σ' s' := by simp [Classical.choose_spec (surjS s')] }
  let P' := Gen.toExtension
  let : Algebra.FormallySmooth R' P'.Ring := instFormallySmoothMvPolynomial S
  let : Algebra P.Ring P'.Ring := MvPolynomial.algebraMvPolynomial
  let : IsScalarTower R P.Ring P'.Ring :=
    IsScalarTower.of_algebraMap_eq (fun x => (MvPolynomial.map_C _ x).symm)
  algebraize [(algebraMap S S').comp (algebraMap P.Ring S)]
  have : IsScalarTower P.Ring P'.Ring S' := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    change (algebraMap S S') (MvPolynomial.aeval _root_.id x) =
      MvPolynomial.aeval Gen.val (MvPolynomial.map (algebraMap R R') x)
    rw [← MvPolynomial.aeval_algebraMap_apply]
    simp [MvPolynomial.aeval_map_algebraMap, Gen]
  let J := RingHom.ker (algebraMap P.Ring S)
  let J' := RingHom.ker (algebraMap P'.Ring S')
  let I := RingHom.ker (algebraMap R R')
  let IS := I.map (algebraMap R S)
  have kerS : RingHom.ker (algebraMap S S') = IS := eqmap
  let IP := I.map (algebraMap R P.Ring)
  have kerP : RingHom.ker (algebraMap P.Ring P'.Ring) = IP := MvPolynomial.ker_map _
  have surjPP' : Function.Surjective (algebraMap P.Ring P'.Ring) :=
    MvPolynomial.map_surjective _ surj
  have ISeq : IS = IP.map (algebraMap P.Ring S) := by
    simp [IP, IS, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  classical
  have surjP : Function.Surjective (algebraMap P.Ring S) := fun x => ⟨P.σ x, P.algebraMap_σ x⟩
  apply (Algebra.FormallySmooth.iff_split_injection surjP).mpr
  have surjP' : Function.Surjective (algebraMap P'.Ring S') := fun x => ⟨P'.σ x, P'.algebraMap_σ x⟩
  rcases (Algebra.FormallySmooth.iff_split_injection surjP').mp smoothq with ⟨σ, hσ⟩
  have infeq : IP ⊓ J = IP * J := by
    refine le_antisymm (fun x hx => ?_) Ideal.mul_le_inf
    have : x in I • (J.restrictScalars R) := by
      change x in I • (IsScalarTower.toAlgHom R P.Ring S).toLinearMap.ker
      rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat I _ surjP]
      simpa using! ⟨hx.2, hx.1⟩
    simpa [← Ideal.smul_restrictScalars I J, Submodule.restrictScalars_mem] using! this
  have h : J'.comap (algebraMap P.Ring P'.Ring) = RingHom.ker (algebraMap P.Ring P'.Ring) ⊔ J :=
    comap_ker_eq_sup_of_ker_eq_map surjP (by simp [kerP, ← ISeq, eqmap, IS, I])
  have Jle : J <= J'.comap (algebraMap P.Ring P'.Ring) := le_of_le_of_eq le_sup_right h.symm
  let mapcot := Ideal.mapCotangent J J' (Algebra.ofId P.Ring P'.Ring) Jle
  have cotsurj : Function.Surjective mapcot := Ideal.mapCotangent_surjective_of_comap_eq surjPP' h
  have cotker : LinearMap.ker mapcot = (Submodule.comap J.subtype (_ ⊓ J)).map J.toCotangent :=
    Ideal.mapCotangent_ker_of_surjective surjPP' h
  rw [kerP]; rw [infeq] at cotker
  let cottoTen := KaehlerDifferential.kerCotangentToTensor R P.Ring S
  let cottoTen' := KaehlerDifferential.kerCotangentToTensor R' P'.Ring S'
  let mapTen : TensorProduct P.Ring S Ω[P.Ring⁄R] ->ₗ[P.Ring]
    TensorProduct P'.Ring S' Ω[P'.Ring⁄R'] :=
    _root_.TensorProduct.lift ((((TensorProduct.mk P'.Ring S' Ω[P'.Ring⁄R']).restrictScalars₁₂
      P.Ring P.Ring).compl₂ (KaehlerDifferential.map R R' P.Ring P'.Ring)).comp
      (IsScalarTower.toAlgHom P.Ring S S').toLinearMap)
  have comm : (cottoTen'.restrictScalars P.Ring).comp mapcot = mapTen.comp cottoTen := by
    ext x
    rcases Ideal.toCotangent_surjective _ x with ⟨y, rfl⟩
    have : (KaehlerDifferential.kerToTensor R' P'.Ring S')
      ⟨(algebraMap P.Ring P'.Ring) y.1, Jle y.2⟩ =
      mapTen ((KaehlerDifferential.kerToTensor R P.Ring S) y) := by
      simp [KaehlerDifferential.kerToTensor, mapTen]
    simpa [mapcot] using! this
  let ediff : Ω[P.Ring⁄R] ≃ₗ[P.Ring] S ->₀ P.Ring := KaehlerDifferential.mvPolynomialEquiv R S
  let eTen : TensorProduct P.Ring S Ω[P.Ring⁄R] ≃ₗ[P.Ring] (S ->₀ S) :=
    ((ediff.lTensor S).trans (TensorProduct.finsuppRight P.Ring P.Ring _ _ S)).trans
    (Finsupp.mapRange.linearEquiv (_root_.TensorProduct.rid P.Ring _))
  let toJ'cot : (S ->₀ S) ->ₗ[P.Ring] J'.Cotangent :=
    ((σ.restrictScalars P.Ring).comp mapTen).comp eTen.symm.toLinearMap
  let eS : (P.Ring ⧸ J) ≃ₗ[P.Ring] S :=
    (Submodule.quotEquivOfEq _ _ rfl).trans
    ((Algebra.linearMap P.Ring S).quotKerEquivOfSurjective surjP)
  let toJcot : (S ->₀ S) ->ₗ[P.Ring] J.Cotangent :=
    Finsupp.lsum P.Ring (fun s => ((LinearMap.toSpanSingleton (P.Ring ⧸ J) J.Cotangent
      (Classical.choose (cotsurj (toJ'cot (Finsupp.single s 1))))).restrictScalars P.Ring).comp
        eS.symm.toLinearMap)
  have toJcot_spec : mapcot.comp toJcot = toJ'cot := by
    ext i s
    simp only [LinearMap.comp_assoc, toJcot, Finsupp.lsum_comp_lsingle]
    rcases Ideal.Quotient.mk_surjective (eS.symm s) with ⟨p, hp⟩
    have (x : J.Cotangent) : mapcot (eS.symm s • x) = p • mapcot x := hp ▸ map_smul mapcot p x
    have psmul : p • 1 = s := by simpa [Algebra.smul_def, eS] using! eS.eq_symm_apply.mp hp
    simp [this, Classical.choose_spec (cotsurj (toJ'cot (Finsupp.single i 1))), ← map_smul, psmul]
  let σ' := toJcot.comp eTen.toLinearMap
  have σ'_spec' : mapcot.comp σ' = (σ.restrictScalars P.Ring).comp mapTen := by
    simp only [← LinearMap.comp_assoc, toJcot_spec, σ']
    apply LinearMap.ext (fun x => ?_)
    exact ((σ.restrictScalars P.Ring).comp mapTen).congr_arg (eTen.symm_apply_apply x)
  have σ'_spec : mapcot.comp (σ'.comp cottoTen) = mapcot := by
    rw [← LinearMap.comp_assoc]; rw [σ'_spec']; rw [LinearMap.comp_assoc]; rw [← comm]; rw [← LinearMap.comp_assoc]; rw [← LinearMap.restrictScalars_comp]; rw [hσ]
    rfl
  let Δ : J.Cotangent ->ₗ[P.Ring] J.Cotangent := LinearMap.id - (σ'.comp cottoTen)
  have rΔle : Δ.range <= (Submodule.comap J.subtype (IP * J)).map J.toCotangent := by
    rintro x ⟨y, hy⟩
    simp only [← cotker, ← hy, LinearMap.mem_ker, Δ]
    rw [LinearMap.sub_apply]; rw [map_sub]; rw [LinearMap.id_apply]; rw [← LinearMap.comp_apply]; rw [σ'_spec]; rw [sub_self]
  have leΔk := mul_le_ker_of_range_le_mul_of_sq_zero (by simp [IP, ← Ideal.map_pow, I, sq0]) Δ rΔle
  let δ := (Submodule.liftQ _ Δ (le_of_eq_of_le cotker leΔk)).comp
    (mapcot.quotKerEquivOfSurjective cotsurj).symm.toLinearMap
  have δ_spec : δ.comp mapcot = Δ := by
    ext
    simp [δ]
  have : σ'.comp cottoTen + δ.comp ((σ.restrictScalars P.Ring).comp (mapTen.comp cottoTen)) =
    LinearMap.id := by
    rw [← comm]; rw [← LinearMap.comp_assoc mapcot]; rw [← LinearMap.restrictScalars_comp]; rw [hσ]
    exact add_eq_of_eq_sub' δ_spec
  exact ⟨σ' + (δ.comp (σ.restrictScalars P.Ring)).comp mapTen, this⟩

Depends on / 依赖: Algebr, Algebra, Algebra.FormallySmooth, Algebra.Generators, Algebra.Generators.self, Classical, Classical.choose, Classical.choose_spec, FormallySmooth, Gen.toExtension, Generators, MvPolynomial, MvPolynomial.X, P.Ring, RingHom, RingHom.ker, algebraMap, choose_spec, instFormallySmoothMvPolynomial, toExtension
-/
lemma Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat [Module.Flat R S]
    (surj : Function.Surjective (algebraMap R R'))
    (surjS : Function.Surjective (algebraMap S S'))
    (eqmap : RingHom.ker (algebraMap S S') = (RingHom.ker (algebraMap R R')).map (algebraMap R S))
    (sq0 : (RingHom.ker (algebraMap R R')) ^ 2 = ⊥) (smoothq : Algebra.FormallySmooth R' S') :
    Algebra.FormallySmooth R S := by
  let P := (Algebra.Generators.self R S).toExtension
  let : Algebra.FormallySmooth R P.Ring := instFormallySmoothMvPolynomial S
  let IP := (RingHom.ker (algebraMap R R')).map (algebraMap R P.Ring)
  let Gen : Algebra.Generators R' S' S := {
    val := algebraMap S S'
    σ' := fun s' => MvPolynomial.X (Classical.choose (surjS s'))
    aeval_val_σ' s' := by simp [Classical.choose_spec (surjS s')] }
  let P' := Gen.toExtension
  let : Algebra.FormallySmooth R' P'.Ring := instFormallySmoothMvPolynomial S
  let : Algebra P.Ring P'.Ring := MvPolynomial.algebraMvPolynomial
  let : IsScalarTower R P.Ring P'.Ring :=
    IsScalarTower.of_algebraMap_eq (fun x => (MvPolynomial.map_C _ x).symm)
  algebraize [(algebraMap S S').comp (algebraMap P.Ring S)]
  have : IsScalarTower P.Ring P'.Ring S' := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    change (algebraMap S S') (MvPolynomial.aeval _root_.id x) =
      MvPolynomial.aeval Gen.val (MvPolynomial.map (algebraMap R R') x)
    rw [← MvPolynomial.aeval_algebraMap_apply]
    simp [MvPolynomial.aeval_map_algebraMap, Gen]
  let J := RingHom.ker (algebraMap P.Ring S)
  let J' := RingHom.ker (algebraMap P'.Ring S')
  let I := RingHom.ker (algebraMap R R')
  let IS := I.map (algebraMap R S)
  have kerS : RingHom.ker (algebraMap S S') = IS := eqmap
  let IP := I.map (algebraMap R P.Ring)
  have kerP : RingHom.ker (algebraMap P.Ring P'.Ring) = IP := MvPolynomial.ker_map _
  have surjPP' : Function.Surjective (algebraMap P.Ring P'.Ring) :=
    MvPolynomial.map_surjective _ surj
  have ISeq : IS = IP.map (algebraMap P.Ring S) := by
    simp [IP, IS, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  classical
  have surjP : Function.Surjective (algebraMap P.Ring S) := fun x => ⟨P.σ x, P.algebraMap_σ x⟩
  apply (Algebra.FormallySmooth.iff_split_injection surjP).mpr
  have surjP' : Function.Surjective (algebraMap P'.Ring S') := fun x => ⟨P'.σ x, P'.algebraMap_σ x⟩
  rcases (Algebra.FormallySmooth.iff_split_injection surjP').mp smoothq with ⟨σ, hσ⟩
  have infeq : IP ⊓ J = IP * J := by
    refine le_antisymm (fun x hx => ?_) Ideal.mul_le_inf
    have : x in I • (J.restrictScalars R) := by
      change x in I • (IsScalarTower.toAlgHom R P.Ring S).toLinearMap.ker
      rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat I _ surjP]
      simpa using! ⟨hx.2, hx.1⟩
    simpa [← Ideal.smul_restrictScalars I J, Submodule.restrictScalars_mem] using! this
  have h : J'.comap (algebraMap P.Ring P'.Ring) = RingHom.ker (algebraMap P.Ring P'.Ring) ⊔ J :=
    comap_ker_eq_sup_of_ker_eq_map surjP (by simp [kerP, ← ISeq, eqmap, IS, I])
  have Jle : J <= J'.comap (algebraMap P.Ring P'.Ring) := le_of_le_of_eq le_sup_right h.symm
  let mapcot := Ideal.mapCotangent J J' (Algebra.ofId P.Ring P'.Ring) Jle
  have cotsurj : Function.Surjective mapcot := Ideal.mapCotangent_surjective_of_comap_eq surjPP' h
  have cotker : LinearMap.ker mapcot = (Submodule.comap J.subtype (_ ⊓ J)).map J.toCotangent :=
    Ideal.mapCotangent_ker_of_surjective surjPP' h
  rw [kerP]; rw [infeq] at cotker
  let cottoTen := KaehlerDifferential.kerCotangentToTensor R P.Ring S
  let cottoTen' := KaehlerDifferential.kerCotangentToTensor R' P'.Ring S'
  let mapTen : TensorProduct P.Ring S Ω[P.Ring⁄R] ->ₗ[P.Ring]
    TensorProduct P'.Ring S' Ω[P'.Ring⁄R'] :=
    _root_.TensorProduct.lift ((((TensorProduct.mk P'.Ring S' Ω[P'.Ring⁄R']).restrictScalars₁₂
      P.Ring P.Ring).compl₂ (KaehlerDifferential.map R R' P.Ring P'.Ring)).comp
      (IsScalarTower.toAlgHom P.Ring S S').toLinearMap)
  have comm : (cottoTen'.restrictScalars P.Ring).comp mapcot = mapTen.comp cottoTen := by
    ext x
    rcases Ideal.toCotangent_surjective _ x with ⟨y, rfl⟩
    have : (KaehlerDifferential.kerToTensor R' P'.Ring S')
      ⟨(algebraMap P.Ring P'.Ring) y.1, Jle y.2⟩ =
      mapTen ((KaehlerDifferential.kerToTensor R P.Ring S) y) := by
      simp [KaehlerDifferential.kerToTensor, mapTen]
    simpa [mapcot] using! this
  let ediff : Ω[P.Ring⁄R] ≃ₗ[P.Ring] S ->₀ P.Ring := KaehlerDifferential.mvPolynomialEquiv R S
  let eTen : TensorProduct P.Ring S Ω[P.Ring⁄R] ≃ₗ[P.Ring] (S ->₀ S) :=
    ((ediff.lTensor S).trans (TensorProduct.finsuppRight P.Ring P.Ring _ _ S)).trans
    (Finsupp.mapRange.linearEquiv (_root_.TensorProduct.rid P.Ring _))
  let toJ'cot : (S ->₀ S) ->ₗ[P.Ring] J'.Cotangent :=
    ((σ.restrictScalars P.Ring).comp mapTen).comp eTen.symm.toLinearMap
  let eS : (P.Ring ⧸ J) ≃ₗ[P.Ring] S :=
    (Submodule.quotEquivOfEq _ _ rfl).trans
    ((Algebra.linearMap P.Ring S).quotKerEquivOfSurjective surjP)
  let toJcot : (S ->₀ S) ->ₗ[P.Ring] J.Cotangent :=
    Finsupp.lsum P.Ring (fun s => ((LinearMap.toSpanSingleton (P.Ring ⧸ J) J.Cotangent
      (Classical.choose (cotsurj (toJ'cot (Finsupp.single s 1))))).restrictScalars P.Ring).comp
        eS.symm.toLinearMap)
  have toJcot_spec : mapcot.comp toJcot = toJ'cot := by
    ext i s
    simp only [LinearMap.comp_assoc, toJcot, Finsupp.lsum_comp_lsingle]
    rcases Ideal.Quotient.mk_surjective (eS.symm s) with ⟨p, hp⟩
    have (x : J.Cotangent) : mapcot (eS.symm s • x) = p • mapcot x := hp ▸ map_smul mapcot p x
    have psmul : p • 1 = s := by simpa [Algebra.smul_def, eS] using! eS.eq_symm_apply.mp hp
    simp [this, Classical.choose_spec (cotsurj (toJ'cot (Finsupp.single i 1))), ← map_smul, psmul]
  let σ' := toJcot.comp eTen.toLinearMap
  have σ'_spec' : mapcot.comp σ' = (σ.restrictScalars P.Ring).comp mapTen := by
    simp only [← LinearMap.comp_assoc, toJcot_spec, σ']
    apply LinearMap.ext (fun x => ?_)
    exact ((σ.restrictScalars P.Ring).comp mapTen).congr_arg (eTen.symm_apply_apply x)
  have σ'_spec : mapcot.comp (σ'.comp cottoTen) = mapcot := by
    rw [← LinearMap.comp_assoc]; rw [σ'_spec']; rw [LinearMap.comp_assoc]; rw [← comm]; rw [← LinearMap.comp_assoc]; rw [← LinearMap.restrictScalars_comp]; rw [hσ]
    rfl
  let Δ : J.Cotangent ->ₗ[P.Ring] J.Cotangent := LinearMap.id - (σ'.comp cottoTen)
  have rΔle : Δ.range <= (Submodule.comap J.subtype (IP * J)).map J.toCotangent := by
    rintro x ⟨y, hy⟩
    simp only [← cotker, ← hy, LinearMap.mem_ker, Δ]
    rw [LinearMap.sub_apply]; rw [map_sub]; rw [LinearMap.id_apply]; rw [← LinearMap.comp_apply]; rw [σ'_spec]; rw [sub_self]
  have leΔk := mul_le_ker_of_range_le_mul_of_sq_zero (by simp [IP, ← Ideal.map_pow, I, sq0]) Δ rΔle
  let δ := (Submodule.liftQ _ Δ (le_of_eq_of_le cotker leΔk)).comp
    (mapcot.quotKerEquivOfSurjective cotsurj).symm.toLinearMap
  have δ_spec : δ.comp mapcot = Δ := by
    ext
    simp [δ]
  have : σ'.comp cottoTen + δ.comp ((σ.restrictScalars P.Ring).comp (mapTen.comp cottoTen)) =
    LinearMap.id := by
    rw [← comm]; rw [← LinearMap.comp_assoc mapcot]; rw [← LinearMap.restrictScalars_comp]; rw [hσ]
    exact add_eq_of_eq_sub' δ_spec
  exact ⟨σ' + (δ.comp (σ.restrictScalars P.Ring)).comp mapTen, this⟩

end

/--
lemma `RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero` / 引理 `RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero`

English:
lemma RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero
  statement: (f : R ->+* S) (flat : f.Flat)
  proof: by
  algebraize [f, qR, qS, g, qS.comp f]
  let _ : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' comm
  exact Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat surjR surjS eqmap sq0 ‹_›

中文:
引理 环态射.形式光滑.of_flat_of_ker_eq_map_of_square_zero
  结论: (f : R ->+* S) (flat : f.平坦)
  证明: by
  algebraize [f, qR, qS, g, qS.comp f]
  let _ : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' comm
  exact Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat surjR surjS eqmap sq0 ‹_›

Depends on / 依赖: Algebra, Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat, FormallySmooth, IsScalarTower, IsScalarTower.of_algebraMap_eq, algebraize, of_algebraMap_eq, of_surjective_of_ker_eq_map_of_flat, qS.comp
-/
lemma RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero (f : R ->+* S) (flat : f.Flat)
    (qR : R ->+* R') (qS : S ->+* S') (g : R' ->+* S') (surjR : Function.Surjective qR)
    (surjS : Function.Surjective qS) (comm : qS.comp f = g.comp qR)
    (sq0 : (RingHom.ker qR) ^ 2 = ⊥) (eqmap : RingHom.ker qS = (RingHom.ker qR).map f)
    (smoothq : g.FormallySmooth) : f.FormallySmooth := by
  algebraize [f, qR, qS, g, qS.comp f]
  let _ : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' comm
  exact Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat surjR surjS eqmap sq0 ‹_›
