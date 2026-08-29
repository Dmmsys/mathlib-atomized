/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.DedekindDomain.LinearDisjoint
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!

# (Absolute) Discriminant and Different Ideal

## Main results
- `NumberField.absNorm_differentIdeal`:
  The norm of `differentIdeal ℤ 𝒪` is the absolute discriminant.
- `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`:
  Formula for the absolute discriminant of `L` in terms of that of `K` in an extension `L/K`.
- `NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow`:
  Assume that `K₁` and `K₂` are two linear disjoint number fields with coprime different ideals.
  Then, the absolute value of the discriminant of their compositum is equal to
  `|discr K₁| ^ [K₂ : ℚ] * |discr K₂| ^ [K₁ : ℚ]`.

-/

public section

namespace NumberField

variable (K 𝒪 : Type*) [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]

open IntermediateField IsDedekindDomain

section

variable [IsFractionRing 𝒪 K] [IsDedekindDomain 𝒪] [CharZero 𝒪]
variable [Module.Finite Int 𝒪]

open nonZeroDivisors IntermediateField Module

/--
lemma `absNorm_differentIdeal` / 引理 `absNorm_differentIdeal`

English:
lemma absNorm_differentIdeal
  statement: (differentIdeal Int 𝒪).absNorm = (discr K).natAbs
  proof: by
  refine (differentIdeal Int 𝒪).toAddSubgroup.relIndex_top_right.symm.trans ?_
  rw [← Submodule.comap_map_eq_of_injective (f := Algebra.linearMap 𝒪 K)
    (FaithfulSMul.algebraMap_injective 𝒪 K) (differentIdeal Int 𝒪)]
  refine (AddSubgroup.relIndex_comap (IsLocalization.coeSubmodule K
    (diff

中文:
引理 absNorm_differentIdeal
  结论: (differentIdeal 整数 𝒪).absNorm = (discr K).natAbs
  证明: by
  refine (differentIdeal Int 𝒪).toAddSubgroup.relIndex_top_right.symm.trans ?_
  rw [← Submodule.comap_map_eq_of_injective (f := Algebra.linearMap 𝒪 K)
    (FaithfulSMul.algebraMap_injective 𝒪 K) (differentIdeal Int 𝒪)]
  refine (AddSubgroup.relIndex_comap (IsLocalization.coeSubmodule K
    (diff

Depends on / 依赖: AddSubgroup, AddSubgroup.relIndex_comap, Algebra, Algebra.linearMap, FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionalIdeal, FractionalIdeal.quotientEquiv, IsLocalization, IsLocalization.coeSubmodule, Submodule, Submodule.comap_map_eq_of_injective, algebraMap, algebraMap_injective, coeSubmodule, comap_map_eq_of_injective, differentIdeal, differentIdeal_ne_b, linearMap, quotientEquiv
-/
lemma absNorm_differentIdeal : (differentIdeal Int 𝒪).absNorm = (discr K).natAbs := by
  refine (differentIdeal Int 𝒪).toAddSubgroup.relIndex_top_right.symm.trans ?_
  rw [← Submodule.comap_map_eq_of_injective (f := Algebra.linearMap 𝒪 K)
    (FaithfulSMul.algebraMap_injective 𝒪 K) (differentIdeal Int 𝒪)]
  refine (AddSubgroup.relIndex_comap (IsLocalization.coeSubmodule K
    (differentIdeal Int 𝒪)).toAddSubgroup (algebraMap 𝒪 K).toAddMonoidHom ⊤).trans ?_
  have := FractionalIdeal.quotientEquiv (R := 𝒪) (K := K) 1 (differentIdeal Int 𝒪)
    (differentIdeal Int 𝒪)⁻¹ 1 (by simp [differentIdeal_ne_bot]) FractionalIdeal.coeIdeal_le_one
    (le_inv_of_le_inv₀ (by simp [pos_iff_ne_zero, differentIdeal_ne_bot])
      (by simpa using FractionalIdeal.coeIdeal_le_one)) one_ne_zero one_ne_zero
  have := Nat.card_congr this.toEquiv
  refine this.trans ?_
  rw [FractionalIdeal.coe_one]; rw [coeIdeal_differentIdeal (K := Rat)]; rw [inv_inv]
  let b := integralBasis K
  let b' := (Algebra.traceForm Rat K).dualBasis (traceForm_nondegenerate Rat K) b
  have hb : Submodule.span Int (Set.range b) = (1 : Submodule 𝒪 K).restrictScalars Int := by
    ext
    let e := IsIntegralClosure.equiv Int (RingOfIntegers K) K 𝒪
    simpa [e.symm.exists_congr_left, e] using mem_span_integralBasis K
  qify
  refine (AddSubgroup.relIndex_eq_abs_det (1 : Submodule 𝒪 K).toAddSubgroup (FractionalIdeal.dual
    Int Rat 1 : FractionalIdeal 𝒪⁰ K).coeToSubmodule.toAddSubgroup ?_ b b' ?_ ?_).trans ?_
  · rw [Submodule.toAddSubgroup_le, ← FractionalIdeal.coe_one]
    exact FractionalIdeal.one_le_dual_one Int Rat (L := K) (B := 𝒪)
  · apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure]; rw [hb]; rw [Submodule.toIntSubmodule_toAddSubgroup]
  · apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure]; rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis]; rw [hb]
    simp
  · simp only [Module.Basis.det_apply, discr, Algebra.discr]
    rw [← eq_intCast (algebraMap Int Rat)]; rw [RingHom.map_det]
    congr! 2
    ext i j
    simp [b', Module.Basis.toMatrix_apply, mul_comm (RingOfIntegers.basis K i),
      b, integralBasis_apply, ← map_mul, Algebra.trace_localization Int Int⁰]

/--
lemma `discr_mem_differentIdeal` / 引理 `discr_mem_differentIdeal`

English:
lemma discr_mem_differentIdeal
  statement: ↑(discr K) in differentIdeal Int 𝒪
  proof: by
  have := (differentIdeal Int 𝒪).absNorm_mem
  cases (discr K).natAbs_eq with
  | inl h =>
    rwa [absNorm_differentIdeal K, ← Int.cast_natCast, ← h] at this
  | inr h =>
    rwa [absNorm_differentIdeal K, ← Int.cast_natCast, Int.eq_neg_comm.mp h,
      Int.cast_neg, neg_mem_iff] at this

中文:
引理 discr_mem_differentIdeal
  结论: ↑(discr K) in differentIdeal 整数 𝒪
  证明: by
  have := (differentIdeal Int 𝒪).absNorm_mem
  cases (discr K).natAbs_eq with
  | inl h =>
    rwa [absNorm_differentIdeal K, ← Int.cast_natCast, ← h] at this
  | inr h =>
    rwa [absNorm_differentIdeal K, ← Int.cast_natCast, Int.eq_neg_comm.mp h,
      Int.cast_neg, neg_mem_iff] at this

Depends on / 依赖: Int.cast_natCast, Int.cast_neg, Int.eq_neg_comm.mp, absNorm_differentIdeal, absNorm_mem, cast_natCast, cast_neg, differentIdeal, eq_neg_comm, natAbs_eq, neg_mem_iff
-/
lemma discr_mem_differentIdeal : ↑(discr K) in differentIdeal Int 𝒪 := by
  have := (differentIdeal Int 𝒪).absNorm_mem
  cases (discr K).natAbs_eq with
  | inl h =>
    rwa [absNorm_differentIdeal K, ← Int.cast_natCast, ← h] at this
  | inr h =>
    rwa [absNorm_differentIdeal K, ← Int.cast_natCast, Int.eq_neg_comm.mp h,
      Int.cast_neg, neg_mem_iff] at this

attribute [local instance] FractionRing.liftAlgebra in
/--
theorem `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow` / 定理 `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`

English:
theorem natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
  statement: (L 𝒪' : Type*) [Field L]
  proof: by
  have := congr_arg Ideal.absNorm
    (differentIdeal_eq_differentIdeal_mul_differentIdeal Int 𝒪 𝒪')
  rwa [absNorm_differentIdeal L, map_mul, Ideal.absNorm_algebraMap,
    absNorm_differentIdeal K, ← IsFractionRing.finrank_eq 𝒪 K 𝒪' L] at this

中文:
定理 natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
  结论: (L 𝒪' : 类型) [域 L]
  证明: by
  have := congr_arg Ideal.absNorm
    (differentIdeal_eq_differentIdeal_mul_differentIdeal Int 𝒪 𝒪')
  rwa [absNorm_differentIdeal L, map_mul, Ideal.absNorm_algebraMap,
    absNorm_differentIdeal K, ← IsFractionRing.finrank_eq 𝒪 K 𝒪' L] at this

Depends on / 依赖: Ideal.absNorm, Ideal.absNorm_algebraMap, IsFractionRing, IsFractionRing.finrank_eq, absNorm, absNorm_algebraMap, absNorm_differentIdeal, congr_arg, differentIdeal_eq_differentIdeal_mul_differentIdeal, finrank_eq, map_mul
-/
theorem natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (L 𝒪' : Type*) [Field L]
    [NumberField L] [CommRing 𝒪'] [Algebra 𝒪' L] [IsFractionRing 𝒪' L]
    [IsDedekindDomain 𝒪'] [CharZero 𝒪'] [Algebra K L] [Algebra 𝒪 𝒪'] [Algebra 𝒪 L]
    [IsScalarTower 𝒪 K L] [IsScalarTower 𝒪 𝒪' L] [IsTorsionFree 𝒪 𝒪'] [Free Int 𝒪']
    [Module.Finite Int 𝒪'] [Module.Finite 𝒪 𝒪'] :
    (discr L).natAbs = Ideal.absNorm (differentIdeal 𝒪 𝒪') *
      (discr K).natAbs ^ Module.finrank K L := by
  have := congr_arg Ideal.absNorm
    (differentIdeal_eq_differentIdeal_mul_differentIdeal Int 𝒪 𝒪')
  rwa [absNorm_differentIdeal L, map_mul, Ideal.absNorm_algebraMap,
    absNorm_differentIdeal K, ← IsFractionRing.finrank_eq 𝒪 K 𝒪' L] at this

variable (L : Type*) [Field L]

/--
theorem `isCoprime_differentIdeal_of_isCoprime_discr` / 定理 `isCoprime_differentIdeal_of_isCoprime_discr`

English:
theorem isCoprime_differentIdeal_of_isCoprime_discr
  statement: {K₁ K₂ : Type*} [Field K₁]
  proof: by
  obtain ⟨u, v, h⟩ := h
  refine Ideal.isCoprime_iff_exists.mpr ⟨u * discr K₁, ?_, v * discr K₂, ?_, ?_⟩
  · apply Ideal.mul_mem_left
    rw [← map_intCast (algebraMap (𝓞 K₁) (𝓞 L))]
exact Ideal.mem_map_of_mem (algebraMap (𝓞 K₁) (𝓞 L)) discr_mem_differentIdeal _ _
  · apply Ideal.mul_mem_left
   

中文:
定理 isCoprime_differentIdeal_of_isCoprime_discr
  结论: {K₁ K₂ : 类型} [域 K₁]
  证明: by
  obtain ⟨u, v, h⟩ := h
  refine Ideal.isCoprime_iff_exists.mpr ⟨u * discr K₁, ?_, v * discr K₂, ?_, ?_⟩
  · apply Ideal.mul_mem_left
    rw [← map_intCast (algebraMap (𝓞 K₁) (𝓞 L))]
exact Ideal.mem_map_of_mem (algebraMap (𝓞 K₁) (𝓞 L)) discr_mem_differentIdeal _ _
  · apply Ideal.mul_mem_left
   

Depends on / 依赖: Ideal.isCoprime_iff_exists.mpr, Ideal.mem_map_of_mem, Ideal.mul_mem_left, Int.cast_add, Int.cast_mul, Int.cast_one, algebraMap, cast_add, cast_mul, cast_one, discr_mem_differentIdeal, isCoprime_iff_exists, map_intCast, mem_map_of_mem, mul_mem_left
-/
theorem isCoprime_differentIdeal_of_isCoprime_discr {K₁ K₂ : Type*} [Field K₁]
    [NumberField K₁] [Field K₂] [NumberField K₂] [Algebra K₁ L] [Algebra K₂ L]
    (h : IsCoprime (discr K₁) (discr K₂)) :
    IsCoprime ((differentIdeal Int (𝓞 K₁)).map (algebraMap (𝓞 K₁) (𝓞 L)))
      ((differentIdeal Int (𝓞 K₂)).map (algebraMap (𝓞 K₂) (𝓞 L))) := by
  obtain ⟨u, v, h⟩ := h
  refine Ideal.isCoprime_iff_exists.mpr ⟨u * discr K₁, ?_, v * discr K₂, ?_, ?_⟩
  · apply Ideal.mul_mem_left
    rw [← map_intCast (algebraMap (𝓞 K₁) (𝓞 L))]
exact Ideal.mem_map_of_mem (algebraMap (𝓞 K₁) (𝓞 L)) discr_mem_differentIdeal _ _
  · apply Ideal.mul_mem_left
    rw [← map_intCast (algebraMap (𝓞 K₂) (𝓞 L))]
exact Ideal.mem_map_of_mem (algebraMap (𝓞 K₂) (𝓞 L)) discr_mem_differentIdeal _ _
  rw [← Int.cast_mul]; rw [← Int.cast_mul]; rw [← Int.cast_add]; rw [h]; rw [Int.cast_one]

variable [NumberField L]

/--
theorem `discr_dvd_discr` / 定理 `discr_dvd_discr`

English:
theorem discr_dvd_discr
  given: [Algebra K L]
  proof: by
  suffices discr K ^ Module.finrank K L ∣ discr L from
    dvd_trans (dvd_pow_self _ (Nat.ne_zero_of_lt Module.finrank_pos)) this
  rw [← Int.dvd_natAbs]; rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]; rw [Nat.cast_mul]; rw [Nat.cast_pow]; rw [← Int.mul_sign_sel

中文:
定理 discr_dvd_discr
  条件: [代数 K L]
  证明: by
  suffices discr K ^ Module.finrank K L ∣ discr L from
    dvd_trans (dvd_pow_self _ (Nat.ne_zero_of_lt Module.finrank_pos)) this
  rw [← Int.dvd_natAbs]; rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]; rw [Nat.cast_mul]; rw [Nat.cast_pow]; rw [← Int.mul_sign_sel

Depends on / 依赖: Int.dvd_mul_right, Int.dvd_natAbs, Int.mul_sign_self, Module, Module.finrank, Module.finrank_pos, Nat.cast_mul, Nat.cast_pow, Nat.ne_zero_of_lt, cast_mul, cast_pow, dvd_mul_right, dvd_natAbs, dvd_pow_self, dvd_trans, finrank, finrank_pos, mul_assoc, mul_comm, mul_pow
-/
theorem discr_dvd_discr [Algebra K L] :
    discr K ∣ discr L := by
  suffices discr K ^ Module.finrank K L ∣ discr L from
    dvd_trans (dvd_pow_self _ (Nat.ne_zero_of_lt Module.finrank_pos)) this
  rw [← Int.dvd_natAbs]; rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]; rw [Nat.cast_mul]; rw [Nat.cast_pow]; rw [← Int.mul_sign_self]; rw [mul_pow]; rw [← mul_assoc]; rw [mul_comm _ (discr K ^ _)]; rw [mul_assoc]
  exact Int.dvd_mul_right _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `linearDisjoint_of_isGalois_isCoprime_discr` / 定理 `linearDisjoint_of_isGalois_isCoprime_discr`

English:
theorem linearDisjoint_of_isGalois_isCoprime_discr
  statement: (K₁ K₂ : IntermediateField Rat L) [IsGalois Rat K₁]
  proof: by
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  suffices IsUnit (discr ↥(K₁ ⊓ K₂)) by
    contrapose! this
    have : 1 < Module.finrank Rat ↥(K₁ ⊓ K₂) := by
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Module.finrank_pos.ne', ?_⟩
      rwa [ne_eq, ← IntermediateField.finrank_eq_o

中文:
定理 linearDisjoint_of_isGalois_isCoprime_discr
  结论: (K₁ K₂ : 中间域 有理数 L) [是Galois 有理数 K₁]
  证明: by
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  suffices IsUnit (discr ↥(K₁ ⊓ K₂)) by
    contrapose! this
    have : 1 < Module.finrank Rat ↥(K₁ ⊓ K₂) := by
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Module.finrank_pos.ne', ?_⟩
      rwa [ne_eq, ← IntermediateField.finrank_eq_o

Depends on / 依赖: Int.isUnit_iff_abs_eq.not.mpr, IntermediateField, IntermediateField.LinearDisjoint.of_inf_eq_bot, IntermediateField.finrank_eq_one_iff, IsUnit, LinearDisjoint, Module, Module.finrank, Module.finrank_pos.ne, Nat.one_lt_iff_ne_zero_and_ne_one.mpr, NumberField, NumberField.discr_dvd_discr, abs_discr_gt_two, contrapose, discr_dvd_discr, finrank, finrank_eq_one_iff, finrank_pos, h.isUnit_of_dvd, isUnit_iff_abs_eq
-/
theorem linearDisjoint_of_isGalois_isCoprime_discr (K₁ K₂ : IntermediateField Rat L) [IsGalois Rat K₁]
    (h : IsCoprime (discr K₁) (discr K₂)) :
    K₁.LinearDisjoint K₂ := by
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  suffices IsUnit (discr ↥(K₁ ⊓ K₂)) by
    contrapose! this
    have : 1 < Module.finrank Rat ↥(K₁ ⊓ K₂) := by
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Module.finrank_pos.ne', ?_⟩
      rwa [ne_eq, ← IntermediateField.finrank_eq_one_iff] at this
exact Int.isUnit_iff_abs_eq.not.mpr by linarith [abs_discr_gt_two this]
  exact h.isUnit_of_dvd' (NumberField.discr_dvd_discr _ _) (NumberField.discr_dvd_discr _ _)

/--
theorem `natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow` / 定理 `natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow`

English:
theorem natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow
  statement: (K₁ K₂ : IntermediateField Rat L)
  proof: by
  let _ : Algebra (FractionRing (𝓞 K₁)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have h_main := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K₂ (𝓞 K₂) L (𝓞 L)
  rwa [differentIdeal_eq_map_differentIdeal Int (𝓞 L) (𝓞 K₂) (𝓞 K₁) (F₁ := K₂) (F₂ := K₁)
    (by rwa [linear

中文:
定理 natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow
  结论: (K₁ K₂ : 中间域 有理数 L)
  证明: by
  let _ : Algebra (FractionRing (𝓞 K₁)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have h_main := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K₂ (𝓞 K₂) L (𝓞 L)
  rwa [differentIdeal_eq_map_differentIdeal Int (𝓞 L) (𝓞 K₂) (𝓞 K₁) (F₁ := K₂) (F₂ := K₁)
    (by rwa [linear

Depends on / 依赖: Algebra, FractionRing, FractionRing.liftAlgebra, Ideal.absNorm_algebraMap, IsFractionRing, IsFractionRing.finrank_eq, absNorm_algebraMap, absNorm_differentIdeal, differentIdeal_eq_map_differentIdeal, finrank_eq, finrank_left, finrank_right_eq_finrank, h_main, isCoprime_comm, liftAlgebra, linearDisjoint_comm, natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow, sup_comm
-/
theorem natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow (K₁ K₂ : IntermediateField Rat L)
    (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal Int (𝓞 K₁)).map (algebraMap (𝓞 K₁) (𝓞 L)))
      ((differentIdeal Int (𝓞 K₂)).map (algebraMap (𝓞 K₂) (𝓞 L)))) :
    (discr L).natAbs =
      (discr K₁).natAbs ^ Module.finrank Rat K₂ * (discr K₂).natAbs ^ Module.finrank Rat K₁ := by
  let _ : Algebra (FractionRing (𝓞 K₁)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have h_main := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K₂ (𝓞 K₂) L (𝓞 L)
  rwa [differentIdeal_eq_map_differentIdeal Int (𝓞 L) (𝓞 K₂) (𝓞 K₁) (F₁ := K₂) (F₂ := K₁)
    (by rwa [linearDisjoint_comm]) (by rwa [sup_comm]) (by rwa [isCoprime_comm]),
    Ideal.absNorm_algebraMap, absNorm_differentIdeal K₁, h₁.finrank_right_eq_finrank h₂,
    ← IsFractionRing.finrank_eq (𝓞 K₁) K₁ (𝓞 L) L, h₁.finrank_left_eq_finrank h₂] at h_main

end

/--
lemma `not_dvd_discr_iff_forall_liesOver` / 引理 `not_dvd_discr_iff_forall_liesOver`

English:
lemma not_dvd_discr_iff_forall_liesOver
  given: [IsIntegralClosure 𝒪 Int K] {p : Int} (hp : Prime p)
  proof: by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension Int Rat K 𝒪
  have := IsIntegralClosure.finite Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  simp_rw 

中文:
引理 not_dvd_discr_iff_对任意_liesOver
  条件: [是整闭包 𝒪 整数 K] {p : 整数} (hp : 素 p)
  证明: by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension Int Rat K 𝒪
  have := IsIntegralClosure.finite Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  simp_rw 

Depends on / 依赖: CharZero, CharZero.of_module, Ideal.exists_isMaximal_dvd_of_dvd_absNorm, Int.dvd_natAbs, IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.finite, IsIntegralClosure.isDedekindDomain, IsIntegralClosure.isFractionRing_of_finite_extension, absNorm_differentIdeal, algebraMap_injective, contrapose, dvd_natAbs, exists_isMaximal_dvd_of_dvd_absNorm, finite, isDedekindDomain, isDomain, isFractionRing_of_finite_extension, not_dvd_differentIdeal_iff, of_module
-/
lemma not_dvd_discr_iff_forall_liesOver [IsIntegralClosure 𝒪 Int K] {p : Int} (hp : Prime p) :
    ¬ p ∣ discr K ↔ forall (P : Ideal 𝒪) (_ : P.IsMaximal), P.LiesOver (.span {p}) ->
      Algebra.IsUnramifiedAt Int P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension Int Rat K 𝒪
  have := IsIntegralClosure.finite Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  simp_rw [← not_dvd_differentIdeal_iff]
  contrapose!
  constructor
  · intro h
    rw [← Int.dvd_natAbs]; rw [← absNorm_differentIdeal K 𝒪] at h
    obtain ⟨P, hP, h₁, h₂⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm hp _ h
    exact ⟨P, hP, ⟨h₁.symm⟩, h₂⟩
  · rintro ⟨P, hP, hP', hP''⟩
    have := Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hP'')
    rw [absNorm_differentIdeal K]; rw [← Ideal.natAbs_pow_inertiaDeg p]; rw [← Int.natAbs_pow]; rw [Int.natAbs_dvd_natAbs] at this
    exact (dvd_pow_self _ (Ideal.inertiaDeg_pos ..).ne').trans this

/--
lemma `not_dvd_discr_iff_isUnramifiedIn` / 引理 `not_dvd_discr_iff_isUnramifiedIn`

English:
lemma not_dvd_discr_iff_isUnramifiedIn
  given: [IsIntegralClosure 𝒪 Int K] {p : Int} (hp : Prime p)
  proof: by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  rw [not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  exact (Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain'
    (Ideal.span_sing

中文:
引理 not_dvd_discr_iff_isUnramifiedIn
  条件: [是整闭包 𝒪 整数 K] {p : 整数} (hp : 素 p)
  证明: by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  rw [not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  exact (Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain'
    (Ideal.span_sing

Depends on / 依赖: Algebra, Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain, CharZero, CharZero.of_module, Ideal.span_singleton_eq_bot.not.mpr, IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.isDedekindDomain, algebraMap_injective, hp.ne_zero, isDedekindDomain, isDomain, isUnramifiedIn_iff_forall_of_isDedekindDomain, ne_zero, not_dvd_discr_iff_forall_liesOver, of_module, span_singleton_eq_bot
-/
lemma not_dvd_discr_iff_isUnramifiedIn [IsIntegralClosure 𝒪 Int K] {p : Int} (hp : Prime p) :
    ¬ p ∣ discr K ↔ Algebra.IsUnramifiedIn 𝒪 (Ideal.span {p}) := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  rw [not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  exact (Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain'
    (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)).symm

/--
lemma `not_dvd_discr_iff_forall_mem` / 引理 `not_dvd_discr_iff_forall_mem`

English:
lemma not_dvd_discr_iff_forall_mem
  given: [IsIntegralClosure 𝒪 Int K] {p : Int} (hp : Prime p)
  proof: by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  rw [NumberField.not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  exact ⟨fun H P hP h => H P (hP.isMaximal (by aesop))
    ((Ideal.liesO

中文:
引理 not_dvd_discr_iff_对任意_mem
  条件: [是整闭包 𝒪 整数 K] {p : 整数} (hp : 素 p)
  证明: by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  rw [NumberField.not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  exact ⟨fun H P hP h => H P (hP.isMaximal (by aesop))
    ((Ideal.liesO

Depends on / 依赖: CharZero, CharZero.of_module, Ideal.liesOver_span_iff, Ideal.mem_span_singleton_self, IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.isDedekindDomain, NumberField, NumberField.not_dvd_discr_iff_forall_liesOver, algebraMap_injective, hP.isMaximal, hP.ne_top, isDedekindDomain, isDomain, isMaximal, liesOver_span_iff, mem_span_singleton_self, ne_top, not_dvd_discr_iff_forall_liesOver, of_module
-/
lemma not_dvd_discr_iff_forall_mem [IsIntegralClosure 𝒪 Int K] {p : Int} (hp : Prime p) :
    ¬ p ∣ discr K ↔ forall (P : Ideal 𝒪) (_ : P.IsPrime), ↑p in P ->
      Algebra.IsUnramifiedAt Int P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  rw [NumberField.not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  exact ⟨fun H P hP h => H P (hP.isMaximal (by aesop))
    ((Ideal.liesOver_span_iff hP.ne_top hp).mpr h),
    fun H P _ h => H P _ (h.1.le (Ideal.mem_span_singleton_self _))⟩

end NumberField
