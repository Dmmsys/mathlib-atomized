/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Residue field of primes in polynomial algebras

## Main results
- `Polynomial.residueFieldMapCAlgEquiv`: `κ(I[X]) ≃ₐ[κ(I)] κ(I)(X)`
- `Polynomial.fiberEquivQuotient`: `κ(p) ⊗[R] (R[X] ⧸ I) = κ(p)[X] / I`

-/

@[expose] public section

namespace Polynomial

open scoped nonZeroDivisors TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) [I.IsPrime] (J : Ideal R[X]) [J.IsPrime] [J.LiesOver I]
  [Algebra (Localization.AtPrime I) (Localization.AtPrime J)]
  [Localization.AtPrime.IsLiesOverAlgebra I J]


set_option backward.isDefEq.respectTransparency.types false in
/-- `κ(I[X]) ≃ₐ[κ(I)] κ(I)(X)`. -/
noncomputable
/--
Definition of `residueFieldMapCAlgEquiv` / `residueFieldMapCAlgEquiv` 的定义

English:
definition residueFieldMapCAlgEquiv
  signature: (hJ : J = I.map C)
  body: by
  letI f : J.ResidueField ->+* RatFunc I.ResidueField := by
    refine Ideal.ResidueField.lift _
        ((algebraMap I.ResidueField[X] _).comp (mapRingHom (algebraMap _ _))) ?_ ?_
    · simp [hJ, Ideal.map_le_iff_le_comap, RingHom.comap_ker _ C, mapRingHom_comp_C,
        RingHom.ker_comp_of_injective, C_injective,
        FaithfulSMul.algebraMap_injective I.ResidueField[X] (RatFunc I.ResidueField)]
    · rintro x (hx : x ∉ J)
      suffices exists i, x.coeff i ∉ I by simpa [IsUnit.mem_submonoid_iff, Polynomial.ext_iff]
      contrapose! hx
      rwa [hJ, Ideal.mem_map_C_iff]
  haveI hf : f.comp (algebraMap I.ResidueField _) = algebraMap _ _ := by
    ext
    simp [f, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  refine .ofAlgHom ⟨f, fun r => congr($hf r)⟩
      (RatFunc.liftAlgHom (aeval (algebraMap R[X] _ X)) fun x => ?_) ?_ ?_
  · suffices Function.Injective (aeval (R := I.ResidueField) (algebraMap R[X] J.ResidueField X)) by
      simp [← this.eq_iff]
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, hr⟩ := map_surjective _ Ideal.Quotient.mk_surjective
      (IsLocalization.integerNormalization (R ⧸ I)⁰ x)
    obtain ⟨s, hs, hr⟩ : exists s ∉ I, r.map (algebraMap _ _) = s • x := by
      obtain ⟨b, hb0, hb⟩ := IsLocalization.integerNormalization_spec (R ⧸ I)⁰ x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨s, by simpa [Ideal.Quotient.eq_zero_iff_mem] using! hb0, ?_⟩
      simpa [← hr, map_map, ← Ideal.Quotient.algebraMap_eq] using! hb
    replace hx : r in J := by
      apply_fun aeval (algebraMap R[X] J.ResidueField X) at hr
      simpa [hx, aeval_map_algebraMap, aeval_algebraMap_apply, Algebra.smul_def] using! hr
    refine ((IsUnit.mk0 (algebraMap R I.ResidueField s) (by simpa)).map C).mul_right_injective ?_
    simp only [← algebraMap_eq, ← Algebra.smul_def]
    rw [algebraMap_smul]
    simp only [← hr]
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using! hJ.le hx
  · apply AlgHom.coe_ringHom_injective
    apply IsFractionRing.injective_comp_algebraMap (A := I.ResidueField[X])
    dsimp [RatFunc.liftAlgHom]
    simp only [AlgHom.comp_toRingHom, AlgHom.coe_ringHom_mk, RingHom.comp_assoc,
      RatFunc.liftRingHom_comp_algebraMap, RingHomCompTriple.comp_eq, f]
    ext <;> simp [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  · apply AlgHom.coe_ringHom_injective
    ext
    · simp [f, RatFunc.liftAlgHom, ← IsScalarTower.algebraMap_apply]; rfl
    · simp [f, RatFunc.liftAlgHom]

@[simp]

中文:
定义 residueFieldMapCAlgEquiv
  签名: (hJ : J = I.map C)
  定义体: by
  letI f : J.ResidueField ->+* RatFunc I.ResidueField := by
    refine Ideal.ResidueField.lift _
        ((algebraMap I.ResidueField[X] _).comp (mapRingHom (algebraMap _ _))) ?_ ?_
    · simp [hJ, Ideal.map_le_iff_le_comap, RingHom.comap_ker _ C, mapRingHom_comp_C,
        RingHom.ker_comp_of_injective, C_injective,
        FaithfulSMul.algebraMap_injective I.ResidueField[X] (RatFunc I.ResidueField)]
    · rintro x (hx : x ∉ J)
      suffices exists i, x.coeff i ∉ I by simpa [IsUnit.mem_submonoid_iff, Polynomial.ext_iff]
      contrapose! hx
      rwa [hJ, Ideal.mem_map_C_iff]
  haveI hf : f.comp (algebraMap I.ResidueField _) = algebraMap _ _ := by
    ext
    simp [f, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  refine .ofAlgHom ⟨f, fun r => congr($hf r)⟩
      (RatFunc.liftAlgHom (aeval (algebraMap R[X] _ X)) fun x => ?_) ?_ ?_
  · suffices Function.Injective (aeval (R := I.ResidueField) (algebraMap R[X] J.ResidueField X)) by
      simp [← this.eq_iff]
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, hr⟩ := map_surjective _ Ideal.Quotient.mk_surjective
      (IsLocalization.integerNormalization (R ⧸ I)⁰ x)
    obtain ⟨s, hs, hr⟩ : exists s ∉ I, r.map (algebraMap _ _) = s • x := by
      obtain ⟨b, hb0, hb⟩ := IsLocalization.integerNormalization_spec (R ⧸ I)⁰ x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨s, by simpa [Ideal.Quotient.eq_zero_iff_mem] using! hb0, ?_⟩
      simpa [← hr, map_map, ← Ideal.Quotient.algebraMap_eq] using! hb
    replace hx : r in J := by
      apply_fun aeval (algebraMap R[X] J.ResidueField X) at hr
      simpa [hx, aeval_map_algebraMap, aeval_algebraMap_apply, Algebra.smul_def] using! hr
    refine ((IsUnit.mk0 (algebraMap R I.ResidueField s) (by simpa)).map C).mul_right_injective ?_
    simp only [← algebraMap_eq, ← Algebra.smul_def]
    rw [algebraMap_smul]
    simp only [← hr]
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using! hJ.le hx
  · apply AlgHom.coe_ringHom_injective
    apply IsFractionRing.injective_comp_algebraMap (A := I.ResidueField[X])
    dsimp [RatFunc.liftAlgHom]
    simp only [AlgHom.comp_toRingHom, AlgHom.coe_ringHom_mk, RingHom.comp_assoc,
      RatFunc.liftRingHom_comp_algebraMap, RingHomCompTriple.comp_eq, f]
    ext <;> simp [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  · apply AlgHom.coe_ringHom_injective
    ext
    · simp [f, RatFunc.liftAlgHom, ← IsScalarTower.algebraMap_apply]; rfl
    · simp [f, RatFunc.liftAlgHom]

@[simp]

Depends on / 依赖: C_injective, FaithfulSMul, FaithfulSMul.algebraMap_injective, I.ResidueField, Ideal.ResidueField.lift, Ideal.map_le_iff_le_comap, IsUnit, IsUnit.mem_submonoid_iff, J.ResidueField, Polynomial, Polynomial.ext_iff, RatFunc, ResidueField, RingHom, RingHom.comap_ker, RingHom.ker_comp_of_injective, algebraMap, algebraMap_injective, comap_ker, contrapose
-/
def residueFieldMapCAlgEquiv (hJ : J = I.map C) :
    J.ResidueField ≃ₐ[I.ResidueField] RatFunc I.ResidueField := by
  letI f : J.ResidueField ->+* RatFunc I.ResidueField := by
    refine Ideal.ResidueField.lift _
        ((algebraMap I.ResidueField[X] _).comp (mapRingHom (algebraMap _ _))) ?_ ?_
    · simp [hJ, Ideal.map_le_iff_le_comap, RingHom.comap_ker _ C, mapRingHom_comp_C,
        RingHom.ker_comp_of_injective, C_injective,
        FaithfulSMul.algebraMap_injective I.ResidueField[X] (RatFunc I.ResidueField)]
    · rintro x (hx : x ∉ J)
      suffices exists i, x.coeff i ∉ I by simpa [IsUnit.mem_submonoid_iff, Polynomial.ext_iff]
      contrapose! hx
      rwa [hJ, Ideal.mem_map_C_iff]
  haveI hf : f.comp (algebraMap I.ResidueField _) = algebraMap _ _ := by
    ext
    simp [f, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  refine .ofAlgHom ⟨f, fun r => congr($hf r)⟩
      (RatFunc.liftAlgHom (aeval (algebraMap R[X] _ X)) fun x => ?_) ?_ ?_
  · suffices Function.Injective (aeval (R := I.ResidueField) (algebraMap R[X] J.ResidueField X)) by
      simp [← this.eq_iff]
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, hr⟩ := map_surjective _ Ideal.Quotient.mk_surjective
      (IsLocalization.integerNormalization (R ⧸ I)⁰ x)
    obtain ⟨s, hs, hr⟩ : exists s ∉ I, r.map (algebraMap _ _) = s • x := by
      obtain ⟨b, hb0, hb⟩ := IsLocalization.integerNormalization_spec (R ⧸ I)⁰ x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨s, by simpa [Ideal.Quotient.eq_zero_iff_mem] using! hb0, ?_⟩
      simpa [← hr, map_map, ← Ideal.Quotient.algebraMap_eq] using! hb
    replace hx : r in J := by
      apply_fun aeval (algebraMap R[X] J.ResidueField X) at hr
      simpa [hx, aeval_map_algebraMap, aeval_algebraMap_apply, Algebra.smul_def] using! hr
    refine ((IsUnit.mk0 (algebraMap R I.ResidueField s) (by simpa)).map C).mul_right_injective ?_
    simp only [← algebraMap_eq, ← Algebra.smul_def]
    rw [algebraMap_smul]
    simp only [← hr]
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using! hJ.le hx
  · apply AlgHom.coe_ringHom_injective
    apply IsFractionRing.injective_comp_algebraMap (A := I.ResidueField[X])
    dsimp [RatFunc.liftAlgHom]
    simp only [AlgHom.comp_toRingHom, AlgHom.coe_ringHom_mk, RingHom.comp_assoc,
      RatFunc.liftRingHom_comp_algebraMap, RingHomCompTriple.comp_eq, f]
    ext <;> simp [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  · apply AlgHom.coe_ringHom_injective
    ext
    · simp [f, RatFunc.liftAlgHom, ← IsScalarTower.algebraMap_apply]; rfl
    · simp [f, RatFunc.liftAlgHom]

@[simp]
/--
lemma `residueFieldMapCAlgEquiv_algebraMap` / 引理 `residueFieldMapCAlgEquiv_algebraMap`

English:
lemma residueFieldMapCAlgEquiv_algebraMap
  given: (hJ : J = I.map C) (p : R[X])
  proof: by
  simp [residueFieldMapCAlgEquiv]

@[simp]

中文:
引理 residueFieldMapCAlgEquiv_algebraMap
  条件: (hJ : J = I.map C) (p : R[X])
  证明: by
  simp [residueFieldMapCAlgEquiv]

@[simp]

Depends on / 依赖: residueFieldMapCAlgEquiv
-/
lemma residueFieldMapCAlgEquiv_algebraMap (hJ : J = I.map C) (p : R[X]) :
    residueFieldMapCAlgEquiv I J hJ (algebraMap _ _ p) =
      algebraMap _ _ (p.map (algebraMap R I.ResidueField)) := by
  simp [residueFieldMapCAlgEquiv]

@[simp]
/--
lemma `residueFieldMapCAlgEquiv_symm_C` / 引理 `residueFieldMapCAlgEquiv_symm_C`

English:
lemma residueFieldMapCAlgEquiv_symm_C
  given: (hJ : J = I.map C) (r)
  proof: (residueFieldMapCAlgEquiv I J hJ).symm.commutes r

@[simp]

中文:
引理 residueFieldMapCAlgEquiv_symm_C
  条件: (hJ : J = I.map C) (r)
  证明: (residueFieldMapCAlgEquiv I J hJ).symm.commutes r

@[simp]

Depends on / 依赖: commutes, residueFieldMapCAlgEquiv, symm.commutes
-/
lemma residueFieldMapCAlgEquiv_symm_C (hJ : J = I.map C) (r) :
    (residueFieldMapCAlgEquiv I J hJ).symm (.C r) = algebraMap _ _ r :=
  (residueFieldMapCAlgEquiv I J hJ).symm.commutes r

@[simp]
/--
lemma `residueFieldMapCAlgEquiv_symm_X` / 引理 `residueFieldMapCAlgEquiv_symm_X`

English:
lemma residueFieldMapCAlgEquiv_symm_X
  given: (hJ : J = I.map C)
  proof: (residueFieldMapCAlgEquiv I J hJ).injective (by simp)

中文:
引理 residueFieldMapCAlgEquiv_symm_X
  条件: (hJ : J = I.map C)
  证明: (residueFieldMapCAlgEquiv I J hJ).injective (by simp)

Depends on / 依赖: injective, residueFieldMapCAlgEquiv
-/
lemma residueFieldMapCAlgEquiv_symm_X (hJ : J = I.map C) :
    (residueFieldMapCAlgEquiv I J hJ).symm .X = algebraMap R[X] _ .X :=
  (residueFieldMapCAlgEquiv I J hJ).injective (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/-- `κ(p) ⊗[R] (R[X] ⧸ I) = κ(p)[X] / I` -/
noncomputable
/--
Definition of `fiberEquivQuotient` / `fiberEquivQuotient` 的定义

English:
definition fiberEquivQuotient
  signature: (f : R[X] ->ₐ[R] S) (hf : Function.Surjective f) (p : Ideal R) [p.IsPrime]
  body: by
  refine .ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (AlgHom.liftOfSurjective _ hf
    ((Ideal.Quotient.mkₐ _ _).comp (mapAlgHom (Algebra.ofId _ _))) ?_) fun _ _ => .all _ _)
    (Ideal.Quotient.liftₐ _ (aeval (1 otimesₜ f .X)) ?_) ?_ ?_
  · simp [AlgHom.comp_toRingHom, ← RingHom.comap_ker, ← Ideal.map_le_iff_le_comap]
  · change Ideal.map _ _ <= RingHom.ker (aeval _).toRingHom
    rw [Ideal.map_le_iff_le_comap]; rw [RingHom.comap_ker]
    have : ((aeval (1 otimesₜ[R] f X : p.Fiber S)).restrictScalars R).comp
        (mapAlgHom (Algebra.ofId R p.ResidueField)) =
        Algebra.TensorProduct.includeRight.comp f := by ext; simp
    exact .trans_eq (by intro; aesop) congr(RingHom.ker $this).symm
  · apply Ideal.Quotient.algHom_ext
    ext
    simp
  · ext x
    obtain ⟨x, rfl⟩ := hf x
    simpa using aeval_algHom_apply
      ((Algebra.TensorProduct.includeRight : S ->ₐ[_] p.Fiber S).comp f) X x

中文:
定义 fiberEquivQuotient
  签名: (f : R[X] ->ₐ[R] S) (hf : 函数.满射 f) (p : 理想 R) [p.是素]
  定义体: by
  refine .ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (AlgHom.liftOfSurjective _ hf
    ((Ideal.Quotient.mkₐ _ _).comp (mapAlgHom (Algebra.ofId _ _))) ?_) fun _ _ => .all _ _)
    (Ideal.Quotient.liftₐ _ (aeval (1 otimesₜ f .X)) ?_) ?_ ?_
  · simp [AlgHom.comp_toRingHom, ← RingHom.comap_ker, ← Ideal.map_le_iff_le_comap]
  · change Ideal.map _ _ <= RingHom.ker (aeval _).toRingHom
    rw [Ideal.map_le_iff_le_comap]; rw [RingHom.comap_ker]
    have : ((aeval (1 otimesₜ[R] f X : p.Fiber S)).restrictScalars R).comp
        (mapAlgHom (Algebra.ofId R p.ResidueField)) =
        Algebra.TensorProduct.includeRight.comp f := by ext; simp
    exact .trans_eq (by intro; aesop) congr(RingHom.ker $this).symm
  · apply Ideal.Quotient.algHom_ext
    ext
    simp
  · ext x
    obtain ⟨x, rfl⟩ := hf x
    simpa using aeval_algHom_apply
      ((Algebra.TensorProduct.includeRight : S ->ₐ[_] p.Fiber S).comp f) X x

Depends on / 依赖: AlgHom, AlgHom.comp_toRingHom, AlgHom.liftOfSurjective, Algebra, Algebra.TensorProduct.lift, Algebra.ofId, Ideal.Quotient.lift, Ideal.Quotient.mk, Ideal.map, Ideal.map_le_iff_le_comap, Quotient, RingHom, RingHom.comap_ker, RingHom.ker, TensorProduct, comap_ker, comp_toRingHom, liftOfSurjective, mapAlgHom, map_le_iff_le_comap
-/
def fiberEquivQuotient (f : R[X] ->ₐ[R] S) (hf : Function.Surjective f) (p : Ideal R) [p.IsPrime] :
    p.Fiber S ≃ₐ[p.ResidueField] p.ResidueField[X] ⧸
      ((RingHom.ker (f : R[X] ->+* S)).map (mapRingHom (algebraMap R p.ResidueField))) := by
  refine .ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (AlgHom.liftOfSurjective _ hf
    ((Ideal.Quotient.mkₐ _ _).comp (mapAlgHom (Algebra.ofId _ _))) ?_) fun _ _ => .all _ _)
    (Ideal.Quotient.liftₐ _ (aeval (1 otimesₜ f .X)) ?_) ?_ ?_
  · simp [AlgHom.comp_toRingHom, ← RingHom.comap_ker, ← Ideal.map_le_iff_le_comap]
  · change Ideal.map _ _ <= RingHom.ker (aeval _).toRingHom
    rw [Ideal.map_le_iff_le_comap]; rw [RingHom.comap_ker]
    have : ((aeval (1 otimesₜ[R] f X : p.Fiber S)).restrictScalars R).comp
        (mapAlgHom (Algebra.ofId R p.ResidueField)) =
        Algebra.TensorProduct.includeRight.comp f := by ext; simp
    exact .trans_eq (by intro; aesop) congr(RingHom.ker $this).symm
  · apply Ideal.Quotient.algHom_ext
    ext
    simp
  · ext x
    obtain ⟨x, rfl⟩ := hf x
    simpa using aeval_algHom_apply
      ((Algebra.TensorProduct.includeRight : S ->ₐ[_] p.Fiber S).comp f) X x

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `fiberEquivQuotient_tmul` / 引理 `fiberEquivQuotient_tmul`

English:
lemma fiberEquivQuotient_tmul
  proof: by
  simp [fiberEquivQuotient, ← Ideal.Quotient.mk_algebraMap]

中文:
引理 fiberEquivQuotient_tmul
  证明: by
  simp [fiberEquivQuotient, ← Ideal.Quotient.mk_algebraMap]

Depends on / 依赖: Ideal.Quotient.mk_algebraMap, Quotient, fiberEquivQuotient, mk_algebraMap
-/
lemma fiberEquivQuotient_tmul
    (f : R[X] ->ₐ[R] S) (hf : Function.Surjective f) (p : Ideal R) [p.IsPrime] (a b) :
    fiberEquivQuotient f hf p (a otimesₜ f b) = Ideal.Quotient.mk _ (C a * b.map (algebraMap _ _)) := by
  simp [fiberEquivQuotient, ← Ideal.Quotient.mk_algebraMap]

/--
theorem `_root_.Ideal.exists_mem_span_singleton_map_residueField_eq` / 定理 `_root_.Ideal.exists_mem_span_singleton_map_residueField_eq`

English:
theorem _root_.Ideal.exists_mem_span_singleton_map_residueField_eq
  proof: by
  obtain ⟨p, hp : _ = Ideal.span _⟩ := (inferInstance :
    (I.map (mapRingHom (algebraMap R P.ResidueField))).IsPrincipal)
  let := (mapRingHom (algebraMap (R ⧸ P) P.ResidueField)).toAlgebra
  have := Polynomial.isLocalization (R ⧸ P)⁰ P.ResidueField
  have : p in (I.map (mapRingHom (algebraMap R (R ⧸ P)))).map (algebraMap _ _) := by
    rw [Ideal.map_map]; rw [RingHom.algebraMap_toAlgebra]; rw [mapRingHom_comp]; rw [← IsScalarTower.algebraMap_eq]; rw [hp]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨⟨⟨r, hr⟩, s⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff ((R ⧸ P)⁰.map C) _).mp this
  obtain ⟨r, hr', rfl⟩ := (Ideal.mem_map_iff_of_surjective _
    (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)).mp hr
  simp only [algebraMap_def, coe_mapRingHom,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at e
  refine ⟨r, hr', le_antisymm ?_ ?_⟩
  · simpa [-le_of_subsingleton, Ideal.span_le] using! Ideal.mem_map_of_mem _ hr'
  · simp only [hp, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    rw [(IsLocalization.map_units P.ResidueField[X] s).unit.eq_mul_inv_iff_mul_eq.mpr e]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

中文:
定理 _root_.理想.存在_mem_span_singleton_map_residueField_eq
  证明: by
  obtain ⟨p, hp : _ = Ideal.span _⟩ := (inferInstance :
    (I.map (mapRingHom (algebraMap R P.ResidueField))).IsPrincipal)
  let := (mapRingHom (algebraMap (R ⧸ P) P.ResidueField)).toAlgebra
  have := Polynomial.isLocalization (R ⧸ P)⁰ P.ResidueField
  have : p in (I.map (mapRingHom (algebraMap R (R ⧸ P)))).map (algebraMap _ _) := by
    rw [Ideal.map_map]; rw [RingHom.algebraMap_toAlgebra]; rw [mapRingHom_comp]; rw [← IsScalarTower.algebraMap_eq]; rw [hp]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨⟨⟨r, hr⟩, s⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff ((R ⧸ P)⁰.map C) _).mp this
  obtain ⟨r, hr', rfl⟩ := (Ideal.mem_map_iff_of_surjective _
    (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)).mp hr
  simp only [algebraMap_def, coe_mapRingHom,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at e
  refine ⟨r, hr', le_antisymm ?_ ?_⟩
  · simpa [-le_of_subsingleton, Ideal.span_le] using! Ideal.mem_map_of_mem _ hr'
  · simp only [hp, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    rw [(IsLocalization.map_units P.ResidueField[X] s).unit.eq_mul_inv_iff_mul_eq.mpr e]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

Depends on / 依赖: I.map, Ideal.map_map, Ideal.mem_span_singleton_self, Ideal.span, IsPrincipal, IsScalarTower, IsScalarTower.algebraMap_eq, P.ResidueField, Polynomial, Polynomial.isLocalization, ResidueField, RingHom, RingHom.algebraMap_toAlgebra, algebraMap, algebraMap_eq, algebraMap_toAlgebra, isLocalization, mapRingHom, mapRingHom_comp, map_map
-/
theorem _root_.Ideal.exists_mem_span_singleton_map_residueField_eq
    (P : Ideal R) [P.IsPrime] (I : Ideal R[X]) :
    exists p in I, Ideal.span {p.map (algebraMap R P.ResidueField)} =
      I.map (mapRingHom (algebraMap R P.ResidueField)) := by
  obtain ⟨p, hp : _ = Ideal.span _⟩ := (inferInstance :
    (I.map (mapRingHom (algebraMap R P.ResidueField))).IsPrincipal)
  let := (mapRingHom (algebraMap (R ⧸ P) P.ResidueField)).toAlgebra
  have := Polynomial.isLocalization (R ⧸ P)⁰ P.ResidueField
  have : p in (I.map (mapRingHom (algebraMap R (R ⧸ P)))).map (algebraMap _ _) := by
    rw [Ideal.map_map]; rw [RingHom.algebraMap_toAlgebra]; rw [mapRingHom_comp]; rw [← IsScalarTower.algebraMap_eq]; rw [hp]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨⟨⟨r, hr⟩, s⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff ((R ⧸ P)⁰.map C) _).mp this
  obtain ⟨r, hr', rfl⟩ := (Ideal.mem_map_iff_of_surjective _
    (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)).mp hr
  simp only [algebraMap_def, coe_mapRingHom,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at e
  refine ⟨r, hr', le_antisymm ?_ ?_⟩
  · simpa [-le_of_subsingleton, Ideal.span_le] using! Ideal.mem_map_of_mem _ hr'
  · simp only [hp, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    rw [(IsLocalization.map_units P.ResidueField[X] s).unit.eq_mul_inv_iff_mul_eq.mpr e]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Polynomial
