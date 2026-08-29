/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.Extension
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.GroupTheory.Solvable

/-!
# Normal field extensions

In this file we prove that for a finite extension, being normal
is the same as being a splitting field (`Normal.of_isSplittingField` and
`Normal.exists_isSplittingField`).

## Additional Results

* `Algebra.IsQuadraticExtension.normal`: the instance that a quadratic extension, given as a class
  `Algebra.IsQuadraticExtension`, is normal.

-/

@[expose] public section


noncomputable section

open Polynomial IsScalarTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/--
theorem `Normal.exists_isSplittingField` / 定理 `Normal.exists_isSplittingField`

English:
theorem Normal.exists_isSplittingField
  given: [h : Normal F K] [FiniteDimensional F K]
  proof: by
  classical
  let s := Module.Basis.ofVectorSpace F K
  refine
    ⟨∏ x, minpoly F (s x), Polynomial.map_prod (algebraMap F K) _ _ ▸
      Splits.prod fun x _ => h.splits (s x), Subalgebra.toSubmodule.injective ?_⟩
  rw [Algebra.top_toSubmodule]; rw [eq_top_iff]; rw [← s.span_eq]; rw [Submodule.s

中文:
定理 正规.存在_isSplittingField
  条件: [h : 正规 F K] [有限维 F K]
  证明: by
  classical
  let s := Module.Basis.ofVectorSpace F K
  refine
    ⟨∏ x, minpoly F (s x), Polynomial.map_prod (algebraMap F K) _ _ ▸
      Splits.prod fun x _ => h.splits (s x), Subalgebra.toSubmodule.injective ?_⟩
  rw [Algebra.top_toSubmodule]; rw [eq_top_iff]; rw [← s.span_eq]; rw [Submodule.s

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Algebra.top_toSubmodule, Finset, Finset.prod_ne_zero_iff, Module, Module.Basis.ofVectorSpace, Multiset, Multiset.mem_toFinset.mpr, Polynomial, Polynomial.map_eq_zero, Polynomial.map_prod, Set.range_subset_iff, Splits, Splits.prod, Subalgebra, Subalgebra.toSubmodule.injective, Submodule, Submodule.span_le, algebraMap
-/
theorem Normal.exists_isSplittingField [h : Normal F K] [FiniteDimensional F K] :
    exists p : F[X], IsSplittingField F K p := by
  classical
  let s := Module.Basis.ofVectorSpace F K
  refine
    ⟨∏ x, minpoly F (s x), Polynomial.map_prod (algebraMap F K) _ _ ▸
      Splits.prod fun x _ => h.splits (s x), Subalgebra.toSubmodule.injective ?_⟩
  rw [Algebra.top_toSubmodule]; rw [eq_top_iff]; rw [← s.span_eq]; rw [Submodule.span_le]; rw [Set.range_subset_iff]
  refine fun x =>
    Algebra.subset_adjoin
      (Multiset.mem_toFinset.mpr <|
        (mem_roots <|
mt (Polynomial.map_eq_zero <| algebraMap F K).1
                Finset.prod_ne_zero_iff.2 fun x _ => ?_).2 ?_)
  · exact minpoly.ne_zero (h.isIntegral (s x))
  rw [IsRoot.def]; rw [eval_map_algebraMap]; rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ _) (minpoly.aeval _ _)

section NormalTower

variable (E : Type*) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

variable {E F}

open IntermediateField

@[stacks 09HU "Normal part"]
/--
theorem `Normal.of_isSplittingField` / 定理 `Normal.of_isSplittingField`

English:
theorem Normal.of_isSplittingField
  given: (p : F[X]) [hFEp : IsSplittingField F E p]
  statement: Normal F E
  proof: by
  rcases eq_or_ne p 0 with (rfl | hp)
  · have := hFEp.adjoin_rootSet
    rw [rootSet_zero]; rw [Algebra.adjoin_empty] at this
    exact Normal.of_algEquiv
      (AlgEquiv.ofBijective (Algebra.ofId F E) (Algebra.bijective_algebraMap_iff.2 this.symm))
  refine normal_iff.mpr fun x => ?_
  have : F

中文:
定理 正规.of_isSplittingField
  条件: (p : F[X]) [hFEp : 是分裂域 F E p]
  结论: 正规 F E
  证明: by
  rcases eq_or_ne p 0 with (rfl | hp)
  · have := hFEp.adjoin_rootSet
    rw [rootSet_zero]; rw [Algebra.adjoin_empty] at this
    exact Normal.of_algEquiv
      (AlgEquiv.ofBijective (Algebra.ofId F E) (Algebra.bijective_algebraMap_iff.2 this.symm))
  refine normal_iff.mpr fun x => ?_
  have : F

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, Algebra, Algebra.adjoin_empty, Algebra.bijective_algebraMap_iff, Algebra.ofId, FiniteDimensional, IsIntegral, IsIntegral.of_finite, IsSplittingField, IsSplittingField.finiteDimensional, Normal, Normal.of_algEquiv, Polynomial, Polynomial.map_mul, SplittingField, SplittingField.splits, adjoin_empty, adjoin_rootSet, bijective_algebraMap_iff
-/
theorem Normal.of_isSplittingField (p : F[X]) [hFEp : IsSplittingField F E p] : Normal F E := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · have := hFEp.adjoin_rootSet
    rw [rootSet_zero]; rw [Algebra.adjoin_empty] at this
    exact Normal.of_algEquiv
      (AlgEquiv.ofBijective (Algebra.ofId F E) (Algebra.bijective_algebraMap_iff.2 this.symm))
  refine normal_iff.mpr fun x => ?_
  have : FiniteDimensional F E := IsSplittingField.finiteDimensional E p
  have hx := IsIntegral.of_finite F x
  let L := (p * minpoly F x).SplittingField
  have hL := SplittingField.splits (p * minpoly F x)
  rw [Polynomial.map_mul]; rw [splits_mul _ (map_ne_zero (minpoly.ne_zero hx))] at hL
  · obtain ⟨hL1, hL2⟩ := hL
    let j : E ->ₐ[F] L := IsSplittingField.lift E p hL1
    rw [← j.comp_algebraMap]; rw [← Polynomial.map_map] at hL2
    refine ⟨hx, Splits.of_splits_map (j : E ->+* L) hL2 fun a ha => ?_⟩
    rw [Polynomial.map_map]; rw [j.comp_algebraMap] at ha
    let : Algebra F⟮x⟯ L := ((algHomAdjoinIntegralEquiv F hx).symm ⟨a, ha⟩).toRingHom.toAlgebra
    let j' : E ->ₐ[F⟮x⟯] L := IsSplittingField.lift E (p.map (algebraMap F F⟮x⟯)) ?_
    · change a in j.range
      rw [← IsSplittingField.adjoin_rootSet_eq_range E p j]; rw [IsSplittingField.adjoin_rootSet_eq_range E p (j'.restrictScalars F)]
      exact ⟨x, (j'.commutes _).trans (algHomAdjoinIntegralEquiv_symm_apply_gen F hx _)⟩
    · rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  · exact Polynomial.map_ne_zero hp

/--
Instance `Polynomial.SplittingField.instNormal` / 实例 `Polynomial.SplittingField.instNormal`

English:
instance Polynomial.SplittingField.instNormal
  signature: (p : F[X])
  body: Normal.of_isSplittingField p

中文:
实例 多项式.分裂域.instNormal
  签名: (p : F[X])
  定义体: Normal.of_isSplittingField p

Depends on / 依赖: Normal, Normal.of_isSplittingField, of_isSplittingField
-/
instance Polynomial.SplittingField.instNormal (p : F[X]) : Normal F p.SplittingField :=
  Normal.of_isSplittingField p

end NormalTower

namespace IntermediateField

/--
Instance `normal_iSup` / 实例 `normal_iSup`

English:
instance normal_iSup
  signature: {ι : Type*} (t : ι -> IntermediateField F K) [h : forall i, Normal F (t i)]
  body: by
  refine { toIsAlgebraic := isAlgebraic_iSup fun i => (h i).1, splits' := fun x => ?_ }
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr'' (fun i => (h i).1) x.2
  let E : IntermediateField F K := ⨆ i in s, adjoin F ((minpoly F (i.2 :)).rootSet K)
  have hF : Normal F E := by
    have : IsSplittingF

中文:
实例 normal_iSup
  签名: {ι : 类型} (t : ι -> 中间域 F K) [h : 对任意 i, 正规 F (t i)]
  定义体: by
  refine { toIsAlgebraic := isAlgebraic_iSup fun i => (h i).1, splits' := fun x => ?_ }
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr'' (fun i => (h i).1) x.2
  let E : IntermediateField F K := ⨆ i in s, adjoin F ((minpoly F (i.2 :)).rootSet K)
  have hF : Normal F E := by
    have : IsSplittingF

Depends on / 依赖: Finset, Finset.prod_ne_zero_iff.mpr, IntermediateField, IsSplittingField, Normal, adjoin, adjoin_rootSet_isSplittingField, exists_finset_of_mem_supr, i.snd, isAlgebraic_iSup, isIntegral, isSplittingField_iSup, minpoly, minpoly.ne_zero, ne_zero, prod_ne_zero_iff, rootSet, splits, toIsAlgebraic
-/
instance normal_iSup {ι : Type*} (t : ι -> IntermediateField F K) [h : forall i, Normal F (t i)] :
    Normal F (⨆ i, t i : IntermediateField F K) := by
  refine { toIsAlgebraic := isAlgebraic_iSup fun i => (h i).1, splits' := fun x => ?_ }
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr'' (fun i => (h i).1) x.2
  let E : IntermediateField F K := ⨆ i in s, adjoin F ((minpoly F (i.2 :)).rootSet K)
  have hF : Normal F E := by
    have : IsSplittingField F E (∏ i in s, minpoly F i.snd) := by
      refine isSplittingField_iSup ?_ fun i _ => adjoin_rootSet_isSplittingField ?_
      · exact Finset.prod_ne_zero_iff.mpr fun i _ => minpoly.ne_zero ((h i.1).isIntegral i.2)
      · simpa [Polynomial.map_map] using! ((h i.1).splits i.2).map (algebraMap (t i.1) K)
    apply Normal.of_isSplittingField (∏ i in s, minpoly F i.2)
  have hE : E <= ⨆ i, t i := by
    refine iSup_le fun i => iSup_le fun _ => le_iSup_of_le i.1 ?_
    rw [adjoin_le_iff]; rw [← ((h i.1).splits i.2).image_rootSet (t i.1).val]
    exact fun _ ⟨a, _, h⟩ => h ▸ a.2
  have := hF.splits ⟨x, hx⟩
  rw [minpoly_eq]; rw [Subtype.coe_mk]; rw [← minpoly_eq] at this
  have := this.map (inclusion hE).toRingHom -- necessary for performance reasons
  rwa [Polynomial.map_map] at this

/-- If a set of algebraic elements in a field extension `K/F` have minimal polynomials that
  split in another extension `L/F`, then all minimal polynomials in the intermediate field
  generated by the set also split in `L/F`. -/
@[stacks 0BR3 "first part"]
/--
theorem `splits_of_mem_adjoin` / 定理 `splits_of_mem_adjoin`

English:
theorem splits_of_mem_adjoin
  statement: {L} [Field L] [Algebra F L] {S : Set K}
  proof: by
  let E : IntermediateField F L := ⨆ x : S, adjoin F ((minpoly F x.val).rootSet L)
  have normal : Normal F E := normal_iSup (h := fun x =>
    Normal.of_isSplittingField (hFEp := adjoin_rootSet_isSplittingField (splits x x.2).2))
  have : forall x in S, ((minpoly F x).map (algebraMap F E)).Split

中文:
定理 splits_of_mem_adjoin
  结论: {L} [域 L] [代数 F L] {S : 集合 K}
  证明: by
  let E : IntermediateField F L := ⨆ x : S, adjoin F ((minpoly F x.val).rootSet L)
  have normal : Normal F E := normal_iSup (h := fun x =>
    Normal.of_isSplittingField (hFEp := adjoin_rootSet_isSplittingField (splits x x.2).2))
  have : forall x in S, ((minpoly F x).map (algebraMap F E)).Split

Depends on / 依赖: IntermediateField, Normal, Normal.of_isSplittingField, Splits, adjoin, adjoin_rootSet_isSplittingField, algebraMap, le_iSup, minpoly, nonempty_algHom_adjoin_of_splits, normal, normal_iSup, of_isSplittingField, rootSet, splits, splits_of_splits, subset_adjoin, x.val
-/
theorem splits_of_mem_adjoin {L} [Field L] [Algebra F L] {S : Set K}
    (splits : forall x in S, IsIntegral F x ∧ ((minpoly F x).map (algebraMap F L)).Splits) {x : K}
    (hx : x in adjoin F S) : ((minpoly F x).map (algebraMap F L)).Splits := by
  let E : IntermediateField F L := ⨆ x : S, adjoin F ((minpoly F x.val).rootSet L)
  have normal : Normal F E := normal_iSup (h := fun x =>
    Normal.of_isSplittingField (hFEp := adjoin_rootSet_isSplittingField (splits x x.2).2))
  have : forall x in S, ((minpoly F x).map (algebraMap F E)).Splits := fun x hx => splits_of_splits
    (splits x hx).2 fun y hy => (le_iSup _ ⟨x, hx⟩ : _ <= E) (subset_adjoin F _ <| by exact hy)
  obtain ⟨φ⟩ := nonempty_algHom_adjoin_of_splits fun x hx => ⟨(splits x hx).1, this x hx⟩
  convert! (normal.splits <| φ ⟨x, hx⟩).map E.val.toRingHom
  simp [minpoly.algHom_eq _ φ.injective, ← minpoly.algHom_eq _ (adjoin F S).val.injective,
    Polynomial.map_map]

/--
Instance `normal_sup` / 实例 `normal_sup`

English:
instance normal_sup
  body: iSup_bool_eq (f := Bool.rec E' E) ▸ normal_iSup (h := by rintro (_ | _) <;> infer_instance)

中文:
实例 normal_sup
  定义体: iSup_bool_eq (f := Bool.rec E' E) ▸ normal_iSup (h := by rintro (_ | _) <;> infer_instance)

Depends on / 依赖: Bool.rec, iSup_bool_eq, infer_instance, normal_iSup
-/
instance normal_sup
    (E E' : IntermediateField F K) [Normal F E] [Normal F E'] :
    Normal F (E ⊔ E' : IntermediateField F K) :=
  iSup_bool_eq (f := Bool.rec E' E) ▸ normal_iSup (h := by rintro (_ | _) <;> infer_instance)

/-- An intersection of normal extensions is normal. -/
@[stacks 09HP]
/--
Instance `normal_iInf` / 实例 `normal_iInf`

English:
instance normal_iInf
  signature: {ι : Type*} [hι : Nonempty ι]
  body: by
  refine { toIsAlgebraic := ?_, splits' := fun x => ?_ }
  · let f := inclusion (iInf_le t hι.some)
    exact Algebra.IsAlgebraic.of_injective f f.injective
  · have hx : forall i, Splits ((minpoly F x).map (algebraMap F (t i))) := by
      intro i
      rw [← minpoly.algHom_eq (inclusion (iInf_l

中文:
实例 normal_iInf
  签名: {ι : 类型} [hι : 非空 ι]
  定义体: by
  refine { toIsAlgebraic := ?_, splits' := fun x => ?_ }
  · let f := inclusion (iInf_le t hι.some)
    exact Algebra.IsAlgebraic.of_injective f f.injective
  · have hx : forall i, Splits ((minpoly F x).map (algebraMap F (t i))) := by
      intro i
      rw [← minpoly.algHom_eq (inclusion (iInf_l

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.of_injective, IsAlgebraic, Splits, Splits.of_isScalarTower, algHom_eq, algebraMap, f.injective, iInf_le, inclusion, injective, minpoly, minpoly.algHom_eq, of_injective, of_isScalarTower, splits, splits_iff_mem, toIsAlgebraic
-/
instance normal_iInf {ι : Type*} [hι : Nonempty ι]
    (t : ι -> IntermediateField F K) [h : forall i, Normal F (t i)] :
    Normal F (⨅ i, t i : IntermediateField F K) := by
  refine { toIsAlgebraic := ?_, splits' := fun x => ?_ }
  · let f := inclusion (iInf_le t hι.some)
    exact Algebra.IsAlgebraic.of_injective f f.injective
  · have hx : forall i, Splits ((minpoly F x).map (algebraMap F (t i))) := by
      intro i
      rw [← minpoly.algHom_eq (inclusion (iInf_le t i)) (inclusion (iInf_le t i)).injective]
      exact (h i).splits' (inclusion (iInf_le t i) x)
    simp only [splits_iff_mem (Splits.of_isScalarTower K (hx hι.some))] at hx ⊢
    rintro y hy - ⟨-, ⟨i, rfl⟩, rfl⟩
    exact hx i y hy

@[stacks 09HP]
/--
Instance `normal_inf` / 实例 `normal_inf`

English:
instance normal_inf
  body: iInf_bool_eq (f := Bool.rec E' E) ▸ normal_iInf (h := by rintro (_ | _) <;> infer_instance)

中文:
实例 normal_inf
  定义体: iInf_bool_eq (f := Bool.rec E' E) ▸ normal_iInf (h := by rintro (_ | _) <;> infer_instance)

Depends on / 依赖: Bool.rec, iInf_bool_eq, infer_instance, normal_iInf
-/
instance normal_inf
    (E E' : IntermediateField F K) [Normal F E] [Normal F E'] :
    Normal F (E ⊓ E' : IntermediateField F K) :=
  iInf_bool_eq (f := Bool.rec E' E) ▸ normal_iInf (h := by rintro (_ | _) <;> infer_instance)

end IntermediateField

variable {F} {K}
variable {K₁ K₂ K₃ : Type*} [Field K₁] [Field K₂] [Field K₃] [Algebra F K₁]
  [Algebra F K₂] [Algebra F K₃] (ϕ : K₁ ->ₐ[F] K₂) (χ : K₁ ≃ₐ[F] K₂) (ψ : K₂ ->ₐ[F] K₃)
  (ω : K₂ ≃ₐ[F] K₃)

section Restrict

variable (E : Type*) [Field E] [Algebra F E] [Algebra E K₁] [Algebra E K₂] [Algebra E K₃]
  [IsScalarTower F E K₁] [IsScalarTower F E K₂] [IsScalarTower F E K₃]

/--
theorem `AlgHom.fieldRange_of_normal` / 定理 `AlgHom.fieldRange_of_normal`

English:
theorem AlgHom.fieldRange_of_normal
  statement: {E : IntermediateField F K} [Normal F E]
  proof: by
  let g := f.restrictNormal' E
  rw [← show E.val.comp ↑g = f from DFunLike.ext_iff.mpr (f.restrictNormal_commutes E)]; rw [← AlgHom.map_fieldRange]; rw [AlgEquiv.fieldRange_eq_top g]; rw [← AlgHom.fieldRange_eq_map]; rw [IntermediateField.fieldRange_val]

中文:
定理 代数态射.fieldRange_of_normal
  结论: {E : 中间域 F K} [正规 F E]
  证明: by
  let g := f.restrictNormal' E
  rw [← show E.val.comp ↑g = f from DFunLike.ext_iff.mpr (f.restrictNormal_commutes E)]; rw [← AlgHom.map_fieldRange]; rw [AlgEquiv.fieldRange_eq_top g]; rw [← AlgHom.fieldRange_eq_map]; rw [IntermediateField.fieldRange_val]

Depends on / 依赖: AlgEquiv, AlgEquiv.fieldRange_eq_top, AlgHom, AlgHom.fieldRange_eq_map, AlgHom.map_fieldRange, DFunLike, DFunLike.ext_iff.mpr, E.val.comp, IntermediateField, IntermediateField.fieldRange_val, ext_iff, f.restrictNormal, f.restrictNormal_commutes, fieldRange_eq_map, fieldRange_eq_top, fieldRange_val, map_fieldRange, restrictNormal, restrictNormal_commutes
-/
theorem AlgHom.fieldRange_of_normal {E : IntermediateField F K} [Normal F E]
    (f : E ->ₐ[F] K) : f.fieldRange = E := by
  let g := f.restrictNormal' E
  rw [← show E.val.comp ↑g = f from DFunLike.ext_iff.mpr (f.restrictNormal_commutes E)]; rw [← AlgHom.map_fieldRange]; rw [AlgEquiv.fieldRange_eq_top g]; rw [← AlgHom.fieldRange_eq_map]; rw [IntermediateField.fieldRange_val]

end Restrict

section lift

variable (E : Type*) [Field E] [Algebra F E] [Algebra K₁ E] [Algebra K₂ E] [IsScalarTower F K₁ E]
  [IsScalarTower F K₂ E]

/-- If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra homomorphism `ϕ : K₁ →ₐ[F] K₂` to `ϕ.liftNormal E : E →ₐ[F] E`. -/
@[stacks 0BME "Part 2"]
/--
Definition of `AlgHom.liftNormal` / `AlgHom.liftNormal` 的定义

English:
definition AlgHom.liftNormal
  signature: [h : Normal F E]
  body: @AlgHom.restrictScalars F K₁ E E _ _ _ _ _ _
((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _ _ _ _
Nonempty.some
      @IntermediateField.nonempty_algHom_of_adjoin_splits _ _ _ _ _ _ _
        ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _
        (fun x _ => ⟨(h.out x

中文:
定义 代数态射.liftNormal
  签名: [h : 正规 F E]
  定义体: @AlgHom.restrictScalars F K₁ E E _ _ _ _ _ _
((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _ _ _ _
Nonempty.some
      @IntermediateField.nonempty_algHom_of_adjoin_splits _ _ _ _ _ _ _
        ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _
        (fun x _ => ⟨(h.out x

Depends on / 依赖: AlgHom, AlgHom.restrictScalars, FastIsEmpty, FastSubsingleton, IntermediateField, IntermediateField.adjoin_univ, IntermediateField.nonempty_algHom_of_adjoin_splits, IsIntegral, IsIntegral.minpoly_splits_tower_top, IsScalarTower, IsScalarTower.toAlgHom, Nonempty, Nonempty.some, RingHom, RingHom.toAlgebra, adjoin_univ, h.out, minpoly_splits_tower_top, nonempty_algHom_of_adjoin_splits, restrictScalars
-/
noncomputable def AlgHom.liftNormal [h : Normal F E] : E ->ₐ[F] E :=
  @AlgHom.restrictScalars F K₁ E E _ _ _ _ _ _
((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _ _ _ _
Nonempty.some
      @IntermediateField.nonempty_algHom_of_adjoin_splits _ _ _ _ _ _ _
        ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _
        (fun x _ => ⟨(h.out x).1.tower_top,
          @IsIntegral.minpoly_splits_tower_top F K₁ E E _ _ _ _ _ _ _ _ x
            (RingHom.toAlgebra _) _ _ (h.out x).1 (h.out x).2⟩)
        (IntermediateField.adjoin_univ _ _)

@[simp]
/--
theorem `AlgHom.liftNormal_commutes` / 定理 `AlgHom.liftNormal_commutes`

English:
theorem AlgHom.liftNormal_commutes
  given: [Normal F E] (x : K₁)
  proof: -- We have to specify one `Algebra` instance by unification, not synthesis.
  @AlgHom.commutes K₁ E E _ _ _ _ (_) _ _

@[simp]

中文:
定理 代数态射.liftNormal_commutes
  条件: [正规 F E] (x : K₁)
  证明: -- We have to specify one `Algebra` instance by unification, not synthesis.
  @AlgHom.commutes K₁ E E _ _ _ _ (_) _ _

@[simp]
-/
theorem AlgHom.liftNormal_commutes [Normal F E] (x : K₁) :
    ϕ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (ϕ x) :=
  -- We have to specify one `Algebra` instance by unification, not synthesis.
  @AlgHom.commutes K₁ E E _ _ _ _ (_) _ _

@[simp]
/--
theorem `AlgHom.restrict_liftNormal` / 定理 `AlgHom.restrict_liftNormal`

English:
theorem AlgHom.restrict_liftNormal
  given: (ϕ : K₁ ->ₐ[F] K₁) [Normal F K₁] [Normal F E]
  proof: AlgHom.ext fun x =>
    (algebraMap K₁ E).injective
      (Eq.trans (AlgHom.restrictNormal_commutes _ K₁ x) (ϕ.liftNormal_commutes E x))

中文:
定理 代数态射.restrict_liftNormal
  条件: (ϕ : K₁ ->ₐ[F] K₁) [正规 F K₁] [正规 F E]
  证明: AlgHom.ext fun x =>
    (algebraMap K₁ E).injective
      (Eq.trans (AlgHom.restrictNormal_commutes _ K₁ x) (ϕ.liftNormal_commutes E x))

Depends on / 依赖: AlgHom, AlgHom.ext, AlgHom.restrictNormal_commutes, Eq.trans, algebraMap, injective, liftNormal_commutes, restrictNormal_commutes
-/
theorem AlgHom.restrict_liftNormal (ϕ : K₁ ->ₐ[F] K₁) [Normal F K₁] [Normal F E] :
    (ϕ.liftNormal E).restrictNormal K₁ = ϕ :=
  AlgHom.ext fun x =>
    (algebraMap K₁ E).injective
      (Eq.trans (AlgHom.restrictNormal_commutes _ K₁ x) (ϕ.liftNormal_commutes E x))

/--
Definition of `AlgEquiv.liftNormal` / `AlgEquiv.liftNormal` 的定义

English:
definition AlgEquiv.liftNormal
  signature: [Normal F E]
  body: AlgEquiv.ofBijective (χ.toAlgHom.liftNormal E) (AlgHom.normal_bijective F E E _)

@[simp]

中文:
定义 代数等价.liftNormal
  签名: [正规 F E]
  定义体: AlgEquiv.ofBijective (χ.toAlgHom.liftNormal E) (AlgHom.normal_bijective F E E _)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, AlgHom, AlgHom.normal_bijective, liftNormal, normal_bijective, ofBijective, toAlgHom, toAlgHom.liftNormal
-/
noncomputable def AlgEquiv.liftNormal [Normal F E] : Gal(E/F) :=
  AlgEquiv.ofBijective (χ.toAlgHom.liftNormal E) (AlgHom.normal_bijective F E E _)

@[simp]
/--
theorem `AlgEquiv.liftNormal_commutes` / 定理 `AlgEquiv.liftNormal_commutes`

English:
theorem AlgEquiv.liftNormal_commutes
  given: [Normal F E] (x : K₁)
  proof: χ.toAlgHom.liftNormal_commutes E x

@[simp]

中文:
定理 代数等价.liftNormal_commutes
  条件: [正规 F E] (x : K₁)
  证明: χ.toAlgHom.liftNormal_commutes E x

@[simp]

Depends on / 依赖: liftNormal_commutes, toAlgHom, toAlgHom.liftNormal_commutes
-/
theorem AlgEquiv.liftNormal_commutes [Normal F E] (x : K₁) :
    χ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (χ x) :=
  χ.toAlgHom.liftNormal_commutes E x

@[simp]
/--
theorem `AlgEquiv.restrict_liftNormal` / 定理 `AlgEquiv.restrict_liftNormal`

English:
theorem AlgEquiv.restrict_liftNormal
  given: (χ : K₁ ≃ₐ[F] K₁) [Normal F K₁] [Normal F E]
  proof: AlgEquiv.ext fun x =>
    (algebraMap K₁ E).injective
      (Eq.trans (AlgEquiv.restrictNormal_commutes _ K₁ x) (χ.liftNormal_commutes E x))

中文:
定理 代数等价.restrict_liftNormal
  条件: (χ : K₁ ≃ₐ[F] K₁) [正规 F K₁] [正规 F E]
  证明: AlgEquiv.ext fun x =>
    (algebraMap K₁ E).injective
      (Eq.trans (AlgEquiv.restrictNormal_commutes _ K₁ x) (χ.liftNormal_commutes E x))

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, AlgEquiv.restrictNormal_commutes, Eq.trans, algebraMap, injective, liftNormal_commutes, restrictNormal_commutes
-/
theorem AlgEquiv.restrict_liftNormal (χ : K₁ ≃ₐ[F] K₁) [Normal F K₁] [Normal F E] :
    (χ.liftNormal E).restrictNormal K₁ = χ :=
  AlgEquiv.ext fun x =>
    (algebraMap K₁ E).injective
      (Eq.trans (AlgEquiv.restrictNormal_commutes _ K₁ x) (χ.liftNormal_commutes E x))

/--
theorem `AlgEquiv.restrictNormalHom_surjective` / 定理 `AlgEquiv.restrictNormalHom_surjective`

English:
theorem AlgEquiv.restrictNormalHom_surjective
  given: [Normal F K₁] [Normal F E]
  proof: fun χ =>
  ⟨χ.liftNormal E, χ.restrict_liftNormal E⟩

中文:
定理 代数等价.restrictNormalHom_surjective
  条件: [正规 F K₁] [正规 F E]
  证明: fun χ =>
  ⟨χ.liftNormal E, χ.restrict_liftNormal E⟩
-/
theorem AlgEquiv.restrictNormalHom_surjective [Normal F K₁] [Normal F E] :
    Function.Surjective (AlgEquiv.restrictNormalHom K₁ : Gal(E/F) -> K₁ ≃ₐ[F] K₁) := fun χ =>
  ⟨χ.liftNormal E, χ.restrict_liftNormal E⟩

open IntermediateField in
/--
theorem `Normal.minpoly_eq_iff_mem_orbit` / 定理 `Normal.minpoly_eq_iff_mem_orbit`

English:
theorem Normal.minpoly_eq_iff_mem_orbit
  given: [h : Normal F E] {x y : E}
  proof: by
  refine ⟨fun he => ?_, fun ⟨f, he⟩ => he ▸ minpoly.algEquiv_eq f y⟩
  obtain ⟨φ, hφ⟩ := exists_algHom_of_splits_of_aeval (normal_iff.mp h) (he ▸ minpoly.aeval F x)
  exact ⟨AlgEquiv.ofBijective φ (φ.normal_bijective F E E), hφ⟩

中文:
定理 正规.minpoly_eq_iff_mem_orbit
  条件: [h : 正规 F E] {x y : E}
  证明: by
  refine ⟨fun he => ?_, fun ⟨f, he⟩ => he ▸ minpoly.algEquiv_eq f y⟩
  obtain ⟨φ, hφ⟩ := exists_algHom_of_splits_of_aeval (normal_iff.mp h) (he ▸ minpoly.aeval F x)
  exact ⟨AlgEquiv.ofBijective φ (φ.normal_bijective F E E), hφ⟩

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, algEquiv_eq, exists_algHom_of_splits_of_aeval, minpoly, minpoly.aeval, minpoly.algEquiv_eq, normal_bijective, normal_iff, normal_iff.mp, ofBijective
-/
theorem Normal.minpoly_eq_iff_mem_orbit [h : Normal F E] {x y : E} :
    minpoly F x = minpoly F y ↔ x in MulAction.orbit Gal(E/F) y := by
  refine ⟨fun he => ?_, fun ⟨f, he⟩ => he ▸ minpoly.algEquiv_eq f y⟩
  obtain ⟨φ, hφ⟩ := exists_algHom_of_splits_of_aeval (normal_iff.mp h) (he ▸ minpoly.aeval F x)
  exact ⟨AlgEquiv.ofBijective φ (φ.normal_bijective F E E), hφ⟩

variable (F K₁)

/--
theorem `isSolvable_of_isScalarTower` / 定理 `isSolvable_of_isScalarTower`

English:
theorem isSolvable_of_isScalarTower
  statement: [Normal F K₁] [h1 : Group.IsSolvable (K₁ ≃ₐ[F] K₁)]
  proof: by
  let f : (E ≃ₐ[K₁] E) ->* Gal(E/F) :=
    { toFun := fun ϕ =>
        AlgEquiv.ofAlgHom (ϕ.toAlgHom.restrictScalars F) (ϕ.symm.toAlgHom.restrictScalars F)
          (AlgHom.ext fun x => ϕ.apply_symm_apply x) (AlgHom.ext fun x => ϕ.symm_apply_apply x)
      map_one' := AlgEquiv.ext fun _ => rfl
 

中文:
定理 isSolvable_of_isScalarTower
  结论: [正规 F K₁] [h1 : 群.是可解 (K₁ ≃ₐ[F] K₁)]
  证明: by
  let f : (E ≃ₐ[K₁] E) ->* Gal(E/F) :=
    { toFun := fun ϕ =>
        AlgEquiv.ofAlgHom (ϕ.toAlgHom.restrictScalars F) (ϕ.symm.toAlgHom.restrictScalars F)
          (AlgHom.ext fun x => ϕ.apply_symm_apply x) (AlgHom.ext fun x => ϕ.symm_apply_apply x)
      map_one' := AlgEquiv.ext fun _ => rfl
 

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, AlgEquiv.ofAlgHom, AlgEquiv.restrictNormalHom, AlgHom, AlgHom.ext, Eq.trans, Group.isSolvable_of_ker_le_range, apply_symm_apply, commutes, inst.inst.false, isSolvable_of_ker_le_range, map_mul, map_one, ofAlgHom, restrictNor, restrictNormalHom, restrictScalars, symm.toAlgHom.restrictScalars, symm_apply_apply
-/
theorem isSolvable_of_isScalarTower [Normal F K₁] [h1 : Group.IsSolvable (K₁ ≃ₐ[F] K₁)]
    [h2 : Group.IsSolvable (E ≃ₐ[K₁] E)] : Group.IsSolvable Gal(E/F) := by
  let f : (E ≃ₐ[K₁] E) ->* Gal(E/F) :=
    { toFun := fun ϕ =>
        AlgEquiv.ofAlgHom (ϕ.toAlgHom.restrictScalars F) (ϕ.symm.toAlgHom.restrictScalars F)
          (AlgHom.ext fun x => ϕ.apply_symm_apply x) (AlgHom.ext fun x => ϕ.symm_apply_apply x)
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  refine
    Group.isSolvable_of_ker_le_range f (AlgEquiv.restrictNormalHom K₁) fun ϕ hϕ =>
      ⟨{ ϕ with commutes' := fun x => ?_ }, AlgEquiv.ext fun _ => rfl⟩
  exact Eq.trans (ϕ.restrictNormal_commutes K₁ x).symm (congr_arg _ (AlgEquiv.ext_iff.mp hϕ x))

end lift

namespace minpoly

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

open AlgEquiv IntermediateField

/--
theorem `exists_algEquiv_of_root` / 定理 `exists_algEquiv_of_root`

English:
theorem exists_algEquiv_of_root
  statement: [Normal K L] {x y : L} (hy : IsAlgebraic K y)
  proof: by
  have hx : IsAlgebraic K x := ⟨minpoly K y, ne_zero hy.isIntegral, h_ev⟩
  set f : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := algEquiv hx (eq_of_root hy h_ev)
  have hxy : (liftNormal f L) ((algebraMap (↥K⟮x⟯) L) (AdjoinSimple.gen K x)) = y := by
    rw [liftNormal_commutes f L]; rw [algEquiv_apply]; rw [AdjoinSimple.a

中文:
定理 存在_algEquiv_of_root
  结论: [正规 K L] {x y : L} (hy : 是代数 K y)
  证明: by
  have hx : IsAlgebraic K x := ⟨minpoly K y, ne_zero hy.isIntegral, h_ev⟩
  set f : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := algEquiv hx (eq_of_root hy h_ev)
  have hxy : (liftNormal f L) ((algebraMap (↥K⟮x⟯) L) (AdjoinSimple.gen K x)) = y := by
    rw [liftNormal_commutes f L]; rw [algEquiv_apply]; rw [AdjoinSimple.a

Depends on / 依赖: AdjoinSimple, AdjoinSimple.algebraMap_gen, AdjoinSimple.gen, IsAlgebraic, algEquiv, algEquiv_apply, algebraMap, algebraMap_gen, eq_of_root, h_ev, hy.isIntegral, isIntegral, liftNormal, liftNormal_commutes, minpoly, ne_zero
-/
theorem exists_algEquiv_of_root [Normal K L] {x y : L} (hy : IsAlgebraic K y)
    (h_ev : (Polynomial.aeval x) (minpoly K y) = 0) : exists σ : Gal(L/K), σ x = y := by
  have hx : IsAlgebraic K x := ⟨minpoly K y, ne_zero hy.isIntegral, h_ev⟩
  set f : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := algEquiv hx (eq_of_root hy h_ev)
  have hxy : (liftNormal f L) ((algebraMap (↥K⟮x⟯) L) (AdjoinSimple.gen K x)) = y := by
    rw [liftNormal_commutes f L]; rw [algEquiv_apply]; rw [AdjoinSimple.algebraMap_gen K y]
  exact ⟨(liftNormal f L), hxy⟩

/--
theorem `exists_algEquiv_of_root'` / 定理 `exists_algEquiv_of_root'`

English:
theorem exists_algEquiv_of_root'
  statement: [Normal K L] {x y : L} (hy : IsAlgebraic K y)
  proof: by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_of_root hy h_ev
  use σ.symm
  rw [← hσ]; rw [symm_apply_apply]

中文:
定理 存在_algEquiv_of_root'
  结论: [正规 K L] {x y : L} (hy : 是代数 K y)
  证明: by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_of_root hy h_ev
  use σ.symm
  rw [← hσ]; rw [symm_apply_apply]

Depends on / 依赖: exists_algEquiv_of_root, h_ev, symm_apply_apply
-/
theorem exists_algEquiv_of_root' [Normal K L] {x y : L} (hy : IsAlgebraic K y)
    (h_ev : (Polynomial.aeval x) (minpoly K y) = 0) : exists σ : Gal(L/K), σ y = x := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_of_root hy h_ev
  use σ.symm
  rw [← hσ]; rw [symm_apply_apply]

end minpoly

/--
Instance `Algebra.IsQuadraticExtension.normal` / 实例 `Algebra.IsQuadraticExtension.normal`

English:
instance Algebra.IsQuadraticExtension.normal
  signature: (F K : Type*) [Field F] [Field K] [Algebra F K]
  body: by
    intro x
    obtain h | h := le_iff_lt_or_eq.mp (finrank_eq_two F K ▸ minpoly.natDegree_le x)
· exact Splits.of_natDegree_le_one natDegree_map_le.trans (by rwa [Nat.le_iff_lt_add_one])
    · exact Splits.of_natDegree_eq_two ((natDegree_map _).trans h)
        ((eval_map_algebraMap _ _).trans (

中文:
实例 代数.是QuadraticExtension.normal
  签名: (F K : 类型) [域 F] [域 K] [代数 F K]
  定义体: by
    intro x
    obtain h | h := le_iff_lt_or_eq.mp (finrank_eq_two F K ▸ minpoly.natDegree_le x)
· exact Splits.of_natDegree_le_one natDegree_map_le.trans (by rwa [Nat.le_iff_lt_add_one])
    · exact Splits.of_natDegree_eq_two ((natDegree_map _).trans h)
        ((eval_map_algebraMap _ _).trans (

Depends on / 依赖: Nat.le_iff_lt_add_one, Splits, Splits.of_natDegree_eq_two, Splits.of_natDegree_le_one, eval_map_algebraMap, finrank_eq_two, le_iff_lt_add_one, le_iff_lt_or_eq, le_iff_lt_or_eq.mp, minpoly, minpoly.aeval, minpoly.natDegree_le, natDegree_le, natDegree_map, natDegree_map_le, natDegree_map_le.trans, of_natDegree_eq_two, of_natDegree_le_one
-/
instance Algebra.IsQuadraticExtension.normal (F K : Type*) [Field F] [Field K] [Algebra F K]
    [IsQuadraticExtension F K] :
    Normal F K where
  splits' := by
    intro x
    obtain h | h := le_iff_lt_or_eq.mp (finrank_eq_two F K ▸ minpoly.natDegree_le x)
· exact Splits.of_natDegree_le_one natDegree_map_le.trans (by rwa [Nat.le_iff_lt_add_one])
    · exact Splits.of_natDegree_eq_two ((natDegree_map _).trans h)
        ((eval_map_algebraMap _ _).trans (minpoly.aeval F x))
