/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!

# Localization and multivariate polynomial rings

In this file we show some results connecting multivariate polynomial rings and localization.

## Main results

- `MvPolynomial.isLocalization`: If `S` is the localization of `R` at a submonoid `M`, then
  `MvPolynomial σ S` is the localization of `MvPolynomial σ R` at the image of `M` in
  `MvPolynomial σ R`.

-/

@[expose] public section

variable {σ R : Type*} [CommRing R] (M : Submonoid R)
variable (S : Type*) [CommRing S] [Algebra R S]

namespace MvPolynomial

variable [IsLocalization M S]

attribute [local instance] algebraMvPolynomial

/--
Instance `isLocalization` / 实例 `isLocalization`

English:
instance isLocalization
  signature: : IsLocalization (M.map <| C (σ := σ)) (MvPolynomial σ S)
  body: isLocalizedModule_iff_isLocalization.mp (isLocalizedModule_iff_isBaseChange M S _).mpr
    .of_equiv (algebraTensorAlgEquiv _ _).toLinearEquiv fun _ => by simp

中文:
实例 isLocalization
  签名: : IsLocalization (M.map <| C (σ := σ)) (MvPolynomial σ S)
  定义体: isLocalizedModule_iff_isLocalization.mp (isLocalizedModule_iff_isBaseChange M S _).mpr
    .of_equiv (algebraTensorAlgEquiv _ _).toLinearEquiv fun _ => by simp

Depends on / 依赖: MvPolynomial
-/
instance isLocalization : IsLocalization (M.map <| C (σ := σ)) (MvPolynomial σ S) :=
isLocalizedModule_iff_isLocalization.mp (isLocalizedModule_iff_isBaseChange M S _).mpr
    .of_equiv (algebraTensorAlgEquiv _ _).toLinearEquiv fun _ => by simp

/--
lemma `isLocalization_C_mk'` / 引理 `isLocalization_C_mk'`

English:
lemma isLocalization_C_mk'
  given: (a : R) (m : M)
  proof: by
  simp_rw [IsLocalization.eq_mk'_iff_mul_eq, algebraMap_def, map_C, ← map_mul,
    IsLocalization.mk'_spec]

中文:
引理 isLocalization_C_mk'
  条件: (a : R) (m : M)
  证明: by
  simp_rw [IsLocalization.eq_mk'_iff_mul_eq, algebraMap_def, map_C, ← map_mul,
    IsLocalization.mk'_spec]
-/
lemma isLocalization_C_mk' (a : R) (m : M) :
    C (IsLocalization.mk' S a m) = IsLocalization.mk' (MvPolynomial σ S) (C (σ := σ) a)
      ⟨C m, Submonoid.mem_map_of_mem C m.property⟩ := by
  simp_rw [IsLocalization.eq_mk'_iff_mul_eq, algebraMap_def, map_C, ← map_mul,
    IsLocalization.mk'_spec]

end MvPolynomial

namespace IsLocalization.Away

open MvPolynomial

variable (r : R) [IsLocalization.Away r S]

set_option backward.privateInPublic true in
/-- The canonical algebra map from `MvPolynomial Unit R` quotiented by
`C r * X () - 1` to the localization of `R` away from `r`. -/
private noncomputable
/--
Definition of `auxHom` / `auxHom` 的定义

English:
definition auxHom
  signature: : (MvPolynomial Unit R) ⧸ (Ideal.span { C r * X () - 1 }) ->ₐ[R] S
  body: Ideal.Quotient.liftₐ (Ideal.span { C r * X () - 1}) (aeval (fun _ => invSelf r)) by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro p ⟨q, rfl⟩
      simp
    · simp
    · intro p q _ _ hp hq
      simp [hp, hq]
    · intro a x _ hx
      simp [hx]

@[simp]

中文:
定义 auxHom
  签名: : (MvPolynomial Unit R) ⧸ (Ideal.span { C r * X () - 1 }) ->ₐ[R] S
  定义体: Ideal.Quotient.liftₐ (Ideal.span { C r * X () - 1}) (aeval (fun _ => invSelf r)) by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro p ⟨q, rfl⟩
      simp
    · simp
    · intro p q _ _ hp hq
      simp [hp, hq]
    · intro a x _ hx
      simp [hx]

@[simp]

Depends on / 依赖: Ideal.Quotient.lift, Ideal.span, Quotient, Submodule, Submodule.span_induction, invSelf, span_induction
-/
def auxHom : (MvPolynomial Unit R) ⧸ (Ideal.span { C r * X () - 1 }) ->ₐ[R] S :=
Ideal.Quotient.liftₐ (Ideal.span { C r * X () - 1}) (aeval (fun _ => invSelf r)) by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro p ⟨q, rfl⟩
      simp
    · simp
    · intro p q _ _ hp hq
      simp [hp, hq]
    · intro a x _ hx
      simp [hx]

@[simp]
/--
lemma `auxHom_mk` / 引理 `auxHom_mk`

English:
lemma auxHom_mk
  given: (p : MvPolynomial Unit R)
  proof: rfl

中文:
引理 auxHom_mk
  条件: (p : MvPolynomial Unit R)
  证明: rfl
-/
private lemma auxHom_mk (p : MvPolynomial Unit R) :
    auxHom S r p = aeval (S₁ := S) (fun _ => invSelf r) p :=
  rfl

set_option backward.privateInPublic true in
private noncomputable
/--
Definition of `auxInv` / `auxInv` 的定义

English:
definition auxInv
  signature: : S ->+* (MvPolynomial Unit R) ⧸ Ideal.span { C r * X () - 1 }
  body: letI g : R ->+* MvPolynomial Unit R ⧸ (Ideal.span { C r * X () - 1 }) :=
    (Ideal.Quotient.mk _).comp C
IsLocalization.Away.lift (S := S) (g := g) r by
    simp only [RingHom.coe_comp, Function.comp_apply, g]
    rw [isUnit_iff_exists_inv]
    use (Ideal.Quotient.mk _ <| X ())
    rw [← map_mul]; 

中文:
定义 auxInv
  签名: : S ->+* (MvPolynomial Unit R) ⧸ Ideal.span { C r * X () - 1 }
  定义体: letI g : R ->+* MvPolynomial Unit R ⧸ (Ideal.span { C r * X () - 1 }) :=
    (Ideal.Quotient.mk _).comp C
IsLocalization.Away.lift (S := S) (g := g) r by
    simp only [RingHom.coe_comp, Function.comp_apply, g]
    rw [isUnit_iff_exists_inv]
    use (Ideal.Quotient.mk _ <| X ())
    rw [← map_mul]; 

Depends on / 依赖: Function, Function.comp_apply, Ideal.Quotient.mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton_self, Ideal.span, IsLocalization, IsLocalization.Away.lift, MvPolynomial, Quotient, RingHom, RingHom.coe_comp, coe_comp, comp_apply, isUnit_iff_exists_inv, map_mul, map_one, mem_span_singleton_self, mk_eq_mk_iff_sub_mem
-/
def auxInv : S ->+* (MvPolynomial Unit R) ⧸ Ideal.span { C r * X () - 1 } :=
  letI g : R ->+* MvPolynomial Unit R ⧸ (Ideal.span { C r * X () - 1 }) :=
    (Ideal.Quotient.mk _).comp C
IsLocalization.Away.lift (S := S) (g := g) r by
    simp only [RingHom.coe_comp, Function.comp_apply, g]
    rw [isUnit_iff_exists_inv]
    use (Ideal.Quotient.mk _ <| X ())
    rw [← map_mul]; rw [← map_one (Ideal.Quotient.mk _)]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.mem_span_singleton_self (C r * X () - 1)

/--
lemma `auxHom_auxInv` / 引理 `auxHom_auxInv`

English:
lemma auxHom_auxInv
  statement: (auxHom S r).toRingHom.comp (auxInv S r) = RingHom.id S
  proof: by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  simp [auxInv]

中文:
引理 auxHom_auxInv
  结论: (auxHom S r).toRingHom.comp (auxInv S r) = RingHom.id S
  证明: by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  simp [auxInv]
-/
private lemma auxHom_auxInv : (auxHom S r).toRingHom.comp (auxInv S r) = RingHom.id S := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  simp [auxInv]

/--
lemma `auxInv_auxHom` / 引理 `auxInv_auxHom`

English:
lemma auxInv_auxHom
  statement: (auxInv S r).comp (auxHom (S := S) r).toRingHom = RingHom.id _
  proof: by
  rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective)]
  ext x
  · simp [auxInv]
  · simp only [auxInv, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, auxHom_mk, aeval_X, RingHomCompTriple.comp_eq, invSelf, Away.lift,
      lift_mk'_spec]
    simp onl

中文:
引理 auxInv_auxHom
  结论: (auxInv S r).comp (auxHom (S := S) r).toRingHom = RingHom.id _
  证明: by
  rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective)]
  ext x
  · simp [auxInv]
  · simp only [auxInv, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, auxHom_mk, aeval_X, RingHomCompTriple.comp_eq, invSelf, Away.lift,
      lift_mk'_spec]
    simp onl
-/
private lemma auxInv_auxHom : (auxInv S r).comp (auxHom (S := S) r).toRingHom = RingHom.id _ := by
  rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective)]
  ext x
  · simp [auxInv]
  · simp only [auxInv, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, auxHom_mk, aeval_X, RingHomCompTriple.comp_eq, invSelf, Away.lift,
      lift_mk'_spec]
    simp only [map_one]
    rw [← map_one (Ideal.Quotient.mk _)]; rw [← map_mul]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [← Ideal.neg_mem_iff]; rw [neg_sub]
    exact Ideal.mem_span_singleton_self (C r * X x - 1)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `mvPolynomialQuotientEquiv` / `mvPolynomialQuotientEquiv` 的定义

English:
definition mvPolynomialQuotientEquiv
  signature: :
  body: auxHom S r
  invFun := auxInv S r
  left_inv x := by
    simpa using congrFun (congrArg DFunLike.coe <| auxInv_auxHom S r) x
  right_inv s := by
    simpa using congrFun (congrArg DFunLike.coe <| auxHom_auxInv S r) s
  map_mul' := by simp
  map_add' := by simp
  commutes' := by simp

@[simp]

中文:
定义 mvPolynomialQuotientEquiv
  签名: :
  定义体: auxHom S r
  invFun := auxInv S r
  left_inv x := by
    simpa using congrFun (congrArg DFunLike.coe <| auxInv_auxHom S r) x
  right_inv s := by
    simpa using congrFun (congrArg DFunLike.coe <| auxHom_auxInv S r) s
  map_mul' := by simp
  map_add' := by simp
  commutes' := by simp

@[simp]

Depends on / 依赖: auxHom
-/
noncomputable def mvPolynomialQuotientEquiv :
    ((MvPolynomial Unit R) ⧸ Ideal.span { C r * X () - 1 }) ≃ₐ[R] S where
  toFun := auxHom S r
  invFun := auxInv S r
  left_inv x := by
    simpa using congrFun (congrArg DFunLike.coe <| auxInv_auxHom S r) x
  right_inv s := by
    simpa using congrFun (congrArg DFunLike.coe <| auxHom_auxInv S r) s
  map_mul' := by simp
  map_add' := by simp
  commutes' := by simp

@[simp]
/--
lemma `mvPolynomialQuotientEquiv_apply` / 引理 `mvPolynomialQuotientEquiv_apply`

English:
lemma mvPolynomialQuotientEquiv_apply
  given: (p : MvPolynomial Unit R)
  proof: rfl

中文:
引理 mvPolynomialQuotientEquiv_apply
  条件: (p : MvPolynomial Unit R)
  证明: rfl

Depends on / 依赖: invSelf
-/
lemma mvPolynomialQuotientEquiv_apply (p : MvPolynomial Unit R) :
    mvPolynomialQuotientEquiv S r (Ideal.Quotient.mk _ p) = aeval (S₁ := S) (fun _ => invSelf r) p :=
  rfl

end IsLocalization.Away
