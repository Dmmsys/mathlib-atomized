/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, David Kurniadi Angdinata, Devon Tuma, Riccardo Brasca
-/
module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Quotients of polynomial rings
-/

@[expose] public section



open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/--
Definition of `quotientSpanXSubCAlgEquiv` / `quotientSpanXSubCAlgEquiv` 的定义

English:
definition quotientSpanXSubCAlgEquiv
  signature: (x : R)
  body: let e := RingHom.quotientKerEquivOfRightInverse (fun x => by
    exact eval_C : Function.RightInverse (fun a : R => (C a : R[X])) (@aeval R R _ _ _ x))
  (Ideal.quotientEquivAlgOfEq R (ker_evalRingHom x).symm).trans
    { e with commutes' := fun r => e.apply_symm_apply r }

@[simp]

中文:
定义 quotientSpanXSubCAlgEquiv
  签名: (x : R)
  定义体: let e := RingHom.quotientKerEquivOfRightInverse (fun x => by
    exact eval_C : Function.RightInverse (fun a : R => (C a : R[X])) (@aeval R R _ _ _ x))
  (Ideal.quotientEquivAlgOfEq R (ker_evalRingHom x).symm).trans
    { e with commutes' := fun r => e.apply_symm_apply r }

@[simp]

Depends on / 依赖: Function, Function.RightInverse, Ideal.quotientEquivAlgOfEq, RightInverse, RingHom, RingHom.quotientKerEquivOfRightInverse, apply_symm_apply, commutes, e.apply_symm_apply, eval_C, ker_evalRingHom, quotientEquivAlgOfEq, quotientKerEquivOfRightInverse
-/
noncomputable def quotientSpanXSubCAlgEquiv (x : R) :
    (R[X] ⧸ Ideal.span ({X - C x} : Set R[X])) ≃ₐ[R] R :=
  let e := RingHom.quotientKerEquivOfRightInverse (fun x => by
    exact eval_C : Function.RightInverse (fun a : R => (C a : R[X])) (@aeval R R _ _ _ x))
  (Ideal.quotientEquivAlgOfEq R (ker_evalRingHom x).symm).trans
    { e with commutes' := fun r => e.apply_symm_apply r }

@[simp]
/--
theorem `quotientSpanXSubCAlgEquiv_mk` / 定理 `quotientSpanXSubCAlgEquiv_mk`

English:
theorem quotientSpanXSubCAlgEquiv_mk
  given: (x : R) (p : R[X])
  proof: rfl

@[simp]

中文:
定理 quotientSpanXSubCAlgEquiv_mk
  条件: (x : R) (p : R[X])
  证明: rfl

@[simp]
-/
theorem quotientSpanXSubCAlgEquiv_mk (x : R) (p : R[X]) :
    quotientSpanXSubCAlgEquiv x (Ideal.Quotient.mk _ p) = p.eval x :=
  rfl

@[simp]
/--
theorem `quotientSpanXSubCAlgEquiv_symm_apply` / 定理 `quotientSpanXSubCAlgEquiv_symm_apply`

English:
theorem quotientSpanXSubCAlgEquiv_symm_apply
  given: (x : R) (y : R)
  proof: rfl

中文:
定理 quotientSpanXSubCAlgEquiv_symm_apply
  条件: (x : R) (y : R)
  证明: rfl
-/
theorem quotientSpanXSubCAlgEquiv_symm_apply (x : R) (y : R) :
    (quotientSpanXSubCAlgEquiv x).symm y = algebraMap R _ y :=
  rfl

/--
Definition of `quotientSpanCXSubCAlgEquiv` / `quotientSpanCXSubCAlgEquiv` 的定义

English:
definition quotientSpanCXSubCAlgEquiv
  signature: (x y : R)
  body: (Ideal.quotientEquivAlgOfEq R (J := _ ⊔ Ideal.span {C x}) <| by
      rw [Ideal.span_insert]; rw [sup_comm]).trans <|
(DoubleQuot.quotQuotEquivQuotSupₐ R _ _).symm.trans
(Ideal.quotientEquivAlg _ _ (quotientSpanXSubCAlgEquiv y) rfl).trans
Ideal.quotientEquivAlgOfEq R by
          simp only [Ideal.map_span, Set.image_singleton]; congr 2; exact eval_C

中文:
定义 quotientSpanCXSubCAlgEquiv
  签名: (x y : R)
  定义体: (Ideal.quotientEquivAlgOfEq R (J := _ ⊔ Ideal.span {C x}) <| by
      rw [Ideal.span_insert]; rw [sup_comm]).trans <|
(DoubleQuot.quotQuotEquivQuotSupₐ R _ _).symm.trans
(Ideal.quotientEquivAlg _ _ (quotientSpanXSubCAlgEquiv y) rfl).trans
Ideal.quotientEquivAlgOfEq R by
          simp only [Ideal.map_span, Set.image_singleton]; congr 2; exact eval_C

Depends on / 依赖: DoubleQuot, DoubleQuot.quotQuotEquivQuotSup, Ideal.map_span, Ideal.quotientEquivAlg, Ideal.quotientEquivAlgOfEq, Ideal.span, Ideal.span_insert, Set.image_singleton, eval_C, image_singleton, map_span, quotientEquivAlg, quotientEquivAlgOfEq, quotientSpanXSubCAlgEquiv, span_insert, sup_comm, symm.trans
-/
noncomputable def quotientSpanCXSubCAlgEquiv (x y : R) :
    (R[X] ⧸ (Ideal.span {C x, X - C y} : Ideal R[X])) ≃ₐ[R] R ⧸ (Ideal.span {x} : Ideal R) :=
  (Ideal.quotientEquivAlgOfEq R (J := _ ⊔ Ideal.span {C x}) <| by
      rw [Ideal.span_insert]; rw [sup_comm]).trans <|
(DoubleQuot.quotQuotEquivQuotSupₐ R _ _).symm.trans
(Ideal.quotientEquivAlg _ _ (quotientSpanXSubCAlgEquiv y) rfl).trans
Ideal.quotientEquivAlgOfEq R by
          simp only [Ideal.map_span, Set.image_singleton]; congr 2; exact eval_C

/--
Definition of `quotientSpanCXSubCXSubCAlgEquiv` / `quotientSpanCXSubCXSubCAlgEquiv` 的定义

English:
definition quotientSpanCXSubCXSubCAlgEquiv
  signature: {x : R} {y : R[X]}
  body: ((quotientSpanCXSubCAlgEquiv (X - C x) y).restrictScalars R).trans quotientSpanXSubCAlgEquiv x

中文:
定义 quotientSpanCXSubCXSubCAlgEquiv
  签名: {x : R} {y : R[X]}
  定义体: ((quotientSpanCXSubCAlgEquiv (X - C x) y).restrictScalars R).trans quotientSpanXSubCAlgEquiv x

Depends on / 依赖: quotientSpanCXSubCAlgEquiv, quotientSpanXSubCAlgEquiv, restrictScalars
-/
noncomputable def quotientSpanCXSubCXSubCAlgEquiv {x : R} {y : R[X]} :
    @AlgEquiv R (R[X][X] ⧸ (Ideal.span {C (X - C x), X - C y} : Ideal <| R[X][X])) R _ _ _
      (Ideal.Quotient.algebra R) _ :=
((quotientSpanCXSubCAlgEquiv (X - C x) y).restrictScalars R).trans quotientSpanXSubCAlgEquiv x

/--
lemma `modByMonic_eq_zero_iff_quotient_eq_zero` / 引理 `modByMonic_eq_zero_iff_quotient_eq_zero`

English:
lemma modByMonic_eq_zero_iff_quotient_eq_zero
  given: (p q : R[X]) (hq : q.Monic)
  proof: by
  rw [modByMonic_eq_zero_iff_dvd hq]; rw [Ideal.Quotient.eq_zero_iff_dvd]

中文:
引理 modByMonic_eq_zero_iff_quotient_eq_zero
  条件: (p q : R[X]) (hq : q.Monic)
  证明: by
  rw [modByMonic_eq_zero_iff_dvd hq]; rw [Ideal.Quotient.eq_zero_iff_dvd]

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_dvd, Quotient, eq_zero_iff_dvd, modByMonic_eq_zero_iff_dvd
-/
lemma modByMonic_eq_zero_iff_quotient_eq_zero (p q : R[X]) (hq : q.Monic) :
    p %ₘ q = 0 ↔ (p : R[X] ⧸ Ideal.span {q}) = 0 := by
  rw [modByMonic_eq_zero_iff_dvd hq]; rw [Ideal.Quotient.eq_zero_iff_dvd]

end Polynomial

namespace Ideal

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

/--
theorem `quotient_map_C_eq_zero` / 定理 `quotient_map_C_eq_zero`

English:
theorem quotient_map_C_eq_zero
  given: {I : Ideal R}
  proof: by
  intro a ha
  rw [RingHom.comp_apply]; rw [Quotient.eq_zero_iff_mem]
  exact mem_map_of_mem _ ha

中文:
定理 quotient_map_C_eq_zero
  条件: {I : 理想 R}
  证明: by
  intro a ha
  rw [RingHom.comp_apply]; rw [Quotient.eq_zero_iff_mem]
  exact mem_map_of_mem _ ha

Depends on / 依赖: Quotient, Quotient.eq_zero_iff_mem, RingHom, RingHom.comp_apply, comp_apply, eq_zero_iff_mem, mem_map_of_mem
-/
theorem quotient_map_C_eq_zero {I : Ideal R} :
    forall a in I, ((Quotient.mk (map (C : R ->+* R[X]) I : Ideal R[X])).comp C) a = 0 := by
  intro a ha
  rw [RingHom.comp_apply]; rw [Quotient.eq_zero_iff_mem]
  exact mem_map_of_mem _ ha

/--
theorem `eval₂_C_mk_eq_zero` / 定理 `eval₂_C_mk_eq_zero`

English:
theorem eval₂_C_mk_eq_zero
  given: {I : Ideal R}
  proof: by
  intro a ha
  rw [← sum_monomial_eq a]
  dsimp
  rw [eval₂_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  dsimp
  rw [eval₂_monomial (C.comp (Quotient.mk I)) X]
  refine mul_eq_zero_of_left (Polynomial.ext fun m => ?_) (X ^ n)
  rw [RingHom.comp_apply]; rw [coeff_C]
  by_cases h : m = 0
  · simpa [h] using Quotient.eq_zero_iff_mem.2 ((mem_map_C_iff.1 ha) n)
  · simp [h]

中文:
定理 eval₂_C_mk_eq_zero
  条件: {I : 理想 R}
  证明: by
  intro a ha
  rw [← sum_monomial_eq a]
  dsimp
  rw [eval₂_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  dsimp
  rw [eval₂_monomial (C.comp (Quotient.mk I)) X]
  refine mul_eq_zero_of_left (Polynomial.ext fun m => ?_) (X ^ n)
  rw [RingHom.comp_apply]; rw [coeff_C]
  by_cases h : m = 0
  · simpa [h] using Quotient.eq_zero_iff_mem.2 ((mem_map_C_iff.1 ha) n)
  · simp [h]

Depends on / 依赖: C.comp, Finset, Finset.sum_eq_zero, Polynomial, Polynomial.ext, Quotient, Quotient.eq_zero_iff_mem, Quotient.mk, RingHom, RingHom.comp_apply, coeff_C, comp_apply, eq_zero_iff_mem, mem_map_C_iff, mul_eq_zero_of_left, sum_eq_zero, sum_monomial_eq
-/
theorem eval₂_C_mk_eq_zero {I : Ideal R} :
    forall f in (map (C : R ->+* R[X]) I : Ideal R[X]), eval₂RingHom (C.comp (Quotient.mk I)) X f = 0 := by
  intro a ha
  rw [← sum_monomial_eq a]
  dsimp
  rw [eval₂_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  dsimp
  rw [eval₂_monomial (C.comp (Quotient.mk I)) X]
  refine mul_eq_zero_of_left (Polynomial.ext fun m => ?_) (X ^ n)
  rw [RingHom.comp_apply]; rw [coeff_C]
  by_cases h : m = 0
  · simpa [h] using Quotient.eq_zero_iff_mem.2 ((mem_map_C_iff.1 ha) n)
  · simp [h]

/--
Definition of `polynomialQuotientEquivQuotientPolynomial` / `polynomialQuotientEquivQuotientPolynomial` 的定义

English:
definition polynomialQuotientEquivQuotientPolynomial
  signature: (I : Ideal R)
  body: eval₂RingHom
      (Quotient.lift I ((Quotient.mk (map C I : Ideal R[X])).comp C) quotient_map_C_eq_zero)
      (Quotient.mk (map C I : Ideal R[X]) X)
  invFun :=
    Quotient.lift (map C I : Ideal R[X]) (eval₂RingHom (C.comp (Quotient.mk I)) X)
      eval₂_C_mk_eq_zero
  map_mul' f g := by simp only [coe_eval₂RingHom, eval₂_mul]
  map_add' f g := by simp only [eval₂_add, coe_eval₂RingHom]
  left_inv := by
    intro f
    refine Polynomial.induction_on' f ?_ ?_
    · intro p q hp hq
      simp only [coe_eval₂RingHom] at hp hq
      simp only [coe_eval₂RingHom, hp, hq, map_add]
    · rintro n ⟨x⟩
      simp only [← smul_X_eq_monomial, C_mul', Quotient.lift_mk, Submodule.Quotient.quot_mk_eq_mk,
        Quotient.mk_eq_mk, eval₂_X_pow, eval₂_smul, coe_eval₂RingHom, map_pow, eval₂_C,
        RingHom.coe_comp, map_mul, eval₂_X, Function.comp_apply]
  right_inv := by
    rintro ⟨f⟩
    refine Polynomial.induction_on' f ?_ ?_
    · intro p q hp hq
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, map_add, Quotient.lift_mk,
        coe_eval₂RingHom] at hp hq ⊢
      rw [hp]; rw [hq]
    · intro n a
      simp only [← smul_X_eq_monomial, ← C_mul' a (X ^ n), Quotient.lift_mk,
        Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk,
        coe_eval₂RingHom, map_pow, eval₂_C, RingHom.coe_comp, map_mul, eval₂_X,
        Function.comp_apply]

中文:
定义 polynomialQuotientEquivQuotientPolynomial
  签名: (I : 理想 R)
  定义体: eval₂RingHom
      (Quotient.lift I ((Quotient.mk (map C I : Ideal R[X])).comp C) quotient_map_C_eq_zero)
      (Quotient.mk (map C I : Ideal R[X]) X)
  invFun :=
    Quotient.lift (map C I : Ideal R[X]) (eval₂RingHom (C.comp (Quotient.mk I)) X)
      eval₂_C_mk_eq_zero
  map_mul' f g := by simp only [coe_eval₂RingHom, eval₂_mul]
  map_add' f g := by simp only [eval₂_add, coe_eval₂RingHom]
  left_inv := by
    intro f
    refine Polynomial.induction_on' f ?_ ?_
    · intro p q hp hq
      simp only [coe_eval₂RingHom] at hp hq
      simp only [coe_eval₂RingHom, hp, hq, map_add]
    · rintro n ⟨x⟩
      simp only [← smul_X_eq_monomial, C_mul', Quotient.lift_mk, Submodule.Quotient.quot_mk_eq_mk,
        Quotient.mk_eq_mk, eval₂_X_pow, eval₂_smul, coe_eval₂RingHom, map_pow, eval₂_C,
        RingHom.coe_comp, map_mul, eval₂_X, Function.comp_apply]
  right_inv := by
    rintro ⟨f⟩
    refine Polynomial.induction_on' f ?_ ?_
    · intro p q hp hq
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, map_add, Quotient.lift_mk,
        coe_eval₂RingHom] at hp hq ⊢
      rw [hp]; rw [hq]
    · intro n a
      simp only [← smul_X_eq_monomial, ← C_mul' a (X ^ n), Quotient.lift_mk,
        Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk,
        coe_eval₂RingHom, map_pow, eval₂_C, RingHom.coe_comp, map_mul, eval₂_X,
        Function.comp_apply]

Depends on / 依赖: C.comp, Polynomial, Polynomial.induction_on, Quotient, Quotient.lift, Quotient.mk, coe_e, induction_on, invFun, left_inv, map_add, map_mul, quotient_map_C_eq_zero
-/
def polynomialQuotientEquivQuotientPolynomial (I : Ideal R) :
    (R ⧸ I)[X] ≃+* R[X] ⧸ (map C I : Ideal R[X]) where
  toFun :=
    eval₂RingHom
      (Quotient.lift I ((Quotient.mk (map C I : Ideal R[X])).comp C) quotient_map_C_eq_zero)
      (Quotient.mk (map C I : Ideal R[X]) X)
  invFun :=
    Quotient.lift (map C I : Ideal R[X]) (eval₂RingHom (C.comp (Quotient.mk I)) X)
      eval₂_C_mk_eq_zero
  map_mul' f g := by simp only [coe_eval₂RingHom, eval₂_mul]
  map_add' f g := by simp only [eval₂_add, coe_eval₂RingHom]
  left_inv := by
    intro f
    refine Polynomial.induction_on' f ?_ ?_
    · intro p q hp hq
      simp only [coe_eval₂RingHom] at hp hq
      simp only [coe_eval₂RingHom, hp, hq, map_add]
    · rintro n ⟨x⟩
      simp only [← smul_X_eq_monomial, C_mul', Quotient.lift_mk, Submodule.Quotient.quot_mk_eq_mk,
        Quotient.mk_eq_mk, eval₂_X_pow, eval₂_smul, coe_eval₂RingHom, map_pow, eval₂_C,
        RingHom.coe_comp, map_mul, eval₂_X, Function.comp_apply]
  right_inv := by
    rintro ⟨f⟩
    refine Polynomial.induction_on' f ?_ ?_
    · intro p q hp hq
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, map_add, Quotient.lift_mk,
        coe_eval₂RingHom] at hp hq ⊢
      rw [hp]; rw [hq]
    · intro n a
      simp only [← smul_X_eq_monomial, ← C_mul' a (X ^ n), Quotient.lift_mk,
        Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk,
        coe_eval₂RingHom, map_pow, eval₂_C, RingHom.coe_comp, map_mul, eval₂_X,
        Function.comp_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `polynomialQuotientEquivQuotientPolynomial_symm_mk` / 定理 `polynomialQuotientEquivQuotientPolynomial_symm_mk`

English:
theorem polynomialQuotientEquivQuotientPolynomial_symm_mk
  given: (I : Ideal R) (f : R[X])
  proof: by
  simp only [polynomialQuotientEquivQuotientPolynomial, coe_eval₂RingHom, RingEquiv.symm_mk,
    RingEquiv.coe_mk, Equiv.coe_fn_symm_mk, Quotient.lift_mk]
  rw [eval₂_eq_eval_map]; rw [← Polynomial.map_map]; rw [← eval₂_eq_eval_map]; rw [Polynomial.eval₂_C_X]

@[simp]

中文:
定理 polynomialQuotientEquivQuotientPolynomial_symm_mk
  条件: (I : 理想 R) (f : R[X])
  证明: by
  simp only [polynomialQuotientEquivQuotientPolynomial, coe_eval₂RingHom, RingEquiv.symm_mk,
    RingEquiv.coe_mk, Equiv.coe_fn_symm_mk, Quotient.lift_mk]
  rw [eval₂_eq_eval_map]; rw [← Polynomial.map_map]; rw [← eval₂_eq_eval_map]; rw [Polynomial.eval₂_C_X]

@[simp]

Depends on / 依赖: Equiv.coe_fn_symm_mk, Polynomial, Polynomial.eval, Polynomial.map_map, Quotient, Quotient.lift_mk, RingEquiv, RingEquiv.coe_mk, RingEquiv.symm_mk, coe_fn_symm_mk, coe_mk, lift_mk, map_map, polynomialQuotientEquivQuotientPolynomial, symm_mk
-/
theorem polynomialQuotientEquivQuotientPolynomial_symm_mk (I : Ideal R) (f : R[X]) :
    I.polynomialQuotientEquivQuotientPolynomial.symm (Quotient.mk _ f) = f.map (Quotient.mk I) := by
  simp only [polynomialQuotientEquivQuotientPolynomial, coe_eval₂RingHom, RingEquiv.symm_mk,
    RingEquiv.coe_mk, Equiv.coe_fn_symm_mk, Quotient.lift_mk]
  rw [eval₂_eq_eval_map]; rw [← Polynomial.map_map]; rw [← eval₂_eq_eval_map]; rw [Polynomial.eval₂_C_X]

@[simp]
/--
theorem `polynomialQuotientEquivQuotientPolynomial_map_mk` / 定理 `polynomialQuotientEquivQuotientPolynomial_map_mk`

English:
theorem polynomialQuotientEquivQuotientPolynomial_map_mk
  given: (I : Ideal R) (f : R[X])
  proof: by
  apply (polynomialQuotientEquivQuotientPolynomial I).symm.injective
  rw [RingEquiv.symm_apply_apply]; rw [polynomialQuotientEquivQuotientPolynomial_symm_mk]

中文:
定理 polynomialQuotientEquivQuotientPolynomial_map_mk
  条件: (I : 理想 R) (f : R[X])
  证明: by
  apply (polynomialQuotientEquivQuotientPolynomial I).symm.injective
  rw [RingEquiv.symm_apply_apply]; rw [polynomialQuotientEquivQuotientPolynomial_symm_mk]

Depends on / 依赖: RingEquiv, RingEquiv.symm_apply_apply, injective, polynomialQuotientEquivQuotientPolynomial, polynomialQuotientEquivQuotientPolynomial_symm_mk, symm.injective, symm_apply_apply
-/
theorem polynomialQuotientEquivQuotientPolynomial_map_mk (I : Ideal R) (f : R[X]) :
    I.polynomialQuotientEquivQuotientPolynomial (f.map <| Quotient.mk I) =
    Quotient.mk (map C I : Ideal R[X]) f := by
  apply (polynomialQuotientEquivQuotientPolynomial I).symm.injective
  rw [RingEquiv.symm_apply_apply]; rw [polynomialQuotientEquivQuotientPolynomial_symm_mk]

/--
theorem `isDomain_map_C_quotient` / 定理 `isDomain_map_C_quotient`

English:
theorem isDomain_map_C_quotient
  given: {P : Ideal R} (_ : IsPrime P)
  proof: MulEquiv.isDomain (Polynomial (R ⧸ P)) (polynomialQuotientEquivQuotientPolynomial P).symm

中文:
定理 isDomain_map_C_quotient
  条件: {P : 理想 R} (_ : 是素 P)
  证明: MulEquiv.isDomain (Polynomial (R ⧸ P)) (polynomialQuotientEquivQuotientPolynomial P).symm

Depends on / 依赖: MulEquiv, MulEquiv.isDomain, Polynomial, isDomain, polynomialQuotientEquivQuotientPolynomial
-/
theorem isDomain_map_C_quotient {P : Ideal R} (_ : IsPrime P) :
    IsDomain (R[X] ⧸ (map (C : R ->+* R[X]) P : Ideal R[X])) :=
  MulEquiv.isDomain (Polynomial (R ⧸ P)) (polynomialQuotientEquivQuotientPolynomial P).symm

/--
theorem `eq_zero_of_polynomial_mem_map_range` / 定理 `eq_zero_of_polynomial_mem_map_range`

English:
theorem eq_zero_of_polynomial_mem_map_range
  statement: (I : Ideal R[X]) (x : ((Quotient.mk I).comp C).range)
  proof: by
  let i := ((Quotient.mk I).comp C).rangeRestrict
  have hi' : RingHom.ker (Polynomial.mapRingHom i) <= I := by
    refine fun f hf => polynomial_mem_ideal_of_coeff_mem_ideal I f fun n => ?_
    rw [mem_comap]; rw [← Quotient.eq_zero_iff_mem]; rw [← RingHom.comp_apply]
    rw [RingHom.mem_ker]; rw [coe_mapRingHom] at hf
    replace hf := congr_arg (fun f : Polynomial _ => f.coeff n) hf
    simp only [coeff_map, coeff_zero] at hf
    rwa [Subtype.ext_iff, RingHom.coe_rangeRestrict] at hf
  obtain ⟨x, hx'⟩ := x
  obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx'
  refine Subtype.ext ?_
  simp only [RingHom.comp_apply, Quotient.eq_zero_iff_mem, ZeroMemClass.coe_zero]
  suffices C (i y) in I.map (Polynomial.mapRingHom i) by
    obtain ⟨f, hf⟩ := mem_image_of_mem_map_of_surjective (Polynomial.mapRingHom i)
      (Polynomial.map_surjective _ (RingHom.rangeRestrict_surjective ((Quotient.mk I).comp C))) this
    refine sub_add_cancel (C y) f ▸ I.add_mem (hi' ?_ : C y - f in I) hf.1
    rw [RingHom.mem_ker]; rw [map_sub]; rw [hf.2]; rw [sub_eq_zero]; rw [coe_mapRingHom]; rw [map_C]
  exact hx

中文:
定理 eq_zero_of_polynomial_mem_map_range
  结论: (I : 理想 R[X]) (x : ((商.mk I).comp C).range)
  证明: by
  let i := ((Quotient.mk I).comp C).rangeRestrict
  have hi' : RingHom.ker (Polynomial.mapRingHom i) <= I := by
    refine fun f hf => polynomial_mem_ideal_of_coeff_mem_ideal I f fun n => ?_
    rw [mem_comap]; rw [← Quotient.eq_zero_iff_mem]; rw [← RingHom.comp_apply]
    rw [RingHom.mem_ker]; rw [coe_mapRingHom] at hf
    replace hf := congr_arg (fun f : Polynomial _ => f.coeff n) hf
    simp only [coeff_map, coeff_zero] at hf
    rwa [Subtype.ext_iff, RingHom.coe_rangeRestrict] at hf
  obtain ⟨x, hx'⟩ := x
  obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx'
  refine Subtype.ext ?_
  simp only [RingHom.comp_apply, Quotient.eq_zero_iff_mem, ZeroMemClass.coe_zero]
  suffices C (i y) in I.map (Polynomial.mapRingHom i) by
    obtain ⟨f, hf⟩ := mem_image_of_mem_map_of_surjective (Polynomial.mapRingHom i)
      (Polynomial.map_surjective _ (RingHom.rangeRestrict_surjective ((Quotient.mk I).comp C))) this
    refine sub_add_cancel (C y) f ▸ I.add_mem (hi' ?_ : C y - f in I) hf.1
    rw [RingHom.mem_ker]; rw [map_sub]; rw [hf.2]; rw [sub_eq_zero]; rw [coe_mapRingHom]; rw [map_C]
  exact hx

Depends on / 依赖: Polynomial, Polynomial.mapRingHom, Quotient, Quotient.eq_zero_iff_mem, Quotient.mk, RingHom, RingHom.coe_rangeRestrict, RingHom.comp_apply, RingHom.ker, RingHom.mem_ker, Subtype, Subtype.ext_iff, coe_mapRingHom, coe_rangeRestrict, coeff_map, coeff_zero, comp_apply, congr_arg, eq_zero_iff_mem, ext_iff
-/
theorem eq_zero_of_polynomial_mem_map_range (I : Ideal R[X]) (x : ((Quotient.mk I).comp C).range)
    (hx : C x in I.map (Polynomial.mapRingHom ((Quotient.mk I).comp C).rangeRestrict)) : x = 0 := by
  let i := ((Quotient.mk I).comp C).rangeRestrict
  have hi' : RingHom.ker (Polynomial.mapRingHom i) <= I := by
    refine fun f hf => polynomial_mem_ideal_of_coeff_mem_ideal I f fun n => ?_
    rw [mem_comap]; rw [← Quotient.eq_zero_iff_mem]; rw [← RingHom.comp_apply]
    rw [RingHom.mem_ker]; rw [coe_mapRingHom] at hf
    replace hf := congr_arg (fun f : Polynomial _ => f.coeff n) hf
    simp only [coeff_map, coeff_zero] at hf
    rwa [Subtype.ext_iff, RingHom.coe_rangeRestrict] at hf
  obtain ⟨x, hx'⟩ := x
  obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx'
  refine Subtype.ext ?_
  simp only [RingHom.comp_apply, Quotient.eq_zero_iff_mem, ZeroMemClass.coe_zero]
  suffices C (i y) in I.map (Polynomial.mapRingHom i) by
    obtain ⟨f, hf⟩ := mem_image_of_mem_map_of_surjective (Polynomial.mapRingHom i)
      (Polynomial.map_surjective _ (RingHom.rangeRestrict_surjective ((Quotient.mk I).comp C))) this
    refine sub_add_cancel (C y) f ▸ I.add_mem (hi' ?_ : C y - f in I) hf.1
    rw [RingHom.mem_ker]; rw [map_sub]; rw [hf.2]; rw [sub_eq_zero]; rw [coe_mapRingHom]; rw [map_C]
  exact hx

/--
lemma `IsField.of_isPrincipalIdealRing_polynomial` / 引理 `IsField.of_isPrincipalIdealRing_polynomial`

English:
lemma IsField.of_isPrincipalIdealRing_polynomial
  given: [IsDomain R] [IsPrincipalIdealRing R[X]]
  proof: by
  apply (quotientSpanXSubCAlgEquiv 0).symm.toMulEquiv.isField
  rw [← Quotient.maximal_ideal_iff_isField_quotient]
  exact PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C 0)

中文:
引理 是域.of_isPrincipalIdealRing_polynomial
  条件: [是整环 R] [是主理想环 R[X]]
  证明: by
  apply (quotientSpanXSubCAlgEquiv 0).symm.toMulEquiv.isField
  rw [← Quotient.maximal_ideal_iff_isField_quotient]
  exact PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C 0)

Depends on / 依赖: PrincipalIdealRing, PrincipalIdealRing.isMaximal_of_irreducible, Quotient, Quotient.maximal_ideal_iff_isField_quotient, irreducible_X_sub_C, isField, isMaximal_of_irreducible, maximal_ideal_iff_isField_quotient, quotientSpanXSubCAlgEquiv, symm.toMulEquiv.isField, toMulEquiv
-/
lemma IsField.of_isPrincipalIdealRing_polynomial [IsDomain R] [IsPrincipalIdealRing R[X]] :
    IsField R := by
  apply (quotientSpanXSubCAlgEquiv 0).symm.toMulEquiv.isField
  rw [← Quotient.maximal_ideal_iff_isField_quotient]
  exact PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C 0)

end

end Ideal

namespace MvPolynomial

variable {R : Type*} {σ : Type*} [CommRing R] {r : R}

/--
theorem `quotient_map_C_eq_zero` / 定理 `quotient_map_C_eq_zero`

English:
theorem quotient_map_C_eq_zero
  given: {I : Ideal R} {i : R} (hi : i in I)
  proof: by
  simp only [Function.comp_apply, RingHom.coe_comp, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hi

中文:
定理 quotient_map_C_eq_zero
  条件: {I : 理想 R} {i : R} (hi : i in I)
  证明: by
  simp only [Function.comp_apply, RingHom.coe_comp, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hi

Depends on / 依赖: Function, Function.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_map_of_mem, Quotient, RingHom, RingHom.coe_comp, coe_comp, comp_apply, eq_zero_iff_mem, mem_map_of_mem
-/
theorem quotient_map_C_eq_zero {I : Ideal R} {i : R} (hi : i in I) :
    (Ideal.Quotient.mk (Ideal.map (C : R ->+* MvPolynomial σ R) I :
      Ideal (MvPolynomial σ R))).comp C i = 0 := by
  simp only [Function.comp_apply, RingHom.coe_comp, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hi

/--
theorem `eval₂_C_mk_eq_zero` / 定理 `eval₂_C_mk_eq_zero`

English:
theorem eval₂_C_mk_eq_zero
  statement: {I : Ideal R} {a : MvPolynomial σ R}
  proof: by
  rw [as_sum a]
  rw [coe_eval₂Hom]; rw [eval₂_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  simp only [eval₂_monomial, Function.comp_apply, RingHom.coe_comp]
  refine mul_eq_zero_of_left ?_ _
  suffices coeff n a in I by
    rw [← @Ideal.mk_ker R _ I]; rw [RingHom.mem_ker] at this
    simp only [this, C_0]
  exact mem_map_C_iff.1 ha n

中文:
定理 eval₂_C_mk_eq_zero
  结论: {I : 理想 R} {a : 多元多项式 σ R}
  证明: by
  rw [as_sum a]
  rw [coe_eval₂Hom]; rw [eval₂_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  simp only [eval₂_monomial, Function.comp_apply, RingHom.coe_comp]
  refine mul_eq_zero_of_left ?_ _
  suffices coeff n a in I by
    rw [← @Ideal.mk_ker R _ I]; rw [RingHom.mem_ker] at this
    simp only [this, C_0]
  exact mem_map_C_iff.1 ha n

Depends on / 依赖: Finset, Finset.sum_eq_zero, Function, Function.comp_apply, Ideal.mk_ker, RingHom, RingHom.coe_comp, RingHom.mem_ker, as_sum, coe_comp, comp_apply, mem_ker, mem_map_C_iff, mk_ker, mul_eq_zero_of_left, sum_eq_zero
-/
theorem eval₂_C_mk_eq_zero {I : Ideal R} {a : MvPolynomial σ R}
    (ha : a in (Ideal.map (C : R ->+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R))) :
    eval₂Hom (C.comp (Ideal.Quotient.mk I)) X a = 0 := by
  rw [as_sum a]
  rw [coe_eval₂Hom]; rw [eval₂_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  simp only [eval₂_monomial, Function.comp_apply, RingHom.coe_comp]
  refine mul_eq_zero_of_left ?_ _
  suffices coeff n a in I by
    rw [← @Ideal.mk_ker R _ I]; rw [RingHom.mem_ker] at this
    simp only [this, C_0]
  exact mem_map_C_iff.1 ha n

/--
lemma `quotientEquivQuotientMvPolynomial_rightInverse` / 引理 `quotientEquivQuotientMvPolynomial_rightInverse`

English:
lemma quotientEquivQuotientMvPolynomial_rightInverse
  given: (I : Ideal R)
  proof: by
  intro f
  apply induction_on f
  · intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp
  · intro p q hp hq
    simp only [map_add, MvPolynomial.eval₂_add]
      at hp hq ⊢
    rw [hp]; rw [hq]
  · intro p i hp
    simp only [hp, coe_eval₂Hom, Ideal.Quotient.lift_mk, eval₂_mul, map_mul, eval₂_X]

中文:
引理 quotientEquivQuotientMvPolynomial_rightInverse
  条件: (I : 理想 R)
  证明: by
  intro f
  apply induction_on f
  · intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp
  · intro p q hp hq
    simp only [map_add, MvPolynomial.eval₂_add]
      at hp hq ⊢
    rw [hp]; rw [hq]
  · intro p i hp
    simp only [hp, coe_eval₂Hom, Ideal.Quotient.lift_mk, eval₂_mul, map_mul, eval₂_X]

Depends on / 依赖: Ideal.Quotient.lift_mk, Ideal.Quotient.mk_surjective, MvPolynomial, MvPolynomial.eval, Quotient, induction_on, lift_mk, map_add, map_mul, mk_surjective
-/
lemma quotientEquivQuotientMvPolynomial_rightInverse (I : Ideal R) :
    Function.RightInverse
      (eval₂ (Ideal.Quotient.lift I
        ((Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C)
          fun _ hi => quotient_map_C_eq_zero hi)
          fun i => Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i))
      (Ideal.Quotient.lift (Ideal.map C I : Ideal (MvPolynomial σ R))
        (eval₂Hom (C.comp (Ideal.Quotient.mk I)) X) fun _ ha => eval₂_C_mk_eq_zero ha) := by
  intro f
  apply induction_on f
  · intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp
  · intro p q hp hq
    simp only [map_add, MvPolynomial.eval₂_add]
      at hp hq ⊢
    rw [hp]; rw [hq]
  · intro p i hp
    simp only [hp, coe_eval₂Hom, Ideal.Quotient.lift_mk, eval₂_mul, map_mul, eval₂_X]

/--
lemma `quotientEquivQuotientMvPolynomial_leftInverse` / 引理 `quotientEquivQuotientMvPolynomial_leftInverse`

English:
lemma quotientEquivQuotientMvPolynomial_leftInverse
  given: (I : Ideal R)
  proof: by
  intro f
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  apply induction_on f
  · intro r
    rw [Ideal.Quotient.lift_mk]; rw [eval₂Hom_C]; rw [RingHom.comp_apply]; rw [eval₂_C]; rw [Ideal.Quotient.lift_mk]; rw [RingHom.comp_apply]
  · intro p q hp hq
    rw [Ideal.Quotient.lift_mk] at hp hq ⊢
    simp only [eval₂_add, map_add, coe_eval₂Hom] at hp hq ⊢
    rw [hp]; rw [hq]
  · intro p i hp
    simp only [coe_eval₂Hom, Ideal.Quotient.lift_mk,
      eval₂_mul, map_mul, eval₂_X] at hp ⊢
    simp only [hp]

中文:
引理 quotientEquivQuotientMvPolynomial_leftInverse
  条件: (I : 理想 R)
  证明: by
  intro f
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  apply induction_on f
  · intro r
    rw [Ideal.Quotient.lift_mk]; rw [eval₂Hom_C]; rw [RingHom.comp_apply]; rw [eval₂_C]; rw [Ideal.Quotient.lift_mk]; rw [RingHom.comp_apply]
  · intro p q hp hq
    rw [Ideal.Quotient.lift_mk] at hp hq ⊢
    simp only [eval₂_add, map_add, coe_eval₂Hom] at hp hq ⊢
    rw [hp]; rw [hq]
  · intro p i hp
    simp only [coe_eval₂Hom, Ideal.Quotient.lift_mk,
      eval₂_mul, map_mul, eval₂_X] at hp ⊢
    simp only [hp]

Depends on / 依赖: Ideal.Quotient.lift_mk, Ideal.Quotient.mk_surjective, Quotient, RingHom, RingHom.comp_apply, comp_apply, induction_on, lift_mk, map_add, map_mul, mk_surjective
-/
lemma quotientEquivQuotientMvPolynomial_leftInverse (I : Ideal R) :
    Function.LeftInverse
      (eval₂ (Ideal.Quotient.lift I
        ((Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C)
          fun _ hi => quotient_map_C_eq_zero hi)
          fun i => Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i))
      (Ideal.Quotient.lift (Ideal.map C I : Ideal (MvPolynomial σ R))
        (eval₂Hom (C.comp (Ideal.Quotient.mk I)) X) fun _ ha => eval₂_C_mk_eq_zero ha) := by
  intro f
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  apply induction_on f
  · intro r
    rw [Ideal.Quotient.lift_mk]; rw [eval₂Hom_C]; rw [RingHom.comp_apply]; rw [eval₂_C]; rw [Ideal.Quotient.lift_mk]; rw [RingHom.comp_apply]
  · intro p q hp hq
    rw [Ideal.Quotient.lift_mk] at hp hq ⊢
    simp only [eval₂_add, map_add, coe_eval₂Hom] at hp hq ⊢
    rw [hp]; rw [hq]
  · intro p i hp
    simp only [coe_eval₂Hom, Ideal.Quotient.lift_mk,
      eval₂_mul, map_mul, eval₂_X] at hp ⊢
    simp only [hp]

/--
Definition of `quotientEquivQuotientMvPolynomial` / `quotientEquivQuotientMvPolynomial` 的定义

English:
definition quotientEquivQuotientMvPolynomial
  signature: (I : Ideal R)
  body: let e : MvPolynomial σ (R ⧸ I) ->ₐ[R]
      MvPolynomial σ R ⧸ (Ideal.map C I : Ideal (MvPolynomial σ R)) :=
    { eval₂Hom
      (Ideal.Quotient.lift I ((Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C)
        fun _ hi => quotient_map_C_eq_zero hi)
      fun i => Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i) with
      commutes' := fun r => eval₂Hom_C _ _ (Ideal.Quotient.mk I r) }
  { e with
    invFun := Ideal.Quotient.lift (Ideal.map C I : Ideal (MvPolynomial σ R))
      (eval₂Hom (C.comp (Ideal.Quotient.mk I)) X) fun _ ha => eval₂_C_mk_eq_zero ha
    left_inv := quotientEquivQuotientMvPolynomial_rightInverse I
    right_inv := quotientEquivQuotientMvPolynomial_leftInverse I }

中文:
定义 quotientEquivQuotientMvPolynomial
  签名: (I : 理想 R)
  定义体: let e : MvPolynomial σ (R ⧸ I) ->ₐ[R]
      MvPolynomial σ R ⧸ (Ideal.map C I : Ideal (MvPolynomial σ R)) :=
    { eval₂Hom
      (Ideal.Quotient.lift I ((Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C)
        fun _ hi => quotient_map_C_eq_zero hi)
      fun i => Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i) with
      commutes' := fun r => eval₂Hom_C _ _ (Ideal.Quotient.mk I r) }
  { e with
    invFun := Ideal.Quotient.lift (Ideal.map C I : Ideal (MvPolynomial σ R))
      (eval₂Hom (C.comp (Ideal.Quotient.mk I)) X) fun _ ha => eval₂_C_mk_eq_zero ha
    left_inv := quotientEquivQuotientMvPolynomial_rightInverse I
    right_inv := quotientEquivQuotientMvPolynomial_leftInverse I }

Depends on / 依赖: C.comp, Ideal.Q, Ideal.Quotient.lift, Ideal.Quotient.mk, Ideal.map, MvPolynomial, Quotient, commutes, invFun, quotient_map_C_eq_zero
-/
noncomputable def quotientEquivQuotientMvPolynomial (I : Ideal R) :
    MvPolynomial σ (R ⧸ I) ≃ₐ[R] MvPolynomial σ R ⧸ (Ideal.map C I : Ideal (MvPolynomial σ R)) :=
  let e : MvPolynomial σ (R ⧸ I) ->ₐ[R]
      MvPolynomial σ R ⧸ (Ideal.map C I : Ideal (MvPolynomial σ R)) :=
    { eval₂Hom
      (Ideal.Quotient.lift I ((Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C)
        fun _ hi => quotient_map_C_eq_zero hi)
      fun i => Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i) with
      commutes' := fun r => eval₂Hom_C _ _ (Ideal.Quotient.mk I r) }
  { e with
    invFun := Ideal.Quotient.lift (Ideal.map C I : Ideal (MvPolynomial σ R))
      (eval₂Hom (C.comp (Ideal.Quotient.mk I)) X) fun _ ha => eval₂_C_mk_eq_zero ha
    left_inv := quotientEquivQuotientMvPolynomial_rightInverse I
    right_inv := quotientEquivQuotientMvPolynomial_leftInverse I }

end MvPolynomial
