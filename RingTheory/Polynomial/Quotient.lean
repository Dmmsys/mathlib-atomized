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

/-- For a commutative ring $R$, evaluating a polynomial at an element $x \in R$ induces an
isomorphism of $R$-algebras $R[X] / \langle X - x \rangle \cong R$. -/
/-
**Polynomial.quotientSpanXSubCAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：quotientSpanXSubCAlgEquiv (x : R) : (R[X] ⧸ Ideal.span ({X - C x} : Set R[
X])) ≃ₐ[R] R
参数：x : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a commutative ring $R$, evaluating a polynomial at an element $x \in R$ indu
ces an
isomorphism of $R$-algebras $R[X] / \langle X - x \rangle \cong R$.
-/
noncomputable def quotientSpanXSubCAlgEquiv (x : R) :
    (R[X] ⧸ Ideal.span ({X - C x} : Set R[X])) ≃ₐ[R] R :=
  let e := RingHom.quotientKerEquivOfRightInverse (fun x => by
    exact eval_C : Function.RightInverse (fun a : R => (C a : R[X])) (@aeval R R _ _ _ x))
  (Ideal.quotientEquivAlgOfEq R (ker_evalRingHom x).symm).trans
    { e with commutes' := fun r => e.apply_symm_apply r }

@[simp]
/-
**Polynomial.quotientSpanXSubCAlgEquiv_mk** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：quotientSpanXSubCAlgEquiv_mk (x : R) (p : R[X]) : quotientSpanXSubCAlgEqui
v x (Ideal.Quotient.mk _ p) = p.eval x
参数：x : R；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotientSpanXSubCAlgEquiv_mk (x : R) (p : R[X]) :
    quotientSpanXSubCAlgEquiv x (Ideal.Quotient.mk _ p) = p.eval x :=
  rfl

@[simp]
/-
**Polynomial.quotientSpanXSubCAlgEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：quotientSpanXSubCAlgEquiv_symm_apply (x : R) (y : R) : (quotientSpanXSubCA
lgEquiv x).symm y = algebraMap R _ y
参数：x : R；y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientSpanXSubCAlgEquiv_symm_apply (x : R) (y : R) :
    (quotientSpanXSubCAlgEquiv x).symm y = algebraMap R _ y :=
  rfl

/-- For a commutative ring $R$, evaluating a polynomial at an element $y \in R$ induces an
isomorphism of $R$-algebras $R[X] / \langle x, X - y \rangle \cong R / \langle x \rangle$. -/
/-
**Polynomial.quotientSpanCXSubCAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：quotientSpanCXSubCAlgEquiv (x y : R) : (R[X] ⧸ (Ideal.span {C x, X - C y} 
: Ideal R[X])) ≃ₐ[R] R ⧸ (Ideal.span {x} : Ideal R)
参数：x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a commutative ring $R$, evaluating a polynomial at an element $y \in R$ indu
ces an
isomorphism of $R$-algebras $R[X] / \langle x, X - y \rangle \cong R / \langle x
 \rangle$.
-/
noncomputable def quotientSpanCXSubCAlgEquiv (x y : R) :
    (R[X] ⧸ (Ideal.span {C x, X - C y} : Ideal R[X])) ≃ₐ[R] R ⧸ (Ideal.span {x} : Ideal R) :=
  (Ideal.quotientEquivAlgOfEq R (J := _ ⊔ Ideal.span {C x}) <| by
      rw [Ideal.span_insert, sup_comm]).trans <|
    (DoubleQuot.quotQuotEquivQuotSupₐ R _ _).symm.trans <|
      (Ideal.quotientEquivAlg _ _ (quotientSpanXSubCAlgEquiv y) rfl).trans <|
        Ideal.quotientEquivAlgOfEq R <| by
          simp only [Ideal.map_span, Set.image_singleton]; congr 2; exact eval_C

/-- For a commutative ring $R$, evaluating a polynomial at elements $y(X) \in R[X]$ and $x \in R$
induces an isomorphism of $R$-algebras $R[X, Y] / \langle X - x, Y - y(X) \rangle \cong R$. -/
/-
**Polynomial.quotientSpanCXSubCXSubCAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomi
al`。
形式化陈述：quotientSpanCXSubCXSubCAlgEquiv {x : R} {y : R[X]} : @AlgEquiv R (R[X][X] 
⧸ (Ideal.span {C (X - C x), X - C y} : Ideal <| R[X][X])) R _ _ _ (Ideal.Quotien
t.algebra R) _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a commutative ring $R$, evaluating a polynomial at elements $y(X) \in R[X]$ 
and $x \in R$
induces an isomorphism of $R$-algebras $R[X, Y] / \langle X - x, Y - y(X) \rangl
e \cong R$.
-/
noncomputable def quotientSpanCXSubCXSubCAlgEquiv {x : R} {y : R[X]} :
    @AlgEquiv R (R[X][X] ⧸ (Ideal.span {C (X - C x), X - C y} : Ideal <| R[X][X])) R _ _ _
      (Ideal.Quotient.algebra R) _ :=
((quotientSpanCXSubCAlgEquiv (X - C x) y).restrictScalars R).trans <| quotientSpanXSubCAlgEquiv x
/-
**Polynomial.modByMonic_eq_zero_iff_quotient_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `
Polynomial`。
形式化陈述：modByMonic_eq_zero_iff_quotient_eq_zero (p q : R[X]) (hq : q.Monic) : p %ₘ
 q = 0 ↔ (p : R[X] ⧸ Ideal.span {q}) = 0
参数：p q : R[X]；hq : q.Monic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `Ideal.Quotient.eq_zero_iff_dvd`：eq_zero_iff_dvd {R} [CommRing R] (x y : 
R) : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y = 0 ↔ x ∣ y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma modByMonic_eq_zero_iff_quotient_eq_zero (p q : R[X]) (hq : q.Monic) :
    p %ₘ q = 0 ↔ (p : R[X] ⧸ Ideal.span {q}) = 0 := by
  rw [modByMonic_eq_zero_iff_dvd hq, Ideal.Quotient.eq_zero_iff_dvd]

end Polynomial

namespace Ideal

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

/-
**Ideal.quotient_map_C_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotient_map_C_eq_zero {I : Ideal R} : forall a in I, ((Quotient.mk (map (
C : R ->+* R[X]) I : Ideal R[X])).comp C) a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
-/
theorem quotient_map_C_eq_zero {I : Ideal R} :
    ∀ a ∈ I, ((Quotient.mk (map (C : R →+* R[X]) I : Ideal R[X])).comp C) a = 0 := by
  intro a ha
  rw [RingHom.comp_apply, Quotient.eq_zero_iff_mem]
  exact mem_map_of_mem _ ha
/-
**Ideal.eval** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C_mk_eq_zero {I : Ideal R} :
    ∀ f ∈ (map (C : R →+* R[X]) I : Ideal R[X]), eval₂RingHom (C.comp (Quotient.mk I)) X f = 0 := by
  intro a ha
  rw [← sum_monomial_eq a]
  dsimp
  rw [eval₂_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  dsimp
  rw [eval₂_monomial (C.comp (Quotient.mk I)) X]
  refine mul_eq_zero_of_left (Polynomial.ext fun m => ?_) (X ^ n)
  rw [RingHom.comp_apply, coeff_C]
  by_cases h : m = 0
  · simpa [h] using Quotient.eq_zero_iff_mem.2 ((mem_map_C_iff.1 ha) n)
  · simp [h]

/-- If `I` is an ideal of `R`, then the ring polynomials over the quotient ring `I.quotient` is
isomorphic to the quotient of `R[X]` by the ideal `map C I`,
where `map C I` contains exactly the polynomials whose coefficients all lie in `I`. -/
/-
**Ideal.polynomialQuotientEquivQuotientPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `Ide
al`。
形式化陈述：polynomialQuotientEquivQuotientPolynomial (I : Ideal R) : (R ⧸ I)[X] ≃+* R
[X] ⧸ (map C I : Ideal R[X]) where toFun
参数：I : Ideal R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.quotient_map_C_eq_zero`：quotient_map_C_eq_zero {I : Ideal R} : for
all a in I, ((Quotient.mk (map (C : R ->+* R[X]) I : Ideal R[X])).comp C) a = 0
· 使用定理 `Ideal.eval₂_C_mk_eq_zero`：eval₂_C_mk_eq_zero {I : Ideal R} : forall f in
 (map (C : R ->+* R[X]) I : Ideal R[X]), eval₂RingHom (C.comp (Quotient.mk I)) X
 f = 0

--- 原说明 ---
If `I` is an ideal of `R`, then the ring polynomials over the quotient ring `I.q
uotient` is
isomorphic to the quotient of `R[X]` by the ideal `map C I`,
where `map C I` contains exactly the polynomials whose coefficients all lie in `
I`.
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
      rw [hp, hq]
    · intro n a
      simp only [← smul_X_eq_monomial, ← C_mul' a (X ^ n), Quotient.lift_mk,
        Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk,
        coe_eval₂RingHom, map_pow, eval₂_C, RingHom.coe_comp, map_mul, eval₂_X,
        Function.comp_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk** 是 Mathlib 中的一个定理，位于命
名空间 `Ideal`。
形式化陈述：polynomialQuotientEquivQuotientPolynomial_symm_mk (I : Ideal R) (f : R[X])
 : I.polynomialQuotientEquivQuotientPolynomial.symm (Quotient.mk _ f) = f.map (Q
uotient.mk I)
参数：I : Ideal R；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.eval₂_C_X`：eval₂_C_X : eval₂ C X p = p
-/
theorem polynomialQuotientEquivQuotientPolynomial_symm_mk (I : Ideal R) (f : R[X]) :
    I.polynomialQuotientEquivQuotientPolynomial.symm (Quotient.mk _ f) = f.map (Quotient.mk I) := by
  simp only [polynomialQuotientEquivQuotientPolynomial, coe_eval₂RingHom, RingEquiv.symm_mk,
    RingEquiv.coe_mk, Equiv.coe_fn_symm_mk, Quotient.lift_mk]
  rw [eval₂_eq_eval_map, ← Polynomial.map_map, ← eval₂_eq_eval_map, Polynomial.eval₂_C_X]

@[simp]
/-
**Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk** 是 Mathlib 中的一个定理，位于命名
空间 `Ideal`。
形式化陈述：polynomialQuotientEquivQuotientPolynomial_map_mk (I : Ideal R) (f : R[X]) 
: I.polynomialQuotientEquivQuotientPolynomial (f.map <| Quotient.mk I) = Quotien
t.mk (map C I : Ideal R[X]) f
参数：I : Ideal R；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk`：polynomialQuoti
entEquivQuotientPolynomial_symm_mk (I : Ideal R) (f : R[X]) : I.polynomialQuotie
ntEquivQuotientPolynomial.symm (Quotient.mk _…
-/
theorem polynomialQuotientEquivQuotientPolynomial_map_mk (I : Ideal R) (f : R[X]) :
    I.polynomialQuotientEquivQuotientPolynomial (f.map <| Quotient.mk I) =
    Quotient.mk (map C I : Ideal R[X]) f := by
  apply (polynomialQuotientEquivQuotientPolynomial I).symm.injective
  rw [RingEquiv.symm_apply_apply, polynomialQuotientEquivQuotientPolynomial_symm_mk]

/-- If `P` is a prime ideal of `R`, then `R[x]/(P)` is an integral domain. -/
/-
**Ideal.isDomain_map_C_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isDomain_map_C_quotient {P : Ideal R} (_ : IsPrime P) : IsDomain (R[X] ⧸ (
map (C : R ->+* R[X]) P : Ideal R[X]))
参数：_ : IsPrime P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.isDomain`：∀ {A : Type u_7} (B : Type u_8) [inst : Semiring A] [
inst_1 : Semiring B] [IsDomain B] (e : A ≃* B), IsDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
If `P` is a prime ideal of `R`, then `R[x]/(P)` is an integral domain.
-/
theorem isDomain_map_C_quotient {P : Ideal R} (_ : IsPrime P) :
    IsDomain (R[X] ⧸ (map (C : R →+* R[X]) P : Ideal R[X])) :=
  MulEquiv.isDomain (Polynomial (R ⧸ P)) (polynomialQuotientEquivQuotientPolynomial P).symm

/-- Given any ring `R` and an ideal `I` of `R[X]`, we get a map `R → R[x] → R[x]/I`.
  If we let `R` be the image of `R` in `R[x]/I` then we also have a map `R[x] → R'[x]`.
  In particular we can map `I` across this map, to get `I'` and a new map `R' → R'[x] → R'[x]/I`.
  This theorem shows `I'` will not contain any non-zero constant polynomials. -/
/-
**Ideal.eq_zero_of_polynomial_mem_map_range** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_zero_of_polynomial_mem_map_range (I : Ideal R[X]) (x : ((Quotient.mk I)
.comp C).range) (hx : C x in I.map (Polynomial.mapRingHom ((Quotient.mk I).comp 
C).rangeRestrict)) : x = 0
参数：I : Ideal R[X]；x : ((Quotient.mk I).comp C).range；hx : C x in I.map (Polynomi
al.mapRingHom ((Quotient.mk I).comp C).rangeRestrict)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Ideal.polynomial_mem_ideal_of_coeff_mem_ideal`：polynomial_mem_ideal_of_c
oeff_mem_ideal (I : Ideal R[X]) (p : R[X]) (hp : forall n : Nat, p.coeff n in I.
comap (C : R ->+* R[X])) : p in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `RingHom.coe_rangeRestrict`：coe_rangeRestrict (f : R ->+* S) (x : R) : (f
.rangeRestrict x : S) = f x
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.mem_range`：mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exi
sts x, f x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Ideal.mem_image_of_mem_map_of_surjective`：mem_image_of_mem_map_of_surjec
tive {I : Ideal R} {y} (H : y in map f I) : y in f '' I
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
· 使用定理 `RingHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : R ->+* S
) : Function.Surjective f.rangeRestrict
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Given any ring `R` and an ideal `I` of `R[X]`, we get a map `R → R[x] → R[x]/I`.
  If we let `R` be the image of `R` in `R[x]/I` then we also have a map `R[x] → 
R'[x]`.
  In particular we can map `I` across this map, to get `I'` and a new map `R' → 
R'[x] → R'[x]/I`.
  This theorem shows `I'` will not contain any non-zero constant polynomials.
-/
theorem eq_zero_of_polynomial_mem_map_range (I : Ideal R[X]) (x : ((Quotient.mk I).comp C).range)
    (hx : C x ∈ I.map (Polynomial.mapRingHom ((Quotient.mk I).comp C).rangeRestrict)) : x = 0 := by
  let i := ((Quotient.mk I).comp C).rangeRestrict
  have hi' : RingHom.ker (Polynomial.mapRingHom i) ≤ I := by
    refine fun f hf => polynomial_mem_ideal_of_coeff_mem_ideal I f fun n => ?_
    rw [mem_comap, ← Quotient.eq_zero_iff_mem, ← RingHom.comp_apply]
    rw [RingHom.mem_ker, coe_mapRingHom] at hf
    replace hf := congr_arg (fun f : Polynomial _ => f.coeff n) hf
    simp only [coeff_map, coeff_zero] at hf
    rwa [Subtype.ext_iff, RingHom.coe_rangeRestrict] at hf
  obtain ⟨x, hx'⟩ := x
  obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx'
  refine Subtype.ext ?_
  simp only [RingHom.comp_apply, Quotient.eq_zero_iff_mem, ZeroMemClass.coe_zero]
  suffices C (i y) ∈ I.map (Polynomial.mapRingHom i) by
    obtain ⟨f, hf⟩ := mem_image_of_mem_map_of_surjective (Polynomial.mapRingHom i)
      (Polynomial.map_surjective _ (RingHom.rangeRestrict_surjective ((Quotient.mk I).comp C))) this
    refine sub_add_cancel (C y) f ▸ I.add_mem (hi' ?_ : C y - f ∈ I) hf.1
    rw [RingHom.mem_ker, map_sub, hf.2, sub_eq_zero, coe_mapRingHom, map_C]
  exact hx

/-- Given a domain `R`, if `R[X]` is a principal ideal ring, then `R` is a field. -/
/-
**Ideal.IsField.of_isPrincipalIdealRing_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `Id
eal.IsField`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [IsDomain R] [IsPrincipalIdealRing (P
olynomial R)], IsField R
参数：Polynomial R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.maximal_ideal_iff_isField_quotient`：maximal_ideal_iff_isF
ield_quotient {R} [CommRing R] (I : Ideal R) : I.IsMaximal ↔ IsField (R ⧸ I)
· 使用定理 `PrincipalIdealRing.isMaximal_of_irreducible`：isMaximal_of_irreducible [C
ommSemiring R] [IsPrincipalIdealRing R] {p : R} (hp : Irreducible p) : Ideal.IsM
aximal (span R ({p} : Set R))
· 使用定理 `Polynomial.irreducible_X_sub_C`：irreducible_X_sub_C (r : R) : Irreducibl
e (X - C r)

--- 原说明 ---
Given a domain `R`, if `R[X]` is a principal ideal ring, then `R` is a field.
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

/-
**MvPolynomial.quotient_map_C_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：quotient_map_C_eq_zero {I : Ideal R} {i : R} (hi : i in I) : (Ideal.Quotie
nt.mk (Ideal.map (C : R ->+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R))).co
mp C i = 0
参数：hi : i in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
-/
theorem quotient_map_C_eq_zero {I : Ideal R} {i : R} (hi : i ∈ I) :
    (Ideal.Quotient.mk (Ideal.map (C : R →+* MvPolynomial σ R) I :
      Ideal (MvPolynomial σ R))).comp C i = 0 := by
  simp only [Function.comp_apply, RingHom.coe_comp, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hi
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C_mk_eq_zero {I : Ideal R} {a : MvPolynomial σ R}
    (ha : a ∈ (Ideal.map (C : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R))) :
    eval₂Hom (C.comp (Ideal.Quotient.mk I)) X a = 0 := by
  rw [as_sum a]
  rw [coe_eval₂Hom, eval₂_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  simp only [eval₂_monomial, Function.comp_apply, RingHom.coe_comp]
  refine mul_eq_zero_of_left ?_ _
  suffices coeff n a ∈ I by
    rw [← @Ideal.mk_ker R _ I, RingHom.mem_ker] at this
    simp only [this, C_0]
  exact mem_map_C_iff.1 ha n

/-- Split off from `quotientEquivQuotientMvPolynomial` for speed. -/
/-
**MvPolynomial.quotientEquivQuotientMvPolynomial_rightInverse** 是 Mathlib 中的一个引理
，位于命名空间 `MvPolynomial`。
形式化陈述：quotientEquivQuotientMvPolynomial_rightInverse (I : Ideal R) : Function.Ri
ghtInverse (eval₂ (Ideal.Quotient.lift I ((Ideal.Quotient.mk (Ideal.map C I : Id
eal (MvPolynomial σ R))).comp C) fun _ hi => quotient_map_C_eq_zero hi) fun i =>
 Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i)) (Ideal.Quot
ient.lift (Ideal.map C I : Ideal (MvPolynomial σ R)) (eval₂Hom (C.comp (Ideal.Qu
otient.mk I)) X) fun _ ha => eval₂_C_mk_eq_zero ha)
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `MvPolynomial.eval₂_C_mk_eq_zero`：eval₂_C_mk_eq_zero {I : Ideal R} {a : M
vPolynomial σ R} (ha : a in (Ideal.map (C : R ->+* MvPolynomial σ R) I : Ideal (
MvPolynomial σ R))) :…
· 使用定理 `MvPolynomial.quotient_map_C_eq_zero`：quotient_map_C_eq_zero {I : Ideal R
} {i : R} (hi : i in I) : (Ideal.Quotient.mk (Ideal.map (C : R ->+* MvPolynomial
 σ R) I : Ideal (MvPolyno…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
· 使用定理 `MvPolynomial.eval₂Hom_C`：eval₂Hom_C (f : R ->+* S₁) (g : σ -> S₁) (r : R
) : eval₂Hom f g (C r) = f r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.eval₂_add`：eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.
eval₂ f g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.eval₂_mul`：eval₂_mul : forall {p}, (p * q).eval₂ f g = p.ev
al₂ f g * q.eval₂ f g
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
Split off from `quotientEquivQuotientMvPolynomial` for speed.
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
    rw [hp, hq]
  · intro p i hp
    simp only [hp, coe_eval₂Hom, Ideal.Quotient.lift_mk, eval₂_mul, map_mul, eval₂_X]

/-- Split off from `quotientEquivQuotientMvPolynomial` for speed. -/
/-
**MvPolynomial.quotientEquivQuotientMvPolynomial_leftInverse** 是 Mathlib 中的一个引理，
位于命名空间 `MvPolynomial`。
形式化陈述：quotientEquivQuotientMvPolynomial_leftInverse (I : Ideal R) : Function.Lef
tInverse (eval₂ (Ideal.Quotient.lift I ((Ideal.Quotient.mk (Ideal.map C I : Idea
l (MvPolynomial σ R))).comp C) fun _ hi => quotient_map_C_eq_zero hi) fun i => I
deal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i)) (Ideal.Quotie
nt.lift (Ideal.map C I : Ideal (MvPolynomial σ R)) (eval₂Hom (C.comp (Ideal.Quot
ient.mk I)) X) fun _ ha => eval₂_C_mk_eq_zero ha)
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `MvPolynomial.quotient_map_C_eq_zero`：quotient_map_C_eq_zero {I : Ideal R
} {i : R} (hi : i in I) : (Ideal.Quotient.mk (Ideal.map (C : R ->+* MvPolynomial
 σ R) I : Ideal (MvPolyno…
· 使用定理 `MvPolynomial.eval₂_C_mk_eq_zero`：eval₂_C_mk_eq_zero {I : Ideal R} {a : M
vPolynomial σ R} (ha : a in (Ideal.map (C : R ->+* MvPolynomial σ R) I : Ideal (
MvPolynomial σ R))) :…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.lift_mk`：lift_mk (f : R ->+* S) (H : forall a : R, a in I
 -> f a = 0) : lift I f H (mk I a) = f a
· 使用定理 `MvPolynomial.eval₂Hom_C`：eval₂Hom_C (f : R ->+* S₁) (g : σ -> S₁) (r : R
) : eval₂Hom f g (C r) = f r
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.eval₂_add`：eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.
eval₂ f g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
· 使用定理 `MvPolynomial.eval₂_mul`：eval₂_mul : forall {p}, (p * q).eval₂ f g = p.ev
al₂ f g * q.eval₂ f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Split off from `quotientEquivQuotientMvPolynomial` for speed.
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
    rw [Ideal.Quotient.lift_mk, eval₂Hom_C, RingHom.comp_apply, eval₂_C, Ideal.Quotient.lift_mk,
      RingHom.comp_apply]
  · intro p q hp hq
    rw [Ideal.Quotient.lift_mk] at hp hq ⊢
    simp only [eval₂_add, map_add, coe_eval₂Hom] at hp hq ⊢
    rw [hp, hq]
  · intro p i hp
    simp only [coe_eval₂Hom, Ideal.Quotient.lift_mk,
      eval₂_mul, map_mul, eval₂_X] at hp ⊢
    simp only [hp]

/-- If `I` is an ideal of `R`, then the ring `MvPolynomial σ I.quotient` is isomorphic as an
`R`-algebra to the quotient of `MvPolynomial σ R` by the ideal generated by `I`. -/
/-
**MvPolynomial.quotientEquivQuotientMvPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `MvPo
lynomial`。
形式化陈述：quotientEquivQuotientMvPolynomial (I : Ideal R) : MvPolynomial σ (R ⧸ I) ≃
ₐ[R] MvPolynomial σ R ⧸ (Ideal.map C I : Ideal (MvPolynomial σ R))
参数：I : Ideal R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `MvPolynomial.quotient_map_C_eq_zero`：quotient_map_C_eq_zero {I : Ideal R
} {i : R} (hi : i in I) : (Ideal.Quotient.mk (Ideal.map (C : R ->+* MvPolynomial
 σ R) I : Ideal (MvPolyno…
· 使用定理 `MvPolynomial.eval₂_C_mk_eq_zero`：eval₂_C_mk_eq_zero {I : Ideal R} {a : M
vPolynomial σ R} (ha : a in (Ideal.map (C : R ->+* MvPolynomial σ R) I : Ideal (
MvPolynomial σ R))) :…
· 使用引理 `MvPolynomial.quotientEquivQuotientMvPolynomial_rightInverse`：quotientEqu
ivQuotientMvPolynomial_rightInverse (I : Ideal R) : Function.RightInverse (eval₂
 (Ideal.Quotient.lift I ((Ideal.Quotient.mk (Idea…
· 使用引理 `MvPolynomial.quotientEquivQuotientMvPolynomial_leftInverse`：quotientEqui
vQuotientMvPolynomial_leftInverse (I : Ideal R) : Function.LeftInverse (eval₂ (I
deal.Quotient.lift I ((Ideal.Quotient.mk (Ideal.…

--- 原说明 ---
If `I` is an ideal of `R`, then the ring `MvPolynomial σ I.quotient` is isomorph
ic as an
`R`-algebra to the quotient of `MvPolynomial σ R` by the ideal generated by `I`.
-/
noncomputable def quotientEquivQuotientMvPolynomial (I : Ideal R) :
    MvPolynomial σ (R ⧸ I) ≃ₐ[R] MvPolynomial σ R ⧸ (Ideal.map C I : Ideal (MvPolynomial σ R)) :=
  let e : MvPolynomial σ (R ⧸ I) →ₐ[R]
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

