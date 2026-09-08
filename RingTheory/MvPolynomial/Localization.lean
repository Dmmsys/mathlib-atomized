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
If `S` is the localization of `R` at a submonoid `M`, then `MvPolynomial σ S`
is the localization of `MvPolynomial σ R` at `M.map MvPolynomial.C`.

See also `Polynomial.isLocalization` for the univariate case. -/
/-
**MvPolynomial.isLocalization** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：isLocalization : IsLocalization (M.map <| C (σ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.instIsScalarTower`：∀ {R : Type u_2} {S : Type u_3} {σ : Typ
e u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],
   IsScalarTower R (…
· 使用定理 `isLocalizedModule_iff_isLocalization`：isLocalizedModule_iff_isLocalizati
on : IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔ IsLocaliz
ation (Algebra.algebraMapS…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用引理 `MvPolynomial.algebraTensorAlgEquiv_tmul`：algebraTensorAlgEquiv_tmul (a :
 A) (p : MvPolynomial σ R) : algebraTensorAlgEquiv R A (a otimesₜ p) = a • MvPol
ynomial.map (algebraMap R A) …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `S` is the localization of `R` at a submonoid `M`, then `MvPolynomial σ S`
is the localization of `MvPolynomial σ R` at `M.map MvPolynomial.C`.

See also `Polynomial.isLocalization` for the univariate case.
-/
instance isLocalization : IsLocalization (M.map <| C (σ := σ)) (MvPolynomial σ S) :=
  isLocalizedModule_iff_isLocalization.mp <| (isLocalizedModule_iff_isBaseChange M S _).mpr <|
    .of_equiv (algebraTensorAlgEquiv _ _).toLinearEquiv fun _ ↦ by simp
/-
**MvPolynomial.isLocalization_C_mk'** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：isLocalization_C_mk' (a : R) (m : M) : C (IsLocalization.mk' S a m) = IsLo
calization.mk' (MvPolynomial σ S) (C (σ
参数：a : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.mem_map_of_mem`：mem_map_of_mem (f : F) {S : Submonoid M} {x : 
M} (hx : x in S) : f x in S.map f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**IsLocalization.Away.auxHom** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization.Away`。
形式化陈述：auxHom : (MvPolynomial Unit R) ⧸ (Ideal.span { C r * X () - 1 }) ->ₐ[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def auxHom : (MvPolynomial Unit R) ⧸ (Ideal.span { C r * X () - 1 }) →ₐ[R] S :=
  Ideal.Quotient.liftₐ (Ideal.span { C r * X () - 1}) (aeval (fun _ ↦ invSelf r)) <| by
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
/-
**IsLocalization.Away.auxHom_mk** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalization.Away`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma auxHom_mk (p : MvPolynomial Unit R) :
    auxHom S r p = aeval (S₁ := S) (fun _ ↦ invSelf r) p :=
  rfl

set_option backward.privateInPublic true in
private noncomputable
/-
**IsLocalization.Away.auxInv** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization.Away`。
形式化陈述：auxInv : S ->+* (MvPolynomial Unit R) ⧸ Ideal.span { C r * X () - 1 }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def auxInv : S →+* (MvPolynomial Unit R) ⧸ Ideal.span { C r * X () - 1 } :=
  letI g : R →+* MvPolynomial Unit R ⧸ (Ideal.span { C r * X () - 1 }) :=
    (Ideal.Quotient.mk _).comp C
  IsLocalization.Away.lift (S := S) (g := g) r <| by
    simp only [RingHom.coe_comp, Function.comp_apply, g]
    rw [isUnit_iff_exists_inv]
    use (Ideal.Quotient.mk _ <| X ())
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.mem_span_singleton_self (C r * X () - 1)
/-
**IsLocalization.Away.auxHom_auxInv** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalization.Aw
ay`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma auxHom_auxInv : (auxHom S r).toRingHom.comp (auxInv S r) = RingHom.id S := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  simp [auxInv]
/-
**IsLocalization.Away.auxInv_auxHom** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalization.Aw
ay`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma auxInv_auxHom : (auxInv S r).comp (auxHom (S := S) r).toRingHom = RingHom.id _ := by
  rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective)]
  ext x
  · simp [auxInv]
  · simp only [auxInv, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, auxHom_mk, aeval_X, RingHomCompTriple.comp_eq, invSelf, Away.lift,
      lift_mk'_spec]
    simp only [map_one]
    rw [← map_one (Ideal.Quotient.mk _), ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      ← Ideal.neg_mem_iff, neg_sub]
    exact Ideal.mem_span_singleton_self (C r * X x - 1)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The canonical algebra isomorphism from `MvPolynomial Unit R` quotiented by
`C r * X () - 1` to the localization of `R` away from `r`. -/
/-
**IsLocalization.Away.mvPolynomialQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsLoc
alization.Away`。
形式化陈述：mvPolynomialQuotientEquiv : ((MvPolynomial Unit R) ⧸ Ideal.span { C r * X 
() - 1 }) ≃ₐ[R] S where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical algebra isomorphism from `MvPolynomial Unit R` quotiented by
`C r * X () - 1` to the localization of `R` away from `r`.
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
/-
**IsLocalization.Away.mvPolynomialQuotientEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 
`IsLocalization.Away`。
形式化陈述：mvPolynomialQuotientEquiv_apply (p : MvPolynomial Unit R) : mvPolynomialQu
otientEquiv S r (Ideal.Quotient.mk _ p) = aeval (S₁
参数：p : MvPolynomial Unit R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma mvPolynomialQuotientEquiv_apply (p : MvPolynomial Unit R) :
    mvPolynomialQuotientEquiv S r (Ideal.Quotient.mk _ p) = aeval (S₁ := S) (fun _ ↦ invSelf r) p :=
  rfl

end IsLocalization.Away

