/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Unramified algebras over fields

## Main results

Let `K` be a field, `A` be a `K`-algebra and `L` be a field extension of `K`.

- `Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing`:
    If `A` is `K`-unramified and `K` is alg-closed, then `K = A`.
- `Algebra.FormallyUnramified.isReduced_of_field`:
    If `A` is `K`-unramified then `A` is reduced.
- `Algebra.FormallyUnramified.iff_isSeparable`:
    `L` is unramified over `K` iff `L` is separable over `K`.

## References

- [B. Iversen, *Generic Local Structure of the Morphisms in Commutative Algebra*][iversen]

-/

public section

open Algebra Module Polynomial
open scoped TensorProduct

universe u

variable (K A L : Type*) [Field K] [Field L] [CommRing A] [Algebra K A] [Algebra K L]

namespace Algebra.FormallyUnramified

/-
**Algebra.FormallyUnramified.of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.F
ormallyUnramified`。
形式化陈述：of_isSeparable [Algebra.IsSeparable K L] : FormallyUnramified K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective`：iff_comp_injective : Form
allyUnramified R A ↔ forall ⦃B : Type u⦄ [CommRing B], forall [Algebra R B] (I :
 Ideal B) (_ : I ^ 2 = ⊥), Function…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Polynomial.eval_add_of_sq_eq_zero`：eval_add_of_sq_eq_zero (p : R[X]) (x 
y : R) (hy : y ^ 2 = 0) : p.eval (x + y) = p.eval x + p.derivative.eval x * y
· 使用定理 `Ideal.pow_mem_pow`：pow_mem_pow {x : R} (hx : x in I) (n : Nat) : x ^ n i
n I ^ n
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `IsUnit.mul_right_eq_zero`：mul_right_eq_zero {a b : M₀} (ha : IsUnit a) :
 a * b = 0 ↔ b = 0
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `Polynomial.Separable.aeval_derivative_ne_zero`：∀ {R : Type u} [inst : Co
mmSemiring R] {S : Type v} [inst_1 : CommSemiring S] [Nontrivial S] [inst_3 : Al
gebra R S]   {p : Polynomial R},   …
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Polynomial.derivative_map`：derivative_map [Semiring S] (p : R[X]) (f : R
 ->+* S) : derivative (p.map f) = p.derivative.map f
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem of_isSeparable [Algebra.IsSeparable K L] : FormallyUnramified K L := by
  rw [iff_comp_injective]
  intro B _ _ I hI f₁ f₂ e
  ext x
  have : f₁ x - f₂ x ∈ I := by
    simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using AlgHom.congr_fun e x
  have := Polynomial.eval_add_of_sq_eq_zero ((minpoly K x).map (algebraMap K B)) (f₂ x)
    (f₁ x - f₂ x) (show (f₁ x - f₂ x) ^ 2 ∈ ⊥ from hI ▸ Ideal.pow_mem_pow this 2)
  simp only [add_sub_cancel, eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero,
    derivative_map, zero_add] at this
  rwa [eq_comm, ((isUnit_iff_ne_zero.mpr
    ((Algebra.IsSeparable.isSeparable K x).aeval_derivative_ne_zero
      (minpoly.aeval K x))).map f₂).mul_right_eq_zero, sub_eq_zero] at this

variable [FormallyUnramified K A] [EssFiniteType K A]
variable [FormallyUnramified K L] [EssFiniteType K L]
/-
**Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing** 是 Mathlib
 中的一个定理，位于命名空间 `Algebra.FormallyUnramified`。
形式化陈述：bijective_of_isAlgClosed_of_isLocalRing [IsAlgClosed K] [IsLocalRing A] : 
Function.Bijective (algebraMap K A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.FormallyUnramified.finite_of_free`：finite_of_free [Module.Free R
 S] : Module.Finite R S
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `isArtinian_of_tower`：isArtinian_of_tower (R) {S M} [Semiring R] [Semirin
g S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R S M
] (h : Is…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.jacobson_eq_maximalIdeal`：jacobson_eq_maximalIdeal (I : Idea
l R) (h : I != ⊤) : I.jacobson = IsLocalRing.maximalIdeal R
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsArtinianRing.isNilpotent_jacobson_bot`：isNilpotent_jacobson_bot {R} [R
ing R] [IsArtinianRing R] : IsNilpotent (Ideal.jacobson (⊥ : Ideal R))
· 使用定理 `IsAlgClosed.algebraMap_bijective_of_isIntegral`：algebraMap_bijective_of_
isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K] [hk : IsAlgClosed k] [A
lgebra k K] [Algebra.IsIntegral k K]…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `instIsIntegralQuotientIdeal`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {I : Ideal A}   [Algebra.I
sIntegral R A], A…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
（共 79 条，此处仅展示前 30 条）
-/
theorem bijective_of_isAlgClosed_of_isLocalRing
    [IsAlgClosed K] [IsLocalRing A] :
    Function.Bijective (algebraMap K A) := by
  have := finite_of_free (R := K) (S := A)
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  have hA : IsNilpotent (IsLocalRing.maximalIdeal A) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥]
    · exact IsArtinianRing.isNilpotent_jacobson_bot
    · exact bot_ne_top
  let e : K ≃ₐ[K] A ⧸ IsLocalRing.maximalIdeal A := {
    __ := Algebra.ofId K (A ⧸ IsLocalRing.maximalIdeal A)
    __ := Equiv.ofBijective _ IsAlgClosed.algebraMap_bijective_of_isIntegral }
  let e' : A ⊗[K] (A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[A] A :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e.symm).trans (Algebra.TensorProduct.rid K A A)
  let f : A ⧸ IsLocalRing.maximalIdeal A →ₗ[A] A := e'.toLinearMap.comp (sec K A _)
  have hf : (Algebra.ofId _ _).toLinearMap ∘ₗ f = LinearMap.id := by
    dsimp [f]
    rw [← LinearMap.comp_assoc, ← comp_sec K A]
    congr 1
    apply LinearMap.restrictScalars_injective K
    apply _root_.TensorProduct.ext'
    intro r s
    obtain ⟨s, rfl⟩ := e.surjective s
    suffices s • (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) r = r • e s by
      simpa [ofId, e']
    simp [Algebra.smul_def, e, ofId, mul_comm]
  have hf₁ : f 1 • (1 : A ⧸ IsLocalRing.maximalIdeal A) = 1 := by
    rw [← algebraMap_eq_smul_one]
    exact LinearMap.congr_fun hf 1
  have hf₂ : 1 - f 1 ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, ← Ideal.Quotient.algebraMap_eq,
     algebraMap_eq_smul_one, hf₁, sub_self]
  have hf₃ : IsIdempotentElem (1 - f 1) := by
    apply IsIdempotentElem.one_sub
    rw [IsIdempotentElem, ← smul_eq_mul, ← map_smul, hf₁]
  have hf₄ : f 1 = 1 := by
    obtain ⟨n, hn⟩ := hA
    have : (1 - f 1) ^ n = 0 := by
      rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hn]
      exact Ideal.pow_mem_pow hf₂ n
    rw [eq_comm, ← sub_eq_zero, ← hf₃.pow_succ_eq n, pow_succ, this, zero_mul]
  refine Equiv.bijective ⟨algebraMap K A, ⇑e.symm ∘ ⇑(algebraMap A _), fun x ↦ by simp, fun x ↦ ?_⟩
  have : ⇑(algebraMap K A) = ⇑f ∘ ⇑e := by
    ext k
    conv_rhs => rw [← mul_one k, ← smul_eq_mul, Function.comp_apply, map_smul,
      LinearMap.map_smul_of_tower, map_one, hf₄, ← algebraMap_eq_smul_one]
  rw [this]
  simp only [Function.comp_apply, AlgEquiv.apply_symm_apply, algebraMap_eq_smul_one,
    map_smul, hf₄, smul_eq_mul, mul_one]
/-
**Algebra.FormallyUnramified.isField_of_isAlgClosed_of_isLocalRing** 是 Mathlib 中
的一个定理，位于命名空间 `Algebra.FormallyUnramified`。
形式化陈述：isField_of_isAlgClosed_of_isLocalRing [IsAlgClosed K] [IsLocalRing A] : Is
Field A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.isField_iff_maximalIdeal_eq`：isField_iff_maximalIdeal_eq : I
sField R ↔ maximalIdeal R = ⊥
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing`：bije
ctive_of_isAlgClosed_of_isLocalRing [IsAlgClosed K] [IsLocalRing A] : Function.B
ijective (algebraMap K A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `RingHom.congr_arg`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} (f : α →+* β) {x_2 y : α},   x_2 = y → f x_2 = f 
y
-/
theorem isField_of_isAlgClosed_of_isLocalRing
    [IsAlgClosed K] [IsLocalRing A] : IsField A := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := (bijective_of_isAlgClosed_of_isLocalRing K A).surjective x
  change _ = 0
  rw [← (algebraMap K A).map_zero]
  by_contra hx'
  exact hx ((isUnit_iff_ne_zero.mpr
    (fun e ↦ hx' ((algebraMap K A).congr_arg e))).map (algebraMap K A))

include K in
/-
**Algebra.FormallyUnramified.isReduced_of_field** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra.FormallyUnramified`。
形式化陈述：isReduced_of_field : IsReduced A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_zero_of_localization`：eq_zero_of_localization (r : R) (h : forall (J 
: Ideal R) (_ : J.IsMaximal), algebraMap R (Localization.AtPrime J) r = 0) : r =
 0
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
· 使用定理 `Algebra.EssFiniteType.of_isLocalization`：∀ {R : Type u_1} (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid
 R)   [IsLocalization M S], A…
· 使用定理 `Algebra.FormallyUnramified.of_isLocalization`：of_isLocalization [IsLocal
ization M Rₘ] : FormallyUnramified R Rₘ
· 使用定理 `Algebra.EssFiniteType.comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type u_
3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 : A
lgebra R S] [ins…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.EssFiniteType.baseChange`：∀ (R : Type u_1) (S : Type u_2) (T : T
ype u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst
_3 : Algebra R S] [ins…
（共 37 条，此处仅展示前 30 条）
-/
theorem isReduced_of_field :
    IsReduced A := by
  constructor
  intro x hx
  let f := (Algebra.TensorProduct.includeRight (R := K) (A := AlgebraicClosure K) (B := A))
  have : Function.Injective f := by
    have : ⇑f = (LinearMap.rTensor A (Algebra.ofId K (AlgebraicClosure K)).toLinearMap).comp
        (Algebra.TensorProduct.lid K A).symm.toLinearMap := by
      ext x; simp [f]
    rw [this]
    suffices Function.Injective
        (LinearMap.rTensor A (Algebra.ofId K (AlgebraicClosure K)).toLinearMap) by
      exact this.comp (Algebra.TensorProduct.lid K A).symm.injective
    apply Module.Flat.rTensor_preserves_injective_linearMap
    exact (algebraMap K _).injective
  apply this
  rw [map_zero]
  apply eq_zero_of_localization
  intro M hM
  have hy := (hx.map f).map (algebraMap _ (Localization.AtPrime M))
  generalize algebraMap _ (Localization.AtPrime M) (f x) = y at *
  have := EssFiniteType.of_isLocalization (Localization.AtPrime M) M.primeCompl
  have := of_isLocalization (Rₘ := Localization.AtPrime M) M.primeCompl
  have := EssFiniteType.comp (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
    (Localization.AtPrime M)
  have := comp (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
    (Localization.AtPrime M)
  let := (isField_of_isAlgClosed_of_isLocalRing (AlgebraicClosure K)
    (A := Localization.AtPrime M)).toField
  exact hy.eq_zero
/-
**Algebra.FormallyUnramified.isRadical_map_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `
Algebra.FormallyUnramified`。
形式化陈述：isRadical_map_isMaximal (B : Type*) [CommRing B] [Algebra A B] [Algebra.Es
sFiniteType A B] [Algebra.FormallyUnramified A B] (p : Ideal A) [p.IsMaximal] : 
(p.map (algebraMap A B)).IsRadical
参数：B : Type*；p : Ideal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.isRadical_iff_quotient_reduced`：Ideal.isRadical_iff_quotient_reduc
ed {R : Type*} [CommRing R] (I : Ideal R) : I.IsRadical ↔ IsReduced (R ⧸ I)
· 使用定理 `Algebra.FormallyUnramified.isReduced_of_field`：isReduced_of_field : IsRe
duced A
· 使用定理 `Algebra.EssFiniteType.quotient_map`：∀ (R : Type u_1) (S : Type u_2) [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssFinit
eType R S] (p : Ideal R)…
-/
theorem isRadical_map_isMaximal (B : Type*) [CommRing B] [Algebra A B]
    [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B] (p : Ideal A) [p.IsMaximal] :
    (p.map (algebraMap A B)).IsRadical := by
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  rw [Ideal.isRadical_iff_quotient_reduced]
  exact Algebra.FormallyUnramified.isReduced_of_field (A ⧸ p) (B ⧸ p.map (algebraMap A B))
/-
**Algebra.FormallyUnramified.range_eq_top_of_isPurelyInseparable** 是 Mathlib 中的一
个定理，位于命名空间 `Algebra.FormallyUnramified`。
形式化陈述：range_eq_top_of_isPurelyInseparable [IsPurelyInseparable K L] : (algebraMa
p K L).range = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `rank_zero_iff`：rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `rank_tensorProduct'`：rank_tensorProduct' : Module.rank R (M otimes[S] M₁
) = Module.rank R M * Module.rank S M₁
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `IsPurelyInseparable.pow_mem`：IsPurelyInseparable.pow_mem [IsPurelyInsepa
rable F E] : exists n : Nat, x ^ q ^ n in (algebraMap F E).range
· 使用引理 `expChar_of_injective_ringHom`：expChar_of_injective_ringHom [NonAssocSemi
ring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (q : Nat)
 [hR : ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用引理 `sub_pow_expChar_pow`：sub_pow_expChar_pow : (x - y) ^ p ^ n = x ^ p ^ n -
 y ^ p ^ n
· 使用定理 `Algebra.TensorProduct.tmul_pow`：tmul_pow (a : A) (b : B) (k : Nat) : a o
timesₜ[R] b ^ k = (a ^ k) otimesₜ[R] (b ^ k)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Algebra.FormallyUnramified.isReduced_of_field`：isReduced_of_field : IsRe
duced A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.EssFiniteType.baseChange`：∀ (R : Type u_1) (S : Type u_2) (T : T
ype u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst
_3 : Algebra R S] [ins…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 85 条，此处仅展示前 30 条）
-/
theorem range_eq_top_of_isPurelyInseparable
    [IsPurelyInseparable K L] : (algebraMap K L).range = ⊤ := by
  classical
  have : Nontrivial (L ⊗[K] L) := by
    rw [← not_subsingleton_iff_nontrivial, ← rank_zero_iff (R := K), rank_tensorProduct',
      mul_eq_zero, or_self, rank_zero_iff, not_subsingleton_iff_nontrivial]
    infer_instance
  rw [← top_le_iff]
  intro x _
  obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem K (ringExpChar K) x
  have : ExpChar (L ⊗[K] L) (ringExpChar K) := by
    refine expChar_of_injective_ringHom (algebraMap K _).injective (ringExpChar K)
  have : (1 ⊗ₜ x - x ⊗ₜ 1 : L ⊗[K] L) ^ (ringExpChar K) ^ n = 0 := by
    rw [sub_pow_expChar_pow, TensorProduct.tmul_pow, one_pow, TensorProduct.tmul_pow, one_pow]
    obtain ⟨r, hr⟩ := hn
    rw [← hr, algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]
  have H : (1 ⊗ₜ x : L ⊗[K] L) = x ⊗ₜ 1 := by
    have inst : IsReduced (L ⊗[K] L) := isReduced_of_field L _
    exact sub_eq_zero.mp (IsNilpotent.eq_zero ⟨_, this⟩)
  by_cases h' : LinearIndependent K ![1, x]
  · have h := h'.linearIndepOn_id
    let S := h.extend (Set.subset_univ _)
    let a : S := ⟨1, h.subset_extend _ (by simp)⟩
    have ha : Basis.extend h a = 1 := by simp [a]
    let b : S := ⟨x, h.subset_extend _ (by simp)⟩
    have hb : Basis.extend h b = x := by simp [b]
    by_cases e : a = b
    · obtain rfl : 1 = x := congr_arg Subtype.val e
      exact ⟨1, map_one _⟩
    have := DFunLike.congr_fun
      (DFunLike.congr_arg ((Basis.extend h).tensorProduct (Basis.extend h)).repr H) (a, b)
    simp only [Basis.tensorProduct_repr_tmul_apply, ← ha, ← hb, Basis.repr_self, smul_eq_mul,
      Finsupp.single_apply, e, Ne.symm e, ↓reduceIte, mul_one, mul_zero, one_ne_zero] at this
  · rw [LinearIndependent.pair_iff] at h'
    simp only [not_forall, not_and, exists_prop] at h'
    obtain ⟨a, b, e, hab⟩ := h'
    have : IsUnit b := by
      rw [isUnit_iff_ne_zero]
      rintro rfl
      rw [zero_smul, ← algebraMap_eq_smul_one, add_zero,
        (injective_iff_map_eq_zero' _).mp (algebraMap K L).injective] at e
      cases hab e rfl
    use (-this.unit⁻¹ * a)
    rw [map_mul, ← Algebra.smul_def, algebraMap_eq_smul_one, eq_neg_iff_add_eq_zero.mpr e,
      smul_neg, neg_smul, neg_neg, smul_smul, this.val_inv_mul, one_smul]
/-
**Algebra.FormallyUnramified.isSeparable** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Form
allyUnramified`。
形式化陈述：isSeparable : Algebra.IsSeparable K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.FormallyUnramified.finite_of_free`：finite_of_free [Module.Free R
 S] : Module.Finite R S
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `separableClosure.eq_top_iff`：separableClosure.eq_top_iff : separableClos
ure F E = ⊤ ↔ Algebra.IsSeparable F E
· 使用定理 `Algebra.FormallyUnramified.of_restrictScalars`：of_restrictScalars [Forma
llyUnramified R B] : FormallyUnramified A B
· 使用定理 `Algebra.EssFiniteType.of_comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type
 u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 
: Algebra R S] [ins…
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `Algebra.FormallyUnramified.range_eq_top_of_isPurelyInseparable`：range_eq
_top_of_isPurelyInseparable [IsPurelyInseparable K L] : (algebraMap K L).range =
 ⊤
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSeparable : Algebra.IsSeparable K L := by
  have := finite_of_free (R := K) (S := L)
  rw [← separableClosure.eq_top_iff]
  have := of_restrictScalars K (separableClosure K L) L
  have := EssFiniteType.of_comp K (separableClosure K L) L
  ext
  change _ ↔ _ ∈ (⊤ : Subring _)
  rw [← range_eq_top_of_isPurelyInseparable (separableClosure K L) L]
  simp
/-
**Algebra.FormallyUnramified.iff_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
FormallyUnramified`。
形式化陈述：iff_isSeparable (L : Type u) [Field L] [Algebra K L] [EssFiniteType K L] :
 FormallyUnramified K L ↔ Algebra.IsSeparable K L
参数：L : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.isSeparable`：isSeparable : Algebra.IsSeparabl
e K L
· 使用定理 `Algebra.FormallyUnramified.of_isSeparable`：of_isSeparable [Algebra.IsSep
arable K L] : FormallyUnramified K L
-/
theorem iff_isSeparable (L : Type u) [Field L] [Algebra K L] [EssFiniteType K L] :
    FormallyUnramified K L ↔ Algebra.IsSeparable K L :=
  ⟨fun _ ↦ isSeparable K L, fun _ ↦ of_isSeparable K L⟩

end Algebra.FormallyUnramified

variable {K A} in
/-- If `A = K[X]/⟨p⟩` is unramified at some prime `Q`, then the minpoly of `X` in `κ(Q)`
only divides `p` once. -/
/-
**Algebra.IsUnramifiedAt.not_minpoly_sq_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsUnramifiedAt.not_minpoly_sq_dvd (Q : Ideal A) [Q.IsPrime] [Algeb
ra.IsUnramifiedAt K Q] (x : A) (p : K[X]) (hp₁ : Ideal.span {p} = RingHom.ker (a
eval x).toRingHom) (hp₂ : Function.Surjective (aeval (R
参数：Q : Ideal A；x : A；p : K[X]；hp₁ : Ideal.span {p} = RingHom.ker (aeval x).toRin
gHom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.of_surjective`：of_surjective [FiniteType R A] (f : A 
->ₐ[R] B) (hf : Surjective f) : FiniteType R B
· 使用定理 `Algebra.FiniteType.instPolynomial`：∀ {R : Type uR} {S : Type uS} [inst :
 CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   [Algebra.Fin
iteType R S], Algebra.F…
· 使用定理 `Algebra.Unramified.finiteType`：∀ {R : Type u_1} {inst : CommRing R} {A :
 Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Unrami
fied R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.inst`：∀ {R : Type u} [inst : CommRing R], Algebra.Etale R 
R
· 使用引理 `Algebra.FormallyUnramified.finite_of_free`：finite_of_free [Module.Free R
 S] : Module.Finite R S
· 使用定理 `Algebra.instEssFiniteTypeLocalization`：∀ (R : Type u_1) (S : Type u_2) [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssFi
niteType R S] (M : Submonoi…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsArtinianRing.of_finite`：IsArtinianRing.of_finite (R S) [Ring R] [Ring 
S] [Module R S] [IsScalarTower R S S] [IsArtinianRing R] [Module.Finite R S] : I
sArtinianRing …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.FormallyUnramified.isReduced_of_field`：isReduced_of_field : IsRe
duced A
· 使用定理 `IsArtinianRing.isField_of_isReduced_of_isLocalRing`：isField_of_isReduced
_of_isLocalRing [IsReduced R] [IsLocalRing R] : IsField R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
If `A = K[X]/⟨p⟩` is unramified at some prime `Q`, then the minpoly of `X` in `κ
(Q)`
only divides `p` once.
-/
theorem Algebra.IsUnramifiedAt.not_minpoly_sq_dvd
    (Q : Ideal A) [Q.IsPrime] [Algebra.IsUnramifiedAt K Q] (x : A) (p : K[X])
    (hp₁ : Ideal.span {p} = RingHom.ker (aeval x).toRingHom)
    (hp₂ : Function.Surjective (aeval (R := K) x)) :
    ¬ minpoly K (algebraMap A Q.ResidueField x) ^ 2 ∣ p := by
  have : Algebra.FiniteType K A := .of_surjective _ hp₂
  have := Algebra.FormallyUnramified.finite_of_free K (Localization.AtPrime Q)
  have : IsField (Localization.AtPrime Q) :=
    have := IsArtinianRing.of_finite K (Localization.AtPrime Q)
    have := Algebra.FormallyUnramified.isReduced_of_field K (Localization.AtPrime Q)
    IsArtinianRing.isField_of_isReduced_of_isLocalRing _
  let := this.toField
  set q := minpoly K (algebraMap A Q.ResidueField x)
  have : algebraMap A (Localization.AtPrime Q) (aeval x q) = 0 := by
    apply (algebraMap (Localization.AtPrime Q) Q.ResidueField).injective
    rw [← IsScalarTower.algebraMap_apply, ← aeval_algebraMap_apply, minpoly.aeval, map_zero]
  obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ _).mp this
  obtain ⟨m, rfl⟩ := hp₂ m
  simp_rw [← map_mul, ← AlgHom.coe_toRingHom, ← AlgHom.toRingHom_eq_coe, ← RingHom.mem_ker,
    ← hp₁, Ideal.mem_span_singleton] at hm'
  rw [pow_two]
  rintro H
  have := (mul_dvd_mul_iff_right (minpoly.ne_zero (Algebra.IsIntegral.isIntegral _))).mp
    (H.trans hm')
  rw [minpoly.dvd_iff, aeval_algebraMap_apply, Q.algebraMap_residueField_eq_zero] at this
  exact hm this
