/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth

/-!
# Smooth algebras are flat

Let `A` be a smooth `R`-algebra. In this file we show that then `A` is `R`-flat.
The proof proceeds in two steps:

1. If `R` is Noetherian, let `R[X₁, ..., Xₙ] →ₐ[R] A` be surjective with kernel `I`. By
  formal smoothness we construct a section `A →ₐ[R] AdicCompletion I R[X₁, ..., Xₙ]`
  of the canonical map `AdicCompletion I R[X₁, ..., Xₙ] →ₐ[R] R[X₁, ..., Xₙ] ⧸ I ≃ₐ[R] A`.
  Since `R` is Noetherian, `AdicCompletion I R` is `R`-flat so `A` is a retract
  of a flat `R`-module and hence flat.
2. In the general case, we choose a model of `A` over a finitely generated
  `ℤ`-subalgebra of `R` and apply 1.


## References

- [Conde-Lago, A short proof of smooth implies flat][condelago2016shortproofsmoothimplies]
-/

public section

namespace Algebra

variable {R A S : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]

/-
**Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing** 是 Mathlib 中的一个定理，位
于命名空间 `Algebra.FormallySmooth`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {S : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : CommRing S] [inst_4 : Algebra 
R S] (f : S →ₐ[R] A),   Function.Surjective ⇑f → ∀ [Module.Flat R S] [IsNoetheri
anRing S] [Algebra.FormallySmooth R A], Module.Flat R A
参数：f : S →ₐ[R] A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Flat.trans`：trans [Flat R S] [Flat S M] : Flat R M
· 使用定理 `Algebra.FormallySmooth.exists_kerProj_comp_eq_id`：∀ {R : Type u_1} {A : 
Type u_2} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {S : 
Type u_3}   [inst_3 : CommRing S] [ins…
· 使用引理 `Module.Flat.of_retract`：of_retract [f : Flat R M] (i : N ->ₗ[R] M) (r : 
M ->ₗ[R] N) (h : r.comp i = LinearMap.id) : Flat R N
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma FormallySmooth.flat_of_algHom_of_isNoetherianRing (f : S →ₐ[R] A) (hf : Function.Surjective f)
    [Module.Flat R S] [IsNoetherianRing S] [FormallySmooth R A] :
    Module.Flat R A := by
  have : Module.Flat R (AdicCompletion (RingHom.ker f) S) := .trans _ S _
  obtain ⟨g, hg⟩ := exists_kerProj_comp_eq_id f hf
  exact .of_retract g.toLinearMap
    (AdicCompletion.kerProj hf).toLinearMap (LinearMap.ext fun x ↦ congr($hg x))

variable (R A)

/-- If `A` is `R`-smooth and `R` is Noetherian, then `A` is `R`-flat. -/
/-
**Algebra.Smooth.flat_of_isNoetherianRing** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Smo
oth`。
形式化陈述：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R] [inst_1 : CommRing A] 
[inst_2 : Algebra R A] [IsNoetherianRing R]   [Algebra.Smooth R A], Module.Flat 
R A
参数：R : Type u_1；A : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial''`：iff_quotient_mvPolynomia
l'' : FiniteType R S ↔ exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] S), S
urjective f
· 使用定理 `Algebra.Smooth.finitePresentation`：∀ {R : Type u_4} {inst : CommRing R} 
{A : Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smoo
th R A], Algebra.Finite…
· 使用定理 `Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing`：∀ {R : Type u
_1} {A : Type u_2} {S : Type u_3} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A]   [inst_3 : CommRing S] [ins…
· 使用定理 `MvPolynomial.instFree`：∀ (σ : Type u) (R : Type v) [inst : CommSemiring 
R], Module.Free R (MvPolynomial σ R)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…

--- 原说明 ---
If `A` is `R`-smooth and `R` is Noetherian, then `A` is `R`-flat.
-/
theorem Smooth.flat_of_isNoetherianRing [IsNoetherianRing R] [Smooth R A] :
    Module.Flat R A := by
  obtain ⟨k, f, hf⟩ := (FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  exact FormallySmooth.flat_of_algHom_of_isNoetherianRing f hf

/-- Any smooth algebra is flat. -/
/-
**Algebra.Smooth.flat** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Smooth`。
形式化陈述：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R] [inst_1 : CommRing A] 
[inst_2 : Algebra R A] [Algebra.Smooth R A],   Module.Flat R A
参数：R : Type u_1；A : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Smooth.exists_finiteType`：∀ (R : Type u_1) [inst : CommRing R] (
A : Type u) (B : Type u_2) [inst_1 : CommRing A] [Algebra R A]   [inst_3 : CommR
ing B] [inst_4 : Algeb…
· 使用定理 `Algebra.FiniteType.isNoetherianRing`：isNoetherianRing (R S : Type*) [Com
mRing R] [CommRing S] [Algebra R S] [h : Algebra.FiniteType R S] [IsNoetherianRi
ng R] : IsNoetherianRing …
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `AddGroup.instFGInt`：AddGroup.FG ℤ
· 使用定理 `Algebra.Smooth.flat_of_isNoetherianRing`：∀ (R : Type u_1) (A : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [IsNoetherianR
ing R]   [Algebra.Smooth R A]…
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N

--- 原说明 ---
Any smooth algebra is flat.
-/
instance Smooth.flat [Smooth R A] : Module.Flat R A := by
  obtain ⟨A₀, B₀, _, _, _, _, _, _, _, _, ⟨e⟩⟩ := exists_finiteType ℤ R A
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ _
  have : Module.Flat A₀ B₀ := Smooth.flat_of_isNoetherianRing _ _
  exact .of_linearEquiv e.toLinearEquiv

end Algebra

/-
**RingHom.Smooth.flat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.Smooth.flat {R S : Type*} [CommRing R] [CommRing S] {f : R ->+* S}
 (hf : f.Smooth) : f.Flat
参数：hf : f.Smooth。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Smooth.flat`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R]
 [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Smooth R A],   Module.Fla
t R A
· 使用定理 `RingHom.Smooth.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRi
ng R] [inst_1 : CommRing S] {f : R →+* S}, f.Smooth → Algebra.Smooth R S
-/
lemma RingHom.Smooth.flat {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.Smooth) :
    f.Flat := by
  algebraize [f]
  exact Algebra.Smooth.flat R S
