/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Ramification index and inertia degree

This file proves that the sum of ramification times inertia equals the degree of the extension.

Typically this is only stated for extensions of Dedekind domains, but we prove it for any finite
flat extension of an integral domain.

## Main results

* `Ideal.sum_ramification_inertia_eq_finrank`: Let `R` be an integral domain, let `S` be a finite
  flat `R`-algebra, and let `p` be a prime ideal of `R`. Then the sum over all prime ideals `q` of
  `S` lying over `p` of the ramification index of `q` times the inertia degree of `q` equals the
  rank of `S` as an `R`-module.
* `Ideal.sum_ramification_inertia_eq_card`: Let `S/R` be a finite flat extension of domains,
  and let `p` be prime ideal of `R`. Assume that `R` is the invariant subring of a finite group `G`
  acting on `S`. Then the sum over all prime ideals `q` of `S` lying over `p` of the ramification
  index of `q` times the inertia degree of `q` equals the cardinality of `G`.

-/

@[expose] public section

section

namespace Ideal

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S]

open IsLocalRing Module OrderIso PrimeSpectrum in
/-
**Ideal.sum_ramification_inertia_eq_finrank_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Ide
al`。
形式化陈述：sum_ramification_inertia_eq_finrank_fiber [Algebra.QuasiFinite R S] [Finty
pe (p.primesOver S)] : ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertia
Deg R = finrank p.ResidueField (p.Fiber S)
参数：p.primesOver S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinianRing.instFinitePrimeSpectrum`：∀ (R : Type u_1) [inst : CommRin
g R] [IsArtinianRing R], Finite (PrimeSpectrum R)
· 使用定理 `Algebra.QuasiFinite.instIsArtinianRingFiber`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.QuasiFinite R S] (P : Ideal R) […
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsArtinianRing.finrank_eq_sum_primeSpectrum`：finrank_eq_sum_primeSpectru
m [Fintype (PrimeSpectrum R)] : Module.finrank F R = ∑ p : PrimeSpectrum R, Modu
le.finrank F (Localization.AtPrim…
· 使用定理 `Algebra.QuasiFinite.finite_fiber`：∀ {R : Type u_1} {S : Type u_2} {inst 
: CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : Algebra.Qua
siFinite R S] (P : Ide…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.instLiesOverFiberOfIsPrime`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [inst
_3 : p.IsPrime] (q : I…
· 使用定理 `Ideal.ramificationIdx_eq`：ramificationIdx_eq [q.LiesOver p] [q.IsPrime] 
: letI Sq
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Ideal.inertiaDeg_eq`：inertiaDeg_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime
] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)] [Localization.AtPr
ime.IsLie…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用引理 `Module.length_eq_finrank`：Module.length_eq_finrank (K M : Type*) [Divisi
onRing K] [AddCommGroup M] [Module K M] [Module.Finite K M] : Module.length K M 
= Module.finra…
· 使用定理 `Algebra.instFiniteResidueFieldOfQuasiFiniteAt`：∀ {R : Type u_1} {S : Typ
e u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ide
al R)   [inst_3 : p.IsPrime] (P : I…
· 使用定理 `Algebra.QuasiFinite.instLocalization`：∀ {R : Type u_1} {S : Type u_2} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid S)
   [Algebra.QuasiFinite R …
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `IsLocalRing.length_restrictScalars`：IsLocalRing.length_restrictScalars :
 length A M = length B M * Module.length (ResidueField A) (ResidueField B)
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用引理 `LinearEquiv.length_eq`：LinearEquiv.length_eq {N : Type*} [AddCommGroup N
] [Module R N] (e : M ≃ₗ[R] N) : Module.length R M = Module.length R N
· 使用定理 `Module.length_eq_of_surjective`：Module.length_eq_of_surjective {S : Type
*} [CommRing S] [Algebra S R] [Module S M] [IsScalarTower S R M] (h : Function.S
urjective (algebraMa…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
（共 35 条，此处仅展示前 30 条）
-/
theorem sum_ramification_inertia_eq_finrank_fiber
    [Algebra.QuasiFinite R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R =
      finrank p.ResidueField (p.Fiber S) := by
  let := Fintype.ofFinite (PrimeSpectrum (p.Fiber S))
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum, ← (primesOverOrderIsoFiber R S p).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [toEquiv_symm, coe_symm_toEquiv, coe_primesOverOrderIsoFiber_symm_apply]
  set r := q.1.comap Algebra.TensorProduct.includeRight
  let := Localization.AtPrime.algebraOfLiesOver p r
  rw [ramificationIdx_eq p r, inertiaDeg_eq p r]
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q.1
  let Sr := Localization.AtPrime r
  let κp := p.ResidueField
  let κr := r.ResidueField
  let A := Sr ⧸ p.map (algebraMap R Sr)
  suffices length Sr A * finrank κp κr = finrank κp Sq by simpa using congr_arg ENat.toNat this
  calc length Sr A * finrank κp κr = length Sr A * length κp κr := by rw [length_eq_finrank]
    _ = length Rp A := (length_restrictScalars Rp Sr A).symm
    _ = length Rp Sq := (Fiber.localizationAlgEquivQuotient p q.1).toLinearEquiv.length_eq.symm
    _ = length κp Sq := length_eq_of_surjective residue_surjective
    _ = finrank κp Sq := length_eq_finrank κp Sq

/-- Let `R` be an integral domain, let `S` be a finite flat `R`-algebra, and let `p` be a prime
ideal of `R`. Then the sum over all prime ideals `q` of `S` lying over `p` of the ramification
index of `q` times the inertia degree of `q` equals the rank of `S` as an `R`-module. -/
/-
**Ideal.sum_ramification_inertia_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：sum_ramification_inertia_eq_finrank [IsDomain R] [Module.Finite R S] [Modu
le.Flat R S] [Fintype (p.primesOver S)] : ∑ q : p.primesOver S, q.1.ramification
Idx R * q.1.inertiaDeg R = Module.finrank R S
参数：p.primesOver S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.sum_ramification_inertia_eq_finrank_fiber`：sum_ramification_inerti
a_eq_finrank_fiber [Algebra.QuasiFinite R S] [Fintype (p.primesOver S)] : ∑ q : 
p.primesOver S, q.1.ramificationIdx R…
· 使用定理 `Algebra.QuasiFinite.instOfFinite`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Finite R S], 
  Algebra.QuasiFinite …
· 使用定理 `Ideal.finrank_fiber_eq_finrank`：∀ {R : Type uR} {M : Type uM} [inst : Co
mmRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Module.Flat 
R M] [Module.Finite …

--- 原说明 ---
Let `R` be an integral domain, let `S` be a finite flat `R`-algebra, and let `p`
 be a prime
ideal of `R`. Then the sum over all prime ideals `q` of `S` lying over `p` of th
e ramification
index of `q` times the inertia degree of `q` equals the rank of `S` as an `R`-mo
dule.
-/
theorem sum_ramification_inertia_eq_finrank
    [IsDomain R] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R = Module.finrank R S := by
  rw [sum_ramification_inertia_eq_finrank_fiber, finrank_fiber_eq_finrank]

/-- Let `S/R` be a finite flat extension of integral domains, and let `p` be prime ideal of `R`.
Assume that `R` is the invariant subring of a finite group `G` acting on `S`. Then the sum over
all prime ideals `q` of `S` lying over `p` of the ramification index of `q` times the inertia
degree of `q` equals the cardinality of `G`. -/
/-
**Ideal.sum_ramification_inertia_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：sum_ramification_inertia_eq_card [IsDomain R] [IsDomain S] [Module.Finite 
R S] [Module.Flat R S] [Fintype (p.primesOver S)] {G : Type*} [Group G] [MulSemi
ringAction G S] [IsGaloisGroup G R S] : ∑ q : p.primesOver S, q.1.ramificationId
x R * q.1.inertiaDeg R = Nat.card G
参数：p.primesOver S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.finite`：∀ (G : Type u_1) [inst : Group G] (R : Type u_5) (
B : Type u_6) [inst_1 : CommRing R] [inst_2 : CommRing B]   [inst_3 : Algebra R 
B] [Module…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.sum_ramification_inertia_eq_finrank`：sum_ramification_inertia_eq_f
inrank [IsDomain R] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver
 S)] : ∑ q : p.primesOver S, q.…
· 使用定理 `IsGaloisGroup.card_eq_finrank'`：card_eq_finrank' : Nat.card G = Module.f
inrank A B
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
Let `S/R` be a finite flat extension of integral domains, and let `p` be prime i
deal of `R`.
Assume that `R` is the invariant subring of a finite group `G` acting on `S`. Th
en the sum over
all prime ideals `q` of `S` lying over `p` of the ramification index of `q` time
s the inertia
degree of `q` equals the cardinality of `G`.
-/
theorem sum_ramification_inertia_eq_card
    [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)]
    {G : Type*} [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R = Nat.card G := by
  let := IsGaloisGroup.finite G R S
  rw [sum_ramification_inertia_eq_finrank, IsGaloisGroup.card_eq_finrank' G R S]

end Ideal

