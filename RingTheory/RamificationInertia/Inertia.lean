/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Inertia degree

Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined
to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`.

## Main definitions

* `Ideal.inertiaDeg q R`: The inertia degree of `q` over `R`.

## Main statements

* `inertiaDeg'_eq_inertiaDeg`: The inertia degree agrees with the usual definition in the case of
  maximal ideals.
* `inertiaDeg_tower`: Inertia degree is multiplicative in towers.
-/

@[expose] public section

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open scoped Classical in
/-- Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined
to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.inertiaDeg'`. -/
/-
**Ideal.inertiaDeg** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R
` is defined
to be the degree of the residue field of `q` over the residue field of its preim
age `p` in `R`.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.inertiaDeg'`.
-/
noncomputable def inertiaDeg : ℕ :=
  if _ : q.IsPrime then
    letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    Module.finrank (q.under R).ResidueField q.ResidueField else 0
/-
**Ideal.inertiaDeg_def** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_def [hq : q.IsPrime] [Algebra (Localization.AtPrime (q.under R)
) (Localization.AtPrime q)] [Localization.AtPrime.IsLiesOverAlgebra (q.under R) 
q] : q.inertiaDeg R = Module.finrank (q.under R).ResidueField q.ResidueField
参数：Localization.AtPrime (q.under R)；Localization.AtPrime q；q.under R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq`：∀ {A : Type u_4} {
B : Type u_5} {inst : CommSemiring A} {inst_1 : CommSemiring B} {inst_2 : Algebr
a A B} {p : Ideal A}   {inst_3 : p.IsPrime…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem inertiaDeg_def [hq : q.IsPrime]
    [Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra (q.under R) q] :
    q.inertiaDeg R = Module.finrank (q.under R).ResidueField q.ResidueField := by
  convert! dif_pos hq
  simp [Algebra.algebra_ext_iff, Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_def := inertiaDeg_def
/-
**Ideal.inertiaDeg_of_not_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_of_not_isPrime (hq : ¬ q.IsPrime) : q.inertiaDeg R = 0
参数：hq : ¬ q.IsPrime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem inertiaDeg_of_not_isPrime (hq : ¬ q.IsPrime) : q.inertiaDeg R = 0 :=
  dif_neg hq

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_of_not_isPrime :=
  inertiaDeg_of_not_isPrime
/-
**Ideal.inertiaDeg_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_pos [hq : q.IsPrime] [Module.Finite R S] : 0 < q.inertiaDeg R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg_def`：inertiaDeg_def [hq : q.IsPrime] [Algebra (Localiza
tion.AtPrime (q.under R)) (Localization.AtPrime q)] [Localization.AtPrime.IsLies
OverAlgebr…
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.instFiniteResidueFieldOfQuasiFiniteAt`：∀ {R : Type u_1} {S : Typ
e u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ide
al R)   [inst_3 : p.IsPrime] (P : I…
· 使用定理 `Algebra.QuasiFinite.instLocalization`：∀ {R : Type u_1} {S : Type u_2} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid S)
   [Algebra.QuasiFinite R …
· 使用定理 `Algebra.QuasiFinite.instOfFinite`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Finite R S], 
  Algebra.QuasiFinite …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
theorem inertiaDeg_pos [hq : q.IsPrime] [Module.Finite R S] : 0 < q.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  rw [inertiaDeg_def]
  apply Module.finrank_pos

end

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) (r : Ideal T)

/-
**Ideal.inertiaDeg_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime] [Algebra (Localizatio
n.AtPrime p) (Localization.AtPrime q)] [Localization.AtPrime.IsLiesOverAlgebra p
 q] : q.inertiaDeg R = Module.finrank p.ResidueField q.ResidueField
参数：Localization.AtPrime p；Localization.AtPrime q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Ideal.inertiaDeg_def`：inertiaDeg_def [hq : q.IsPrime] [Algebra (Localiza
tion.AtPrime (q.under R)) (Localization.AtPrime q)] [Localization.AtPrime.IsLies
OverAlgebr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inertiaDeg_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    q.inertiaDeg R = Module.finrank p.ResidueField q.ResidueField := by
  have := Ideal.over_def q p
  subst this
  exact inertiaDeg_def q R

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_eq := inertiaDeg_eq
/-
**Ideal.inertiaDeg_eq_of_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_eq_of_isFractionRing [q.LiesOver p] [p.IsPrime] [q.IsPrime] (K 
L : Type*) [Field K] [Field L] [Algebra (R ⧸ p) K] [IsFractionRing (R ⧸ p) K] [A
lgebra (S ⧸ q) L] [IsFractionRing (S ⧸ q) L] [Algebra R K] [IsScalarTower R (R ⧸
 p) K] [Algebra S L] [IsScalarTower S (S ⧸ q) L] [Algebra R L] [IsScalarTower R 
S L] [Algebra K L] [IsScalarTower R K L] : q.inertiaDeg R = Module.finrank K L
参数：K L : Type*；R ⧸ p；R ⧸ p；S ⧸ q；S ⧸ q；R ⧸ p；S ⧸ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg_eq`：inertiaDeg_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime
] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)] [Localization.AtPr
ime.IsLie…
· 使用定理 `Algebra.finrank_eq_of_equiv_equiv`：finrank_eq_of_equiv_equiv {R₀ S₀ : Ty
pe*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀] {R₁ S₁ : Type*} [CommSemiri
ng R₁] [Semiring S₁] [A…
· 使用定理 `instIsFractionRingQuotientIdealResidueField`：∀ {R : Type u_1} [inst : Co
mmRing R] (I : Ideal R) [inst_1 : I.IsPrime], IsFractionRing (R ⧸ I) I.ResidueFi
eld
· 使用定理 `instIsScalarTowerQuotientIdealResidueField`：∀ {R : Type u_1} {A : Type u
_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal 
A)   [inst_3 : I.IsPrime], IsSca…
· 使用定理 `IsFractionRing.ringHom_ext`：ringHom_ext {f1 f2 : K ->+* L} (hf : forall 
x : A, f1 (algebraMap A K x) = f2 (algebraMap A K x)) : f1 = f2
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst_3
 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inertiaDeg_eq_of_isFractionRing [q.LiesOver p] [p.IsPrime] [q.IsPrime]
    (K L : Type*) [Field K] [Field L]
    [Algebra (R ⧸ p) K] [IsFractionRing (R ⧸ p) K]
    [Algebra (S ⧸ q) L] [IsFractionRing (S ⧸ q) L]
    [Algebra R K] [IsScalarTower R (R ⧸ p) K]
    [Algebra S L] [IsScalarTower S (S ⧸ q) L]
    [Algebra R L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L] :
    q.inertiaDeg R = Module.finrank K L := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  rw [inertiaDeg_eq p q]
  apply Algebra.finrank_eq_of_equiv_equiv
    (IsFractionRing.algEquivOfAlgEquiv (R := R) (A := R ⧸ p) (K := p.ResidueField) (L := K) .refl)
    (IsFractionRing.algEquivOfAlgEquiv (R := S) (A := S ⧸ q) (K := q.ResidueField) (L := L) .refl)
  apply IsFractionRing.ringHom_ext (A := R ⧸ p)
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [← IsScalarTower.algebraMap_apply R p.ResidueField q.ResidueField,
    IsScalarTower.algebraMap_apply R S q.ResidueField,
    ← IsScalarTower.algebraMap_apply R K L, ← IsScalarTower.algebraMap_apply R S L]

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_eq_of_isFractionRing :=
inertiaDeg_eq_of_isFractionRing
/-
**Ideal.inertiaDeg_eq_of_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_eq_of_isMaximal [q.LiesOver p] [p.IsMaximal] [q.IsMaximal] : q.
inertiaDeg R = Module.finrank (R ⧸ p) (S ⧸ q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.inertiaDeg_eq_of_isFractionRing`：inertiaDeg_eq_of_isFractionRing [
q.LiesOver p] [p.IsPrime] [q.IsPrime] (K L : Type*) [Field K] [Field L] [Algebra
 (R ⧸ p) K] [IsFractionRing…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `instIsFractionRing`：∀ {R : Type u_6} [inst : Field R], IsFractionRing R 
R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
-/
theorem inertiaDeg_eq_of_isMaximal [q.LiesOver p] [p.IsMaximal] [q.IsMaximal] :
    q.inertiaDeg R = Module.finrank (R ⧸ p) (S ⧸ q) := by
  let : Field (R ⧸ p) := Quotient.field p
  let : Field (S ⧸ q) := Quotient.field q
  exact inertiaDeg_eq_of_isFractionRing p q (R ⧸ p) (S ⧸ q)

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_eq_of_isMaximal :=
  inertiaDeg_eq_of_isMaximal
/-
**Ideal.inertiaDeg'_eq_inertiaDeg** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (p : Ideal R)   (q : Ideal S) [q.LiesOver p] [p.IsMaximal
] [q.IsMaximal], p.inertiaDeg' q = q.inertiaDeg R
参数：p : Ideal R；q : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg'_algebraMap`：∀ {R : Type u} [inst : CommRing R] {S : Ty
pe v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)  
 [inst_3 : P.LiesO…
· 使用定理 `Ideal.inertiaDeg_eq_of_isMaximal`：inertiaDeg_eq_of_isMaximal [q.LiesOver
 p] [p.IsMaximal] [q.IsMaximal] : q.inertiaDeg R = Module.finrank (R ⧸ p) (S ⧸ q
)
-/
theorem inertiaDeg'_eq_inertiaDeg [q.LiesOver p] [p.IsMaximal] [q.IsMaximal] :
    p.inertiaDeg' q = q.inertiaDeg R := by
  rw [inertiaDeg'_algebraMap, inertiaDeg_eq_of_isMaximal p q]

@[deprecated (since := "2026-07-03")] alias inertiaDeg_eq_inertiaDeg' := inertiaDeg'_eq_inertiaDeg
/-
**Ideal.inertiaDeg_tower** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_tower [r.LiesOver q] : r.inertiaDeg R = q.inertiaDeg R * r.iner
tiaDeg S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.isPrime_of_liesOver`：isPrime_of_liesOver [P.LiesOver p] [P.IsPrime
] : p.IsPrime
· 使用定理 `Ideal.LiesOver.tower_bot`：∀ {A : Type u_2} [inst : CommSemiring A] {B : 
Type u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst
_3 : Algebra A…
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg_def`：inertiaDeg_def [hq : q.IsPrime] [Algebra (Localiza
tion.AtPrime (q.under R)) (Localization.AtPrime q)] [Localization.AtPrime.IsLies
OverAlgebr…
· 使用定理 `Ideal.inertiaDeg_eq`：inertiaDeg_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime
] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)] [Localization.AtPr
ime.IsLie…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower_1`：∀ {R : Type u_1} {S : Type
 u_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst
_3 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra_1`：∀ {A : Type
 u_4} {B : Type u_5} {C : Type u_6} [inst : CommSemiring A] [inst_1 : CommSemiri
ng B] [inst_2 : Algebra A B]   [inst_3 : CommSemi…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Ideal.inertiaDeg_of_not_isPrime`：inertiaDeg_of_not_isPrime (hq : ¬ q.IsP
rime) : q.inertiaDeg R = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem inertiaDeg_tower [r.LiesOver q] :
    r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
    let := Localization.AtPrime.algebraOfLiesOver (r.under R) r
    let := Localization.AtPrime.algebraOfLiesOver (r.under R) q
    let := Localization.AtPrime.algebraOfLiesOver q r
    rw [inertiaDeg_def, inertiaDeg_eq (r.under R), inertiaDeg_eq q, eq_comm]
    apply Module.finrank_mul_finrank
  · rw [inertiaDeg_of_not_isPrime r R hr, inertiaDeg_of_not_isPrime r S hr, mul_zero]

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_tower := inertiaDeg_tower
/-
**Ideal.inertiaDeg_below_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_below_dvd [r.LiesOver q] : q.inertiaDeg R ∣ r.inertiaDeg R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.inertiaDeg_tower`：inertiaDeg_tower [r.LiesOver q] : r.inertiaDeg R
 = q.inertiaDeg R * r.inertiaDeg S
-/
theorem inertiaDeg_below_dvd [r.LiesOver q] :
    q.inertiaDeg R ∣ r.inertiaDeg R := by
  use r.inertiaDeg S
  rw [← inertiaDeg_tower]

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_below_dvd := inertiaDeg_below_dvd
/-
**Ideal.inertiaDeg_above_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_above_dvd [r.LiesOver q] : r.inertiaDeg S ∣ r.inertiaDeg R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.inertiaDeg_tower`：inertiaDeg_tower [r.LiesOver q] : r.inertiaDeg R
 = q.inertiaDeg R * r.inertiaDeg S
-/
theorem inertiaDeg_above_dvd [r.LiesOver q] :
    r.inertiaDeg S ∣ r.inertiaDeg R := by
  use q.inertiaDeg R
  rw [mul_comm, ← inertiaDeg_tower]

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_above_dvd := inertiaDeg_above_dvd
/-
**Ideal.inertiaDeg_below_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_below_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] : q.ine
rtiaDeg R <= r.inertiaDeg R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ideal.inertiaDeg_pos`：inertiaDeg_pos [hq : q.IsPrime] [Module.Finite R S
] : 0 < q.inertiaDeg R
· 使用定理 `Ideal.inertiaDeg_below_dvd`：inertiaDeg_below_dvd [r.LiesOver q] : q.iner
tiaDeg R ∣ r.inertiaDeg R
-/
theorem inertiaDeg_below_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] :
    q.inertiaDeg R ≤ r.inertiaDeg R :=
  Nat.le_of_dvd (r.inertiaDeg_pos R) (q.inertiaDeg_below_dvd r)

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_below_le := inertiaDeg_below_le
/-
**Ideal.inertiaDeg_above_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_above_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] : r.ine
rtiaDeg S <= r.inertiaDeg R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ideal.inertiaDeg_pos`：inertiaDeg_pos [hq : q.IsPrime] [Module.Finite R S
] : 0 < q.inertiaDeg R
· 使用定理 `Ideal.inertiaDeg_above_dvd`：inertiaDeg_above_dvd [r.LiesOver q] : r.iner
tiaDeg S ∣ r.inertiaDeg R
-/
theorem inertiaDeg_above_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] :
    r.inertiaDeg S ≤ r.inertiaDeg R :=
  Nat.le_of_dvd (r.inertiaDeg_pos R) (q.inertiaDeg_above_dvd r)

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_above_le := inertiaDeg_above_le

variable (R) in
open Pointwise in
@[simp]
/-
**Ideal.inertiaDeg_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_smul {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommCla
ss G R S] (g : G) : (g • q).inertiaDeg R = q.inertiaDeg R
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.IsPrime.smul`：∀ {M : Type u_1} {R : Type u_3} [inst : Group M] [in
st_1 : Semiring R] [inst_2 : MulSemiringAction M R] {I : Ideal R}   [H : I.IsPri
me] (g :…
· 使用定理 `Ideal.LiesOver.smul`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] {P : Ideal B}   {p : Ideal A} 
{G : Type…
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg_eq`：inertiaDeg_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime
] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)] [Localization.AtPr
ime.IsLie…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Ideal.comap_symm`：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.sym
m = I.map f
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Ideal.inertiaDeg_of_not_isPrime`：inertiaDeg_of_not_isPrime (hq : ¬ q.IsP
rime) : q.inertiaDeg R = 0
-/
theorem inertiaDeg_smul {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (g : G) : (g • q).inertiaDeg R = q.inertiaDeg R := by
  by_cases hq : q.IsPrime; swap
  · rw [inertiaDeg_of_not_isPrime, inertiaDeg_of_not_isPrime] <;> simpa
  · let p := q.under R
    let f₀ := MulSemiringAction.toAlgAut G R S g
    let := Localization.AtPrime.algebraOfLiesOver p q
    let := Localization.AtPrime.algebraOfLiesOver p (g • q)
    rw [inertiaDeg_eq p q, inertiaDeg_eq p (g • q)]
    let e₂ := Ideal.residueFieldAlgEquiv' p (g • q) q f₀.symm (comap_symm f₀.toRingEquiv).symm
    exact e₂.toLinearEquiv.finrank_eq

@[deprecated (since := "2026-07-03")] alias inertiaDeg'_smul := inertiaDeg_smul
/-
**Ideal.cardQuot_pow_inertiaDeg** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：cardQuot_pow_inertiaDeg [Module.Finite R S] [p.IsMaximal] [q.IsMaximal] [q
.LiesOver p] : p.cardQuot ^ q.inertiaDeg R = q.cardQuot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.inertiaDeg'_eq_inertiaDeg`：∀ {R : Type u_1} {S : Type u_2} [inst :
 CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   (q : I
deal S) [q.LiesOver p…
· 使用定理 `Ideal.inertiaDeg'_algebraMap`：∀ {R : Type u} [inst : CommRing R] {S : Ty
pe v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)  
 [inst_3 : P.LiesO…
· 使用定理 `Module.natCard_eq_pow_finrank`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [Module.Fini
te K V], Nat.card V…
-/
theorem cardQuot_pow_inertiaDeg [Module.Finite R S] [p.IsMaximal] [q.IsMaximal] [q.LiesOver p] :
    p.cardQuot ^ q.inertiaDeg R = q.cardQuot := by
  let _ : Field (R ⧸ p) := Quotient.field p
  rw [← inertiaDeg'_eq_inertiaDeg p q, inertiaDeg'_algebraMap p q]
  exact Module.natCard_eq_pow_finrank.symm

@[deprecated (since := "2026-07-03")] alias cardQuot_pow_inertiaDeg' := cardQuot_pow_inertiaDeg
/-
**Ideal.absNorm_pow_inertiaDeg** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_pow_inertiaDeg [Module.Finite R S] [q.IsPrime] [q.LiesOver p] [IsD
edekindDomain R] [IsDedekindDomain S] [Module.Free Int R] [Module.Free Int S] : 
p.absNorm ^ q.inertiaDeg R = q.absNorm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.absNorm_bot`：absNorm_bot : absNorm (⊥ : Ideal S) = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ideal.eq_bot_of_liesOver_bot`：eq_bot_of_liesOver_bot [Nontrivial A] [IsD
omain B] [h : P.LiesOver (⊥ : Ideal A)] : P = ⊥
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ideal.inertiaDeg_pos`：inertiaDeg_pos [hq : q.IsPrime] [Module.Finite R S
] : 0 < q.inertiaDeg R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.isPrime_of_liesOver`：isPrime_of_liesOver [P.LiesOver p] [P.IsPrime
] : p.IsPrime
· 使用引理 `Ideal.isMaximal_of_isPrime_of_ne_bot`：Ideal.isMaximal_of_isPrime_of_ne_b
ot [NoZeroDivisors R] [Ring.KrullDimLE 1 R] (I : Ideal R) [I.IsPrime] (hI' : I !
= ⊥) : I.IsMaximal
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ring.DimensionLEOne.instKrullDimLEOfNatNat`：∀ {R : Type u_4} [inst : Com
mRing R] [Ring.DimensionLEOne R], Ring.KrullDimLE 1 R
· 使用定理 `Ideal.IsMaximal.of_liesOver_isMaximal`：∀ {A : Type u_1} [inst : CommRing
 A] {B : Type u_2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsInt
egral A B] (P : Ideal B) (p…
· 使用定理 `Ideal.cardQuot_pow_inertiaDeg`：cardQuot_pow_inertiaDeg [Module.Finite R 
S] [p.IsMaximal] [q.IsMaximal] [q.LiesOver p] : p.cardQuot ^ q.inertiaDeg R = q.
cardQuot
-/
theorem absNorm_pow_inertiaDeg [Module.Finite R S] [q.IsPrime] [q.LiesOver p]
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Free ℤ R] [Module.Free ℤ S] :
    p.absNorm ^ q.inertiaDeg R = q.absNorm := by
  by_cases hp : p = ⊥
  · subst hp
    simpa [eq_bot_of_liesOver_bot R q] using (inertiaDeg_pos q R).ne'
  have := isPrime_of_liesOver q p
  have := isMaximal_of_isPrime_of_ne_bot p hp
  have := IsMaximal.of_liesOver_isMaximal q p
  exact cardQuot_pow_inertiaDeg p q

@[deprecated (since := "2026-07-03")] alias absNorm_pow_inertiaDeg' := absNorm_pow_inertiaDeg
/-
**Ideal.natAbs_pow_inertiaDeg** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：natAbs_pow_inertiaDeg [IsDedekindDomain R] [Module.Free Int R] [Module.Fin
ite Int R] (p : Int) (P : Ideal R) [P.IsPrime] [P.LiesOver (span {p})] : p.natAb
s ^ P.inertiaDeg Int = absNorm P
参数：p : Int；P : Ideal R；span {p}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `AddGroup.instFGInt`：AddGroup.FG ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `Algebra.norm_self`：norm_self : Algebra.norm R = MonoidHom.id R
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `Ideal.absNorm_pow_inertiaDeg`：absNorm_pow_inertiaDeg [Module.Finite R S]
 [q.IsPrime] [q.LiesOver p] [IsDedekindDomain R] [IsDedekindDomain S] [Module.Fr
ee Int R] [Module.…
-/
theorem natAbs_pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] (p : ℤ)
    (P : Ideal R) [P.IsPrime] [P.LiesOver (span {p})] :
    p.natAbs ^ P.inertiaDeg ℤ = absNorm P := by
  simpa using absNorm_pow_inertiaDeg (span {p}) P

@[deprecated (since := "2026-07-03")] alias natAbs_pow_inertiaDeg' := natAbs_pow_inertiaDeg
/-
**Ideal.pow_inertiaDeg** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pow_inertiaDeg [IsDedekindDomain R] [Module.Free Int R] [Module.Finite Int
 R] (p : Nat) (P : Ideal R) [P.IsPrime] [P.LiesOver (span {(p : Int)})] : p ^ P.
inertiaDeg Int = absNorm P
参数：p : Nat；P : Ideal R；span {(p : Int)}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.natAbs_pow_inertiaDeg`：natAbs_pow_inertiaDeg [IsDedekindDomain R] 
[Module.Free Int R] [Module.Finite Int R] (p : Int) (P : Ideal R) [P.IsPrime] [P
.LiesOver (span {…
-/
theorem pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] (p : ℕ)
    (P : Ideal R) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    p ^ P.inertiaDeg ℤ = absNorm P :=
  natAbs_pow_inertiaDeg p P

end

end Ideal

