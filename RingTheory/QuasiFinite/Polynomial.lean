/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
public import Mathlib.RingTheory.QuasiFinite.Weakly

/-! # Quasi-finite primes in polynomial algebras -/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

namespace Polynomial

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.WeaklyQuasiFiniteAt.finite_locoalization in
/-
**Polynomial.not_weaklyQuasiFiniteAt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：not_weaklyQuasiFiniteAt (P : Ideal R[X]) [P.IsPrime] : ¬ Algebra.WeaklyQua
siFiniteAt R P
参数：P : Ideal R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Module.Finite.of_injective`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_
3} {N : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommM
onoid M] [inst_3…
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用引理 `Algebra.WeaklyQuasiFiniteAt.finite_locoalization`：finite_locoalization {
K : Type*} [Field K] [Algebra K S] [WeaklyQuasiFiniteAt K q] : Module.Finite K (
Localization.AtPrime q)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.transcendental_X`：Polynomial.transcendental_X : Transcendenta
l R (X (R
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Algebra.WeaklyQuasiFiniteAt.baseChange`：baseChange (p : Ideal S) [p.IsPr
ime] [WeaklyQuasiFiniteAt R p] {A : Type*} [CommRing A] [Algebra R A] (q : Ideal
 (A otimes[R] S)) [q.IsPrime…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
-/
lemma not_weaklyQuasiFiniteAt (P : Ideal R[X]) [P.IsPrime] : ¬ Algebra.WeaklyQuasiFiniteAt R P := by
  intro H
  wlog hR : IsField R
  · let p := P.under R
    obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber R R[X]
        ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, rfl⟩
    have inst : Algebra.WeaklyQuasiFiniteAt p.ResidueField Q.asIdeal :=
      .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
    exact this (Q.asIdeal.comap (polyEquivTensor' R p.ResidueField).toRingHom)
      inferInstance (Field.toIsField _)
  let := hR.toField
  have := Module.Finite.of_injective
    (IsScalarTower.toAlgHom R R[X] (Localization.AtPrime P)).toLinearMap
    (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors)
  exact transcendental_X R (Algebra.IsIntegral.isIntegral X).isAlgebraic

/-- `R[X]` is not quasi-finite over `R` at any prime. -/
/-
**Polynomial.not_quasiFiniteAt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：not_quasiFiniteAt (P : Ideal R[X]) [P.IsPrime] : ¬ Algebra.QuasiFiniteAt R
 P
参数：P : Ideal R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.not_weaklyQuasiFiniteAt`：not_weaklyQuasiFiniteAt (P : Ideal R
[X]) [P.IsPrime] : ¬ Algebra.WeaklyQuasiFiniteAt R P
· 使用定理 `Algebra.WeaklyQuasiFiniteAt.instOfQuasiFiniteAt`：∀ {R : Type u_1} {S : T
ype u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (q : I
deal S)   [inst_3 : q.IsPrime] [Algeb…

--- 原说明 ---
`R[X]` is not quasi-finite over `R` at any prime.
-/
lemma not_quasiFiniteAt (P : Ideal R[X]) [P.IsPrime] : ¬ Algebra.QuasiFiniteAt R P :=
  fun _ ↦ not_weaklyQuasiFiniteAt P inferInstance
/-
**Polynomial.map_under_lt_comap_of_weaklyQuasiFiniteAt** 是 Mathlib 中的一个引理，位于命名空间
 `Polynomial`。
形式化陈述：map_under_lt_comap_of_weaklyQuasiFiniteAt (f : R[X] ->ₐ[R] S) (P : Ideal S
) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] : (P.under R).map C < P.comap (f
 : R[X] ->+* S)
参数：f : R[X] ->ₐ[R] S；P : Ideal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.algebraMap_eq`：algebraMap_eq : algebraMap R R[X] = C
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用引理 `Algebra.WeaklyQuasiFiniteAt.finite_residueField`：finite_residueField [p.
IsPrime] [q.LiesOver p] [WeaklyQuasiFiniteAt R q] [Algebra (Localization.AtPrime
 p) (Localization.AtPrime q)] [Locali…
· 使用定理 `Module.Finite.of_injective`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_
3} {N : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommM
onoid M] [inst_3…
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower_1`：∀ {R : Type u_1} {S : Type
 u_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst
_3 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra_1`：∀ {A : Type
 u_4} {B : Type u_5} {C : Type u_6} [inst : CommSemiring A] [inst_1 : CommSemiri
ng B] [inst_2 : Algebra A B]   [inst_3 : CommSemi…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用引理 `RatFunc.transcendental_X`：transcendental_X : Transcendental K (X : K⟮X⟯)
（共 33 条，此处仅展示前 30 条）
-/
lemma map_under_lt_comap_of_weaklyQuasiFiniteAt
    (f : R[X] →ₐ[R] S) (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
    (P.under R).map C < P.comap (f : R[X] →+* S) := by
  algebraize [f.toRingHom]
  refine lt_of_le_of_ne (Ideal.map_le_iff_le_comap.mpr ?_) fun e ↦ ?_
  · rw [Ideal.comap_comap, ← algebraMap_eq, f.comp_algebraMap]
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) (P.under R[X])
  let := Localization.AtPrime.algebraOfLiesOver (P.under R[X]) P
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) P
  have : Module.Finite (Ideal.under R P).ResidueField P.ResidueField :=
    Algebra.WeaklyQuasiFiniteAt.finite_residueField ..
  have : Module.Finite (P.under R).ResidueField (P.under R[X]).ResidueField :=
    .of_injective (IsScalarTower.toAlgHom _ _ P.ResidueField).toLinearMap
      (algebraMap (P.under R[X]).ResidueField P.ResidueField).injective
  have : Module.Finite (P.under R).ResidueField (RatFunc (P.under R).ResidueField) :=
    .of_surjective (residueFieldMapCAlgEquiv _ (P.under _) e.symm).toLinearMap
      (residueFieldMapCAlgEquiv _ (P.under _) e.symm).surjective
  exact RatFunc.transcendental_X (K := (P.under R).ResidueField)
    (Algebra.IsIntegral.isIntegral _).isAlgebraic
/-
**Polynomial.map_under_lt_comap_of_quasiFiniteAt** 是 Mathlib 中的一个引理，位于命名空间 `Poly
nomial`。
形式化陈述：map_under_lt_comap_of_quasiFiniteAt (f : R[X] ->ₐ[R] S) (P : Ideal S) [P.I
sPrime] [Algebra.QuasiFiniteAt R P] : (P.under R).map C < P.comap (f : R[X] ->+*
 S)
参数：f : R[X] ->ₐ[R] S；P : Ideal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.map_under_lt_comap_of_weaklyQuasiFiniteAt`：map_under_lt_comap
_of_weaklyQuasiFiniteAt (f : R[X] ->ₐ[R] S) (P : Ideal S) [P.IsPrime] [Algebra.W
eaklyQuasiFiniteAt R P] : (P.under R).map …
· 使用定理 `Algebra.WeaklyQuasiFiniteAt.instOfQuasiFiniteAt`：∀ {R : Type u_1} {S : T
ype u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (q : I
deal S)   [inst_3 : q.IsPrime] [Algeb…
-/
lemma map_under_lt_comap_of_quasiFiniteAt
    (f : R[X] →ₐ[R] S) (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    (P.under R).map C < P.comap (f : R[X] →+* S) :=
  map_under_lt_comap_of_weaklyQuasiFiniteAt f P
/-
**Polynomial.not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt** 是 Mathlib 中
的一个引理，位于命名空间 `Polynomial`。
形式化陈述：not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt (f : R[X] ->ₐ[R] S) 
(hf : Function.Surjective f) (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFinit
eAt R P] : ¬ RingHom.ker f <= (P.under R).map C
参数：f : R[X] ->ₐ[R] S；hf : Function.Surjective f；P : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.instIsTwoSidedBot`：∀ {α : Type u} [inst : Semiring α], ⊥.IsTwoSide
d
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用引理 `Algebra.WeaklyQuasiFiniteAt.baseChange`：baseChange (p : Ideal S) [p.IsPr
ime] [WeaklyQuasiFiniteAt R p] {A : Type*} [CommRing A] [Algebra R A] (q : Ideal
 (A otimes[R] S)) [q.IsPrime…
· 使用引理 `Polynomial.not_weaklyQuasiFiniteAt`：not_weaklyQuasiFiniteAt (P : Ideal R
[X]) [P.IsPrime] : ¬ Algebra.WeaklyQuasiFiniteAt R P
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
-/
lemma not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt
    (f : R[X] →ₐ[R] S) (hf : Function.Surjective f)
    (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
    ¬ RingHom.ker f ≤ (P.under R).map C := by
  intro H
  algebraize [f.toRingHom]
  let p := P.under R
  have H' : (RingHom.ker f).map (mapRingHom (algebraMap R p.ResidueField)) = ⊥ := by
    rw [← le_bot_iff, Ideal.map_le_iff_le_comap]
    intro x hx
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using! H hx
  let g' : p.ResidueField[X] ≃ₐ[p.ResidueField] p.Fiber S :=
    .trans ((AlgEquiv.quotientBot _ _).symm.trans (Ideal.quotientEquivAlgOfEq _ H'.symm))
      (Polynomial.fiberEquivQuotient f hf _).symm
  obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber _ _
      ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, PrimeSpectrum.ext (P.over_def p).symm⟩
  have inst : Algebra.WeaklyQuasiFiniteAt p.ResidueField Q.asIdeal :=
    .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
  exact Polynomial.not_weaklyQuasiFiniteAt (Q.asIdeal.comap g'.toRingHom) inferInstance

/--
If `P` is a prime of `R[X]/I` that is quasi finite over `R`,
then `I` is not contained in `(P ∩ R)[X]`.

For usability, we replace `I` by the kernel of a surjective map `R[X] →ₐ[R] S`. -/
/-
**Polynomial.not_ker_le_map_C_of_surjective_of_quasiFiniteAt** 是 Mathlib 中的一个引理，
位于命名空间 `Polynomial`。
形式化陈述：not_ker_le_map_C_of_surjective_of_quasiFiniteAt (f : R[X] ->ₐ[R] S) (hf : 
Function.Surjective f) (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] : ¬
 RingHom.ker f <= (P.under R).map C
参数：f : R[X] ->ₐ[R] S；hf : Function.Surjective f；P : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt`：not_ke
r_le_map_C_of_surjective_of_weaklyQuasiFiniteAt (f : R[X] ->ₐ[R] S) (hf : Functi
on.Surjective f) (P : Ideal S) [P.IsPrime] [Algebra.We…
· 使用定理 `Algebra.WeaklyQuasiFiniteAt.instOfQuasiFiniteAt`：∀ {R : Type u_1} {S : T
ype u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (q : I
deal S)   [inst_3 : q.IsPrime] [Algeb…

--- 原说明 ---
If `P` is a prime of `R[X]/I` that is quasi finite over `R`,
then `I` is not contained in `(P ∩ R)[X]`.

For usability, we replace `I` by the kernel of a surjective map `R[X] →ₐ[R] S`.
-/
lemma not_ker_le_map_C_of_surjective_of_quasiFiniteAt
    (f : R[X] →ₐ[R] S) (hf : Function.Surjective f)
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    ¬ RingHom.ker f ≤ (P.under R).map C :=
  not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt f hf P

end Polynomial

