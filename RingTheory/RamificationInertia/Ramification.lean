/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Ramification index

Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying over a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the image of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the quotient `Sq/pSq` as
an `Sq`-module.

## Main definitions

* `Ideal.ramificationIdx q R`: The ramification index of `q` over `R`.

## Main statements

* `ramificationIdx'_eq_ramificationIdx`: The ramification index agrees with the usual definition in
  the case of Dedekind domains.
* `ramificationIdx_tower`: Ramification index is multiplicative in towers.

-/

@[expose] public section

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open scoped Classical in
/-- Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying over a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the image of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the quotient `Sq/pSq` as
an `Sq`-module.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.ramificationIdx'`. -/
/-
**Ideal.ramificationIdx** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying ov
er a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the im
age of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the q
uotient `Sq/pSq` as
an `Sq`-module.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.ramificationIdx'`
.
-/
noncomputable def ramificationIdx : ℕ :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0
/-
**Ideal.ramificationIdx_def** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_def [q.IsPrime] : letI Sq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem ramificationIdx_def [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx R = (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat :=
  dif_pos _

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_def := ramificationIdx_def
/-
**Ideal.ramificationIdx_of_not_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_of_not_isPrime (hq : ¬ q.IsPrime) : q.ramificationIdx R = 
0
参数：hq : ¬ q.IsPrime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem ramificationIdx_of_not_isPrime (hq : ¬ q.IsPrime) : q.ramificationIdx R = 0 :=
  dif_neg hq

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_of_not_isPrime :=
  ramificationIdx_of_not_isPrime
/-
**Ideal.ramificationIdx_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_pos [q.IsPrime] [Module.Finite R S] : 0 < q.ramificationId
x R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdx_def`：ramificationIdx_def [q.IsPrime] : letI Sq
· 使用定理 `ENat.toNat_pos`：toNat_pos (hn0 : n != 0) (hxt : n != ⊤) : 0 < n.toNat
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用引理 `Module.length_pos_iff`：Module.length_pos_iff : 0 < Module.length R M ↔ N
ontrivial M
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `Ideal.IsMaximal.lt_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I < ⊤
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply`：PrimeSpectrum.coe_
primesOverOrderIsoFiber_symm_apply (q : PrimeSpectrum (p.Fiber S)) : (primesOver
OrderIsoFiber R S p).symm q = q.1.comap Al…
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.instLiesOverFiberOfIsPrime`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [inst
_3 : p.IsPrime] (q : I…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 43 条，此处仅展示前 30 条）
-/
theorem ramificationIdx_pos [q.IsPrime] [Module.Finite R S] : 0 < q.ramificationIdx R := by
  let p := q.under R
  let Sq := Localization.AtPrime q
  rw [ramificationIdx_def]
  apply ENat.toNat_pos
  · rw [← pos_iff_ne_zero, Module.length_pos_iff, Submodule.Quotient.nontrivial_iff,
      IsScalarTower.algebraMap_eq R S, ← map_map, ← lt_top_iff_ne_top]
    grw [map_mono map_comap_le, Localization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).lt_top
  · let r := PrimeSpectrum.primesOverOrderIsoFiber R S p (primesOver.mk p q)
    have : q = r.1.comap Algebra.TensorProduct.includeRight := by
      rw [← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply, OrderIso.symm_apply_apply]
    let := Localization.AtPrime.algebraOfLiesOver p (r.1.comap Algebra.TensorProduct.includeRight)
    have : IsArtinianRing (Sq ⧸ map (algebraMap R Sq) p) := by
      convert (Fiber.localizationAlgEquivQuotient p r.1).toRingEquiv.isArtinianRing
    rwa [Module.length_eq_of_surjective (R := Sq ⧸ p.map (algebraMap R Sq)) Quotient.mk_surjective,
      Module.length_ne_top_iff, ← isArtinianRing_iff_isFiniteLength]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_pos := ramificationIdx_pos
/-
**Ideal.ramificationIdx_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_eq_one [q.IsPrime] [Algebra.EssFiniteType R S] [Algebra.Is
UnramifiedAt R q] : q.ramificationIdx R = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Algebra.EssFiniteType.of_comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type
 u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 
: Algebra R S] [ins…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Algebra.instEssFiniteTypeLocalization`：∀ (R : Type u_1) (S : Type u_2) [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssFi
niteType R S] (M : Submonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdx_def`：ramificationIdx_def [q.IsPrime] : letI Sq
· 使用定理 `ENat.toNat_eq_iff_eq_natCast`：∀ (n : ℕ∞) (m : ℕ) [NeZero m], n.toNat = m
 ↔ n = ↑m
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Module.length_eq_one_iff`：Module.length_eq_one_iff : Module.length R M =
 1 ↔ IsSimpleModule R M
· 使用定理 `isSimpleModule_iff_isCoatom`：isSimpleModule_iff_isCoatom : IsSimpleModul
e R (M ⧸ m) ↔ IsCoatom m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.isMaximal_def`：isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoato
m I
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `IsLocalRing.isMaximal_iff`：isMaximal_iff {I : Ideal R} : I.IsMaximal ↔ I
 = maximalIdeal R where mp hI
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `Algebra.FormallyUnramified.map_maximalIdeal`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [inst_3 
: IsLocalRing R] [inst_4 : IsLoca…
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Algebra.instFormallyUnramifiedAtPrimeOfIsUnramifiedAtOfIsLiesOverAlgebra
`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A] (p : Ideal R)   [inst_3 : p.IsPrime] (q : I…
-/
theorem ramificationIdx_eq_one [q.IsPrime] [Algebra.EssFiniteType R S]
    [Algebra.IsUnramifiedAt R q] : q.ramificationIdx R = 1 := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  rw [ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff,
    IsScalarTower.algebraMap_eq R Rp Sq, ← map_map, Localization.AtPrime.map_eq_maximalIdeal]
  exact Algebra.FormallyUnramified.map_maximalIdeal

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq_one := ramificationIdx_eq_one

variable {q R} in
/-
**Ideal.ramificationIdx_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_eq_one_iff [q.IsPrime] [Algebra.EssFiniteType R S] [Algebr
a.IsIntegral R S] [PerfectField (q.under R).ResidueField] : q.ramificationIdx R 
= 1 ↔ Algebra.IsUnramifiedAt R q
参数：q.under R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Algebra.EssFiniteType.of_comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type
 u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 
: Algebra R S] [ins…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Algebra.instEssFiniteTypeLocalization`：∀ (R : Type u_1) (S : Type u_2) [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssFi
niteType R S] (M : Submonoi…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`：∀ {R : Type u_1} {S 
: Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [
inst_3 : IsLocalRing R] [inst_4 : IsLoca…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `instIsAlgebraicResidueFieldOfIsIntegral`：∀ {A : Type u_2} {B : Type u_3}
 [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra A B] (p : Ideal A) 
  (q : Ideal B) [inst_3 : q.L…
· 使用定理 `IsLocalRing.isMaximal_iff`：isMaximal_iff {I : Ideal R} : I.IsMaximal ↔ I
 = maximalIdeal R where mp hI
· 使用定理 `Ideal.isMaximal_def`：isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoato
m I
· 使用定理 `isSimpleModule_iff_isCoatom`：isSimpleModule_iff_isCoatom : IsSimpleModul
e R (M ⧸ m) ↔ IsCoatom m
· 使用引理 `Module.length_eq_one_iff`：Module.length_eq_one_iff : Module.length R M =
 1 ↔ IsSimpleModule R M
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENat.toNat_eq_iff_eq_natCast`：∀ (n : ℕ∞) (m : ℕ) [NeZero m], n.toNat = m
 ↔ n = ↑m
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Ideal.ramificationIdx_def`：ramificationIdx_def [q.IsPrime] : letI Sq
· 使用定理 `Algebra.FormallyUnramified.comp`：comp [FormallyUnramified R A] [Formally
Unramified A B] : FormallyUnramified R B
· 使用定理 `Algebra.FormallyUnramified.instLocalization`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.FormallyUnramified R S] (M : Sub…
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.inst`：∀ {R : Type u} [inst : CommRing R], Algebra.Etale R 
R
· 使用定理 `Ideal.ramificationIdx_eq_one`：ramificationIdx_eq_one [q.IsPrime] [Algebr
a.EssFiniteType R S] [Algebra.IsUnramifiedAt R q] : q.ramificationIdx R = 1
-/
theorem ramificationIdx_eq_one_iff [q.IsPrime] [Algebra.EssFiniteType R S]
    [Algebra.IsIntegral R S] [PerfectField (q.under R).ResidueField] :
    q.ramificationIdx R = 1 ↔ Algebra.IsUnramifiedAt R q := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ramificationIdx_eq_one q R⟩
  rw [ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at h
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have := Algebra.EssFiniteType.of_comp R Rp Sq
  suffices Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq,
    ← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq]
  exact ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField, h⟩

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq_one_iff :=
  ramificationIdx_eq_one_iff

end

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) (r : Ideal T)

/-
**Ideal.ramificationIdx_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_eq [q.LiesOver p] [q.IsPrime] : letI Sq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdx_def`：ramificationIdx_def [q.IsPrime] : letI Sq
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
-/
theorem ramificationIdx_eq [q.LiesOver p] [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx R = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat := by
  rw [ramificationIdx_def, over_def q p]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq := ramificationIdx_eq

open Localization IsLocalization.AtPrime in
/-
**Ideal.ramificationIdx'_eq_ramificationIdx'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (p : Ideal R)   (q : Ideal S) [IsDedekindDomain S] [q.Lie
sOver p] [hq : q.IsPrime],   Ideal.map (algebraMap R S) p ≠ ⊥ → p.ramificationId
x' q = q.ramificationIdx R
参数：p : Ideal R；q : Ideal S；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `Ideal.map_le_of_le_comap`：map_le_of_le_comap : I <= K.comap f -> I.map f
 <= K
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.eq_prime_pow_mul_coprime`：eq_prime_pow_mul_coprime {I : Ideal T} (
hI : I != ⊥) (P : Ideal T) [hpm : P.IsMaximal] : exists Q : Ideal T, P ⊔ Q = ⊤ ∧
 I = P ^ (Multiset.c…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`：IsLoc
alization.AtPrime.isDiscreteValuationRing_of_dedekind_domain [IsDedekindDomain A
] {P : Ideal A} (hP : P != ⊥) [pP : P.IsPrime] (Aₘ : Ty…
· 使用定理 `Ideal.ramificationIdx_eq`：ramificationIdx_eq [q.LiesOver p] [q.IsPrime] 
: letI Sq
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `IsLocalization.AtPrime.map_eq_top_of_not_le`：map_eq_top_of_not_le {I : I
deal R} {p : Ideal R} [p.IsPrime] [IsLocalization.AtPrime S p] (hle : ¬ I <= p) 
: Ideal.map (algebraMap R S) I = …
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `Ideal.map_mul`：∀ {S : Type v} {F : Type u_1} [inst : CommSemiring S] {R 
: Type u_2} [inst_1 : Semiring R] [inst_2 : FunLike F R S]   [RingHomClass F R S
] (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count`：∀ {R
 : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Alge
bra R S] {p : Ideal R} {P : Ideal S}   [inst_3 : IsDedek…
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsDiscreteValuationRing.length_quotient_pow_maximalIdeal`：length_quotien
t_pow_maximalIdeal (n : Nat) : Module.length R (R ⧸ maximalIdeal R ^ n) = n
· 使用定理 `ENat.toNat_natCast`：toNat_natCast (n : Nat) : toNat n = n
-/
theorem ramificationIdx'_eq_ramificationIdx' [IsDedekindDomain S]
    [q.LiesOver p] [hq : q.IsPrime] (hpS : p.map (algebraMap R S) ≠ ⊥) :
    p.ramificationIdx' q = q.ramificationIdx R := by
  have hq' : q ≠ ⊥ := ne_bot_of_le_ne_bot hpS (map_le_of_le_comap (q.over_def p).le)
  have : q.IsMaximal := hq.isMaximal hq'
  obtain ⟨I, hqI, h⟩ := Ideal.eq_prime_pow_mul_coprime hpS q
  replace hqI : ¬ I ≤ q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact hq.ne_top
  rw [← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hpS hq hq'] at h
  apply_fun (map (algebraMap S (Localization.AtPrime q))) at h
  rw [map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_mul, Ideal.map_pow,
    map_eq_top_of_not_le (Localization.AtPrime q) hqI, mul_top, AtPrime.map_eq_maximalIdeal] at h
  have hSq := isDiscreteValuationRing_of_dedekind_domain S hq' (Localization.AtPrime q)
  rw [ramificationIdx_eq p q, h, hSq.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_ramificationIdx'' :=
  ramificationIdx'_eq_ramificationIdx'
/-
**Ideal.ramificationIdx'_eq_ramificationIdx** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (p : Ideal R)   (q : Ideal S) [IsDomain R] [IsDedekindDom
ain S] [Module.IsTorsionFree R S] [q.LiesOver p] [hq : q.IsPrime],   p ≠ ⊥ → p.r
amificationIdx' q = q.ramificationIdx R
参数：p : Ideal R；q : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_ne_bot_of_ne_bot`：map_ne_bot_of_ne_bot {R S : Type*} [CommSemi
ring R] [Semiring S] [Algebra R S] [FaithfulSMul R S] {I : Ideal R} (h : I != ⊥)
 : map (algebraM…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.ramificationIdx'_eq_ramificationIdx'`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal 
R)   (q : Ideal S) [IsDedekindDo…
-/
theorem ramificationIdx'_eq_ramificationIdx [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] [q.LiesOver p] [hq : q.IsPrime] (hp : p ≠ ⊥) :
    p.ramificationIdx' q = q.ramificationIdx R := by
  have hpS : p.map (algebraMap R S) ≠ ⊥ := map_ne_bot_of_ne_bot hp
  exact ramificationIdx'_eq_ramificationIdx' p q hpS

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_ramificationIdx' :=
  ramificationIdx'_eq_ramificationIdx

namespace IsDedekindDomain

open UniqueFactorizationMonoid

/-
**Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count** 是 Mathlib 中的一个定理，位于命
名空间 `Ideal.IsDedekindDomain`。
形式化陈述：ramificationIdx_eq_factors_count [IsDedekindDomain S] [q.LiesOver p] (hp0 
: p.map (algebraMap R S) != ⊥) : q.ramificationIdx R = (factors (p.map (algebraM
ap R S))).count q
参数：hp0 : p.map (algebraMap R S) != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `Ideal.map_le_of_le_comap`：map_le_of_le_comap : I <= K.comap f -> I.map f
 <= K
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.ramificationIdx'_eq_ramificationIdx'`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal 
R)   (q : Ideal S) [IsDedekindDo…
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_eq_factors_count`：∀ {R : Type u}
 [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {
p : Ideal R} {P : Ideal S}   [inst_3 : IsDedek…
· 使用定理 `Ideal.ramificationIdx_of_not_isPrime`：ramificationIdx_of_not_isPrime (hq
 : ¬ q.IsPrime) : q.ramificationIdx R = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Multiset.count_eq_zero`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Mul
tiset α} {a : α}, Multiset.count a s = 0 ↔ a ∉ s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `UniqueFactorizationMonoid.prime_of_factor`：prime_of_factor {a : α} (x : 
α) (hx : x in factors a) : Prime x
-/
theorem ramificationIdx_eq_factors_count [IsDedekindDomain S]
    [q.LiesOver p] (hp0 : p.map (algebraMap R S) ≠ ⊥) :
    q.ramificationIdx R = (factors (p.map (algebraMap R S))).count q := by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime q R hq, eq_comm, Multiset.count_eq_zero]
    contrapose! hq
    exact isPrime_of_prime (prime_of_factor q hq)
  have hq0 : q ≠ ⊥ := ne_bot_of_le_ne_bot hp0 (map_le_of_le_comap (q.over_def p).le)
  rw [← ramificationIdx'_eq_ramificationIdx' p q hp0, ramificationIdx'_eq_factors_count hp0 ‹_› hq0]

open UniqueFactorizationMonoid in
/-
**Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count** 是 Mathlib 
中的一个定理，位于命名空间 `Ideal.IsDedekindDomain`。
形式化陈述：ramificationIdx_eq_normalizedFactors_count [IsDedekindDomain S] [q.LiesOve
r p] (hp0 : p.map (algebraMap R S) != ⊥) : q.ramificationIdx R = (normalizedFact
ors (p.map (algebraMap R S))).count q
参数：hp0 : p.map (algebraMap R S) != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.factors_eq_normalizedFactors`：factors_eq_norma
lizedFactors {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M] [S
ubsingleton Mˣ] (x : M) : factors x = normal…
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count`：ramificationIdx
_eq_factors_count [IsDedekindDomain S] [q.LiesOver p] (hp0 : p.map (algebraMap R
 S) != ⊥) : q.ramificationIdx R = (factors (p…
-/
theorem ramificationIdx_eq_normalizedFactors_count [IsDedekindDomain S]
    [q.LiesOver p] (hp0 : p.map (algebraMap R S) ≠ ⊥) :
    q.ramificationIdx R = (normalizedFactors (p.map (algebraMap R S))).count q := by
  rw [← factors_eq_normalizedFactors, ← ramificationIdx_eq_factors_count p q hp0]

open UniqueFactorizationMonoid in
/-
**Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity** 是 Mathlib 中的一个定理，位于命名
空间 `Ideal.IsDedekindDomain`。
形式化陈述：ramificationIdx_eq_multiplicity [IsDedekindDomain S] [q.IsPrime] [q.LiesOv
er p] (hp : p.map (algebraMap R S) != ⊥) : q.ramificationIdx R = multiplicity q 
(p.map (algebraMap R S))
参数：hp : p.map (algebraMap R S) != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `Ideal.map_le_of_le_comap`：map_le_of_le_comap : I <= K.comap f -> I.map f
 <= K
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count`：ramif
icationIdx_eq_normalizedFactors_count [IsDedekindDomain S] [q.LiesOver p] (hp0 :
 p.map (algebraMap R S) != ⊥) : q.ramificationIdx R = (…
· 使用定理 `multiplicity_eq_of_emultiplicity_eq_some`：multiplicity_eq_of_emultiplici
ty_eq_some {n : Nat} (h : emultiplicity a b = n) : multiplicity a b = n
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
-/
theorem ramificationIdx_eq_multiplicity [IsDedekindDomain S]
    [q.IsPrime] [q.LiesOver p] (hp : p.map (algebraMap R S) ≠ ⊥) :
    q.ramificationIdx R = multiplicity q (p.map (algebraMap R S)) := by
  have hq : q ≠ ⊥ := ne_bot_of_le_ne_bot hp (map_le_of_le_comap (q.over_def p).le)
  rw [ramificationIdx_eq_normalizedFactors_count p q hp,
    multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_count_normalizedFactors
      (prime_of_isPrime hq inferInstance).irreducible hp), normalize_eq]

end IsDedekindDomain

/-- See `ramificationIdx_tower` for a version that does not assume primality. -/
/-
**Ideal.ramificationIdx_tower'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_tower' [q.IsPrime] [r.IsPrime] [r.LiesOver q] [Algebra (Lo
calization.AtPrime q) (Localization.AtPrime r)] [Localization.AtPrime.IsLiesOver
Algebra q r] [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] : r
.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S
参数：Localization.AtPrime q；Localization.AtPrime r；Localization.AtPrime q；Localiza
tion.AtPrime r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.tower_bot`：∀ {A : Type u_2} [inst : CommSemiring A] {B : 
Type u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst
_3 : Algebra A…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Ideal.ramificationIdx_def`：ramificationIdx_def [q.IsPrime] : letI Sq
· 使用定理 `Ideal.ramificationIdx_eq`：ramificationIdx_eq [q.LiesOver p] [q.IsPrime] 
: letI Sq
· 使用引理 `LinearEquiv.length_eq`：LinearEquiv.length_eq {N : Type*} [AddCommGroup N
] [Module R N] (e : M ≃ₗ[R] N) : Module.length R M = Module.length R N
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `IsLocalRing.length_baseChange`：IsLocalRing.length_baseChange : length B 
(B otimes[A] M) = length A M * length B (B ⧸ (maximalIdeal A).map (algebraMap A 
B))
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `ENat.toNat_mul`：∀ (a b : ℕ∞), (a * b).toNat = a.toNat * b.toNat
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…

--- 原说明 ---
See `ramificationIdx_tower` for a version that does not assume primality.
-/
theorem ramificationIdx_tower' [q.IsPrime] [r.IsPrime] [r.LiesOver q]
    [Algebra (Localization.AtPrime q) (Localization.AtPrime r)]
    [Localization.AtPrime.IsLiesOverAlgebra q r]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S := by
  have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
  let f := (Ideal.quotientEquivAlgOfEq (Localization.AtPrime r)
    (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime r)
        ((r.under R).map (algebraMap R (Localization.AtPrime q))))
  rw [ramificationIdx_def, ramificationIdx_eq (r.under R), ramificationIdx_eq q,
    f.toLinearEquiv.length_eq, IsLocalRing.length_baseChange, ENat.toNat_mul,
    ← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_tower' := ramificationIdx_tower'

/-- See `ramificationIdx_tower'` for a version that only assumes local flatness. -/
/-
**Ideal.ramificationIdx_tower** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_tower [r.LiesOver q] [Module.Flat S T] : r.ramificationIdx
 R = q.ramificationIdx R * r.ramificationIdx S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.isPrime_of_liesOver`：isPrime_of_liesOver [P.LiesOver p] [P.IsPrime
] : p.IsPrime
· 使用定理 `Ideal.ramificationIdx_tower'`：ramificationIdx_tower' [q.IsPrime] [r.IsPr
ime] [r.LiesOver q] [Algebra (Localization.AtPrime q) (Localization.AtPrime r)] 
[Localization.AtPr…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `instFlatAtPrimeOfIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u_5} [ins
t : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra A B] [Module.Flat A B]  
 (p : Ideal A) [inst_4 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdx_of_not_isPrime`：ramificationIdx_of_not_isPrime (hq
 : ¬ q.IsPrime) : q.ramificationIdx R = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
See `ramificationIdx_tower'` for a version that only assumes local flatness.
-/
theorem ramificationIdx_tower [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    let := Localization.AtPrime.algebraOfLiesOver q r
    apply ramificationIdx_tower'
  · rw [ramificationIdx_of_not_isPrime r R hr, ramificationIdx_of_not_isPrime r S hr, mul_zero]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_tower := ramificationIdx_tower
/-
**Ideal.ramificationIdx_below_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_below_dvd [r.LiesOver q] [Module.Flat S T] : q.ramificatio
nIdx R ∣ r.ramificationIdx R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.ramificationIdx_tower`：ramificationIdx_tower [r.LiesOver q] [Modul
e.Flat S T] : r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S
-/
theorem ramificationIdx_below_dvd [r.LiesOver q] [Module.Flat S T] :
    q.ramificationIdx R ∣ r.ramificationIdx R := by
  use r.ramificationIdx S
  rw [← ramificationIdx_tower]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_below_dvd := ramificationIdx_below_dvd
/-
**Ideal.ramificationIdx_above_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_above_dvd [r.LiesOver q] [Module.Flat S T] : r.ramificatio
nIdx S ∣ r.ramificationIdx R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.ramificationIdx_tower`：ramificationIdx_tower [r.LiesOver q] [Modul
e.Flat S T] : r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S
-/
theorem ramificationIdx_above_dvd [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx S ∣ r.ramificationIdx R := by
  use q.ramificationIdx R
  rw [mul_comm, ← ramificationIdx_tower]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_above_dvd := ramificationIdx_above_dvd
/-
**Ideal.ramificationIdx_below_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_below_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [M
odule.Flat S T] : q.ramificationIdx R <= r.ramificationIdx R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ideal.ramificationIdx_pos`：ramificationIdx_pos [q.IsPrime] [Module.Finit
e R S] : 0 < q.ramificationIdx R
· 使用定理 `Ideal.ramificationIdx_below_dvd`：ramificationIdx_below_dvd [r.LiesOver q
] [Module.Flat S T] : q.ramificationIdx R ∣ r.ramificationIdx R
-/
theorem ramificationIdx_below_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [Module.Flat S T] :
    q.ramificationIdx R ≤ r.ramificationIdx R :=
  Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_below_dvd r)

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_below_le :=
  ramificationIdx_below_le
/-
**Ideal.ramificationIdx_above_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_above_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [M
odule.Flat S T] : r.ramificationIdx S <= r.ramificationIdx R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ideal.ramificationIdx_pos`：ramificationIdx_pos [q.IsPrime] [Module.Finit
e R S] : 0 < q.ramificationIdx R
· 使用定理 `Ideal.ramificationIdx_above_dvd`：ramificationIdx_above_dvd [r.LiesOver q
] [Module.Flat S T] : r.ramificationIdx S ∣ r.ramificationIdx R
-/
theorem ramificationIdx_above_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [Module.Flat S T] :
    r.ramificationIdx S ≤ r.ramificationIdx R :=
  Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_above_dvd r)

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_above_le := ramificationIdx_above_le

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
open Pointwise in
@[simp]
/-
**Ideal.ramificationIdx_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_smul {G : Type*} [Group G] [MulSemiringAction G S] [SMulCo
mmClass G R S] (g : G) : (g • q).ramificationIdx R = q.ramificationIdx R
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.pointwise_smul_def`：pointwise_smul_def {a : M} (S : Ideal R) : a •
 S = S.map (MulSemiringAction.toRingHom _ _ a)
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `Ideal.comap_map_of_bijective`：comap_map_of_bijective : (I.map f).comap f
 = I
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用引理 `AlgEquiv.toAlgHom_toRingHom`：toAlgHom_toRingHom : ((e : A₁ ->ₐ[R] A₂) : 
A₁ ->+* A₂) = e
· 使用引理 `AlgEquiv.toAlgHom_ofBijective`：toAlgHom_ofBijective (f : A₁ ->ₐ[R] A₂) (
hf : Function.Bijective f) : (ofBijective f hf).toAlgHom = f
· 使用定理 `Algebra.toRingHom_ofId`：∀ {R : Type u} (A : Type v) [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   ↑(Algebra.ofId R A) = algebr
aMap R A
· 使用定理 `Ideal.ramificationIdx_eq`：ramificationIdx_eq [q.LiesOver p] [q.IsPrime] 
: letI Sq
· 使用引理 `LinearEquiv.length_eq`：LinearEquiv.length_eq {N : Type*} [AddCommGroup N
] [Module R N] (e : M ≃ₗ[R] N) : Module.length R M = Module.length R N
· 使用定理 `Module.length_eq_of_surjective`：Module.length_eq_of_surjective {S : Type
*} [CommRing S] [Algebra S R] [Module S M] [IsScalarTower S R M] (h : Function.S
urjective (algebraMa…
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Ideal.ramificationIdx_of_not_isPrime`：ramificationIdx_of_not_isPrime (hq
 : ¬ q.IsPrime) : q.ramificationIdx R = 0
-/
theorem ramificationIdx_smul {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (g : G) : (g • q).ramificationIdx R = q.ramificationIdx R := by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime, ramificationIdx_of_not_isPrime] <;> simpa
  · let p := q.under R
    let f₀ := MulSemiringAction.toAlgAut G R S g
    have hg : g • q = q.map f₀ := q.pointwise_smul_def
    let Sq := Localization.AtPrime q
    let Sq' := Localization.AtPrime (q.map f₀)
    let f : Sq ≃ₐ[R] Sq' :=
      Localization.localAlgEquiv q (q.map f₀) f₀ (comap_map_of_bijective f₀ f₀.bijective).symm
    let : Algebra Sq Sq' := f.toRingHom.toAlgebra
    have : IsScalarTower R Sq Sq' := IsScalarTower.of_algHom f.toAlgHom
    let e : (Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Sq] Sq' ⧸ p.map (algebraMap R Sq') :=
      Ideal.quotientEquivAlg _ _ (AlgEquiv.ofBijective (Algebra.ofId Sq Sq') f.bijective)
        (by rw [IsScalarTower.algebraMap_eq R Sq Sq', Ideal.map_map,
          ← AlgEquiv.toAlgHom_toRingHom, AlgEquiv.toAlgHom_ofBijective, Algebra.toRingHom_ofId])
    rw [hg, ramificationIdx_eq p q, ramificationIdx_eq p (q.map f₀),
      e.toLinearEquiv.length_eq, Module.length_eq_of_surjective f.surjective]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_smul := ramificationIdx_smul

end

end Ideal

