/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!

# Unramified and ramification index

We connect `Ideal.ramificationIdx` to the commutative algebra notion predicate of `IsUnramifiedAt`.

## Main result
- `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`:
  Let `R` be a domain of characteristic 0, finite rank over `ℤ`, `S ⊇ R` be a Dedekind domain
  that is a finite `R`-algebra. Let `p` be a prime of `S`, then `p` is unramified iff `e(p) = 1`.

-/

public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

local notation3 "e(" P "|" R ")" =>
  Ideal.ramificationIdx P R

open IsLocalRing Algebra

/-
**Ideal.ramificationIdx_eq_one_of_isUnramifiedAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.ramificationIdx_eq_one_of_isUnramifiedAt {p : Ideal S} [p.IsPrime] [
IsUnramifiedAt R p] [EssFiniteType R S] : e(p|R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ramificationIdx_eq_one`：ramificationIdx_eq_one [q.IsPrime] [Algebr
a.EssFiniteType R S] [Algebra.IsUnramifiedAt R q] : q.ramificationIdx R = 1
-/
lemma Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    {p : Ideal S} [p.IsPrime] [IsUnramifiedAt R p] [EssFiniteType R S] :
    e(p|R) = 1 :=
  p.ramificationIdx_eq_one R

variable (R) in
/-
**IsUnramifiedAt.of_liesOver_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnramifiedAt.of_liesOver_of_ne_bot (p : Ideal S) (P : Ideal T) [P.LiesOv
er p] [p.IsPrime] [P.IsPrime] [IsUnramifiedAt R P] [EssFiniteType R S] [EssFinit
eType R T] [IsDedekindDomain S] (hP₁ : P.primeCompl <= nonZeroDivisors T) (hP₂ :
 p != ⊥ -> P != ⊥) : IsUnramifiedAt R p
参数：p : Ideal S；P : Ideal T；hP₁ : P.primeCompl <= nonZeroDivisors T；hP₂ : p != ⊥ 
-> P != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.trans`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type
 u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 :
 Algebra A…
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `Algebra.EssFiniteType.of_comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type
 u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 
: Algebra R S] [ins…
· 使用定理 `Algebra.EssFiniteType.isNoetherianRing`：∀ (R : Type u_3) (S : Type u_4) 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssF
initeType R S] [IsNoetherian…
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.isUnramifiedAt_iff_map_eq`：isUnramifiedAt_iff_map_eq : Algebra.I
sUnramifiedAt R q ↔ Algebra.IsSeparable p.ResidueField q.ResidueField ∧ p.map (a
lgebraMap R (Localizati…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.isSeparable_tower_bot_of_isSeparable`：Algebra.isSeparable_tower_
bot_of_isSeparable [h : Algebra.IsSeparable F E] : Algebra.IsSeparable F K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower_1`：∀ {R : Type u_1} {S : Type
 u_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst
_3 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra_1`：∀ {A : Type
 u_4} {B : Type u_5} {C : Type u_6} [inst : CommSemiring A] [inst_1 : CommSemiri
ng B] [inst_2 : Algebra A B]   [inst_3 : CommSemi…
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff`：∀ {R : Type u} [inst
 : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] [IsDede
kindDomain S]   {p : Ideal R} {P : Ideal…
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Ideal.ramificationIdx'_ne_one_iff`：∀ {R : Type u} [inst : CommRing R] {S
 : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal R}   {P : Ide
al S}, Ideal.map (algeb…
· 使用定理 `Ideal.ramificationIdx'_eq_one_of_map_localization`：∀ {R : Type u} [inst 
: CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ide
al R} {P : Ideal S}   [inst_3 : P.IsPri…
（共 37 条，此处仅展示前 30 条）
-/
lemma IsUnramifiedAt.of_liesOver_of_ne_bot
    (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R P] [EssFiniteType R S] [EssFiniteType R T]
    [IsDedekindDomain S] (hP₁ : P.primeCompl ≤ nonZeroDivisors T) (hP₂ : p ≠ ⊥ → P ≠ ⊥) :
    IsUnramifiedAt R p := by
  let p₀ : Ideal R := p.under R
  have : P.LiesOver p₀ := .trans P p p₀
  let := Localization.AtPrime.algebraOfLiesOver p₀ p
  let := Localization.AtPrime.algebraOfLiesOver p P
  let := Localization.AtPrime.algebraOfLiesOver p₀ P
  have hp₀ : p₀ = P.under R := Ideal.LiesOver.over
  have : EssFiniteType S T := .of_comp R S T
  have := Algebra.EssFiniteType.isNoetherianRing S T
  rw [isUnramifiedAt_iff_map_eq R p₀ p]
  have ⟨h₁, h₂⟩ := (isUnramifiedAt_iff_map_eq R p₀ P).mp ‹_›
  refine ⟨Algebra.isSeparable_tower_bot_of_isSeparable _ _ P.ResidueField, ?_⟩
  by_cases hp : p = ⊥
  · have : p₀.map (algebraMap R S) = p := by
      subst hp
      exact le_bot_iff.mp (Ideal.map_comap_le)
    rw [IsScalarTower.algebraMap_eq _ S, ← Ideal.map_map, this,
      Localization.AtPrime.map_eq_maximalIdeal]
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hp Ideal.map_comap_le,
    ← not_ne_iff, Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le]
  intro H
  have := Ideal.ramificationIdx'_eq_one_of_map_localization
    (hp₀ ▸ Ideal.map_comap_le) (hP₂ hp) hP₁ h₂
  rw [← not_ne_iff, Ideal.ramificationIdx'_ne_one_iff (hp₀ ▸ Ideal.map_comap_le)] at this
  replace H := Ideal.map_mono (f := algebraMap S T) H
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_pow] at H
  refine this (H.trans (Ideal.pow_right_mono ?_ _))
  exact Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le

section IsUnramifiedIn

namespace Algebra

variable (R) in
/--
Up to technical conditions, If `T/S/R` is a tower of algebras, `P` is a prime of `T` unramified
in `R`, then `P ∩ S` (as a prime of `S`) is also unramified in `R`.
-/
/-
**Algebra.IsUnramifiedAt.of_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsUnrami
fiedAt`。
形式化陈述：∀ (R : Type u_1) {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
S T] [inst_5 : Algebra R T] [IsScalarTower R S T] (p : Ideal S) (P : Ideal T)   
[P.LiesOver p] [inst_8 : p.IsPrime] [inst_9 : P.IsPrime] [Algebra.IsUnramifiedAt
 R P] [Algebra.EssFiniteType R S]   [Algebra.EssFiniteType R T] [IsDedekindDomai
n S] [IsDomain T] [Module.IsTorsionFree S T], Algebra.IsUnramifiedAt R p
参数：R : Type u_1；p : Ideal S；P : Ideal T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnramifiedAt.of_liesOver_of_ne_bot`：IsUnramifiedAt.of_liesOver_of_ne_b
ot (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime] [IsUnramif
iedAt R P] [EssFiniteType …
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ideal.ne_bot_of_liesOver_of_ne_bot`：ne_bot_of_liesOver_of_ne_bot (hp : p
 != ⊥) (P : Ideal B) [P.LiesOver p] : P != ⊥
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
Up to technical conditions, If `T/S/R` is a tower of algebras, `P` is a prime of
 `T` unramified
in `R`, then `P ∩ S` (as a prime of `S`) is also unramified in `R`.
-/
lemma IsUnramifiedAt.of_liesOver
    (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R P] [EssFiniteType R S] [EssFiniteType R T]
    [IsDedekindDomain S] [IsDomain T] [Module.IsTorsionFree S T] : IsUnramifiedAt R p :=
  IsUnramifiedAt.of_liesOver_of_ne_bot R p P P.primeCompl_le_nonZeroDivisors
    (Ideal.ne_bot_of_liesOver_of_ne_bot · P)


/-- Let `R` be a domain of characteristic 0, finite rank over `ℤ`, `S` be a Dedekind domain
that is a finite `R`-algebra. Let `p` be a prime of `S`, then `p` is unramified iff `e(p) = 1`. -/
@[deprecated "Use `Ideal.ramificationIdx'_eq_one_iff` instead." (since := "2026-06-30")]
/-
**Algebra.isUnramifiedAt_iff_of_isDedekindDomain** 是 Mathlib 中的一个引理，位于命名空间 `Alge
bra`。
形式化陈述：isUnramifiedAt_iff_of_isDedekindDomain {p : Ideal S} [p.IsPrime] [EssFinit
eType R S] [IsDomain R] [Module.Finite Int R] [CharZero R] [Algebra.IsIntegral R
 S] : Algebra.IsUnramifiedAt R p ↔ e(p|R) = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ideal.ramificationIdx'_eq_one_iff`：∀ {S : Type u_1} [inst : CommRing S] 
{q : Ideal S} {R : Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra R S]   [ins
t_3 : q.IsPrime] [Algeb…
· 使用定理 `Ring.HasFiniteQuotients.instPerfectFieldResidueFieldOfFractionRing`：∀ {R
 : Type u_1} [inst : CommRing R] [Ring.HasFiniteQuotients R] [inst_2 : IsDomain 
R] [PerfectField (FractionRing R)]   (P : Ideal R) [inst…
· 使用定理 `Ring.HasFiniteQuotients.instOfIsDomainOfFiniteInt`：∀ {R : Type u_1} [ins
t : CommRing R] [IsDomain R] [Module.Finite ℤ R], Ring.HasFiniteQuotients R
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…

--- 原说明 ---
Let `R` be a domain of characteristic 0, finite rank over `ℤ`, `S` be a Dedekind
 domain
that is a finite `R`-algebra. Let `p` be a prime of `S`, then `p` is unramified 
iff `e(p) = 1`.
-/
lemma isUnramifiedAt_iff_of_isDedekindDomain
    {p : Ideal S} [p.IsPrime] [EssFiniteType R S] [IsDomain R]
    [Module.Finite ℤ R] [CharZero R] [Algebra.IsIntegral R S] :
    Algebra.IsUnramifiedAt R p ↔ e(p|R) = 1 :=
  Ideal.ramificationIdx'_eq_one_iff.symm

/-- In characteristic zero the generic point is unramified: if `S` is a domain that is integral
over a characteristic-zero domain `R` and `R → S` is injective, then `S` is unramified at the zero
ideal. -/
/-
**Algebra.isUnramifiedAt_bot** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：isUnramifiedAt_bot [IsDomain R] [IsDomain S] [Module.IsTorsionFree R S] [C
harZero R] [Algebra.IsIntegral R S] : IsUnramifiedAt R (⊥ : Ideal S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.primeCompl_bot`：primeCompl_bot [Nontrivial α] [NoZeroDivisors α] :
 (⊥ : Ideal α).primeCompl = nonZeroDivisors α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `isAlgebraic_of_isFractionRing`：isAlgebraic_of_isFractionRing (R S K L) [
CommRing R] [CommRing S] [Field K] [CommRing L] [Algebra R S] [Algebra R K] [Alg
ebra R L] [Algebra …
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `Algebra.FormallyUnramified.of_isSeparable`：of_isSeparable [Algebra.IsSep
arable K L] : FormallyUnramified K L
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

--- 原说明 ---
In characteristic zero the generic point is unramified: if `S` is a domain that 
is integral
over a characteristic-zero domain `R` and `R → S` is injective, then `S` is unra
mified at the zero
ideal.
-/
theorem isUnramifiedAt_bot [IsDomain R] [IsDomain S] [Module.IsTorsionFree R S] [CharZero R]
    [Algebra.IsIntegral R S] : IsUnramifiedAt R (⊥ : Ideal S) := by
  have : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal S).primeCompl)
  let : Field (Localization.AtPrime (⊥ : Ideal S)) := IsFractionRing.toField S
  have : FaithfulSMul R (Localization.AtPrime (⊥ : Ideal S)) := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq R S (Localization.AtPrime ⊥)]
    exact (IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective R S)
  let := FractionRing.liftAlgebra R (Localization.AtPrime (⊥ : Ideal S))
  have : Algebra.IsAlgebraic (FractionRing R) (Localization.AtPrime ⊥) :=
    isAlgebraic_of_isFractionRing R S (FractionRing R) (Localization.AtPrime (⊥ : Ideal S))
  have : FormallyUnramified (FractionRing R) (Localization.AtPrime (⊥ : Ideal S)) :=
    FormallyUnramified.of_isSeparable _ _
  exact FormallyUnramified.comp R (FractionRing R) (Localization.AtPrime ⊥)

/-- In characteristic zero, the zero ideal is unramified in an integral domain extension. -/
/-
**Algebra.isUnramifiedIn_bot** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：isUnramifiedIn_bot [IsDomain R] [IsDomain S] [FaithfulSMul R S] [CharZero 
R] [Algebra.IsIntegral R S] : IsUnramifiedIn S (⊥ : Ideal R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.eq_bot_of_liesOver_bot`：eq_bot_of_liesOver_bot [Nontrivial A] [IsD
omain B] [h : P.LiesOver (⊥ : Ideal A)] : P = ⊥
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Algebra.IsUnramifiedAt.congr_simp`：∀ (R : Type u_1) {A : Type u_2} [inst
 : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (q q_1 : Ideal A)   
(e_q : q = q_1) [inst_3…
· 使用定理 `Algebra.isUnramifiedAt_bot`：isUnramifiedAt_bot [IsDomain R] [IsDomain S]
 [Module.IsTorsionFree R S] [CharZero R] [Algebra.IsIntegral R S] : IsUnramified
At R (⊥ : Ideal …
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α

--- 原说明 ---
In characteristic zero, the zero ideal is unramified in an integral domain exten
sion.
-/
theorem isUnramifiedIn_bot [IsDomain R] [IsDomain S] [FaithfulSMul R S] [CharZero R]
    [Algebra.IsIntegral R S] : IsUnramifiedIn S (⊥ : Ideal R) := by
  intro P _ hP
  simpa [Ideal.eq_bot_of_liesOver_bot R P] using isUnramifiedAt_bot

/-- Let `S` be a Dedekind domain that is torsion-free over a domain `R`, and let `p ≠ ⊥` be an
ideal of `R`. Then `p` is unramified in `S` if and only if `S` is unramified at every maximal
ideal `P` of `S` lying over `p`.

See `Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain` if `R` is of characteristic zero. -/
/-
**Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain'** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra`。
形式化陈述：isUnramifiedIn_iff_forall_of_isDedekindDomain' [IsDomain R] [IsDedekindDom
ain S] [Module.IsTorsionFree R S] {p : Ideal R} (hp : p != ⊥) : IsUnramifiedIn S
 p ↔ forall (P : Ideal S) (_ : P.IsMaximal), P.LiesOver p -> IsUnramifiedAt R P
参数：hp : p != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.ne_bot_of_liesOver_of_ne_bot`：ne_bot_of_liesOver_of_ne_bot (hp : p
 != ⊥) (P : Ideal B) [P.LiesOver p] : P != ⊥
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
Let `S` be a Dedekind domain that is torsion-free over a domain `R`, and let `p 
≠ ⊥` be an
ideal of `R`. Then `p` is unramified in `S` if and only if `S` is unramified at 
every maximal
ideal `P` of `S` lying over `p`.

See `Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain` if `R` is of charact
eristic zero.
-/
theorem isUnramifiedIn_iff_forall_of_isDedekindDomain' [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] {p : Ideal R} (hp : p ≠ ⊥) :
    IsUnramifiedIn S p ↔
      ∀ (P : Ideal S) (_ : P.IsMaximal), P.LiesOver p → IsUnramifiedAt R P :=
  ⟨fun h P hP hlo ↦ h P hP.isPrime hlo,
    fun h P hP hlo ↦ h P (hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hp P)) hlo⟩

/-- Let `S` be a Dedekind domain that is integral and torsion-free over a characteristic-zero
domain `R`. Then an ideal `p` of `R` is unramified in `S` if and only if `S` is unramified at every
maximal ideal `P` of `S` lying over `p`. -/
/-
**Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain** 是 Mathlib 中的一个定理，位于命名空
间 `Algebra`。
形式化陈述：isUnramifiedIn_iff_forall_of_isDedekindDomain [IsDomain R] [IsDedekindDoma
in S] [Module.IsTorsionFree R S] [CharZero R] [Algebra.IsIntegral R S] {p : Idea
l R} : IsUnramifiedIn S p ↔ forall (P : Ideal S) (_ : P.IsMaximal), P.LiesOver p
 -> IsUnramifiedAt R P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Algebra.isUnramifiedAt_bot`：isUnramifiedAt_bot [IsDomain R] [IsDomain S]
 [Module.IsTorsionFree R S] [CharZero R] [Algebra.IsIntegral R S] : IsUnramified
At R (⊥ : Ideal …
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal

--- 原说明 ---
Let `S` be a Dedekind domain that is integral and torsion-free over a characteri
stic-zero
domain `R`. Then an ideal `p` of `R` is unramified in `S` if and only if `S` is 
unramified at every
maximal ideal `P` of `S` lying over `p`.
-/
theorem isUnramifiedIn_iff_forall_of_isDedekindDomain [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] [CharZero R] [Algebra.IsIntegral R S] {p : Ideal R} :
    IsUnramifiedIn S p ↔
      ∀ (P : Ideal S) (_ : P.IsMaximal), P.LiesOver p → IsUnramifiedAt R P := by
  refine ⟨fun h P hP hlo ↦ h P hP.isPrime hlo, fun h P hP hlo ↦ ?_⟩
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · exact isUnramifiedAt_bot
  · exact h P (hP.isMaximal hPbot) hlo

/-- For a prime `𝔓` of `S` lying over an unramified prime `𝔭` of `R`, the ramification index
`e(𝔓 ∣ 𝔭)` equals `1`. -/
/-
**Algebra.IsUnramifiedIn.ramificationIdx_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra.IsUnramifiedIn`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [IsDomain R]   [Module.Finite ℤ R] [CharZero R] [Algebra.
EssFiniteType R S] [Algebra.IsIntegral R S] {𝔭 : Ideal R},   Algebra.IsUnramifie
dIn S 𝔭 → ∀ {𝔓 : Ideal S} [𝔓.IsPrime], 𝔓.LiesOver 𝔭 → 𝔓.ramificationIdx R = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.ramificationIdx_eq_one_iff`：ramificationIdx_eq_one_iff [q.IsPrime]
 [Algebra.EssFiniteType R S] [Algebra.IsIntegral R S] [PerfectField (q.under R).
ResidueField] : q.rami…
· 使用定理 `Ring.HasFiniteQuotients.instPerfectFieldResidueFieldOfFractionRing`：∀ {R
 : Type u_1} [inst : CommRing R] [Ring.HasFiniteQuotients R] [inst_2 : IsDomain 
R] [PerfectField (FractionRing R)]   (P : Ideal R) [inst…
· 使用定理 `Ring.HasFiniteQuotients.instOfIsDomainOfFiniteInt`：∀ {R : Type u_1} [ins
t : CommRing R] [IsDomain R] [Module.Finite ℤ R], Ring.HasFiniteQuotients R
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…

--- 原说明 ---
For a prime `𝔓` of `S` lying over an unramified prime `𝔭` of `R`, the ramificati
on index
`e(𝔓 ∣ 𝔭)` equals `1`.
-/
theorem IsUnramifiedIn.ramificationIdx_eq_one [IsDomain R]
    [Module.Finite ℤ R] [CharZero R] [EssFiniteType R S]
    [Algebra.IsIntegral R S] {𝔭 : Ideal R} (hunr : IsUnramifiedIn S 𝔭) {𝔓 : Ideal S}
    [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) : Ideal.ramificationIdx 𝔓 R = 1 :=
  Ideal.ramificationIdx_eq_one_iff.mpr
    (hunr 𝔓 inferInstance hP)

/-- A nonzero ideal of `R` is unramified in `S` if and only if every prime ideal of `S` lying
over it has ramification index `1`. -/
/-
**Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one** 是 Mathlib 中的一个定理，位于
命名空间 `Algebra`。
形式化陈述：isUnramifiedIn_iff_forall_ramificationIdx_eq_one [IsDomain R] [Module.Fini
te Int R] [CharZero R] [EssFiniteType R S] [Algebra.IsIntegral R S] {𝔭 : Ideal R
} : IsUnramifiedIn S 𝔭 ↔ forall (𝔓 : Ideal S) [𝔓.IsPrime], 𝔓.LiesOver 𝔭 -> Ideal
.ramificationIdx 𝔓 R = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsUnramifiedIn.ramificationIdx_eq_one`：∀ {R : Type u_1} {S : Typ
e u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [IsDomai
n R]   [Module.Finite ℤ R] [CharZer…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.ramificationIdx_eq_one_iff`：ramificationIdx_eq_one_iff [q.IsPrime]
 [Algebra.EssFiniteType R S] [Algebra.IsIntegral R S] [PerfectField (q.under R).
ResidueField] : q.rami…
· 使用定理 `Ring.HasFiniteQuotients.instPerfectFieldResidueFieldOfFractionRing`：∀ {R
 : Type u_1} [inst : CommRing R] [Ring.HasFiniteQuotients R] [inst_2 : IsDomain 
R] [PerfectField (FractionRing R)]   (P : Ideal R) [inst…
· 使用定理 `Ring.HasFiniteQuotients.instOfIsDomainOfFiniteInt`：∀ {R : Type u_1} [ins
t : CommRing R] [IsDomain R] [Module.Finite ℤ R], Ring.HasFiniteQuotients R
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…

--- 原说明 ---
A nonzero ideal of `R` is unramified in `S` if and only if every prime ideal of 
`S` lying
over it has ramification index `1`.
-/
theorem isUnramifiedIn_iff_forall_ramificationIdx_eq_one [IsDomain R]
    [Module.Finite ℤ R] [CharZero R] [EssFiniteType R S]
    [Algebra.IsIntegral R S] {𝔭 : Ideal R} :
    IsUnramifiedIn S 𝔭 ↔
      ∀ (𝔓 : Ideal S) [𝔓.IsPrime], 𝔓.LiesOver 𝔭 → Ideal.ramificationIdx 𝔓 R = 1 := by
  refine ⟨fun hunr 𝔓 _ hP ↦ hunr.ramificationIdx_eq_one hP, fun h 𝔓 _ hP ↦ ?_⟩
  rw [← Ideal.ramificationIdx_eq_one_iff]
  exact h 𝔓 hP

end Algebra

end IsUnramifiedIn

