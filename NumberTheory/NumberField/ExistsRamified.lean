/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.RingTheory.Unramified.Dedekind

/-!
# Every number field has a ramified prime over `ℚ`

...except `ℚ` itself.

This is a trivial corollary of `NumberField.not_dvd_discr_iff_forall_mem` and
`NumberField.abs_discr_gt_two` but is placed in a separate file to avoid large imports.

-/
@[expose] public section

open scoped NumberField nonZeroDivisors

variable {K 𝒪 : Type*} [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsIntegralClosure 𝒪 ℤ K]

/-- If `K` is a number field with positive rank, then some prime is ramified in `K`. -/
/-
**NumberField.exists_not_isUnramifiedIn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NumberField.exists_not_isUnramifiedIn (H : Module.finrank Rat K != 1) : ex
ists p : Nat, p.Prime ∧ ¬ Algebra.IsUnramifiedIn 𝒪 (Ideal.span {(p : Int)})
参数：H : Module.finrank Rat K != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NumberField.abs_discr_gt_two`：abs_discr_gt_two (h : 1 < finrank Rat K) :
 2 < |discr K|
· 使用定理 `Int.exists_prime_and_dvd`：exists_prime_and_dvd {n : Int} (hn : n.natAbs 
!= 1) : exists p, Prime p ∧ p ∣ n
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
If `K` is a number field with positive rank, then some prime is ramified in `K`.
-/
lemma NumberField.exists_not_isUnramifiedIn (H : Module.finrank ℚ K ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ¬ Algebra.IsUnramifiedIn 𝒪 (Ideal.span {(p : ℤ)}) := by
  have : 0 < Module.finrank ℚ K := Module.finrank_pos
  have : 2 < |discr K| := abs_discr_gt_two (by lia)
  obtain ⟨p, hp1, hp2⟩ := (discr K).exists_prime_and_dvd (by linarith)
  use p.natAbs, p.prime_iff_natAbs_prime.mp hp1
  simpa [← not_dvd_discr_iff_isUnramifiedIn K 𝒪 hp1]

/-- If `K` is a number field with positive rank, then there exists some maximal ideal of `𝓞 K`
that is ramified over `ℤ`. -/
/-
**NumberField.exists_not_isUnramifiedAt_int** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NumberField.exists_not_isUnramifiedAt_int (H : Module.finrank Rat K != 1) 
: exists (P : Ideal 𝒪) (_ : P.IsMaximal), ¬ Algebra.IsUnramifiedAt Int P
参数：H : Module.finrank Rat K != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用引理 `NumberField.exists_not_isUnramifiedIn`：NumberField.exists_not_isUnramifi
edIn (H : Module.finrank Rat K != 1) : exists p : Nat, p.Prime ∧ ¬ Algebra.IsUnr
amifiedIn 𝒪 (Ideal.span {(p…
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `IsIntegralClosure.isDedekindDomain`：IsIntegralClosure.isDedekindDomain [
IsDedekindDomain A] : IsDedekindDomain C
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用引理 `IsIntegralClosure.isTorsionFree`：isTorsionFree [Module R A] [IsScalarTow
er R A B] [IsTorsionFree R B] : IsTorsionFree R A
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A

--- 原说明 ---
If `K` is a number field with positive rank, then there exists some maximal idea
l of `𝓞 K`
that is ramified over `ℤ`.
-/
lemma NumberField.exists_not_isUnramifiedAt_int (H : Module.finrank ℚ K ≠ 1) :
    ∃ (P : Ideal 𝒪) (_ : P.IsMaximal), ¬ Algebra.IsUnramifiedAt ℤ P := by
  obtain ⟨p, hp1, hp2⟩ := NumberField.exists_not_isUnramifiedIn (𝒪 := 𝒪) H
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := IsIntegralClosure.isTorsionFree ℤ (A := 𝒪) K
  have := IsIntegralClosure.isIntegral_algebra ℤ (A := 𝒪) K
  grind [Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain]

/-- Any number field that is unramified over `ℚ` has rank `1`. -/
/-
**NumberField.finrank_eq_one_of_unramified** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NumberField.finrank_eq_one_of_unramified [Algebra.Unramified Int 𝒪] : Modu
le.finrank Rat K = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用引理 `NumberField.exists_not_isUnramifiedAt_int`：NumberField.exists_not_isUnra
mifiedAt_int (H : Module.finrank Rat K != 1) : exists (P : Ideal 𝒪) (_ : P.IsMax
imal), ¬ Algebra.IsUnramifiedAt…
· 使用定理 `Algebra.FormallyUnramified.instLocalization`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.FormallyUnramified R S] (M : Sub…
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…

--- 原说明 ---
Any number field that is unramified over `ℚ` has rank `1`.
-/
lemma NumberField.finrank_eq_one_of_unramified [Algebra.Unramified ℤ 𝒪] :
    Module.finrank ℚ K = 1 := by
  by_contra H
  obtain ⟨P, _, H⟩ := NumberField.exists_not_isUnramifiedAt_int (𝒪 := 𝒪) H
  exact H inferInstance

/-- If `𝒪` is a domain that is a finite and unramified extension of `ℤ`, then `𝒪 = ℤ`. -/
/-
**bijective_algebraMap_int_of_finite_of_unramified** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bijective_algebraMap_int_of_finite_of_unramified [Module.Finite Int 𝒪] [Al
gebra.Unramified Int 𝒪] [IsDomain 𝒪] [FaithfulSMul Int 𝒪] : Function.Bijective (
algebraMap Int 𝒪)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isDedekindDomain.of_formallyUnramified`：isDedekindDomain.of_formallyUnra
mified : IsDedekindDomain B
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用引理 `Algebra.charZero_of_charZero`：Algebra.charZero_of_charZero [CharZero R] 
: CharZero A
· 使用引理 `Module.Finite.of_isLocalization`：of_isLocalization (R S) {Rₚ Sₚ : Type*}
 [CommSemiring R] [CommSemiring S] [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra 
R S] [Algebra R Rₚ] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors
`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用引理 `NumberField.finrank_eq_one_of_unramified`：NumberField.finrank_eq_one_of_
unramified [Algebra.Unramified Int 𝒪] : Module.finrank Rat K = 1
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `IsIntegralClosure.of_algEquiv`：of_algEquiv {S : Type*} [CommRing S] [Alg
ebra A S] [Algebra R S] (f : B ≃ₐ[R] S) (h : forall x, algebraMap A S x = f (alg
ebraMap A B x)) : I…
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.finrank_eq_one_iff_bijective_algebraMap`：∀ {F : Type u_1} {E : T
ype u_2} [inst : CommRing F] [StrongRankCondition F] [inst_2 : Ring E] [inst_3 :
 Algebra F E]   [Module.Free F E], Mo…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
If `𝒪` is a domain that is a finite and unramified extension of `ℤ`, then `𝒪 = ℤ
`.
-/
lemma bijective_algebraMap_int_of_finite_of_unramified
    [Module.Finite ℤ 𝒪] [Algebra.Unramified ℤ 𝒪] [IsDomain 𝒪] [FaithfulSMul ℤ 𝒪] :
    Function.Bijective (algebraMap ℤ 𝒪) := by
  have := isDedekindDomain.of_formallyUnramified ℤ 𝒪
  let K := FractionRing 𝒪
  let : Algebra ℤ K := Ring.toIntAlgebra K
  have : CharZero 𝒪 := Algebra.charZero_of_charZero ℤ _
  have : NumberField K := { to_finiteDimensional := Module.Finite.of_isLocalization ℤ 𝒪 ℤ⁰ }
  have := NumberField.finrank_eq_one_of_unramified (K := K) (𝒪 := 𝒪)
  have : IsIntegralClosure ℤ ℤ K := .of_algEquiv _ (.ofBijective (IsScalarTower.toAlgHom _ _ _)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp this)) (by simp)
  exact bijective_algebraMap_of_linearEquiv (IsIntegralClosure.equiv ℤ ℤ K 𝒪).toLinearEquiv

/-- If `K` is a number field with positive rank such that `K/ℚ` is galois, then there exists
some rational prime `p : ℕ` such that every prime of `K` over `p` is ramified. -/
/-
**NumberField.exists_not_isUnramifiedAt_int_of_isGalois** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：NumberField.exists_not_isUnramifiedAt_int_of_isGalois [IsGalois Rat K] (H 
: 1 < Module.finrank Rat K) : exists p : Nat, p.Prime ∧ forall (P : Ideal 𝒪) (_ 
: P.IsPrime), ↑p in P -> ¬ Algebra.IsUnramifiedAt Int P
参数：H : 1 < Module.finrank Rat K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `IsIntegralClosure.isDedekindDomain`：IsIntegralClosure.isDedekindDomain [
IsDedekindDomain A] : IsDedekindDomain C
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `IsIntegralClosure.isFractionRing_of_finite_extension`：isFractionRing_of_
finite_extension [IsDomain A] [Algebra K L] [IsScalarTower A K L] [FiniteDimensi
onal K L] : IsFractionRing C L
· 使用定理 `IsIntegralClosure.finite`：IsIntegralClosure.finite [IsIntegrallyClosed A
] [IsNoetherianRing A] : Module.Finite A C
· 使用定理 `Ring.HasFiniteQuotients.instIsNoetherianRing`：∀ {R : Type u_1} [inst : C
ommRing R] [Ring.HasFiniteQuotients R], IsNoetherianRing R
· 使用定理 `Ring.HasFiniteQuotients.instInt`：Ring.HasFiniteQuotients ℤ
· 使用引理 `CharZero.of_module`：CharZero.of_module [Semiring R] [AddCommMonoidWithOn
e M] [CharZero M] [Module R M] : CharZero R
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `IsGaloisGroup.of_isFractionRing`：IsGaloisGroup.of_isFractionRing [hGKL :
 IsGaloisGroup G K L] [IsIntegrallyClosed A] [Algebra.IsIntegral A B] : IsGalois
Group G A B
· 使用定理 `instSMulDistribClassAlgEquiv`：∀ (A : Type u_1) (K : Type u_2) (L : Type 
u_3) (B : Type u_4) [inst : CommRing A] [inst_1 : CommRing B]   [inst_2 : Field 
K] [inst_3 : Field…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用引理 `NumberField.exists_not_isUnramifiedAt_int`：NumberField.exists_not_isUnra
mifiedAt_int (H : Module.finrank Rat K != 1) : exists (P : Ideal 𝒪) (_ : P.IsMax
imal), ¬ Algebra.IsUnramifiedAt…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `Ideal.IsMaximal.ne_bot_of_isIntegral_int`：Ideal.IsMaximal.ne_bot_of_isIn
tegral_int [CharZero R] [Algebra.IsIntegral Int R] (I : Ideal R) [I.IsMaximal] :
 I != ⊥
· 使用定理 `Ideal.eq_bot_of_comap_eq_bot`：eq_bot_of_comap_eq_bot [Nontrivial R] [IsD
omain S] [Algebra.IsIntegral R S] (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
If `K` is a number field with positive rank such that `K/ℚ` is galois, then ther
e exists
some rational prime `p : ℕ` such that every prime of `K` over `p` is ramified.
-/
lemma NumberField.exists_not_isUnramifiedAt_int_of_isGalois [IsGalois ℚ K]
    (H : 1 < Module.finrank ℚ K) :
    ∃ p : ℕ, p.Prime ∧ ∀ (P : Ideal 𝒪) (_ : P.IsPrime), ↑p ∈ P → ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K 𝒪
  have := IsIntegralClosure.finite ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  let : MulSemiringAction Gal(K/ℚ) 𝒪 := IsIntegralClosure.MulSemiringAction ℤ ℚ K 𝒪
  have := IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ 𝒪 ℚ K
  obtain ⟨P, _, hP'⟩ := NumberField.exists_not_isUnramifiedAt_int (𝒪 := 𝒪) H.ne'
  obtain ⟨p, hp : _ = Ideal.span _⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have hp0 : p ≠ 0 := fun hp0 ↦ Ideal.IsMaximal.ne_bot_of_isIntegral_int _
    (Ideal.eq_bot_of_comap_eq_bot (hp.trans (by aesop)))
  have : Prime p := by rw [← Ideal.span_singleton_prime hp0, ← hp]; infer_instance
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp this, fun Q _ hQ ↦ ?_⟩
  replace hQ : (p : 𝒪) ∈ Q := Q.mem_of_dvd
    (map_dvd (algebraMap _ _) p.associated_natAbs.symm.dvd) (by simpa using hQ)
  have : .span {p} = Ideal.under ℤ Q :=
    ((Ideal.liesOver_span_iff Ideal.IsPrime.ne_top' this).mpr hQ).1
  rwa [← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) _ Gal(K/ℚ), ← this, ← hp,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ P Gal(K/ℚ), Ideal.ramificationIdx_eq_one_iff]
