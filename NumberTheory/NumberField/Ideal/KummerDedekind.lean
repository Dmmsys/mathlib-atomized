/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.KummerDedekind
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Ideal.Int

/-!
# Kummer-Dedekind criterion for the splitting of prime numbers

In this file, we give a specialized version of the Kummer-Dedekind criterion for the case of the
splitting of rational primes in number fields.

## Main definitions

Let `K` be a number field and `θ` an algebraic integer of `K`.

* `RingOfIntegers.exponent`: the smallest positive integer `d` contained in the conductor of `θ`.
  It is the smallest integer such that `d • 𝓞 K ⊆ ℤ[θ]`, see `RingOfIntegers.exponent_eq_sInf`.

* `RingOfIntegers.ZModXQuotSpanEquivQuotSpan`: The isomorphism between `(ℤ / pℤ)[X] / (minpoly θ)`
  and `𝓞 K / p(𝓞 K)` for a prime `p` which doesn't divide the exponent of `θ`.

* `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`: The bijection between the prime ideals
  of `K` above `p` and the monic irreducible factors of `minpoly ℤ θ` modulo `p` for a prime `p`
  which doesn't divide the exponent of `θ`.

## Main results

* `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`: The ideal corresponding to the class
  of `Q ∈ ℤ[X]` modulo `p` via `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is spanned
  by `p` and `Q(θ)`.

* `NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply`: The residual degree
  of the ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
  `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is equal to the degree of `Q mod p`.

* `NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply`: The
  ramification index of the ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
  `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is equal to the multiplicity of `Q mod p`
  in `minpoly ℤ θ`.

-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal KummerDedekind UniqueFactorizationMonoid

variable {K : Type*} [Field K]

namespace RingOfIntegers

/--
The smallest positive integer `d` contained in the conductor of `θ`. It is the smallest integer
such that `d • 𝓞 K ⊆ ℤ[θ]`, see `exponent_eq_sInf`. It is set to `0` if `d` does not exists.
-/
/-
**RingOfIntegers.exponent** 是 Mathlib 中的一个定义，位于命名空间 `RingOfIntegers`。
形式化陈述：exponent (θ : 𝓞 K) : Nat
参数：θ : 𝓞 K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest positive integer `d` contained in the conductor of `θ`. It is the s
mallest integer
such that `d • 𝓞 K ⊆ ℤ[θ]`, see `exponent_eq_sInf`. It is set to `0` if `d` does
 not exists.
-/
def exponent (θ : 𝓞 K) : ℕ := absNorm (under ℤ (conductor ℤ θ))

variable {θ : 𝓞 K}
/-
**RingOfIntegers.exponent_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：exponent_eq_one_iff : exponent θ = 1 ↔ Algebra.adjoin Int {θ} = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingOfIntegers.exponent.eq_1`：∀ {K : Type u_1} [inst : Field K] (θ : Num
berField.RingOfIntegers K),   RingOfIntegers.exponent θ = Ideal.absNorm (Ideal.u
nder ℤ (conductor …
· 使用定理 `Ideal.absNorm_eq_one_iff`：absNorm_eq_one_iff {I : Ideal S} : absNorm I =
 1 ↔ I = ⊤
· 使用定理 `Ideal.comap_eq_top_iff`：comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔
 I = ⊤
· 使用定理 `conductor_eq_top_iff_adjoin_eq_top`：conductor_eq_top_iff_adjoin_eq_top {
x : S} : conductor R x = ⊤ ↔ R[x] = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem exponent_eq_one_iff : exponent θ = 1 ↔ Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [exponent, absNorm_eq_one_iff, comap_eq_top_iff, conductor_eq_top_iff_adjoin_eq_top]
/-
**RingOfIntegers.not_dvd_exponent_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`
。
形式化陈述：not_dvd_exponent_iff {p : Nat} [Fact (Nat.Prime p)] : ¬ p ∣ exponent θ ↔ C
odisjoint (comap (algebraMap Int (𝓞 K)) (conductor Int θ)) (span {↑p})
参数：Nat.Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_comm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] {a b : α}, Codisjoint a b ↔ Codisjoint b a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsCoatom.not_le_iff_codisjoint`：IsCoatom.not_le_iff_codisjoint (ha : IsC
oatom a) : ¬ b <= a ↔ Codisjoint a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.isMaximal_def`：isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoato
m I
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
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
· 使用定理 `Int.ideal_span_absNorm_eq_self`：Int.ideal_span_absNorm_eq_self (J : Idea
l Int) : span {(absNorm J : Int)} = J
· 使用定理 `Ideal.span_singleton_dvd_span_singleton_iff_dvd`：span_singleton_dvd_span
_singleton_iff_dvd {a b : R} : span {a} ∣ span ({b} : Set R) ↔ a ∣ b
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `RingOfIntegers.exponent.eq_1`：∀ {K : Type u_1} [inst : Field K] (θ : Num
berField.RingOfIntegers K),   RingOfIntegers.exponent θ = Ideal.absNorm (Ideal.u
nder ℤ (conductor …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_dvd_exponent_iff {p : ℕ} [Fact (Nat.Prime p)] :
    ¬ p ∣ exponent θ ↔ Codisjoint (comap (algebraMap ℤ (𝓞 K)) (conductor ℤ θ)) (span {↑p}) := by
  rw [codisjoint_comm, ← IsCoatom.not_le_iff_codisjoint, ← under_def, ← Ideal.dvd_iff_le,
    ← Int.ideal_span_absNorm_eq_self (under ℤ (conductor ℤ θ)),
    Ideal.span_singleton_dvd_span_singleton_iff_dvd, Int.natCast_dvd_natCast, exponent]
  exact isMaximal_def.mp <| Int.ideal_span_isMaximal_of_prime p
/-
**RingOfIntegers.exponent_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：exponent_eq_sInf : exponent θ = sInf {d : Nat | 0 < d ∧ (d : 𝓞 K) in condu
ctor Int θ}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingOfIntegers.exponent.eq_1`：∀ {K : Type u_1} [inst : Field K] (θ : Num
berField.RingOfIntegers K),   RingOfIntegers.exponent θ = Ideal.absNorm (Ideal.u
nder ℤ (conductor …
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
· 使用定理 `Int.absNorm_under_eq_sInf`：absNorm_under_eq_sInf : absNorm (under Int I)
 = sInf {d : Nat | 0 < d ∧ (d : R) in I}
-/
theorem exponent_eq_sInf : exponent θ = sInf {d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ} := by
  rw [exponent, Int.absNorm_under_eq_sInf]

variable [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact p.Prime]

/--
If `p` doesn't divide the exponent of `θ`, then `(ℤ / pℤ)[X] / (minpoly θ) ≃+* 𝓞 K / p(𝓞 K)`.
-/
/-
**RingOfIntegers.ZModXQuotSpanEquivQuotSpan** 是 Mathlib 中的一个定义，位于命名空间 `RingOfInt
egers`。
形式化陈述：ZModXQuotSpanEquivQuotSpan (hp : ¬ p ∣ exponent θ) : (ZMod p)[X] ⧸ span {m
ap (Int.castRingHom (ZMod p)) (minpoly Int θ)} ≃+* 𝓞 K ⧸ span {(p : 𝓞 K)}
参数：hp : ¬ p ∣ exponent θ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.isIntegral`：isIntegral (x : 𝓞 K) : IsIntegral
 Int x

--- 原说明 ---
If `p` doesn't divide the exponent of `θ`, then `(ℤ / pℤ)[X] / (minpoly θ) ≃+* 𝓞
 K / p(𝓞 K)`.
-/
def ZModXQuotSpanEquivQuotSpan (hp : ¬ p ∣ exponent θ) :
    (ZMod p)[X] ⧸ span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} ≃+*
      𝓞 K ⧸ span {(p : 𝓞 K)} :=
  (quotientEquivAlgOfEq ℤ (by simp [Ideal.map_span, Polynomial.map_map])).toRingEquiv.trans
    ((quotientEquiv _ _ (mapEquiv (Int.quotientSpanNatEquivZMod p)) rfl).symm.trans
      ((quotMapEquivQuotQuotMap (not_dvd_exponent_iff.mp hp).eq_top θ.isIntegral).symm.trans
        (quotientEquivAlgOfEq ℤ (by simp [map_span])).toRingEquiv))
/-
**RingOfIntegers.ZModXQuotSpanEquivQuotSpan_mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `
RingOfIntegers`。
形式化陈述：ZModXQuotSpanEquivQuotSpan_mk_apply (hp : ¬ p ∣ exponent θ) (Q : Int[X]) :
 (ZModXQuotSpanEquivQuotSpan hp) (Ideal.Quotient.mk (span {map (Int.castRingHom 
(ZMod p)) (minpoly Int θ)}) (map (Int.castRingHom (ZMod p)) Q)) = Ideal.Quotient
.mk (span {(p : 𝓞 K)}) (aeval θ Q)
参数：hp : ¬ p ∣ exponent θ；Q : Int[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.isIntegral`：isIntegral (x : 𝓞 K) : IsIntegral
 Int x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.quotientEquiv_symm_apply`：∀ {R : Type u} [inst : Ring R] {S : Type
 v} [inst_1 : Ring S] (I : Ideal R) (J : Ideal S) [inst_2 : I.IsTwoSided]   [ins
t_3 : J.IsTwoSided] …
· 使用定理 `Ideal.quotientMap_mk`：quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTw
oSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} {x : R} : quotientMap
 I f H (Qu…
· 使用定理 `Polynomial.mapEquiv_symm_apply`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] (e : R ≃+* S) (a : Polynomial S),   (Polynomial.ma
pEquiv e).symm a = P…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Int.quotientSpanNatEquivZMod_comp_castRingHom`：quotientSpanNatEquivZMod_
comp_castRingHom (n : Nat) : ((Int.quotientSpanNatEquivZMod n).symm : _ ->+* _).
comp (Int.castRingHom (ZMod n)) = I…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingOfIntegers.not_dvd_exponent_iff`：not_dvd_exponent_iff {p : Nat} [Fac
t (Nat.Prime p)] : ¬ p ∣ exponent θ ↔ Codisjoint (comap (algebraMap Int (𝓞 K)) (
conductor Int θ)) (span {…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
（共 32 条，此处仅展示前 30 条）
-/
theorem ZModXQuotSpanEquivQuotSpan_mk_apply (hp : ¬ p ∣ exponent θ) (Q : ℤ[X]) :
    (ZModXQuotSpanEquivQuotSpan hp)
      (Ideal.Quotient.mk (span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)})
      (map (Int.castRingHom (ZMod p)) Q)) = Ideal.Quotient.mk (span {(p : 𝓞 K)}) (aeval θ Q) := by
  simp only [ZModXQuotSpanEquivQuotSpan, algebraMap_int_eq,
    RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, quotientEquivAlgOfEq_mk,
    quotientEquiv_symm_apply, quotientMap_mk, RingHom.coe_coe, mapEquiv_symm_apply,
    Polynomial.map_map, Int.quotientSpanNatEquivZMod_comp_castRingHom]
  exact congr_arg (quotientEquivAlgOfEq ℤ (by simp [map_span])) <|
    quotMapEquivQuotQuotMap_symm_apply (not_dvd_exponent_iff.mp hp).eq_top θ.isIntegral Q

variable (p θ) in
/--
The finite set of monic irreducible factors of `minpoly ℤ θ` modulo `p`.
-/
/-
**RingOfIntegers.monicFactorsMod** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingOfIntegers`。
形式化陈述：monicFactorsMod : Finset ((ZMod p)[X])
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite set of monic irreducible factors of `minpoly ℤ θ` modulo `p`.
-/
abbrev monicFactorsMod : Finset ((ZMod p)[X]) :=
  (normalizedFactors (map (Int.castRingHom (ZMod p)) (minpoly ℤ θ))).toFinset

/--
If `p` does not divide `exponent θ` and `Q` is a lift of a monic irreducible factor of
`minpoly ℤ θ` modulo `p`, then `(ℤ / pℤ)[X] / Q ≃+* 𝓞 K / (p, Q(θ))`.
-/
/-
**RingOfIntegers.ZModXQuotSpanEquivQuotSpanPair** 是 Mathlib 中的一个定义，位于命名空间 `RingO
fIntegers`。
形式化陈述：ZModXQuotSpanEquivQuotSpanPair (hp : ¬ p ∣ exponent θ) {Q : Int[X]} (hQ : 
Q.map (Int.castRingHom (ZMod p)) in monicFactorsMod θ p) : (ZMod p)[X] ⧸ span {P
olynomial.map (Int.castRingHom (ZMod p)) Q} ≃+* 𝓞 K ⧸ span {(p : 𝓞 K), (aeval θ)
 Q}
参数：hp : ¬ p ∣ exponent θ；hQ : Q.map (Int.castRingHom (ZMod p)) in monicFactorsMo
d θ p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p` does not divide `exponent θ` and `Q` is a lift of a monic irreducible fac
tor of
`minpoly ℤ θ` modulo `p`, then `(ℤ / pℤ)[X] / Q ≃+* 𝓞 K / (p, Q(θ))`.
-/
def ZModXQuotSpanEquivQuotSpanPair (hp : ¬ p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    (ZMod p)[X] ⧸ span {Polynomial.map (Int.castRingHom (ZMod p)) Q} ≃+*
      𝓞 K ⧸ span {(p : 𝓞 K), (aeval θ) Q} :=
  have h₀ : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
      map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have h_eq₁ : span {map (Int.castRingHom (ZMod p)) Q} =
      span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} ⊔
        span {map (Int.castRingHom (ZMod p)) Q} := by
    rw [← span_insert, span_pair_comm, span_pair_eq_span_left_iff_dvd.mpr]
    simp only [Multiset.mem_toFinset] at hQ
    exact ((Polynomial.mem_normalizedFactors_iff h₀).mp hQ).2.2
  have h_eq₂ : span {↑p} ⊔ span {(aeval θ) Q} = span {↑p, (aeval θ) Q} := by
    rw [span_insert]
  ((Ideal.quotEquivOfEq h_eq₁).trans (DoubleQuot.quotQuotEquivQuotSup _ _).symm).trans <|
    (Ideal.quotientEquiv
      (Ideal.map (Ideal.Quotient.mk _) (span {(Polynomial.map (Int.castRingHom (ZMod p)) Q)}))
      (Ideal.map (Ideal.Quotient.mk _) (span {aeval θ Q})) (ZModXQuotSpanEquivQuotSpan hp) (by
        simp [map_span, ZModXQuotSpanEquivQuotSpan_mk_apply])).trans <|
    (DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq h_eq₂)

end RingOfIntegers

open RingOfIntegers IsDedekindDomain
namespace NumberField.Ideal

variable {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]

attribute [local instance] Int.ideal_span_isMaximal_of_prime Ideal.Quotient.field

set_option backward.privateInPublic true in
open scoped Classical in
/-
**NumberField.Ideal.primesOverSpanEquivMonicFactorsModAux** 是 Mathlib 中的一个定义，位于命
名空间 `NumberField.Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def primesOverSpanEquivMonicFactorsModAux (A : ℤ[X]) :
    {Q // Q ∈ normalizedFactors (map (Ideal.Quotient.mk (span {(p : ℤ)})) A)} ≃
    (normalizedFactors (map (Int.castRingHom (ZMod p)) A)).toFinset :=
  (normalizedFactorsEquiv (f := (mapEquiv (Int.quotientSpanNatEquivZMod p)).toMulEquiv)
    (by simp) (map (Ideal.Quotient.mk (span {(p : ℤ)})) A)).trans
      (Equiv.subtypeEquivRight (fun _ ↦ by simp [Polynomial.map_map]))
/-
**NumberField.Ideal.primesOverSpanEquivMonicFactorsModAux_symm_apply** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem primesOverSpanEquivMonicFactorsModAux_symm_apply (A : ℤ[X]) {Q : (ZMod p)[X]}
    (hQ : Q ∈ (normalizedFactors (map (Int.castRingHom (ZMod p)) A)).toFinset) :
    ((primesOverSpanEquivMonicFactorsModAux A).symm ⟨Q, hQ⟩ : (ℤ ⧸ span {(p : ℤ)})[X]) =
      Polynomial.map ((Int.quotientSpanNatEquivZMod p).symm) Q := rfl

variable [NumberField K]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
If `p` does not divide `exponent θ`, then the prime ideals above `p` in `K` are in bijection
with the monic irreducible factors of `minpoly ℤ θ` modulo `p`.
-/
/-
**NumberField.Ideal.primesOverSpanEquivMonicFactorsMod** 是 Mathlib 中的一个定义，位于命名空间
 `NumberField.Ideal`。
形式化陈述：primesOverSpanEquivMonicFactorsMod (hp : ¬ p ∣ exponent θ) : primesOver (s
pan {(p : Int)}) (𝓞 K) ≃ monicFactorsMod θ p
参数：hp : ¬ p ∣ exponent θ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.RingOfIntegers.isIntegral`：isIntegral (x : 𝓞 K) : IsIntegral
 Int x

--- 原说明 ---
If `p` does not divide `exponent θ`, then the prime ideals above `p` in `K` are 
in bijection
with the monic irreducible factors of `minpoly ℤ θ` modulo `p`.
-/
def primesOverSpanEquivMonicFactorsMod (hp : ¬ p ∣ exponent θ) :
    primesOver (span {(p : ℤ)}) (𝓞 K) ≃ monicFactorsMod θ p :=
  have h : span {(p : ℤ)} ≠ ⊥ := by simp [NeZero.ne p]
  ((Equiv.setCongr (by ext; simp [mem_primesOver_iff_mem_normalizedFactors _ h])).trans
    (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    (Int.ideal_span_isMaximal_of_prime p) h
      (not_dvd_exponent_iff.mp hp).eq_top θ.isIntegral)).trans <|
        (primesOverSpanEquivMonicFactorsModAux _)
/-
**NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.Ideal`。
形式化陈述：primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ) {Q :
 (ZMod p)[X]} (hQ : Q in monicFactorsMod θ p) : ((primesOverSpanEquivMonicFactor
sMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) = (normalizedFactorsMapEquivNormalizedFacto
rsMinPolyMk inferInstance (by simp [NeZero.ne p]) (not_dvd_exponent_iff.mp hp).e
q_top θ.isIntegral).symm ⟨Q.map (Int.quotientSpanNatEquivZMod p).symm, by rw [← 
primesOverSpanEquivMonicFactorsModAux_symm_apply] exact ((primesOverSpanEquivMon
icFactorsModAux _).symm ⟨Q
参数：hp : ¬ p ∣ exponent θ；ZMod p；hQ : Q in monicFactorsMod θ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ p) :
    ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
      (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
        inferInstance (by simp [NeZero.ne p]) (not_dvd_exponent_iff.mp hp).eq_top θ.isIntegral).symm
        ⟨Q.map (Int.quotientSpanNatEquivZMod p).symm, by
          rw [← primesOverSpanEquivMonicFactorsModAux_symm_apply]
          exact ((primesOverSpanEquivMonicFactorsModAux _).symm ⟨Q, hQ⟩).prop⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
The ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is spanned by `p` and `Q(θ)`.
-/
/-
**NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span** 是 Ma
thlib 中的一个定理，位于命名空间 `NumberField.Ideal`。
形式化陈述：primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span (hp : ¬ p ∣ exponent
 θ) {Q : Int[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) in monicFactorsMod θ p) 
: ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q.map (Int.castRingHom (ZMod p)
), hQ⟩ : Ideal (𝓞 K)) = span {(p : (𝓞 K)), aeval θ Q}
参数：hp : ¬ p ∣ exponent θ；hQ : Q.map (Int.castRingHom (ZMod p)) in monicFactorsMo
d θ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingOfIntegers.not_dvd_exponent_iff`：not_dvd_exponent_iff {p : Nat} [Fac
t (Nat.Prime p)] : ¬ p ∣ exponent θ ↔ Codisjoint (comap (algebraMap Int (𝓞 K)) (
conductor Int θ)) (span {…
· 使用定理 `NumberField.RingOfIntegers.isIntegral`：isIntegral (x : 𝓞 K) : IsIntegral
 Int x
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.quotientSpanNatEquivZMod_comp_castRingHom`：quotientSpanNatEquivZMod_
comp_castRingHom (n : Nat) : ((Int.quotientSpanNatEquivZMod n).symm : _ ->+* _).
comp (Int.castRingHom (ZMod n)) = I…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_
apply_eq_span`：normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq
_span (hI : I.IsMaximal) {Q : R[X]} (hQ : Q.map (Ideal.Quotient.mk I) in no…
· 使用定理 `Ideal.span_union`：span_union (s t : Set α) : span (s union t) = span s ⊔
 span t
· 使用定理 `Ideal.span_eq`：span_eq : span (I : Set α) = I
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is spanned by `p` and `Q(
θ)`.
-/
theorem primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span (hp : ¬ p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        span {(p : (𝓞 K)), aeval θ Q} := by
  simp only [primesOverSpanEquivMonicFactorsMod_symm_apply, Polynomial.map_map,
    Int.quotientSpanNatEquivZMod_comp_castRingHom]
  rw [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span,
    span_union, span_eq, map_span, Set.image_singleton, map_natCast, ← span_insert]
/-
**NumberField.Ideal.liesOver_primesOverSpanEquivMonicFactorsMod_symm** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.Ideal`。
形式化陈述：liesOver_primesOverSpanEquivMonicFactorsMod_symm (hp : ¬ p ∣ exponent θ) {
Q : Int[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) in monicFactorsMod θ p) : Lie
sOver (span {(p : (𝓞 K)), aeval θ Q}) (span {(p : Int)})
参数：hp : ¬ p ∣ exponent θ；hQ : Q.map (Int.castRingHom (ZMod p)) in monicFactorsMo
d θ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span`
：primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span (hp : ¬ p ∣ exponent θ) {
Q : Int[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) in monicFa…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem liesOver_primesOverSpanEquivMonicFactorsMod_symm (hp : ¬ p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    LiesOver (span {(p : (𝓞 K)), aeval θ Q}) (span {(p : ℤ)}) := by
  rw [← Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hp hQ]
  exact ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩).prop.2

/--
The residual degree of the ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is equal to the degree of `Q mod p`.
-/
/-
**NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply** 是
 Mathlib 中的一个定理，位于命名空间 `NumberField.Ideal`。
形式化陈述：inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ expon
ent θ) {Q : Int[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) in monicFactorsMod θ 
p) : inertiaDeg ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q.map (Int.castRi
ngHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) Int = natDegree (Q.map (Int.castRingHom (ZMo
d p)))
参数：hp : ¬ p ∣ exponent θ；hQ : Q.map (Int.castRingHom (ZMod p)) in monicFactorsMo
d θ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span`
：primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span (hp : ¬ p ∣ exponent θ) {
Q : Int[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) in monicFa…
· 使用定理 `Ideal.primesOver.isMaximal`：∀ {A : Type u_1} [inst : CommRing A] {p : Id
eal A} [p.IsMaximal] {B : Type u_2} [inst_2 : CommRing B]   [inst_3 : Algebra A 
B] [Algebra.IsIn…
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralInt`：∀ {K : Type u_1} [inst : F
ield K], Algebra.IsIntegral ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.Ideal.liesOver_primesOverSpanEquivMonicFactorsMod_symm`：lies
Over_primesOverSpanEquivMonicFactorsMod_symm (hp : ¬ p ∣ exponent θ) {Q : Int[X]
} (hQ : Q.map (Int.castRingHom (ZMod p)) in monicFactors…
· 使用定理 `Ideal.inertiaDeg_eq_of_isMaximal`：inertiaDeg_eq_of_isMaximal [q.LiesOver
 p] [p.IsMaximal] [q.IsMaximal] : q.inertiaDeg R = Module.finrank (R ⧸ p) (S ⧸ q
)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `finrank_quotient_span_eq_natDegree`：∀ {K : Type u_5} [inst : Field K] {f
 : Polynomial K}, Module.finrank K (Polynomial K ⧸ Ideal.span {f}) = f.natDegree
· 使用定理 `Algebra.finrank_eq_of_equiv_equiv`：finrank_eq_of_equiv_equiv {R₀ S₀ : Ty
pe*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀] {R₁ S₁ : Type*} [CommSemiri
ng R₁] [Semiring S₁] [A…
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The residual degree of the ideal corresponding to the class of `Q ∈ ℤ[X]` modulo
 `p` via
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is equal to the degree of
 `Q mod p`.
-/
theorem inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    inertiaDeg ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) ℤ =
        natDegree (Q.map (Int.castRingHom (ZMod p))) := by
  -- This is needed for `inertiaDeg_algebraMap` below to work
  have : (span {↑p, (aeval θ) Q}).IsMaximal := by
    rw [← Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hp hQ]
    apply Ideal.primesOver.isMaximal
  have := liesOver_primesOverSpanEquivMonicFactorsMod_symm hp hQ
  rw [primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span,
    inertiaDeg_eq_of_isMaximal (span {(p : ℤ)}),
    ← finrank_quotient_span_eq_natDegree]
  refine Algebra.finrank_eq_of_equiv_equiv (Int.quotientSpanNatEquivZMod p) ?_ (by ext; simp)
  exact (ZModXQuotSpanEquivQuotSpanPair hp hQ).symm
/-
**NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'** 
是 Mathlib 中的一个定理，位于命名空间 `NumberField.Ideal`。
形式化陈述：inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣ expo
nent θ) {Q : (ZMod p)[X]} (hQ : Q in monicFactorsMod θ p) : inertiaDeg ((primesO
verSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) Int = natDegree Q
参数：hp : ¬ p ∣ exponent θ；ZMod p；hQ : Q in monicFactorsMod θ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
· 使用定理 `ZMod.ringHom_surjective`：ringHom_surjective [NonAssocRing R] (f : R ->+*
 ZMod n) : Function.Surjective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_app
ly`：inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponen
t θ) {Q : Int[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) in moni…
-/
theorem inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ p) :
    inertiaDeg
      ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) ℤ = natDegree Q := by
  obtain ⟨S, rfl⟩ := (map_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))) Q
  rw [inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply]

/--
The ramification index of the ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is equal to the multiplicity of `Q mod p` in
`minpoly ℤ θ`.
-/
/-
**NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_appl
y** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Ideal`。
形式化陈述：ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ 
exponent θ) {Q : Int[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) in monicFactorsM
od θ p) : ramificationIdx ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q.map (
Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) Int = multiplicity (Q.map (Int.cas
tRingHom (ZMod p))) ((minpoly Int θ).map (Int.castRingHom (ZMod p)))
参数：hp : ¬ p ∣ exponent θ；hQ : Q.map (Int.castRingHom (ZMod p)) in monicFactorsMo
d θ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity`：ramificationIdx_
eq_multiplicity [IsDedekindDomain S] [q.IsPrime] [q.LiesOver p] (hp : p.map (alg
ebraMap R S) != ⊥) : q.ramificationIdx R = m…
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.primesOver.isPrime`：∀ {A : Type u_2} [inst : CommSemiring A] (p : 
Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.
primesOver B))…
· 使用定理 `Ideal.primesOver.liesOver`：∀ {A : Type u_2} [inst : CommSemiring A] (p :
 Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p
.primesOver B))…
· 使用定理 `Ideal.map_ne_bot_of_ne_bot`：map_ne_bot_of_ne_bot {R S : Type*} [CommSemi
ring R] [Semiring S] [Algebra R S] [FaithfulSMul R S] {I : Ideal R} (h : I != ⊥)
 : map (algebraM…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `multiplicity_eq_of_emultiplicity_eq`：multiplicity_eq_of_emultiplicity_eq
 {c d : β} (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = mult
iplicity c d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `emultiplicity_map_eq`：emultiplicity_map_eq {F : Type*} [EquivLike F α β]
 [MulEquivClass F α β] (f : F) {a b : α} : emultiplicity (f a) (f b) = emultipli
city a b
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
The ramification index of the ideal corresponding to the class of `Q ∈ ℤ[X]` mod
ulo `p` via
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is equal to the multiplic
ity of `Q mod p` in
`minpoly ℤ θ`.
-/
theorem ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    ramificationIdx
      ((primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) ℤ =
          multiplicity (Q.map (Int.castRingHom (ZMod p)))
            ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  rw [ramificationIdx_eq_multiplicity (span {↑p}) _ (map_ne_bot_of_ne_bot (by simp [NeZero.ne p]))]
  · apply multiplicity_eq_of_emultiplicity_eq
    rw [← emultiplicity_map_eq (mapEquiv (Int.quotientSpanNatEquivZMod p).symm),
      emultiplicity_factors_map_eq_emultiplicity inferInstance (by simp [NeZero.ne p])
      (not_dvd_exponent_iff.mp hp).eq_top θ.isIntegral]
    · simp only [primesOverSpanEquivMonicFactorsMod_symm_apply,
        Equiv.apply_symm_apply (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk _ _ _ _),
        Polynomial.map_map, Int.quotientSpanNatEquivZMod_comp_castRingHom, mapEquiv_apply]
    · rw [← mem_primesOver_iff_mem_normalizedFactors _ (by simp [NeZero.ne p])]
      exact ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩).coe_prop
/-
**NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_appl
y'** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Ideal`。
形式化陈述：ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣
 exponent θ) {Q : (ZMod p)[X]} (hQ : Q in monicFactorsMod θ p) : ramificationIdx
 ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) Int = mult
iplicity Q ((minpoly Int θ).map (Int.castRingHom (ZMod p)))
参数：hp : ¬ p ∣ exponent θ；ZMod p；hQ : Q in monicFactorsMod θ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
· 使用定理 `ZMod.ringHom_surjective`：ringHom_surjective [NonAssocRing R] (f : R ->+*
 ZMod n) : Function.Surjective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_sym
m_apply`：ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p
 ∣ exponent θ) {Q : Int[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) in…
-/
theorem ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ p) :
    ramificationIdx
      ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) ℤ =
        multiplicity Q ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  obtain ⟨S, rfl⟩ := (map_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))) Q
  rw [ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply]

end NumberField.Ideal

