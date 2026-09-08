/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Integral and algebraic elements of a fraction field

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


variable {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*} [CommRing S]
variable [Algebra R S]

open Polynomial

namespace IsLocalization

section IntegerNormalization

open Polynomial

variable [IsLocalization M S]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
/-
**IsLocalization.exists_integer_polynomial_multiple_and_support_subset** 是 Mathl
ib 中的一个定理，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_integer_polynomial_multiple_and_support_subset (p : S[X]) :
    ∃ b ∈ M, ∃ (q : R[X]), q.map (algebraMap R S) = b • p ∧ q.support ⊆ p.support := by
  obtain ⟨⟨_, b, hb, rfl⟩, h⟩ := exists_integer_multiple (Submonoid.map C M) p
  rw [Subtype.coe_mk, C_eq_algebraMap, algebraMap_smul] at h
  obtain ⟨q', h₁, h₂⟩ := exists_support_eq_of_mem_lifts h
  exact ⟨b, hb, q', h₁, h₂ ▸ support_smul b p⟩

/-- `integerNormalization p` normalizes `p` to have integer coefficients
by clearing the denominators -/
/-
**IsLocalization.integerNormalization** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`
。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     (M : Submonoid R) →       {S 
: Type u_2} →         [inst_1 : CommRing S] → [inst_2 : Algebra R S] → [IsLocali
zation M S] → Polynomial S → Polynomial R
参数：M : Submonoid R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.Localization.Integral.0.IsLocalization.exist
s_integer_polynomial_multiple_and_support_subset`：∀ {R : Type u_1} [inst : CommR
ing R] (M : Submonoid R) {S : Type u_2} [inst_1 : CommRing S] [inst_2 : Algebra 
R S]   [IsLocalization M S] (p…

--- 原说明 ---
`integerNormalization p` normalizes `p` to have integer coefficients
by clearing the denominators
-/
@[no_expose] noncomputable def integerNormalization (p : S[X]) : R[X] :=
  (exists_integer_polynomial_multiple_and_support_subset M p).choose_spec.2.choose
/-
**IsLocalization.integerNormalization_spec** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliza
tion`。
形式化陈述：integerNormalization_spec (p : S[X]) : exists b in M, (integerNormalizatio
n M p).map (algebraMap R S) = b • p
参数：p : S[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.Localization.Integral.0.IsLocalization.exist
s_integer_polynomial_multiple_and_support_subset`：∀ {R : Type u_1} [inst : CommR
ing R] (M : Submonoid R) {S : Type u_2} [inst_1 : CommRing S] [inst_2 : Algebra 
R S]   [IsLocalization M S] (p…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integerNormalization_spec (p : S[X]) :
    ∃ b ∈ M, (integerNormalization M p).map (algebraMap R S) = b • p :=
  let e := exists_integer_polynomial_multiple_and_support_subset M p
  ⟨e.choose, e.choose_spec.1, e.choose_spec.2.choose_spec.1⟩
/-
**IsLocalization.integerNormalization_support** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
ization`。
形式化陈述：integerNormalization_support (p : S[X]) : (integerNormalization M p).suppo
rt subseteq p.support
参数：p : S[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.RingTheory.Localization.Integral.0.IsLocalization.exist
s_integer_polynomial_multiple_and_support_subset`：∀ {R : Type u_1} [inst : CommR
ing R] (M : Submonoid R) {S : Type u_2} [inst_1 : CommRing S] [inst_2 : Algebra 
R S]   [IsLocalization M S] (p…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem integerNormalization_support (p : S[X]) :
    (integerNormalization M p).support ⊆ p.support :=
  (exists_integer_polynomial_multiple_and_support_subset M p).choose_spec.2.choose_spec.2

/-- `coeffIntegerNormalization p` gives the coefficients of the polynomial
`integerNormalization p` -/
@[deprecated integerNormalization (since := "2026-02-05")]
/-
**IsLocalization.coeffIntegerNormalization** 是 Mathlib 中的一个定义，位于命名空间 `IsLocaliza
tion`。
形式化陈述：coeffIntegerNormalization (p : S[X]) (i : Nat) : R
参数：p : S[X]；i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coeffIntegerNormalization p` gives the coefficients of the polynomial
`integerNormalization p`
-/
noncomputable def coeffIntegerNormalization (p : S[X]) (i : ℕ) : R :=
  (integerNormalization M p).coeff i

@[deprecated integerNormalization_support (since := "2026-02-05")]
/-
**IsLocalization.coeffIntegerNormalization_of_coeff_zero** 是 Mathlib 中的一个定理，位于命名
空间 `IsLocalization`。
形式化陈述：coeffIntegerNormalization_of_coeff_zero (p : S[X]) (i : Nat) (h : coeff p 
i = 0) : coeffIntegerNormalization M p i = 0
参数：p : S[X]；i : Nat；h : coeff p i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.notMem_support_iff`：notMem_support_iff : n ∉ p.support ↔ p.co
eff n = 0
· 使用定理 `Finset.not_mem_subset`：∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → ∀ {a :
 α}, a ∉ t → a ∉ s
· 使用定理 `IsLocalization.integerNormalization_support`：integerNormalization_suppor
t (p : S[X]) : (integerNormalization M p).support subseteq p.support
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem coeffIntegerNormalization_of_coeff_zero (p : S[X]) (i : ℕ) (h : coeff p i = 0) :
    coeffIntegerNormalization M p i = 0 :=
  notMem_support_iff.mp <| Finset.not_mem_subset (integerNormalization_support M p) <|
    notMem_support_iff.mpr h

@[deprecated integerNormalization_support (since := "2026-02-05")]
/-
**IsLocalization.coeffIntegerNormalization_mem_support** 是 Mathlib 中的一个定理，位于命名空间
 `IsLocalization`。
形式化陈述：coeffIntegerNormalization_mem_support (p : S[X]) (i : Nat) (h : coeffInteg
erNormalization M p i != 0) : i in p.support
参数：p : S[X]；i : Nat；h : coeffIntegerNormalization M p i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `IsLocalization.coeffIntegerNormalization_of_coeff_zero`：coeffIntegerNorm
alization_of_coeff_zero (p : S[X]) (i : Nat) (h : coeff p i = 0) : coeffIntegerN
ormalization M p i = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem coeffIntegerNormalization_mem_support (p : S[X]) (i : ℕ)
    (h : coeffIntegerNormalization M p i ≠ 0) : i ∈ p.support := by
  contrapose h
  simp only [mem_support_iff, ne_eq, not_not] at h
  exact coeffIntegerNormalization_of_coeff_zero M p i h

@[deprecated integerNormalization_spec (since := "2026-02-05")]
/-
**IsLocalization.integerNormalization_coeff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliz
ation`。
形式化陈述：integerNormalization_coeff (p : S[X]) (i : Nat) : (integerNormalization M 
p).coeff i = coeffIntegerNormalization M p i
参数：p : S[X]；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integerNormalization_coeff (p : S[X]) (i : ℕ) :
    (integerNormalization M p).coeff i = coeffIntegerNormalization M p i :=
  rfl

variable {M} in
/-
**IsLocalization.integerNormalization_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsL
ocalization`。
形式化陈述：integerNormalization_eq_zero_iff [IsDomain R] (hM : M <= nonZeroDivisors R
) (p : S[X]) : integerNormalization M p = 0 ↔ p = 0
参数：hM : M <= nonZeroDivisors R；p : S[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.integerNormalization_spec`：integerNormalization_spec (p :
 S[X]) : exists b in M, (integerNormalization M p).map (algebraMap R S) = b • p
· 使用定理 `IsLocalization.isDomain_of_le_nonZeroDivisors`：isDomain_of_le_nonZeroDiv
isors (hM : M <= nonZeroDivisors R) : IsDomain S where __ : IsCancelMulZero S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `Polynomial.map_injective_iff`：map_injective_iff : Function.Injective (ma
p f) ↔ Function.Injective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `Polynomial.instIsTorsionFree`：∀ {R : Type u} [inst : Semiring R] {S : Ty
pe u_1} [inst_1 : Semiring S] [inst_2 : _root_.Module S R]   [Module.IsTorsionFr
ee S R], Module.Is…
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
-/
theorem integerNormalization_eq_zero_iff [IsDomain R] (hM : M ≤ nonZeroDivisors R) (p : S[X]) :
    integerNormalization M p = 0 ↔ p = 0 := by
  obtain ⟨_, hb₁, hb₂⟩ := integerNormalization_spec M p
  let := isDomain_of_le_nonZeroDivisors S hM
  let := (faithfulSMul_iff_algebraMap_injective R S).mpr <| IsLocalization.injective S hM
  let : Function.Injective <| mapRingHom (algebraMap R S) := by
    rw [coe_mapRingHom, map_injective_iff]
    exact IsLocalization.injective S hM
  rw [← _root_.map_eq_zero_iff (mapRingHom (algebraMap R S)) this, coe_mapRingHom, hb₂]
  exact smul_eq_zero_iff_right <| nonZeroDivisors.ne_zero (hM hb₁)

@[deprecated integerNormalization_spec (since := "2026-02-05")]
/-
**IsLocalization.integerNormalization_map_to_map** 是 Mathlib 中的一个定理，位于命名空间 `IsLo
calization`。
形式化陈述：integerNormalization_map_to_map (p : S[X]) : exists b : M, (integerNormali
zation M p).map (algebraMap R S) = (b : R) • p
参数：p : S[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.integerNormalization_spec`：integerNormalization_spec (p :
 S[X]) : exists b in M, (integerNormalization M p).map (algebraMap R S) = b • p
-/
theorem integerNormalization_map_to_map (p : S[X]) :
    ∃ b : M, (integerNormalization M p).map (algebraMap R S) = (b : R) • p := by
  obtain ⟨b, hb₁, hb₂⟩ := integerNormalization_spec M p
  exact ⟨⟨b, hb₁⟩, hb₂⟩

variable {R' : Type*} [CommRing R']
/-
**IsLocalization.integerNormalization_eval** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliza
tion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integerNormalization_eval₂_eq_zero (g : S →+* R') (p : S[X]) {x : R'}
    (hx : eval₂ g x p = 0) : eval₂ (g.comp (algebraMap R S)) x (integerNormalization M p) = 0 :=
  let ⟨b, hb₁, hb₂⟩ := integerNormalization_spec M p
  _root_.trans (eval₂_map (algebraMap R S) g x).symm
    (by rw [hb₂, ← IsScalarTower.algebraMap_smul S b p, eval₂_smul, hx, mul_zero])
/-
**IsLocalization.integerNormalization_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `I
sLocalization`。
形式化陈述：integerNormalization_aeval_eq_zero [Algebra R R'] [Algebra S R'] [IsScalar
Tower R S R'] (p : S[X]) {x : R'} (hx : aeval x p = 0) : aeval x (integerNormali
zation M p) = 0
参数：p : S[X]；hx : aeval x p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `IsLocalization.integerNormalization_eval₂_eq_zero`：integerNormalization_
eval₂_eq_zero (g : S ->+* R') (p : S[X]) {x : R'} (hx : eval₂ g x p = 0) : eval₂
 (g.comp (algebraMap R S)) x (integerNo…
-/
theorem integerNormalization_aeval_eq_zero [Algebra R R'] [Algebra S R'] [IsScalarTower R S R']
    (p : S[X]) {x : R'} (hx : aeval x p = 0) : aeval x (integerNormalization M p) = 0 := by
  rwa [aeval_def, IsScalarTower.algebraMap_eq R S R', integerNormalization_eval₂_eq_zero]

end IntegerNormalization

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable {A K C : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
variable [CommRing C]

/-
**IsFractionRing.integerNormalization_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsF
ractionRing`。
形式化陈述：integerNormalization_eq_zero_iff {p : K[X]} : integerNormalization (nonZer
oDivisors A) p = 0 ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.integerNormalization_eq_zero_iff`：integerNormalization_eq
_zero_iff [IsDomain R] (hM : M <= nonZeroDivisors R) (p : S[X]) : integerNormali
zation M p = 0 ↔ p = 0
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem integerNormalization_eq_zero_iff {p : K[X]} :
    integerNormalization (nonZeroDivisors A) p = 0 ↔ p = 0 :=
  IsLocalization.integerNormalization_eq_zero_iff le_rfl p

variable (A K C)

/-- An element of a ring is algebraic over the ring `A` iff it is algebraic
over the field of fractions of `A`.
-/
/-
**IsFractionRing.isAlgebraic_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] {x : C} 
: IsAlgebraic A x ↔ IsAlgebraic K x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsFractionRing.to_map_eq_zero_iff`：to_map_eq_zero_iff {x : R} : algebraM
ap R K x = 0 ↔ x = 0
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `IsFractionRing.integerNormalization_eq_zero_iff`：integerNormalization_eq
_zero_iff {p : K[X]} : integerNormalization (nonZeroDivisors A) p = 0 ↔ p = 0
· 使用定理 `IsLocalization.integerNormalization_aeval_eq_zero`：integerNormalization_
aeval_eq_zero [Algebra R R'] [Algebra S R'] [IsScalarTower R S R'] (p : S[X]) {x
 : R'} (hx : aeval x p = 0) : aeval x (…

--- 原说明 ---
An element of a ring is algebraic over the ring `A` iff it is algebraic
over the field of fractions of `A`.
-/
theorem isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] {x : C} :
    IsAlgebraic A x ↔ IsAlgebraic K x := by
  constructor <;> rintro ⟨p, hp, px⟩
  · refine ⟨p.map (algebraMap A K), fun h => hp (Polynomial.ext fun i => ?_), ?_⟩
    · have : algebraMap A K (p.coeff i) = 0 :=
        _root_.trans (Polynomial.coeff_map _ _).symm (by simp [h])
      exact to_map_eq_zero_iff.mp this
    · exact (Polynomial.aeval_map_algebraMap K _ _).trans px
  · exact
      ⟨integerNormalization _ p, mt integerNormalization_eq_zero_iff.mp hp,
        integerNormalization_aeval_eq_zero _ p px⟩

variable {A K C}

/-- A ring is algebraic over the ring `A` iff it is algebraic over the field of fractions of `A`.
-/
/-
**IsFractionRing.comap_isAlgebraic_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing
`。
形式化陈述：comap_isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] : 
Algebra.IsAlgebraic A C ↔ Algebra.IsAlgebraic K C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsFractionRing.isAlgebraic_iff`：isAlgebraic_iff [Algebra A C] [Algebra K
 C] [IsScalarTower A K C] {x : C} : IsAlgebraic A x ↔ IsAlgebraic K x
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
A ring is algebraic over the ring `A` iff it is algebraic over the field of frac
tions of `A`.
-/
theorem comap_isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] :
    Algebra.IsAlgebraic A C ↔ Algebra.IsAlgebraic K C :=
  ⟨fun h => ⟨fun x => (isAlgebraic_iff A K C).mp (h.isAlgebraic x)⟩,
   fun h => ⟨fun x => (isAlgebraic_iff A K C).mpr (h.isAlgebraic x)⟩⟩

end IsFractionRing

open IsLocalization

section IsIntegral

variable {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]
variable [Algebra R Rₘ] [IsLocalization M Rₘ]
variable [Algebra S Sₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable {M}

open Polynomial

/-
**RingHom.isIntegralElem_localization_at_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：RingHom.isIntegralElem_localization_at_leadingCoeff {R S : Type*} [CommSem
iring R] [CommSemiring S] (f : R ->+* S) (x : S) (p : R[X]) (hf : p.eval₂ f x = 
0) (M : Submonoid R) (hM : p.leadingCoeff in M) {Rₘ Sₘ : Type*} [CommRing Rₘ] [C
ommRing Sₘ] [Algebra R Rₘ] [IsLocalization M Rₘ] [Algebra S Sₘ] [IsLocalization 
(M.map f : Submonoid S) Sₘ] : (map Sₘ f M.le_comap_map : Rₘ ->+* _).IsIntegralEl
em (algebraMap S Sₘ x)
参数：f : R ->+* S；x : S；p : R[X]；hf : p.eval₂ f x = 0；M : Submonoid R；hM : p.leadi
ngCoeff in M；M.map f : Submonoid S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Polynomial.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R[X]
) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval₂_zero`：eval₂_zero : (0 : R[X]).eval₂ f x = 0
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one`：monic_mul_C_of_leadin
gCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) : Monic (p * C b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero`：leadingCoeff_map_of
_leadingCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : leadingCoe
ff (p.map f) = f (leadingCoeff p)
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.eval₂_mul_eq_zero_of_left`：eval₂_mul_eq_zero_of_left (q : R[X
]) (hp : p.eval₂ f x = 0) : (p * q).eval₂ f x = 0
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `Polynomial.hom_eval₂`：hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.c
omp f) (g x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
theorem RingHom.isIntegralElem_localization_at_leadingCoeff {R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (x : S) (p : R[X]) (hf : p.eval₂ f x = 0) (M : Submonoid R)
    (hM : p.leadingCoeff ∈ M) {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ]
    [IsLocalization M Rₘ] [Algebra S Sₘ] [IsLocalization (M.map f : Submonoid S) Sₘ] :
    (map Sₘ f M.le_comap_map : Rₘ →+* _).IsIntegralElem (algebraMap S Sₘ x) := by
  by_cases triv : (1 : Rₘ) = 0
  · exact ⟨0, ⟨_root_.trans leadingCoeff_zero triv.symm, eval₂_zero _ _⟩⟩
  have : Nontrivial Rₘ := nontrivial_of_ne 1 0 triv
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (map_units Rₘ ⟨p.leadingCoeff, hM⟩)
  refine ⟨p.map (algebraMap R Rₘ) * C b, ⟨?_, ?_⟩⟩
  · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    rwa [leadingCoeff_map_of_leadingCoeff_ne_zero (algebraMap R Rₘ)]
    refine fun hfp => zero_ne_one
      (_root_.trans (zero_mul b).symm (hfp ▸ hb) : (0 : Rₘ) = 1)
  · refine eval₂_mul_eq_zero_of_left _ _ _ ?_
    rw [eval₂_map, IsLocalization.map_comp, ← hom_eval₂ _ f (algebraMap S Sₘ) x]
    exact _root_.trans (congr_arg (algebraMap S Sₘ) hf) (map_zero _)

/-- Given a particular witness to an element being algebraic over an algebra `R → S`,
We can localize to a submonoid containing the leading coefficient to make it integral.
Explicitly, the map between the localizations will be an integral ring morphism -/
/-
**is_integral_localization_at_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：is_integral_localization_at_leadingCoeff {x : S} (p : R[X]) (hp : aeval x 
p = 0) (hM : p.leadingCoeff in M) : (map Sₘ (algebraMap R S) (show _ <= (Algebra
.algebraMapSubmonoid S M).comap _ from M.le_comap_map) : Rₘ ->+* _).IsIntegralEl
em (algebraMap S Sₘ x)
参数：p : R[X]；hp : aeval x p = 0；hM : p.leadingCoeff in M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isIntegralElem_localization_at_leadingCoeff`：RingHom.isIntegralE
lem_localization_at_leadingCoeff {R S : Type*} [CommSemiring R] [CommSemiring S]
 (f : R ->+* S) (x : S) (p : R[X]) (hf : …

--- 原说明 ---
Given a particular witness to an element being algebraic over an algebra `R → S`
,
We can localize to a submonoid containing the leading coefficient to make it int
egral.
Explicitly, the map between the localizations will be an integral ring morphism
-/
theorem is_integral_localization_at_leadingCoeff {x : S} (p : R[X]) (hp : aeval x p = 0)
    (hM : p.leadingCoeff ∈ M) :
    (map Sₘ (algebraMap R S)
            (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
          Rₘ →+* _).IsIntegralElem
      (algebraMap S Sₘ x) :=
  haveI : IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ)
  (algebraMap R S).isIntegralElem_localization_at_leadingCoeff x p hp M hM

/-- If `R → S` is an integral extension, `M` is a submonoid of `R`,
`Rₘ` is the localization of `R` at `M`,
and `Sₘ` is the localization of `S` at the image of `M` under the extension map,
then the induced map `Rₘ → Sₘ` is also an integral extension -/
/-
**isIntegral_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_localization [Algebra.IsIntegral R S] : (map Sₘ (algebraMap R S
) (show _ <= (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) : Rₘ
 ->+* _).IsIntegral
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_exists_inv'`：isUnit_iff_exists_inv' [Monoid M] [IsDedekindFin
iteMonoid M] {a : M} : IsUnit a ↔ exists b, b * a = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsIntegral.of_mul_unit`：IsIntegral.of_mul_unit {x y : B} {r : R} (hr : a
lgebraMap R B r * y = 1) (hx : IsIntegral R (x * y)) : IsIntegral R x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `localizationAlgebraMap_def`：localizationAlgebraMap_def : @algebraMap Rₘ 
Sₘ _ _ (localizationAlgebra M S) = map Sₘ (algebraMap R S) (show _ <= (Algebra.a
lgebraMapSubmono…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `is_integral_localization_at_leadingCoeff`：is_integral_localization_at_le
adingCoeff {x : S} (p : R[X]) (hp : aeval x p = 0) (hM : p.leadingCoeff in M) : 
(map Sₘ (algebraMap R S) (show…
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `R → S` is an integral extension, `M` is a submonoid of `R`,
`Rₘ` is the localization of `R` at `M`,
and `Sₘ` is the localization of `S` at the image of `M` under the extension map,
then the induced map `Rₘ → Sₘ` is also an integral extension
-/
theorem isIntegral_localization [Algebra.IsIntegral R S] :
    (map Sₘ (algebraMap R S)
          (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
        Rₘ →+* _).IsIntegral := by
  intro x
  obtain ⟨⟨s, ⟨u, hu⟩⟩, hx⟩ := surj (Algebra.algebraMapSubmonoid S M) x
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := isUnit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩)
  refine @IsIntegral.of_mul_unit Rₘ _ _ _ (localizationAlgebra M S) x (algebraMap S Sₘ u) v' ?_ ?_
  · replace hv' := congr_arg (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) hv'
    rw [map_mul, map_one, localizationAlgebraMap_def, IsLocalization.map_eq] at hv'
    exact hv.2 ▸ hv'
  · obtain ⟨p, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    exact hx.symm ▸ is_integral_localization_at_leadingCoeff p hp.2 (hp.1.symm ▸ M.one_mem)
/-
**isIntegral_localization'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_localization' {R S : Type*} [CommRing R] [CommRing S] {f : R ->
+* S} (hf : f.IsIntegral) (M : Submonoid R) : (map (Localization (M.map (f : R -
>* S))) f (M.le_comap_map : _ <= Submonoid.comap (f : R ->* S) _) : Localization
 M ->+* _).IsIntegral
参数：hf : f.IsIntegral；M : Submonoid R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `isIntegral_localization`：isIntegral_localization [Algebra.IsIntegral R S
] : (map Sₘ (algebraMap R S) (show _ <= (Algebra.algebraMapSubmonoid S M).comap 
_ from M.le_c…
-/
theorem isIntegral_localization' {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.IsIntegral) (M : Submonoid R) :
    (map (Localization (M.map (f : R →* S))) f
          (M.le_comap_map : _ ≤ Submonoid.comap (f : R →* S) _) :
        Localization M →+* _).IsIntegral :=
  let _ := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid S M)
    (Localization (Submonoid.map (f : R →* S) M)) := Localization.isLocalization
  isIntegral_localization

variable (M)
/-
**IsLocalization.scaleRoots_commonDenom_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.scaleRoots_commonDenom_mem_lifts (p : Rₘ[X]) (hp : p.leadin
gCoeff in (algebraMap R Rₘ).range) : p.scaleRoots (algebraMap R Rₘ <| IsLocaliza
tion.commonDenom M p.support p.coeff) in Polynomial.lifts (algebraMap R Rₘ)
参数：p : Rₘ[X]；hp : p.leadingCoeff in (algebraMap R Rₘ).range。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.lifts_iff_coeff_lifts`：lifts_iff_coeff_lifts (p : S[X]) : p i
n lifts f ↔ forall n : Nat, p.coeff n in Set.range f
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_tsub_of_add_le_left`：le_tsub_of_add_le_left (h : a + b <= c) : b <= c
 - a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `RingHom.mem_range_self`：mem_range_self (f : R ->+* S) (x : R) : f x in f
.range
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
（共 36 条，此处仅展示前 30 条）
-/
theorem IsLocalization.scaleRoots_commonDenom_mem_lifts (p : Rₘ[X])
    (hp : p.leadingCoeff ∈ (algebraMap R Rₘ).range) :
    p.scaleRoots (algebraMap R Rₘ <| IsLocalization.commonDenom M p.support p.coeff) ∈
      Polynomial.lifts (algebraMap R Rₘ) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.coeff_scaleRoots]
  by_cases h₁ : n ∈ p.support
  on_goal 1 => by_cases h₂ : n = p.natDegree
  · rwa [h₂, Polynomial.coeff_natDegree, tsub_self, pow_zero, _root_.mul_one]
  · have : n + 1 ≤ p.natDegree := lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp _ h₁) h₂
    rw [← tsub_add_cancel_of_le (le_tsub_of_add_le_left this), pow_add, pow_one, mul_comm,
      _root_.mul_assoc, ← map_pow]
    change _ ∈ (algebraMap R Rₘ).range
    apply mul_mem
    · exact RingHom.mem_range_self _ _
    · rw [← Algebra.smul_def]
      exact ⟨_, IsLocalization.map_integerMultiple M p.support p.coeff ⟨n, h₁⟩⟩
  · rw [Polynomial.notMem_support_iff] at h₁
    rw [h₁, zero_mul]
    exact zero_mem (algebraMap R Rₘ).range
/-
**IsIntegral.exists_multiple_integral_of_isLocalization** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：IsIntegral.exists_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsSc
alarTower R Rₘ S] (x : S) (hx : IsIntegral Rₘ x) : exists m : M, IsIntegral R (m
 • x)
参数：x : S；hx : IsIntegral Rₘ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `RingHom.codomain_trivial`：codomain_trivial (f : α ->+* β) [h : Subsingle
ton α] : Subsingleton β
· 使用定理 `Polynomial.monic_X`：monic_X : Monic (X : R[X])
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Polynomial.lifts_and_natDegree_eq_and_monic`：lifts_and_natDegree_eq_and_
monic {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic) : exists q : R[X], map f
 q = p ∧ q.natDegree = p.natDegre…
· 使用定理 `IsLocalization.scaleRoots_commonDenom_mem_lifts`：IsLocalization.scaleRoo
ts_commonDenom_mem_lifts (p : Rₘ[X]) (hp : p.leadingCoeff in (algebraMap R Rₘ).r
ange) : p.scaleRoots (algebraMap R Rₘ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Polynomial.monic_scaleRoots_iff`：monic_scaleRoots_iff {p : R[X]} (s : R)
 : Monic (scaleRoots p s) ↔ Monic p
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Polynomial.scaleRoots_eval₂_eq_zero`：scaleRoots_eval₂_eq_zero {p : S[X]}
 (f : S ->+* R) {r : R} {s : S} (hr : eval₂ f r p = 0) : eval₂ f (f s * r) (scal
eRoots p s) = 0
-/
theorem IsIntegral.exists_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsScalarTower R Rₘ S]
    (x : S) (hx : IsIntegral Rₘ x) : ∃ m : M, IsIntegral R (m • x) := by
  rcases subsingleton_or_nontrivial Rₘ with _ | nontriv
  · have := (algebraMap Rₘ S).codomain_trivial
    exact ⟨1, Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
  obtain ⟨p, hp₁, hp₂⟩ := hx
  -- Porting note: obtain doesn't support side goals
  have :=
    lifts_and_natDegree_eq_and_monic (IsLocalization.scaleRoots_commonDenom_mem_lifts M p ?_) ?_
  · obtain ⟨p', hp'₁, -, hp'₂⟩ := this
    refine ⟨IsLocalization.commonDenom M p.support p.coeff, p', hp'₂, ?_⟩
    rw [IsScalarTower.algebraMap_eq R Rₘ S, ← Polynomial.eval₂_map, hp'₁, Submonoid.smul_def,
      Algebra.smul_def, IsScalarTower.algebraMap_apply R Rₘ S]
    exact Polynomial.scaleRoots_eval₂_eq_zero _ hp₂
  · rw [hp₁.leadingCoeff]
    exact one_mem _
  · rwa [Polynomial.monic_scaleRoots_iff]

/-- If `t` is `R`-integral in `S[M⁻¹]` where `M` is a submonoid of `R`,
then `m • t` is integral in `S` for some `m ∈ M`. -/
/-
**IsLocalization.exists_isIntegral_smul_of_isIntegral_map** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：IsLocalization.exists_isIntegral_smul_of_isIntegral_map {R S Sₘ : Type*} [
CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ] [Algebra R S
ₘ] [IsScalarTower R S Sₘ] (M : Submonoid R) [IsLocalization (Algebra.algebraMapS
ubmonoid S M) Sₘ] {x : S} (hx : IsIntegral R (algebraMap S Sₘ x)) : exists m in 
M, IsIntegral R (m • x)
参数：M : Submonoid R；Algebra.algebraMapSubmonoid S M；hx : IsIntegral R (algebraMap
 S Sₘ x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Polynomial.leadingCoeff_mul_monic`：leadingCoeff_mul_monic {p q : R[X]} (
hq : Monic q) : leadingCoeff (p * q) = leadingCoeff p
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `RingHom.isIntegralElem_leadingCoeff_mul`：RingHom.isIntegralElem_leadingC
oeff_mul (h : p.eval₂ f x = 0) : f.IsIntegralElem (f p.leadingCoeff * x)
· 使用定理 `Polynomial.eval₂_mul`：eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.ev
al₂ f x
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a

--- 原说明 ---
If `t` is `R`-integral in `S[M⁻¹]` where `M` is a submonoid of `R`,
then `m • t` is integral in `S` for some `m ∈ M`.
-/
lemma IsLocalization.exists_isIntegral_smul_of_isIntegral_map
    {R S Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] (M : Submonoid R)
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] {x : S}
    (hx : IsIntegral R (algebraMap S Sₘ x)) : ∃ m ∈ M, IsIntegral R (m • x) := by
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid S M), Algebra.algebraMapSubmonoid,
    Subtype.exists, Submonoid.mem_map, exists_prop, exists_exists_and_eq_and] at hp
  obtain ⟨m, hm, e⟩ := hp
  exact ⟨m, hm, by simpa [Algebra.smul_def, leadingCoeff_mul_monic hpm] using!
    RingHom.isIntegralElem_leadingCoeff_mul (algebraMap R S) (C m * p) x (by simpa)⟩

/-- If `t` is `R`-integral in `S[1/r]` where `r : S` is integral over `R`,
then `r ^ n • t` is integral in `S` for some `n`. -/
/-
**IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap** 是 Mathlib
 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap {R S Sₘ
 : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ] [
Algebra R Sₘ] [IsScalarTower R S Sₘ] {r : S} (hr : IsIntegral R r) [IsLocalizati
on.Away r Sₘ] {x : S} (hx : IsIntegral R (algebraMap S Sₘ x)) : exists n, IsInte
gral R (r ^ n * x)
参数：hr : IsIntegral R r；hx : IsIntegral R (algebraMap S Sₘ x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `isIntegral_leadingCoeff_smul`：isIntegral_leadingCoeff_smul [Algebra R S]
 (h : aeval x p = 0) : IsIntegral R (p.leadingCoeff • x)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `Polynomial.Monic.leadingCoeff_C_mul`：∀ {R : Type u} [inst : Semiring R] 
{p : Polynomial R}, p.Monic → ∀ (r : R), (Polynomial.C r * p).leadingCoeff = r
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `t` is `R`-integral in `S[1/r]` where `r : S` is integral over `R`,
then `r ^ n • t` is integral in `S` for some `n`.
-/
lemma IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap
    {R S Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] {r : S} (hr : IsIntegral R r)
    [IsLocalization.Away r Sₘ] {x : S}
    (hx : IsIntegral R (algebraMap S Sₘ x)) : ∃ n, IsIntegral R (r ^ n * x) := by
  nontriviality S
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (.powers r), Subtype.exists, Submonoid.mem_powers_iff,
    exists_prop, exists_exists_eq_and] at hp
  obtain ⟨m, hm⟩ := hp
  have := isIntegral_trans (R := R) _ (isIntegral_leadingCoeff_smul (R := integralClosure R S)
    (C ⟨r, hr⟩ ^ m * p.map (algebraMap _ _)) x (by simpa [← aeval_def] using hm))
  rw [← map_pow, (hpm.map _).leadingCoeff_C_mul] at this
  exact ⟨m, this⟩
/-
**IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_mk'** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_mk' {R S Sₘ : Type
*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ] [Algebra
 R Sₘ] [IsScalarTower R S Sₘ] {r : S} (hr : IsIntegral R r) [IsLocalization.Away
 r Sₘ] {x : S} {a : Submonoid.powers r} (hx : IsIntegral R (IsLocalization.mk' S
ₘ x a)) : exists n, IsIntegral R (r ^ n * x)
参数：hr : IsIntegral R r；hx : IsIntegral R (IsLocalization.mk' Sₘ x a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用引理 `IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap`：IsLo
calization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap {R S Sₘ : Type*} 
[CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [A…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_spec'_mk`：∀ {R : Type u_1} [inst : CommSemiring R] {M
 : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S
] [inst_3 : IsLoc…
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `IsIntegral.pow`：IsIntegral.pow {x : B} (h : IsIntegral R x) (n : Nat) : 
IsIntegral R (x ^ n)
-/
lemma IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_mk'
    {R S Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] {r : S} (hr : IsIntegral R r)
    [IsLocalization.Away r Sₘ] {x : S} {a : Submonoid.powers r}
    (hx : IsIntegral R (IsLocalization.mk' Sₘ x a)) : ∃ n, IsIntegral R (r ^ n * x) := by
  refine IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap (Sₘ := Sₘ) hr ?_
  obtain ⟨_, ⟨n, rfl⟩⟩ := a
  convert! (hr.pow n).algebraMap.mul hx
  exact (mk'_spec'_mk ..).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- If `t` is integral over `R[1/t]`, then it is integral over `R`. -/
/-
**isIntegral_of_isIntegral_adjoin_of_mul_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegral_of_isIntegral_adjoin_of_mul_eq_one (t s : S) (hst : s * t = 1) 
(ht : IsIntegral (Algebra.adjoin R {s}) t) : IsIntegral R t
参数：t s : S；hst : s * t = 1；ht : IsIntegral (Algebra.adjoin R {s}) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.lifts_iff_coeff_lifts`：lifts_iff_coeff_lifts (p : S[X]) : p i
n lifts f ↔ forall n : Nat, p.coeff n in Set.range f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Polynomial.lifts_and_degree_eq_and_monic`：lifts_and_degree_eq_and_monic 
[Nontrivial S] {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic) : exists q : R[
X], map f q = p ∧ q.degree = p…
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_reflect_mul_pow`：eval₂_reflect_mul_pow (i : R ->+* S) (
x : S) [Invertible x] (N : Nat) (f : R[X]) (hf : f.natDegree <= N) : eval₂ i (⅟x
) (reflect N f) * x ^ …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Polynomial.natDegree_reflect_le`：natDegree_reflect_le {N : Nat} {p : R[X
]} : (p.reflect N).natDegree <= max N p.natDegree
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.reflect_reflect`：∀ {R : Type u_1} [inst : Semiring R] {N : ℕ}
 {p : Polynomial R}, Polynomial.reflect N (Polynomial.reflect N p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.monic_of_natDegree_le_of_coeff_eq_one`：monic_of_natDegree_le_
of_coeff_eq_one (n : Nat) (pn : p.natDegree <= n) (p1 : p.coeff n = 1) : Monic p
（共 89 条，此处仅展示前 30 条）

--- 原说明 ---
If `t` is integral over `R[1/t]`, then it is integral over `R`.
-/
lemma isIntegral_of_isIntegral_adjoin_of_mul_eq_one
    (t s : S) (hst : s * t = 1) (ht : IsIntegral (Algebra.adjoin R {s}) t) :
    IsIntegral R t := by
  nontriviality S
  let φ := aeval (R := R) s
  obtain ⟨q, hqm, hqt⟩ : φ.IsIntegralElem t := by
    obtain ⟨p, hpm, hpt⟩ := ht
    have : p.map (algebraMap _ S) ∈ lifts φ.toRingHom := (lifts_iff_coeff_lifts _).mpr
      (by simp [← AlgHom.mem_range, φ, ← Algebra.adjoin_singleton_eq_range_aeval])
    obtain ⟨q, hqp, hqd, hqm⟩ := lifts_and_degree_eq_and_monic this (hpm.map _)
    exact ⟨q, hqm, by rw [← eval_map, hqp, eval_map, hpt]⟩
  let N := q.support.sup (q.coeff · |>.natDegree)
  have hN (i : _) : (q.coeff i).natDegree ≤ N := by
    by_cases hi : i ∈ q.support
    · exact Finset.le_sup (f := (q.coeff · |>.natDegree)) hi
    · simp_all
  let q' := q.sum fun i r ↦ X ^ i * r.reflect N
  have (i : _) : aeval t (reflect N (q.coeff i)) = t ^ N * (aeval s (q.coeff i)) := by
    let : Invertible t := ⟨s, hst, (mul_comm _ _).trans hst⟩
    rw [aeval_def, ← eval₂_reflect_mul_pow _ _ N _ ((natDegree_reflect_le ..).trans (by simp [hN]))]
    simp +instances [mul_comm, this, aeval_def]
  refine ⟨q', ?_, ?_⟩
  · refine monic_of_natDegree_le_of_coeff_eq_one (q.natDegree + N) ?_ ?_
    · refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
      grw [natDegree_mul_le, natDegree_pow_le, natDegree_X_le, natDegree_reflect_le]
      simp [max_eq_left (hN _), le_natDegree_of_mem_supp _ hi]
    · simp only [sum, finsetSum_coeff, coeff_X_pow_mul', coeff_reflect, q']
      rw [Finset.sum_eq_single q.natDegree]
      · simp [hqm.leadingCoeff]
      · intro i hi₁ hi₂
        have : N + i < q.natDegree + N :=
          add_comm N i ▸ add_lt_add_left ((le_natDegree_of_mem_supp _ hi₁).lt_of_ne hi₂) _
        simpa [(le_natDegree_of_mem_supp _ hi₁).trans, revAt, this.not_ge] using
          coeff_eq_zero_of_natDegree_lt (by grind)
      · simp +contextual
  · trans t ^ N * q.sum (t ^ · * φ.toRingHom ·)
    · simp [φ, q', Polynomial.sum, ← aeval_def, this, mul_left_comm _ (t ^ N), ← Finset.mul_sum]
    · simp_rw [mul_comm (t ^ _), ← eval₂_eq_sum, hqt, zero_mul]

/-- If `t` is integral in `S[1/t]`, then it is integral in `S`. -/
/-
**IsLocalization.Away.isIntegral_of_isIntegral_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalization.Away.isIntegral_of_isIntegral_map {R S Sₘ : Type*} [CommRin
g R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ] [Algebra R Sₘ] [IsS
calarTower R S Sₘ] (x : S) [IsLocalization.Away x Sₘ] (hx : IsIntegral R (algebr
aMap S Sₘ x)) : IsIntegral R x
参数：x : S；hx : IsIntegral R (algebraMap S Sₘ x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Polynomial.Monic.mul`：∀ {R : Type u} [inst : Semiring R] {p q : Polynomi
al R}, p.Monic → q.Monic → (p * q).Monic
· 使用定理 `Polynomial.monic_X_pow`：monic_X_pow (n : Nat) : Monic (X ^ n : R[X])
· 使用定理 `Polynomial.eval₂_mul`：eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.ev
al₂ f x
· 使用定理 `Polynomial.eval₂_X_pow`：eval₂_X_pow {n : Nat} : (X ^ n).eval₂ f x = x ^ 
n

--- 原说明 ---
If `t` is integral in `S[1/t]`, then it is integral in `S`.
-/
lemma IsLocalization.Away.isIntegral_of_isIntegral_map
    {R S Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] (x : S) [IsLocalization.Away x Sₘ]
    (hx : IsIntegral R (algebraMap S Sₘ x)) : IsIntegral R x := by
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, IsLocalization.map_eq_zero_iff (.powers x),
    Subtype.exists, Submonoid.mem_powers_iff, ← hom_eval₂, exists_prop, exists_exists_eq_and] at hp
  obtain ⟨n, hn⟩ := hp
  exact ⟨X ^ n * p, (monic_X_pow n).mul hpm, by simpa⟩

end IsIntegral

variable {A K : Type*} [CommRing A]

namespace IsIntegralClosure

variable (A)
variable {L : Type*} [Field K] [Field L] [Algebra A K] [Algebra A L] [IsFractionRing A K]
variable (C : Type*) [CommRing C] [IsDomain C] [Algebra C L] [IsIntegralClosure C A L]
variable [Algebra A C] [IsScalarTower A C L]

open Algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
/-
**IsIntegralClosure.isFractionRing_of_algebraic** 是 Mathlib 中的一个定理，位于命名空间 `IsInt
egralClosure`。
形式化陈述：isFractionRing_of_algebraic [Algebra.IsAlgebraic A L] (inj : forall x, alg
ebraMap A L x = 0 -> x = 0) : IsFractionRing C L
参数：inj : forall x, algebraMap A L x = 0 -> x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `IsAlgebraic.exists_integral_multiple`：exists_integral_multiple (hz : IsA
lgebraic R z) : exists y != (0 : R), IsIntegral R (y • z)
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsIntegralClosure.algebraMap_mk'`：algebraMap_mk' (x : B) (hx : IsIntegra
l R x) : algebraMap A B (mk' A x hx) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`.
-/
theorem isFractionRing_of_algebraic [Algebra.IsAlgebraic A L]
    (inj : ∀ x, algebraMap A L x = 0 → x = 0) : IsFractionRing C L :=
  { map_units := fun ⟨y, hy⟩ =>
      IsUnit.mk0 _
        (show algebraMap C L y ≠ 0 from fun h =>
          mem_nonZeroDivisors_iff_ne_zero.mp hy
            ((injective_iff_map_eq_zero (algebraMap C L)).mp (algebraMap_injective C A L) _ h))
    surj := fun z =>
      let ⟨x, hx, int⟩ := (Algebra.IsAlgebraic.isAlgebraic z).exists_integral_multiple
      ⟨⟨mk' C _ int, algebraMap _ _ x, mem_nonZeroDivisors_of_ne_zero fun h ↦
        hx (inj _ <| by rw [IsScalarTower.algebraMap_apply A C L, h, map_zero])⟩, by
        rw [algebraMap_mk', ← IsScalarTower.algebraMap_apply A C L, Algebra.smul_def, mul_comm]⟩
    exists_of_eq := fun {x y} h => ⟨1, by simpa using algebraMap_injective C A L h⟩ }

variable (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
/-
**IsIntegralClosure.isFractionRing_of_finite_extension** 是 Mathlib 中的一个定理，位于命名空间
 `IsIntegralClosure`。
形式化陈述：isFractionRing_of_finite_extension [IsDomain A] [Algebra K L] [IsScalarTow
er A K L] [FiniteDimensional K L] : IsFractionRing C L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsFractionRing.comap_isAlgebraic_iff`：comap_isAlgebraic_iff [Algebra A C
] [Algebra K C] [IsScalarTower A K C] : Algebra.IsAlgebraic A C ↔ Algebra.IsAlge
braic K C
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsIntegralClosure.isFractionRing_of_algebraic`：isFractionRing_of_algebra
ic [Algebra.IsAlgebraic A L] (inj : forall x, algebraMap A L x = 0 -> x = 0) : I
sFractionRing C L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsFractionRing.to_map_eq_zero_iff`：to_map_eq_zero_iff {x : R} : algebraM
ap R K x = 0 ↔ x = 0
· 使用定理 `map_eq_zero`：map_eq_zero : f a = 0 ↔ a = 0
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)

--- 原说明 ---
If the field `L` is a finite extension of the fraction field of the integral dom
ain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`.
-/
theorem isFractionRing_of_finite_extension [IsDomain A] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] : IsFractionRing C L :=
  have : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic K L)
  isFractionRing_of_algebraic A C
    fun _ hx =>
    IsFractionRing.to_map_eq_zero_iff.mp
      ((map_eq_zero <| algebraMap K L).mp <| (IsScalarTower.algebraMap_apply _ _ _ _).symm.trans hx)

end IsIntegralClosure

namespace integralClosure

variable {L : Type*} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]

open Algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
/-
**integralClosure.isFractionRing_of_algebraic** 是 Mathlib 中的一个定理，位于命名空间 `integra
lClosure`。
形式化陈述：isFractionRing_of_algebraic [Algebra A L] [Algebra.IsAlgebraic A L] (inj :
 forall x, algebraMap A L x = 0 -> x = 0) : IsFractionRing (integralClosure A L)
 L
参数：inj : forall x, algebraMap A L x = 0 -> x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isFractionRing_of_algebraic`：isFractionRing_of_algebra
ic [Algebra.IsAlgebraic A L] (inj : forall x, algebraMap A L x = 0 -> x = 0) : I
sFractionRing C L
· 使用定理 `instIsDomainSubtypeMemSubalgebraIntegralClosure`：∀ {R : Type u_1} {S : T
ype u_2} [inst : CommRing R] [inst_1 : CommRing S] [IsDomain S] [inst_3 : Algebr
a R S],   IsDomain ↥(integralClosure …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`.
-/
theorem isFractionRing_of_algebraic [Algebra A L] [Algebra.IsAlgebraic A L]
    (inj : ∀ x, algebraMap A L x = 0 → x = 0) : IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L) inj

variable (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
/-
**integralClosure.isFractionRing_of_finite_extension** 是 Mathlib 中的一个定理，位于命名空间 `
integralClosure`。
形式化陈述：isFractionRing_of_finite_extension [IsDomain A] [Algebra A L] [Algebra K L
] [IsScalarTower A K L] [FiniteDimensional K L] : IsFractionRing (integralClosur
e A L) L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isFractionRing_of_finite_extension`：isFractionRing_of_
finite_extension [IsDomain A] [Algebra K L] [IsScalarTower A K L] [FiniteDimensi
onal K L] : IsFractionRing C L
· 使用定理 `instIsDomainSubtypeMemSubalgebraIntegralClosure`：∀ {R : Type u_1} {S : T
ype u_2} [inst : CommRing R] [inst_1 : CommRing S] [IsDomain S] [inst_3 : Algebr
a R S],   IsDomain ↥(integralClosure …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If the field `L` is a finite extension of the fraction field of the integral dom
ain `A`,
the integral closure of `A` in `L` has fraction field `L`.
-/
theorem isFractionRing_of_finite_extension [IsDomain A] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L] : IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)

end integralClosure

section

variable {Rf Sf : Type*} [CommRing Rf] [CommRing Sf] [Algebra R Rf] [Algebra S Sf]
    [Algebra Rf Sf] [Algebra R Sf] [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]

/-- Taking integral closure commutes with localizations. -/
-- We take in an arbitrary `Algebra (integralClosure R S) (integralClosure Rf Sf)` instance
-- so that it applies more easily.
/-
**IsLocalization.integralClosure** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
[inst_2 : Algebra R S] {Rf : Type u_5}   {Sf : Type u_6} [inst_3 : CommRing Rf] 
[inst_4 : CommRing Sf] [inst_5 : Algebra R Rf] [inst_6 : Algebra S Sf]   [inst_7
 : Algebra Rf Sf] [inst_8 : Algebra R Sf] [IsScalarTower R S Sf] [inst_10 : IsSc
alarTower R Rf Sf]   (M : Submonoid R) [IsLocalization M Rf] [IsLocalization (Al
gebra.algebraMapSubmonoid S M) Sf]   [inst_13 : Algebra ↥(integralClosure R S) ↥
(integralClosure Rf Sf)]   [IsScalarTower (↥(integralClosure R S)) (↥(integralCl
osure Rf Sf)) Sf]   [IsScalarTower R ↥(integralClosure R S) ↥(integralClosure Rf
 Sf)],   IsLocalization (Algebra.algebraMapSubmonoid (↥(integralClosure R S)) M)
 ↥(integralClosure Rf Sf)
参数：M : Submonoid R；Algebra.algebraMapSubmonoid S M；integralClosure R S；integralC
losure Rf Sf；↥(integralClosure R S)；↥(integralClosure Rf Sf)；integralClosure R S
；integralClosure Rf Sf；Algebra.algebraMapSubmonoid (↥(integralClosure R S)) M；in
tegralClosure Rf Sf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `IsIntegral.exists_multiple_integral_of_isLocalization`：IsIntegral.exists
_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsScalarTower R Rₘ S] (x : 
S) (hx : IsIntegral Rₘ x) : exists m : M, I…
· 使用引理 `IsLocalization.exists_isIntegral_smul_of_isIntegral_map`：IsLocalization.
exists_isIntegral_smul_of_isIntegral_map {R S Sₘ : Type*} [CommRing R] [CommRing
 S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Subalgebra.instFaithfulSMulSubtypeMem`：∀ {R : Type u} {A : Type v} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_1}  
 [inst_3 : SMul A α] [Faith…
· 使用定理 `instFaithfulSMul`：∀ (R : Type u_4) [inst : MulOneClass R], FaithfulSMul 
R R
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
（共 47 条，此处仅展示前 30 条）
-/
protected lemma IsLocalization.integralClosure
    (M : Submonoid R) [IsLocalization M Rf] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf]
    [Algebra (integralClosure R S) (integralClosure Rf Sf)]
    [IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf]
    [IsScalarTower R (integralClosure R S) (integralClosure Rf Sf)] :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R S) M)
      (integralClosure Rf Sf) := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, f, hf, rfl⟩
    convert!
      (IsLocalization.map_units (S := Rf) ⟨f, hf⟩).map (algebraMap Rf (integralClosure Rf Sf))
    simp [← IsScalarTower.algebraMap_apply]
  · rintro ⟨s, hs⟩
    obtain ⟨⟨x, _, m₁, hm₁, rfl⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S M) s
    simp only [← IsScalarTower.algebraMap_apply] at e
    obtain ⟨⟨m₂, hm₂⟩, hm₂s⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M _ hs
    simp only [Submonoid.smul_def, Algebra.smul_def] at hm₂s
    obtain ⟨m₃, hm₃, hm₃s⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (Sₘ := Sf)
      M (x := m₂ • x) <| by
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← e, ← mul_assoc]
        exact hm₂s.mul (.algebraMap (Algebra.IsIntegral.isIntegral _))
    refine ⟨⟨⟨_, hm₃s⟩, _, _, mul_mem hm₁ (mul_mem hm₂ hm₃), rfl⟩, ?_⟩
    · apply (FaithfulSMul.algebraMap_injective (integralClosure Rf Sf) Sf)
      simp [← IsScalarTower.algebraMap_apply, e, ← mul_assoc, Algebra.smul_def]
      ring
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ e
    have := congr(algebraMap _ Sf $e)
    have : algebraMap S Sf a = algebraMap S Sf b := by
      simpa only [← IsScalarTower.algebraMap_apply] using! this
    obtain ⟨⟨_, m, hm, rfl⟩, h⟩ :=
      (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S M) _).mp this
    refine ⟨⟨_, m, hm, rfl⟩, FaithfulSMul.algebraMap_injective (integralClosure R S) S ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply]

-- We take in an arbitrary `Algebra (integralClosure R S) (integralClosure Rf Sf)` instance
-- so that it applies more easily.
/-
**IsLocalization.Away.integralClosure** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization.
Away`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
[inst_2 : Algebra R S] {Rf : Type u_5}   {Sf : Type u_6} [inst_3 : CommRing Rf] 
[inst_4 : CommRing Sf] [inst_5 : Algebra R Rf] [inst_6 : Algebra S Sf]   [inst_7
 : Algebra Rf Sf] [inst_8 : Algebra R Sf] [IsScalarTower R S Sf] [inst_10 : IsSc
alarTower R Rf Sf] (f : R)   [IsLocalization.Away f Rf] [IsLocalization.Away ((a
lgebraMap R S) f) Sf]   [inst_13 : Algebra ↥(integralClosure R S) ↥(integralClos
ure Rf Sf)]   [IsScalarTower (↥(integralClosure R S)) (↥(integralClosure Rf Sf))
 Sf]   [IsScalarTower R ↥(integralClosure R S) ↥(integralClosure Rf Sf)],   IsLo
calization.Away ((algebraMap R ↥(integralClosure R S)) f) ↥(integralClosure Rf S
f)
参数：f : R；(algebraMap R S) f；integralClosure R S；integralClosure Rf Sf；↥(integral
Closure R S)；↥(integralClosure Rf Sf)；integralClosure R S；integralClosure Rf Sf；
(algebraMap R ↥(integralClosure R S)) f；integralClosure Rf Sf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.algebraMapSubmonoid_powers`：algebraMapSubmonoid_powers (r : R) :
 Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalization.integralClosure`：∀ {R : Type u_1} [inst : CommRing R] {S 
: Type u_2} [inst_1 : CommRing S] [inst_2 : Algebra R S] {Rf : Type u_5}   {Sf :
 Type u_6} [inst_3 :…
· 使用定理 `IsLocalization.Away.instAlgebraMapSubmonoidPowersOfCoeRingHomAlgebraMap`
：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_5} [inst_1 : CommSemiring 
A] [inst_2 : Algebra R A] (Aₚ : Type u_7)   [inst_3 : CommSem…
-/
protected lemma IsLocalization.Away.integralClosure
    (f : R) [IsLocalization.Away f Rf] [IsLocalization.Away (algebraMap R S f) Sf]
    [Algebra (integralClosure R S) (integralClosure Rf Sf)]
    [IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf]
    [IsScalarTower R (integralClosure R S) (integralClosure Rf Sf)] :
    IsLocalization.Away (algebraMap R (integralClosure R S) f) (integralClosure Rf Sf) := by
  convert! IsLocalization.integralClosure (S := S) (Rf := Rf) (Sf := Sf) (.powers f)
  simp

end
namespace IsFractionRing

variable (R S K)

/-- `S` is algebraic over `R` iff a fraction ring of `S` is algebraic over `R` -/
/-
**IsFractionRing.isAlgebraic_iff'** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：isAlgebraic_iff' [Field K] [IsDomain R] [Algebra R K] [Algebra S K] [Modul
e.IsTorsionFree R K] [IsFractionRing S K] [IsScalarTower R S K] : Algebra.IsAlge
braic R S ↔ Algebra.IsAlgebraic R K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionWithZero.nontrivial`：∀ (M₀ : Type u_2) (A : Type u_7) [inst : M
onoidWithZero M₀] [inst_1 : Zero A] [MulActionWithZero M₀ A] [Nontrivial A],   N
ontrivial M₀
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractionRing.isAlgebraic_iff`：isAlgebraic_iff [Algebra A C] [Algebra K
 C] [IsScalarTower A K C] {x : C} : IsAlgebraic A x ↔ IsAlgebraic K x
· 使用定理 `isAlgebraic_iff_isIntegral`：isAlgebraic_iff_isIntegral {x : A} : IsAlgeb
raic K x ↔ IsIntegral K x
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsAlgebraic.extendScalars`：IsAlgebraic.extendScalars (hinj : Function.In
jective (algebraMap R S)) {x : A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsAlgebraic.algebraMap`：∀ {R : Type u} {S : Type u_1} {A : Type v} [inst
 : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R A] 
[inst_4 : Al…
· 使用定理 `IsIntegral.inv`：IsIntegral.inv (int : IsIntegral R x) : IsIntegral R x⁻¹
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)

--- 原说明 ---
`S` is algebraic over `R` iff a fraction ring of `S` is algebraic over `R`
-/
theorem isAlgebraic_iff' [Field K] [IsDomain R] [Algebra R K] [Algebra S K]
    [Module.IsTorsionFree R K] [IsFractionRing S K] [IsScalarTower R S K] :
    Algebra.IsAlgebraic R S ↔ Algebra.IsAlgebraic R K := by
  simp only [Algebra.isAlgebraic_def]
  constructor
  · intro h x
    let := MulActionWithZero.nontrivial S K
    let := FractionRing.liftAlgebra R K
    have := FractionRing.isScalarTower_liftAlgebra R K
    rw [IsFractionRing.isAlgebraic_iff R (FractionRing R) K, isAlgebraic_iff_isIntegral]
    obtain ⟨a : S, b, ha, rfl⟩ := div_surjective S x
    obtain ⟨f, hf₁, hf₂⟩ := h b
    rw [div_eq_mul_inv]
    refine .mul ?_ (.inv ?_) <;> exact isAlgebraic_iff_isIntegral.mp <|
      (h _).algebraMap.extendScalars (FaithfulSMul.algebraMap_injective R _)
  · intro h x
    obtain ⟨f, hf₁, hf₂⟩ := h (algebraMap S K x)
    use f, hf₁
    rw [Polynomial.aeval_algebraMap_apply] at hf₂
    exact
      (injective_iff_map_eq_zero (algebraMap S K)).1 (FaithfulSMul.algebraMap_injective _ _) _
        hf₂

open nonZeroDivisors

variable {S K}

/-- If the `S`-multiples of `a` are contained in some `R`-span, then `Frac(S)`-multiples of `a`
are contained in the equivalent `Frac(R)`-span. -/
/-
**IsFractionRing.ideal_span_singleton_map_subset** 是 Mathlib 中的一个定理，位于命名空间 `IsFr
actionRing`。
形式化陈述：ideal_span_singleton_map_subset {L : Type*} [IsDomain R] [IsDomain S] [Fie
ld K] [Field L] [Algebra R K] [Algebra R L] [Algebra S L] [Algebra.IsAlgebraic R
 S] [IsFractionRing S L] [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K 
L] {a : S} {b : Set S} (inj : Function.Injective (algebraMap R L)) (h : (Ideal.s
pan ({a} : Set S) : Set S) subseteq Submodule.span R b) : (Ideal.span ({algebraM
ap S L a} : Set L) : Set L) subseteq Submodule.span K (algebraMap S L '' b)
参数：inj : Function.Injective (algebraMap R L)；h : (Ideal.span ({a} : Set S) : Set
 S) subseteq Submodule.span R b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Algebra.IsAlgebraic.exists_smul_eq_mul`：Algebra.IsAlgebraic.exists_smul_
eq_mul [NoZeroDivisors S] [Algebra.IsAlgebraic R S] (a : S) {b : S} (hb : b != 0
) : existsᵉ (c : S) (d != (0…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `map_mem_nonZeroDivisors`：map_mem_nonZeroDivisors [Nontrivial M₀] [NoZero
Divisors M₀'] [ZeroHomClass F M₀ M₀'] (g : F) (hg : Injective g) {x : M₀} (h : x
 in M₀⁰) : g …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `IsLocalization.mk'_eq_of_eq`：∀ {R : Type u_1} [inst : CommSemiring R] {M
 : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S
] [inst_3 : IsLoc…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Submodule.span_subset_span`：span_subset_span : ↑(span R s) subseteq (spa
n S s : Set M)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `Submodule.span_algebraMap_image_of_tower`：span_algebraMap_image_of_tower
 {S T : Type*} [CommSemiring S] [Semiring T] [Module R S] [Algebra R T] [Algebra
 S T] [IsScalarTower R S T] (a…
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If the `S`-multiples of `a` are contained in some `R`-span, then `Frac(S)`-multi
ples of `a`
are contained in the equivalent `Frac(R)`-span.
-/
theorem ideal_span_singleton_map_subset {L : Type*} [IsDomain R] [IsDomain S] [Field K] [Field L]
    [Algebra R K] [Algebra R L] [Algebra S L] [Algebra.IsAlgebraic R S] [IsFractionRing S L]
    [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L] {a : S} {b : Set S}
    (inj : Function.Injective (algebraMap R L))
    (h : (Ideal.span ({a} : Set S) : Set S) ⊆ Submodule.span R b) :
    (Ideal.span ({algebraMap S L a} : Set L) : Set L) ⊆ Submodule.span K (algebraMap S L '' b) := by
  intro x hx
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨y', z', rfl⟩ := IsLocalization.exists_mk'_eq S⁰ x'
  obtain ⟨y, z, hz0, yz_eq⟩ :=
    Algebra.IsAlgebraic.exists_smul_eq_mul R y' (nonZeroDivisors.coe_ne_zero z')
  have injRS : Function.Injective (algebraMap R S) := by
    refine
      Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ algebraMap R S) from ?_)
    rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  have hz0' : algebraMap R S z ∈ S⁰ :=
    map_mem_nonZeroDivisors (algebraMap R S) injRS (mem_nonZeroDivisors_of_ne_zero hz0)
  have mk_yz_eq : IsLocalization.mk' L y' z' = IsLocalization.mk' L y ⟨_, hz0'⟩ := by
    rw [Algebra.smul_def, mul_comm _ y, mul_comm _ y'] at yz_eq
    exact IsLocalization.mk'_eq_of_eq (by rw [mul_comm _ y, mul_comm _ y', yz_eq])
  suffices hy : algebraMap S L (a * y) ∈ Submodule.span K ((algebraMap S L) '' b) by
    rw [mk_yz_eq, IsFractionRing.mk'_eq_div, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K L, div_eq_mul_inv, ← mul_assoc, mul_comm, ← map_inv₀, ←
      Algebra.smul_def, ← map_mul]
    exact (Submodule.span K _).smul_mem _ hy
  refine Submodule.span_subset_span R K _ ?_
  rw [Submodule.span_algebraMap_image_of_tower]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify the value of `f` here:
  exact Submodule.mem_map_of_mem (f := LinearMap.restrictScalars _ _)
    (h (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩))

end IsFractionRing

open nonZeroDivisors in
/-
**isAlgebraic_of_isFractionRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isAlgebraic_of_isFractionRing (R S K L) [CommRing R] [CommRing S] [Field K
] [CommRing L] [Algebra R S] [Algebra R K] [Algebra R L] [Algebra S L] [Algebra 
K L] [IsScalarTower R S L] [IsScalarTower R K L] [IsFractionRing S L] [Algebra.I
sIntegral R S] : Algebra.IsAlgebraic K L
参数：R S K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.mk'_eq_mul_mk'_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…
· 使用定理 `RingHom.IsIntegralElem.mul`：RingHom.IsIntegralElem.mul {x y : S} (hx : f
.IsIntegralElem x) (hy : f.IsIntegralElem y) : f.IsIntegralElem (x * y)
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isAlgebraic_iff_isIntegral`：isAlgebraic_iff_isIntegral {x : A} : IsAlgeb
raic K x ↔ IsIntegral K x
· 使用引理 `IsAlgebraic.invOf_iff`：IsAlgebraic.invOf_iff {x : S} [Invertible x] : Is
Algebraic R (⅟x) ↔ IsAlgebraic R x
-/
lemma isAlgebraic_of_isFractionRing (R S K L) [CommRing R] [CommRing S] [Field K] [CommRing L]
    [Algebra R S] [Algebra R K] [Algebra R L] [Algebra S L] [Algebra K L] [IsScalarTower R S L]
    [IsScalarTower R K L] [IsFractionRing S L]
    [Algebra.IsIntegral R S] : Algebra.IsAlgebraic K L := by
  constructor
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S⁰ x
  apply IsIntegral.isAlgebraic
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  apply RingHom.IsIntegralElem.mul
  · apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact Algebra.IsIntegral.isIntegral x
  · change IsIntegral _ _
    rw [← isAlgebraic_iff_isIntegral, ← IsAlgebraic.invOf_iff, isAlgebraic_iff_isIntegral]
    apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact Algebra.IsIntegral.isIntegral (s : S)
