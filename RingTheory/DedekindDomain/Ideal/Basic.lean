/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Pointwise
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Dedekind domains and invertible ideals

In this file, we show a ring is a Dedekind domain iff all fractional ideals are invertible,
and prove instances such as the unique factorization of ideals.
Further results on the structure of ideals in a Dedekind domain are found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`.

## Main definitions

- `isDedekindDomain_iff_mul_inv_cancel` shows an integral domain is
  a Dedekind domain iff every nonzero fractional ideal is invertible.

## Main results:

- `isDedekindDomain_iff_mul_inv_cancel`
- `Ideal.uniqueFactorizationMonoid`

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

public section Inverse

variable [Algebra A K] [IsFractionRing A K]

variable {A K}

variable {R} [IsDomain A] in
/-
**FractionalIdeal.adjoinIntegral_eq_one_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FractionalIdeal.adjoinIntegral_eq_one_of_isUnit (x : K) (hx : IsIntegral A
 x) (hI : IsUnit (adjoinIntegral A⁰ x hx)) : adjoinIntegral A⁰ x hx = 1
参数：x : K；hx : IsIntegral A x；hI : IsUnit (adjoinIntegral A⁰ x hx)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `Subalgebra.isIdempotentElem_toSubmodule`：isIdempotentElem_toSubmodule (S
 : Subalgebra R A) : IsIdempotentElem S.toSubmodule
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mul_inv_cancel_iff_isUnit`：mul_inv_cancel_iff_isUnit {I 
: FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ IsUnit I
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem FractionalIdeal.adjoinIntegral_eq_one_of_isUnit (x : K)
    (hx : IsIntegral A x) (hI : IsUnit (adjoinIntegral A⁰ x hx)) : adjoinIntegral A⁰ x hx = 1 := by
  set I := adjoinIntegral A⁰ x hx
  have mul_self : IsIdempotentElem I := by
    apply coeToSubmodule_injective
    simp only [coe_mul, adjoinIntegral_coe, I]
    rw [(Algebra.adjoin A {x}).isIdempotentElem_toSubmodule]
  convert! congr_arg (· * I⁻¹) mul_self <;>
    simp only [(mul_inv_cancel_iff_isUnit K).mpr hI, mul_assoc, mul_one]
/-
**FractionalIdeal.one_mem_inv_coe_ideal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FractionalIdeal.one_mem_inv_coe_ideal [IsDomain A] {I : Ideal A} (hI : I !
= ⊥) : (1 : K) in (I : FractionalIdeal A⁰ K)⁻¹
参数：hI : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.mem_inv_iff`：mem_inv_iff (hI : I != 0) {x : K} : x in I⁻
¹ ↔ forall y in I, x * y in (1 : FractionalIdeal R₁⁰ K)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.coeIdeal_ne_zero`：coeIdeal_ne_zero {I : Ideal R} : (I : 
FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `FractionalIdeal.coeIdeal_le_one`：coeIdeal_le_one {I : Ideal R} : (I : Fr
actionalIdeal S P) <= 1
-/
theorem FractionalIdeal.one_mem_inv_coe_ideal [IsDomain A] {I : Ideal A} (hI : I ≠ ⊥) :
    (1 : K) ∈ (I : FractionalIdeal A⁰ K)⁻¹ := by
  rw [mem_inv_iff (coeIdeal_ne_zero.mpr hI)]
  intro y hy
  rw [one_mul]
  exact coeIdeal_le_one hy

@[deprecated (since := "2026-04-16")]
alias one_mem_inv_coe_ideal := FractionalIdeal.one_mem_inv_coe_ideal

/-- Specialization of `exists_primeSpectrum_prod_le_and_ne_bot_of_domain` to Dedekind domains:
Let `I : Ideal A` be a nonzero ideal, where `A` is a Dedekind domain that is not a field.
Then `exists_primeSpectrum_prod_le_and_ne_bot_of_domain` states we can find a product of prime
ideals that is contained within `I`. This lemma extends that result by making the product minimal:
let `M` be a maximal ideal that contains `I`, then the product including `M` is contained within `I`
and the product excluding `M` is not contained within `I`. -/
/-
**PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le [IsDedekindDoma
in A] (hNF : ¬IsField A) {I M : Ideal A} (hI0 : I != ⊥) (hIM : I <= M) [hM : M.I
sMaximal] : exists Z : Multiset (PrimeSpectrum A), (M ::ₘ Z.map asIdeal).prod <=
 I ∧ ¬Multiset.prod (Z.map asIdeal) <= I
参数：hNF : ¬IsField A；hI0 : I != ⊥；hIM : I <= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain`：exists_
primeSpectrum_prod_le_and_ne_bot_of_domain (h_fA : ¬IsField A) {I : Ideal A} (h_
nzI : I != ⊥) : exists Z : Multiset (PrimeSpectrum A)…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.IsPrime.multiset_prod_le`：∀ {R : Type u} [inst : CommSemiring R] {
s : Multiset (Ideal R)} {P : Ideal R}, P.IsPrime → (s.prod ≤ P ↔ ∃ I ∈ s, I ≤ P)
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Multiset.map_erase`：map_erase [DecidableEq α] [DecidableEq β] (f : α -> 
β) (hf : Function.Injective f) (x : α) (s : Multiset α) : (s.erase x).map f = (s
.map f).…
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Ideal.mul_eq_bot`：mul_eq_bot [NoZeroDivisors R] : I * J = ⊥ ↔ I = ⊥ ∨ J 
= ⊥
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Specialization of `exists_primeSpectrum_prod_le_and_ne_bot_of_domain` to Dedekin
d domains:
Let `I : Ideal A` be a nonzero ideal, where `A` is a Dedekind domain that is not
 a field.
Then `exists_primeSpectrum_prod_le_and_ne_bot_of_domain` states we can find a pr
oduct of prime
ideals that is contained within `I`. This lemma extends that result by making th
e product minimal:
let `M` be a maximal ideal that contains `I`, then the product including `M` is 
contained within `I`
and the product excluding `M` is not contained within `I`.
-/
theorem PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le [IsDedekindDomain A]
    (hNF : ¬IsField A) {I M : Ideal A} (hI0 : I ≠ ⊥) (hIM : I ≤ M) [hM : M.IsMaximal] :
    ∃ Z : Multiset (PrimeSpectrum A),
      (M ::ₘ Z.map asIdeal).prod ≤ I ∧
        ¬Multiset.prod (Z.map asIdeal) ≤ I := by
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := exists_primeSpectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    wellFounded_lt.has_min
      {Z | (Z.map asIdeal).prod ≤ I ∧ (Z.map asIdeal).prod ≠ ⊥}
      ⟨Z₀, hZ₀.1, hZ₀.2⟩
  obtain ⟨_, hPZ', hPM⟩ := hM.isPrime.multiset_prod_le.mp (hZI.trans hIM)
  -- Then in fact there is a `P ∈ Z` with `P ≤ M`.
  obtain ⟨P, hPZ, rfl⟩ := Multiset.mem_map.mp hPZ'
  classical
    have := Multiset.map_erase asIdeal (fun _ _ => PrimeSpectrum.ext) P Z
    obtain ⟨hP0, hZP0⟩ : P.asIdeal ≠ ⊥ ∧ ((Z.erase P).map asIdeal).prod ≠ ⊥ := by
      rwa [Ne, ← Multiset.cons_erase hPZ', Multiset.prod_cons, Ideal.mul_eq_bot, not_or, ←
        this] at hprodZ
    -- By maximality of `P` and `M`, we have that `P ≤ M` implies `P = M`.
    have hPM' := (P.isPrime.isMaximal hP0).eq_of_le hM.ne_top hPM
    subst hPM'
    -- By minimality of `Z`, erasing `P` from `Z` is exactly what we need.
    refine ⟨Z.erase P, ?_, ?_⟩
    · convert! hZI
      rw [this, Multiset.cons_erase hPZ']
    · refine fun h => h_eraseZ (Z.erase P) ⟨h, ?_⟩ (Multiset.erase_lt.mpr hPZ)
      exact hZP0

@[deprecated (since := "2026-04-16")]
alias exists_multiset_prod_cons_le_and_prod_not_le :=
  PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le

namespace FractionalIdeal
variable [IsDedekindDomain A] {I : Ideal A}

open Ideal

/-
**FractionalIdeal.not_inv_le_one_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `Fractional
Ideal`。
形式化陈述：not_inv_le_one_of_ne_bot (hI0 : I != ⊥) (hI1 : I != ⊤) : ¬(I⁻¹ : Fractiona
lIdeal A⁰ K) <= 1
参数：hI0 : I != ⊥；hI1 : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Ideal.bot_lt_of_maximal`：bot_lt_of_maximal (M : Ideal R) [hm : M.IsMaxim
al] (non_field : ¬IsField R) : ⊥ < M
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Submodule.nonzero_mem_of_bot_lt`：nonzero_mem_of_bot_lt {p : Submodule R 
M} (bot_lt : ⊥ < p) : exists a : p, a != 0
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le`：PrimeSpectru
m.exists_multiset_prod_cons_le_and_prod_not_le [IsDedekindDomain A] (hNF : ¬IsFi
eld A) {I M : Ideal A} (hI0 : I != ⊥) (hIM : I <…
· 使用定理 `SetLike.not_le_iff_exists`：not_le_iff_exists : ¬p <= q ↔ exists x in p, 
x ∉ q
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `FractionalIdeal.mem_inv_iff`：mem_inv_iff (hI : I != 0) {x : K} : x in I⁻
¹ ↔ forall y in I, x * y in (1 : FractionalIdeal R₁⁰ K)
· 使用定理 `FractionalIdeal.coeIdeal_ne_zero`：coeIdeal_ne_zero {I : Ideal R} : (I : 
FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `FractionalIdeal.mem_coeIdeal`：mem_coeIdeal {x : P} {I : Ideal R} : x in 
(I : FractionalIdeal S P) ↔ exists x', x' in I ∧ algebraMap R P x' = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
（共 46 条，此处仅展示前 30 条）
-/
lemma not_inv_le_one_of_ne_bot (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    ¬(I⁻¹ : FractionalIdeal A⁰ K) ≤ 1 := by
  have hNF : ¬IsField A := fun h ↦ letI := h.toField; (eq_bot_or_eq_top I).elim hI0 hI1
  wlog hM : I.IsMaximal generalizing I
  · rcases I.exists_le_maximal hI1 with ⟨M, hmax, hIM⟩
    have hMbot : M ≠ ⊥ := (M.bot_lt_of_maximal hNF).ne'
    refine mt (le_trans <| inv_anti_mono ?_ ?_ ?_) (this hMbot hmax.ne_top hmax) <;>
      simpa only [coeIdeal_ne_zero, coeIdeal_le_coeIdeal]
  have hI0 : ⊥ < I := I.bot_lt_of_maximal hNF
  obtain ⟨⟨a, haI⟩, ha0⟩ := Submodule.nonzero_mem_of_bot_lt hI0
  replace ha0 : a ≠ 0 := Subtype.coe_injective.ne ha0
  let J : Ideal A := Ideal.span {a}
  have hJ0 : J ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp ha0
  have hJI : J ≤ I := I.span_singleton_le_iff_mem.2 haI
  -- Then we can find a product of prime (hence maximal) ideals contained in `J`,
  -- such that removing element `M` from the product is not contained in `J`.
  obtain ⟨Z, hle, hnle⟩ := PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le hNF hJ0 hJI
  -- Choose an element `b` of the product that is not in `J`.
  obtain ⟨b, hbZ, hbJ⟩ := SetLike.not_le_iff_exists.mp hnle
  have hnz_fa : algebraMap A K a ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective A K) a) ha0
  -- Then `b a⁻¹ : K` is in `M⁻¹` but not in `1`.
  refine Set.not_subset.2 ⟨algebraMap A K b * (algebraMap A K a)⁻¹, (mem_inv_iff ?_).mpr ?_, ?_⟩
  · exact coeIdeal_ne_zero.mpr hI0.ne'
  · rintro y₀ hy₀
    obtain ⟨y, h_Iy, rfl⟩ := (mem_coeIdeal _).mp hy₀
    rw [mul_comm, ← mul_assoc, ← map_mul]
    have h_yb : y * b ∈ J := by
      apply hle
      rw [Multiset.prod_cons]
      exact Submodule.smul_mem_smul h_Iy hbZ
    rw [Ideal.mem_span_singleton'] at h_yb
    rcases h_yb with ⟨c, hc⟩
    rw [← hc, map_mul, mul_assoc, mul_inv_cancel₀ hnz_fa, mul_one]
    apply coe_mem_one
  · refine mt (mem_one_iff _).mp ?_
    rintro ⟨x', h₂_abs⟩
    rw [← div_eq_mul_inv, eq_div_iff_mul_eq hnz_fa, ← map_mul] at h₂_abs
    have := Ideal.mem_span_singleton'.mpr ⟨x', IsFractionRing.injective A K h₂_abs⟩
    contradiction
/-
**FractionalIdeal.mul_inv_cancel_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Fractional
Ideal`。
形式化陈述：mul_inv_cancel_of_le_one (hI0 : I != ⊥) (hI : (I * (I : FractionalIdeal A⁰
 K)⁻¹)⁻¹ <= 1) : I * (I : FractionalIdeal A⁰ K)⁻¹ = 1
参数：hI0 : I != ⊥；hI : (I * (I : FractionalIdeal A⁰ K)⁻¹)⁻¹ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.le_one_iff_exists_coeIdeal`：le_one_iff_exists_coeIdeal {
J : FractionalIdeal S P} : J <= (1 : FractionalIdeal S P) ↔ exists I : Ideal R, 
↑I = J
· 使用定理 `FractionalIdeal.mul_one_div_le_one`：mul_one_div_le_one {I : FractionalId
eal R₁⁰ K} : I * (1 / I) <= 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coeIdeal_le_coeIdeal`：coeIdeal_le_coeIdeal (K : Type*) [
CommRing K] [Algebra R K] [IsFractionRing R K] {I J : Ideal R} : (I : Fractional
Ideal R⁰ K) <= J ↔ I <= J
· 使用定理 `FractionalIdeal.coe_ideal_le_self_mul_inv`：coe_ideal_le_self_mul_inv (I 
: Ideal R₁) : (I : FractionalIdeal R₁⁰ K) <= I * (I : FractionalIdeal R₁⁰ K)⁻¹
· 使用定理 `FractionalIdeal.coeIdeal_top`：coeIdeal_top : ((⊤ : Ideal R) : Fractional
Ideal S P) = 1
· 使用引理 `FractionalIdeal.not_inv_le_one_of_ne_bot`：not_inv_le_one_of_ne_bot (hI0 
: I != ⊥) (hI1 : I != ⊤) : ¬(I⁻¹ : FractionalIdeal A⁰ K) <= 1
-/
theorem mul_inv_cancel_of_le_one (hI0 : I ≠ ⊥) (hI : (I * (I : FractionalIdeal A⁰ K)⁻¹)⁻¹ ≤ 1) :
    I * (I : FractionalIdeal A⁰ K)⁻¹ = 1 := by
  -- We'll show a contradiction with `exists_notMem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, (J : FractionalIdeal A⁰ K) = I * (I : FractionalIdeal A⁰ K)⁻¹ :=
    le_one_iff_exists_coeIdeal.mp mul_one_div_le_one
  by_cases hJ0 : J = ⊥
  · subst hJ0
    refine absurd ?_ hI0
    rw [eq_bot_iff, ← coeIdeal_le_coeIdeal K, hJ]
    exact coe_ideal_le_self_mul_inv K I
  by_cases hJ1 : J = ⊤
  · rw [← hJ, hJ1, coeIdeal_top]
  exact (not_inv_le_one_of_ne_bot (K := K) hJ0 hJ1 (hJ ▸ hI)).elim

/-- Nonzero integral ideals in a Dedekind domain are invertible.

We will use this to show that nonzero fractional ideals are invertible,
and finally conclude that fractional ideals in a Dedekind domain form a group with zero.
-/
/-
**FractionalIdeal.coe_ideal_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_ideal_mul_inv (I : Ideal A) (hI0 : I != ⊥) : I * (I : FractionalIdeal 
A⁰ K)⁻¹ = 1
参数：I : Ideal A；hI0 : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.mul_inv_cancel_of_le_one`：mul_inv_cancel_of_le_one (hI0 
: I != ⊥) (hI : (I * (I : FractionalIdeal A⁰ K)⁻¹)⁻¹ <= 1) : I * (I : Fractional
Ideal A⁰ K)⁻¹ = 1
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.inv_zero'`：inv_zero' : (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0
· 使用定理 `FractionalIdeal.zero_le`：zero_le (I : FractionalIdeal S P) : 0 <= I
· 使用定理 `mem_integralClosure_iff_mem_fg`：mem_integralClosure_iff_mem_fg {r : A} :
 r in integralClosure R A ↔ exists M : Subalgebra R A, M.toSubmodule.FG ∧ r in M
· 使用定理 `FractionalIdeal.mem_inv_iff`：mem_inv_iff (hI : I != 0) {x : K} : x in I⁻
¹ ↔ forall y in I, x * y in (1 : FractionalIdeal R₁⁰ K)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.coeIdeal_ne_zero`：coeIdeal_ne_zero {I : Ideal R} : (I : 
FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `FractionalIdeal.mul_mem_mul`：mul_mem_mul {I J : FractionalIdeal S P} {i 
j : P} (hi : i in I) (hj : j in J) : i * j in I * J
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isNoetherian_submodule`：isNoetherian_submodule {N : Submodule R M} : IsN
oetherian R N ↔ forall s : Submodule R M, s <= N -> s.FG
· 使用定理 `FractionalIdeal.isNoetherian`：isNoetherian [IsNoetherianRing R₁] (I : Fr
actionalIdeal R₁⁰ K) : IsNoetherian R₁ I
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `AlgHom.mem_range`：mem_range (φ : A ->ₐ[R] B) {y : B} : y in φ.range ↔ ex
ists x, φ x = y
· 使用定理 `Polynomial.aeval_eq_sum_range`：aeval_eq_sum_range [Algebra R S] {p : R[X
]} (x : S) : aeval x p = ∑ i in Finset.range (p.natDegree + 1), p.coeff i • x ^ 
i
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `FractionalIdeal.one_mem_inv_coe_ideal`：FractionalIdeal.one_mem_inv_coe_i
deal [IsDomain A] {I : Ideal A} (hI : I != ⊥) : (1 : K) in (I : FractionalIdeal 
A⁰ K)⁻¹
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Nonzero integral ideals in a Dedekind domain are invertible.

We will use this to show that nonzero fractional ideals are invertible,
and finally conclude that fractional ideals in a Dedekind domain form a group wi
th zero.
-/
theorem coe_ideal_mul_inv (I : Ideal A) (hI0 : I ≠ ⊥) : I * (I : FractionalIdeal A⁰ K)⁻¹ = 1 := by
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0
  by_cases hJ0 : I * (I : FractionalIdeal A⁰ K)⁻¹ = 0
  · rw [hJ0, inv_zero']; exact zero_le _
  intro x hx
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices x ∈ integralClosure A K by
    rwa [IsIntegrallyClosed.integralClosure_eq_bot, Algebra.mem_bot, Set.mem_range,
      ← mem_one_iff] at this
  -- For that, we'll find a subalgebra that is f.g. as a module and contains `x`.
  -- `A` is a Noetherian ring, so we just need to find a subalgebra between `{x}` and `I⁻¹`.
  rw [mem_integralClosure_iff_mem_fg]
  have x_mul_mem : ∀ b ∈ (I⁻¹ : FractionalIdeal A⁰ K), x * b ∈ (I⁻¹ : FractionalIdeal A⁰ K) := by
    intro b hb
    rw [mem_inv_iff (coeIdeal_ne_zero.mpr hI0)]
    rw [mem_inv_iff hJ0] at hx
    simp_rw [mul_assoc, mul_comm b]
    exact fun y hy ↦ hx _ (mul_mem_mul hy hb)
  -- It turns out the subalgebra consisting of all `p(x)` for `p : A[X]` works.
  refine ⟨AlgHom.range (Polynomial.aeval x : A[X] →ₐ[A] K),
    isNoetherian_submodule.mp (isNoetherian (I : FractionalIdeal A⁰ K)⁻¹) _ fun y hy => ?_,
    ⟨Polynomial.X, Polynomial.aeval_X x⟩⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hy
  rw [Polynomial.aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  clear hi
  induction i with
  | zero => rw [pow_zero]; exact one_mem_inv_coe_ideal hI0
  | succ i ih => rw [pow_succ']; exact x_mul_mem _ ih

end FractionalIdeal

end Inverse

section IsDedekindDomainInv

/-- An integral domain is a Dedekind domain if every fractional ideal has an inverse.
This is an auxiliary definition used to
prove `isDedekindDomain_iff_mul_inv_cancel` and `FractionalIdeal.semifield`. -/
/-
**IsDedekindDomainInv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsDedekindDomainInv [IsDomain A] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An integral domain is a Dedekind domain if every fractional ideal has an inverse
.
This is an auxiliary definition used to
prove `isDedekindDomain_iff_mul_inv_cancel` and `FractionalIdeal.semifield`.
-/
def IsDedekindDomainInv [IsDomain A] : Prop :=
  ∀ I ≠ (⊥ : FractionalIdeal A⁰ (FractionRing A)), I * I⁻¹ = 1

open FractionalIdeal

variable {A K} [Algebra A K] [IsFractionRing A K]

variable {R} in
/-
**isDedekindDomainInv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDedekindDomainInv_iff [IsDomain A] : IsDedekindDomainInv A ↔ forall I !=
 (⊥ : FractionalIdeal A⁰ K), I * I⁻¹ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isDedekindDomainInv_iff [IsDomain A] :
    IsDedekindDomainInv A ↔ ∀ I ≠ (⊥ : FractionalIdeal A⁰ K), I * I⁻¹ = 1 := by
  let h : FractionalIdeal A⁰ (FractionRing A) ≃+* FractionalIdeal A⁰ K :=
    FractionalIdeal.mapEquiv (FractionRing.algEquiv A K)
  refine h.toEquiv.forall_congr (fun {x} => ?_)
  rw [← h.toEquiv.apply_eq_iff_eq]
  simp [h]

namespace IsDedekindDomainInv

variable (K) [IsDomain A] (h : IsDedekindDomainInv A) {I J : FractionalIdeal A⁰ K}
include h

/-- `IsDedekindDomainInv A` implies that fractional ideals over it form a commutative group with
zero. -/
/-
**IsDedekindDomainInv.commGroupWithZero** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsDedekindD
omainInv`。
形式化陈述：commGroupWithZero : CommGroupWithZero (FractionalIdeal A⁰ K) where inv_zer
o
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsDedekindDomainInv A` implies that fractional ideals over it form a commutativ
e group with
zero.
-/
noncomputable abbrev commGroupWithZero : CommGroupWithZero (FractionalIdeal A⁰ K) where
  inv_zero := inv_zero' _
  mul_inv_cancel := isDedekindDomainInv_iff.mp h
  div_eq_mul_inv I J := by
    obtain rfl | hJ := eq_or_ne J 0
    · simp [inv_zero']
    refine le_antisymm ?_ ((FractionalIdeal.le_div_iff_mul_le hJ).2 ?_)
    · suffices I / J * J ≤ I by
        simpa [mul_assoc, isDedekindDomainInv_iff.mp h _ hJ] using mul_left_mono (a := J⁻¹) this
      simp [FractionalIdeal.mul_le, mem_div_iff_of_ne_zero hJ]
    · rw [mul_assoc, mul_comm _ J, isDedekindDomainInv_iff.mp h _ hJ, mul_one]
/-
**IsDedekindDomainInv.isNoetherianRing** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDoma
inInv`。
形式化陈述：isNoetherianRing : IsNoetherianRing A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNoetherianRing : IsNoetherianRing A := by
  let := h.commGroupWithZero (FractionRing A)
  refine isNoetherianRing_iff.mpr ⟨fun I : Ideal A => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; apply Submodule.fg_bot
  have hI : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr hI
  exact I.fg_of_isUnit (IsFractionRing.injective A (FractionRing A)) hI.isUnit
/-
**IsDedekindDomainInv.integrallyClosed** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDoma
inInv`。
形式化陈述：integrallyClosed : IsIntegrallyClosed A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integrallyClosed : IsIntegrallyClosed A := by
  let := h.commGroupWithZero (FractionRing A)
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr (fun {x hx} => ?_)
  rw [← Set.mem_range, ← Algebra.mem_bot, ← Subalgebra.mem_toSubmodule, Algebra.toSubmodule_bot,
    Submodule.one_eq_span, ← coe_spanSingleton A⁰ (1 : FractionRing A), spanSingleton_one, ←
    FractionalIdeal.adjoinIntegral_eq_one_of_isUnit x hx (Ne.isUnit _)]
  · exact mem_adjoinIntegral_self A⁰ x hx
  · exact fun h => one_ne_zero (eq_zero_iff.mp h 1 (Algebra.adjoin A {x}).one_mem)

open Ring
/-
**IsDedekindDomainInv.dimensionLEOne** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain
Inv`。
形式化陈述：dimensionLEOne : DimensionLEOne A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dimensionLEOne : DimensionLEOne A := by
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  let := h.commGroupWithZero (K := FractionRing A)
  constructor
  rintro P P_ne hP
  refine Ideal.isMaximal_def.mpr ⟨hP.ne_top, fun M hM => ?_⟩
  -- We may assume `P` and `M` (as fractional ideals) are nonzero.
  have P'_ne : (P : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr P_ne
  have M'_ne : (M : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr hM.ne_bot
  -- In particular, we'll show `M⁻¹ * P ≤ P`
  suffices (M⁻¹ : FractionalIdeal A⁰ (FractionRing A)) * P ≤ P by
    rw [eq_top_iff, ← coeIdeal_le_coeIdeal (FractionRing A), coeIdeal_top]
    calc
      (1 : FractionalIdeal A⁰ (FractionRing A)) = (↑M)⁻¹ * P * ((↑P)⁻¹ * M) := by
        simp [mul_assoc, *]
      _ ≤ P * ((↑P)⁻¹ * M) := by gcongr
      _ = M := by simp [*]
  -- Suppose we have `x ∈ M⁻¹ * P`, then in fact `x = algebraMap _ _ y` for some `y`.
  intro x hx
  have le_one : (M⁻¹ : FractionalIdeal A⁰ (FractionRing A)) * P ≤ 1 := by
    rw [← inv_mul_cancel₀ M'_ne]; gcongr
  obtain ⟨y, _hy, rfl⟩ := (mem_coeIdeal _).mp (le_one hx)
  -- Since `M` is strictly greater than `P`, let `z ∈ M \ P`.
  obtain ⟨z, hzM, hzp⟩ := SetLike.exists_of_lt hM
  -- We have `z * y ∈ M * (M⁻¹ * P) = P`.
  have zy_mem := mul_mem_mul (mem_coeIdeal_of_mem A⁰ hzM) hx
  rw [← map_mul, ← mul_assoc, mul_inv_cancel₀ M'_ne, one_mul] at zy_mem
  obtain ⟨zy, hzy, zy_eq⟩ := (mem_coeIdeal A⁰).mp zy_mem
  rw [IsFractionRing.injective A (FractionRing A) zy_eq] at hzy
  -- But `P` is a prime ideal, so `z ∉ P` implies `y ∈ P`, as desired.
  exact mem_coeIdeal_of_mem A⁰ (Or.resolve_left (hP.mem_or_mem hzy) hzp)

end IsDedekindDomainInv

/-- `IsDedekindDomain` and `IsDedekindDomainInv` are equivalent ways
to express that an integral domain is a Dedekind domain. -/
/-
**isDedekindDomain_iff_isDedekindDomainInv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDedekindDomain_iff_isDedekindDomainInv [IsDomain A] : IsDedekindDomain A
 ↔ IsDedekindDomainInv A
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsDedekindDomain` and `IsDedekindDomainInv` are equivalent ways
to express that an integral domain is a Dedekind domain.
-/
theorem isDedekindDomain_iff_isDedekindDomainInv [IsDomain A] :
    IsDedekindDomain A ↔ IsDedekindDomainInv A := by
  refine ⟨fun _ I hI => ?_, fun h =>
    { h.isNoetherianRing, h.dimensionLEOne, h.integrallyClosed with }⟩
  obtain ⟨a, J, ha, hJ⟩ := exists_eq_spanSingleton_mul (K := FractionRing A) I
  suffices h₂ : I * (spanSingleton A⁰ (algebraMap _ _ a) * (J : FractionalIdeal A⁰ _)⁻¹) = 1 by
    rw [mul_inv_cancel_iff]
    exact ⟨spanSingleton A⁰ (algebraMap _ _ a) * (J : FractionalIdeal A⁰ _)⁻¹, h₂⟩
  subst hJ
  rw [mul_assoc, mul_left_comm (J : FractionalIdeal A⁰ _), coe_ideal_mul_inv, mul_one,
    spanSingleton_mul_spanSingleton, inv_mul_cancel₀, spanSingleton_one]
  · exact mt ((injective_iff_map_eq_zero (algebraMap A _)).mp (IsFractionRing.injective A _) _) ha
  · exact coeIdeal_ne_zero.mp (right_ne_zero_of_mul hI)

public theorem isDedekindDomain_iff_mul_inv_cancel [IsDomain A] :
    IsDedekindDomain A ↔ ∀ I ≠ (⊥ : FractionalIdeal A⁰ K), I * I⁻¹ = 1 :=
  isDedekindDomain_iff_isDedekindDomainInv.trans isDedekindDomainInv_iff

end IsDedekindDomainInv

public section IsDedekindDomain

variable {R A}
variable [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal Ideal

namespace FractionalIdeal

/-
**FractionalIdeal.semifield** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
形式化陈述：semifield : Semifield (FractionalIdeal A⁰ K) where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
-/
noncomputable instance semifield : Semifield (FractionalIdeal A⁰ K) where
  __ := coeIdeal_injective.nontrivial
  __ : CommSemiring (FractionalIdeal A⁰ K) := inferInstance
  inv_zero := inv_zero' K
  mul_inv_cancel := isDedekindDomain_iff_mul_inv_cancel.mp ‹_›
  div_eq_mul_inv := by
    let := (isDedekindDomain_iff_isDedekindDomainInv.mp ‹_›).commGroupWithZero K
    exact div_eq_mul_inv
  nnqsmul := _
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PosMulStrictMono (FractionalIdeal A⁰ K) := PosMulMono.toPosMulStrictMono
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulPosStrictMono (FractionalIdeal A⁰ K) := MulPosMono.toMulPosStrictMono
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PosMulReflectLE (FractionalIdeal A⁰ K) where
  elim I J K hJK := by simpa [I.2.ne'] using mul_right_mono (a := I.1⁻¹) hJK
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulPosReflectLE (FractionalIdeal A⁰ K) where
  elim I J K hJK := by simpa [I.2.ne'] using mul_left_mono (a := I.1⁻¹) hJK
/-
**FractionalIdeal.mul_left_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal
`。
形式化陈述：mul_left_strictMono {I : FractionalIdeal A⁰ K} (hI : I != 0) : StrictMono 
(· * I)
参数：hI : I != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `FractionalIdeal.instMulPosStrictMonoNonZeroDivisors`：∀ {A : Type u_2} (K
 : Type u_3) [inst : CommRing A] [inst_1 : Field K] [IsDedekindDomain A] [inst_3
 : Algebra A K]   [IsFractionRing A K], M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `FractionalIdeal.instCanonicallyOrderedAdd`：∀ {R : Type u_1} [inst : Comm
Ring R] {S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra
 R P],   CanonicallyOrderedAdd …
-/
lemma mul_left_strictMono {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : StrictMono (· * I) :=
  fun _J _K hJK ↦ mul_lt_mul_of_pos_right hJK <| pos_iff_ne_zero.2 hI
/-
**FractionalIdeal.mul_right_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdea
l`。
形式化陈述：mul_right_strictMono {I : FractionalIdeal A⁰ K} (hI : I != 0) : StrictMono
 (I * ·)
参数：hI : I != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `FractionalIdeal.instPosMulStrictMonoNonZeroDivisors`：∀ {A : Type u_2} (K
 : Type u_3) [inst : CommRing A] [inst_1 : Field K] [IsDedekindDomain A] [inst_3
 : Algebra A K]   [IsFractionRing A K], P…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `FractionalIdeal.instCanonicallyOrderedAdd`：∀ {R : Type u_1} [inst : Comm
Ring R] {S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra
 R P],   CanonicallyOrderedAdd …
-/
lemma mul_right_strictMono {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : StrictMono (I * ·) :=
  fun _J _K hJK ↦ mul_lt_mul_of_pos_left hJK <| pos_iff_ne_zero.2 hI
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PosMulReflectLE (Ideal A) where
  elim I J K e := by
    dsimp
    rwa [← FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing A),
      ← mul_le_mul_iff_right₀ (α := FractionalIdeal A⁰ (FractionRing A)) (a := I.1)
        (by simpa [pos_iff_ne_zero] using I.2.ne'),
      ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_le_coeIdeal]

end FractionalIdeal

/-
**Ideal.isCancelMulZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ideal.isCancelMulZero : IsCancelMulZero (Ideal A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [
inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : 
M₀ → M₀'),   Function.In…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coeIdeal_injective`：coeIdeal_injective : Function.Inject
ive (fun (I : Ideal R) => (I : FractionalIdeal R⁰ K))
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
noncomputable instance Ideal.isCancelMulZero : IsCancelMulZero (Ideal A) :=
  Function.Injective.isCancelMulZero (coeIdealHom A⁰ (FractionRing A)) coeIdeal_injective
    (map_zero _) (map_mul _)
/-
**Ideal.isDomain** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {A : Type u_2} [inst : CommRing A] [IsDedekindDomain A], IsDomain (Ideal
 A)
参数：Ideal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
-/
instance Ideal.isDomain : IsDomain (Ideal A) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PosMulStrictMono (Ideal A) := PosMulMono.toPosMulStrictMono
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulPosStrictMono (Ideal A) := MulPosMono.toMulPosStrictMono

/-- For ideals in a Dedekind domain, to divide is to contain. -/
/-
**Ideal.dvd_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.le_of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {I J : Ideal R},
 I ∣ J → J ≤ I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionalIdeal.coeIdeal_ne_zero`：coeIdeal_ne_zero {I : Ideal R} : (I : 
FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `FractionalIdeal.instMulLeftMono`：∀ {R : Type u_1} [inst : CommRing R] {S
 : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P],   M
ulLeftMono (Fractiona…
· 使用定理 `FractionalIdeal.instMulRightMono`：∀ {R : Type u_1} [inst : CommRing R] {
S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P],   
MulRightMono (Fraction…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `FractionalIdeal.coeIdeal_le_coeIdeal._gcongr_1`：∀ {R : Type u_1} [inst :
 CommRing R] (K : Type u_3) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFrac
tionRing R K]   {I J : Ideal R}, I ≤…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.le_one_iff_exists_coeIdeal`：le_one_iff_exists_coeIdeal {
J : FractionalIdeal S P} : J <= (1 : FractionalIdeal S P) ↔ exists I : Ideal R, 
↑I = J
· 使用定理 `FractionalIdeal.coeIdeal_injective`：coeIdeal_injective : Function.Inject
ive (fun (I : Ideal R) => (I : FractionalIdeal R⁰ K))
· 使用定理 `FractionalIdeal.coeIdeal_mul`：coeIdeal_mul (I J : Ideal R) : (↑(I * J) :
 FractionalIdeal S P) = I * J
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
For ideals in a Dedekind domain, to divide is to contain.
-/
theorem Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J ≤ I :=
  ⟨Ideal.le_of_dvd, fun h => by
    by_cases hI : I = ⊥
    · have hJ : J = ⊥ := by rwa [hI, ← eq_bot_iff] at h
      rw [hI, hJ]
    have hI' : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr hI
    have : (I : FractionalIdeal A⁰ (FractionRing A))⁻¹ * J ≤ 1 := by
      rw [← inv_mul_cancel₀ hI']; gcongr
    obtain ⟨H, hH⟩ := le_one_iff_exists_coeIdeal.mp this
    use H
    refine coeIdeal_injective (show (J : FractionalIdeal A⁰ (FractionRing A)) = ↑(I * H) from ?_)
    rw [coeIdeal_mul, hH, ← mul_assoc, mul_inv_cancel₀ hI', one_mul]⟩
/-
**Ideal.liesOver_iff_dvd_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.liesOver_iff_dvd_map [Algebra R A] {p : Ideal R} {P : Ideal A} (hP :
 P != ⊤) [p.IsMaximal] : P.LiesOver p ↔ P ∣ Ideal.map (algebraMap R A) p
参数：hP : P != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用引理 `IsCoatom.le_iff_eq`：IsCoatom.le_iff_eq (ha : IsCoatom a) (hb : b != ⊤) :
 a <= b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.isMaximal_def`：isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoato
m I
· 使用定理 `Ideal.comap_ne_top`：comap_ne_top [RingHomClass F R S] (hK : K != ⊤) : co
map f K != ⊤
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ideal.liesOver_iff_dvd_map [Algebra R A] {p : Ideal R} {P : Ideal A} (hP : P ≠ ⊤)
    [p.IsMaximal] :
    P.LiesOver p ↔ P ∣ Ideal.map (algebraMap R A) p := by
  rw [liesOver_iff, dvd_iff_le, under_def, map_le_iff_le_comap,
    IsCoatom.le_iff_eq (by rwa [← isMaximal_def]) (comap_ne_top _ hP), eq_comm]
/-
**Ideal.dvdNotUnit_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.dvdNotUnit_iff_lt {I J : Ideal A} : DvdNotUnit I J ↔ J < I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `dvdNotUnit_of_dvd_of_not_dvd`：dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd
 : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem Ideal.dvdNotUnit_iff_lt {I J : Ideal A} : DvdNotUnit I J ↔ J < I :=
  ⟨fun ⟨hI, H, hunit, hmul⟩ =>
    lt_of_le_of_ne (Ideal.dvd_iff_le.mp ⟨H, hmul⟩)
      (mt
        (fun h =>
          have : H = 1 := mul_left_cancel₀ hI (by rw [← hmul, h, mul_one])
          show IsUnit H from this.symm ▸ isUnit_one)
        hunit),
    fun h =>
    dvdNotUnit_of_dvd_of_not_dvd (Ideal.dvd_iff_le.mpr (le_of_lt h))
      (mt Ideal.dvd_iff_le.mp (not_le_of_gt h))⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WfDvdMonoid (Ideal A) where
  wf := by
    have : WellFoundedGT (Ideal A) := inferInstance
    convert! this.wf using 3
    exact Ideal.dvdNotUnit_iff_lt
/-
**Ideal.uniqueFactorizationMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ideal.uniqueFactorizationMonoid : UniqueFactorizationMonoid (Ideal A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instWfDvdMonoidIdeal`：∀ {A : Type u_2} [inst : CommRing A] [IsDedekindDo
main A], WfDvdMonoid (Ideal A)
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isUnit_iff`：isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤
· 使用定理 `Ideal.dvdNotUnit_iff_lt`：Ideal.dvdNotUnit_iff_lt {I J : Ideal A} : DvdNo
tUnit I J ↔ J < I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
-/
instance Ideal.uniqueFactorizationMonoid : UniqueFactorizationMonoid (Ideal A) :=
  { irreducible_iff_prime := by
      intro P
      exact ⟨fun hirr => ⟨hirr.ne_zero, hirr.not_isUnit, fun I J => by
        have : P.IsMaximal := by
          refine ⟨⟨mt Ideal.isUnit_iff.mpr hirr.not_isUnit, ?_⟩⟩
          intro J hJ
          obtain ⟨_J_ne, H, hunit, P_eq⟩ := Ideal.dvdNotUnit_iff_lt.mpr hJ
          exact Ideal.isUnit_iff.mp ((hirr.isUnit_or_isUnit P_eq).resolve_right hunit)
        rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.dvd_iff_le, SetLike.le_def, SetLike.le_def,
          SetLike.le_def]
        contrapose!
        rintro ⟨⟨x, x_mem, x_notMem⟩, ⟨y, y_mem, y_notMem⟩⟩
        exact
          ⟨x * y, Ideal.mul_mem_mul x_mem y_mem,
            mt this.isPrime.mem_or_mem (not_or_intro x_notMem y_notMem)⟩⟩, Prime.irreducible⟩ }
/-
**Ideal.strongNormalizationMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ideal.strongNormalizationMonoid : StrongNormalizationMonoid (Ideal A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Ideal.strongNormalizationMonoid : StrongNormalizationMonoid (Ideal A) :=
  inferInstance

@[deprecated (since := "2026-07-08")]
alias Ideal.normalizationMonoid := Ideal.strongNormalizationMonoid

end IsDedekindDomain

