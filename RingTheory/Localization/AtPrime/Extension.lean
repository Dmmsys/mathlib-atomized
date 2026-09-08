/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Primes in an extension of localization at prime

Let `R ⊆ S` be an extension of Dedekind domains and `p` be a prime ideal of `R`. Let `Rₚ` be the
localization of `R` at the complement of `p` and `Sₚ` the localization of `S` at the (image)
of the complement of `p`.

In this file, we study the relation between the (nonzero) prime ideals of `Sₚ` and the prime
ideals of `S` above `p`. In particular, we prove that (under suitable conditions) they are in
bijection and that the residual degree and ramification index are preserved by this bijection.

## Main definitions and results

- `IsLocalization.AtPrime.mem_primesOver_of_isPrime`: The nonzero prime ideals of `Sₚ` are
  primes over the maximal ideal of `Rₚ`.

- `IsLocalization.AtPrime.equivQuotientMapOfIsMaximal`: `S ⧸ P ≃+* Sₚ ⧸ P·Sₚ` where
  `P` is a maximal ideal of `S` above `p`.

- `IsDedekindDomain.primesOverEquivPrimesOver`: the bijection between the primes over
  `p` in `S` and the primes over the maximal ideal of `Rₚ` in `Sₚ`.

- `IsDedekindDomain.primesOverEquivPrimesOver_inertiagDeg_eq`: the bijection
  `primesOverEquivPrimesOver` preserves the inertia degree.

- `IsDedekindDomain.primesOverEquivPrimesOver_ramificationIdx_eq`: the bijection
  `primesOverEquivPrimesOver` preserves the ramification index.

-/

@[expose] public section

open Algebra Module IsLocalRing Ideal Localization.AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
  [Algebra Rₚ Sₚ] (P : Ideal S) [hPp : P.LiesOver p]

namespace IsLocalization.AtPrime

/--
The nonzero prime ideals of `Sₚ` are prime ideals over the maximal ideal of `Rₚ`.
See `Localization.AtPrime.primesOverEquivPrimesOver` for the bijection between the prime ideals
of `Sₚ` over the maximal ideal of `Rₚ` and the primes ideals of `S` above `p`.
-/
/-
**IsLocalization.AtPrime.mem_primesOver_of_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Is
Localization.AtPrime`。
形式化陈述：mem_primesOver_of_isPrime {Q : Ideal Sₚ} [Q.IsMaximal] [Algebra.IsIntegral
 Rₚ Sₚ] : Q in (maximalIdeal Rₚ).primesOver Sₚ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `Ideal.IsMaximal.under`：∀ (A : Type u_1) [inst : CommRing A] {B : Type u_
2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : 
Ideal B) [P…

--- 原说明 ---
The nonzero prime ideals of `Sₚ` are prime ideals over the maximal ideal of `Rₚ`
.
See `Localization.AtPrime.primesOverEquivPrimesOver` for the bijection between t
he prime ideals
of `Sₚ` over the maximal ideal of `Rₚ` and the primes ideals of `S` above `p`.
-/
theorem mem_primesOver_of_isPrime {Q : Ideal Sₚ} [Q.IsMaximal] [Algebra.IsIntegral Rₚ Sₚ] :
    Q ∈ (maximalIdeal Rₚ).primesOver Sₚ := by
  refine ⟨inferInstance, ?_⟩
  rw [liesOver_iff, ← eq_maximalIdeal]
  exact IsMaximal.under Rₚ Q
/-
**IsLocalization.AtPrime.liesOver_comap_of_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `I
sLocalization.AtPrime`。
形式化陈述：liesOver_comap_of_liesOver {T : Type*} [CommRing T] [Algebra R T] [Algebra
 Rₚ T] [Algebra S T] [IsScalarTower R S T] [IsScalarTower R Rₚ T] (Q : Ideal T) 
[Q.LiesOver (maximalIdeal Rₚ)] : (comap (algebraMap S T) Q).LiesOver p
参数：Q : Ideal T；maximalIdeal Rₚ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.trans`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type
 u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 :
 Algebra A…
-/
theorem liesOver_comap_of_liesOver {T : Type*} [CommRing T] [Algebra R T] [Algebra Rₚ T]
    [Algebra S T] [IsScalarTower R S T] [IsScalarTower R Rₚ T] (Q : Ideal T)
    [Q.LiesOver (maximalIdeal Rₚ)] : (comap (algebraMap S T) Q).LiesOver p := by
  have : Q.LiesOver p := by
    have : (maximalIdeal Rₚ).LiesOver p := liesOver_maximalIdeal Rₚ p _
    exact LiesOver.trans Q (IsLocalRing.maximalIdeal Rₚ) p
  exact comap_liesOver Q p <| IsScalarTower.toAlgHom R S T

include p in
/-
**IsLocalization.AtPrime.liesOver_map_of_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `IsL
ocalization.AtPrime`。
形式化陈述：liesOver_map_of_liesOver [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTo
wer R Rₚ Sₚ] [P.IsPrime] : (P.map (algebraMap S Sₚ)).LiesOver (IsLocalRing.maxim
alIdeal Rₚ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.AtPrime.map_eq_maximalIdeal`：map_eq_maximalIdeal : p.map 
(algebraMap R Rₚ) = maximalIdeal Rₚ
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.under_map_eq_map_under`：under_map_eq_map_under {C D : Type*} [Comm
Semiring C] [Semiring D] [Algebra A C] [Algebra C D] [Algebra A D] [Algebra B D]
 [IsScalarTower A …
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `IsLocalization.AtPrime.isPrime_map_of_liesOver`：isPrime_map_of_liesOver 
[P.IsPrime] [P.LiesOver p] : (P.map (algebraMap S Sₚ)).IsPrime
-/
theorem liesOver_map_of_liesOver [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
    [P.IsPrime] :
    (P.map (algebraMap S Sₚ)).LiesOver (IsLocalRing.maximalIdeal Rₚ) := by
  rw [liesOver_iff, eq_comm, ← map_eq_maximalIdeal p, over_def P p]
  exact under_map_eq_map_under _
    (over_def P p ▸ map_eq_maximalIdeal p Rₚ ▸ maximalIdeal.isMaximal Rₚ)
    (isPrime_map_of_liesOver S p Sₚ P).ne_top

attribute [local instance] Ideal.Quotient.field

include p in
/-
**IsLocalization.AtPrime.exists_algebraMap_quot_eq_of_mem_quot** 是 Mathlib 中的一个定
理，位于命名空间 `IsLocalization.AtPrime`。
形式化陈述：exists_algebraMap_quot_eq_of_mem_quot [P.IsMaximal] (x : Sₚ ⧸ P.map (algeb
raMap S Sₚ)) : exists a, (algebraMap S (Sₚ ⧸ P.map (algebraMap S Sₚ))) a = x
参数：x : Sₚ ⧸ P.map (algebraMap S Sₚ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `IsLocalization.AtPrime.isPrime_map_of_liesOver`：isPrime_map_of_liesOver 
[P.IsPrime] [P.LiesOver p] : (P.map (algebraMap S Sₚ)).IsPrime
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Ideal.disjoint_primeCompl_of_liesOver`：disjoint_primeCompl_of_liesOver [
p.IsPrime] [hPp : 𝔓.LiesOver p] : Disjoint ((Algebra.algebraMapSubmonoid C p.pri
meCompl) : Set C) (𝔓 : Set …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.comap_map_eq_self_of_isMaximal`：comap_map_eq_self_of_isMaximal (f 
: R ->+* S) {p : Ideal R} [hP' : p.IsMaximal] (hP : Ideal.map f p != ⊤) : (map f
 p).comap f = p
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `IsLocalization.mul_mk'_eq_mk'_of_mul`：∀ {R : Type u_1} [inst : CommSemir
ing R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Al
gebra R S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_mul_cancel_left`：∀ {R : Type u_1} [inst : CommSemirin
g R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Alge
bra R S] [inst_3 : IsLoc…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
（共 38 条，此处仅展示前 30 条）
-/
theorem exists_algebraMap_quot_eq_of_mem_quot [P.IsMaximal]
    (x : Sₚ ⧸ P.map (algebraMap S Sₚ)) :
    ∃ a, (algebraMap S (Sₚ ⧸ P.map (algebraMap S Sₚ))) a = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (algebraMapSubmonoid S p.primeCompl) x
  obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := P) (Ideal.Quotient.mk P s)⁻¹
  simp only [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), Quotient.algebraMap_eq, RingHom.comp_apply]
  use x * s'
  rw [← sub_eq_zero, ← map_sub, Quotient.eq_zero_iff_mem]
  have h₀ : (P.map (algebraMap S Sₚ)).IsPrime := isPrime_map_of_liesOver S p Sₚ P
  have h₁ : s.1 ∉ P := (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver P p) s.prop
  have h₂ : algebraMap S Sₚ s ∉ Ideal.map (algebraMap S Sₚ) P := by
    rwa [← mem_comap, comap_map_eq_self_of_isMaximal _ h₀.ne_top]
  refine (h₀.mem_or_mem ?_).resolve_left h₂
  rw [mul_sub, mul_mk'_eq_mk'_of_mul, mk'_mul_cancel_left, ← map_mul, ← map_sub, ← mem_comap,
    comap_map_eq_self_of_isMaximal _ IsPrime.ne_top', ← Ideal.Quotient.eq, map_mul, map_mul, hs,
    mul_comm, inv_mul_cancel_right₀ (Quotient.eq_zero_iff_mem.not.mpr h₁)]

/--
The isomorphism `S ⧸ P ≃+* Sₚ ⧸ P·Sₚ`, where `Sₚ` is the localization of `S` at the (image) of
the complement of `p` and `P` is a maximal ideal of `S` above `p`.
Note that this isomorphism makes the obvious diagram involving `R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ`
commute, see `IsLocalization.AtPrime.algebraMap_equivQuotMaximalIdeal_symm_apply`.
-/
/-
**IsLocalization.AtPrime.equivQuotientMapOfIsMaximal** 是 Mathlib 中的一个定义，位于命名空间 `
IsLocalization.AtPrime`。
形式化陈述：equivQuotientMapOfIsMaximal [P.IsMaximal] : S ⧸ P ≃+* Sₚ ⧸ P.map (algebraM
ap S Sₚ)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsLocalization.AtPrime.exists_algebraMap_quot_eq_of_mem_quot`：exists_alg
ebraMap_quot_eq_of_mem_quot [P.IsMaximal] (x : Sₚ ⧸ P.map (algebraMap S Sₚ)) : e
xists a, (algebraMap S (Sₚ ⧸ P.map (algebraMap S S…

--- 原说明 ---
The isomorphism `S ⧸ P ≃+* Sₚ ⧸ P·Sₚ`, where `Sₚ` is the localization of `S` at 
the (image) of
the complement of `p` and `P` is a maximal ideal of `S` above `p`.
Note that this isomorphism makes the obvious diagram involving `R ⧸ p ≃+* Rₚ ⧸ m
aximalIdeal Rₚ`
commute, see `IsLocalization.AtPrime.algebraMap_equivQuotMaximalIdeal_symm_apply
`.
-/
noncomputable def equivQuotientMapOfIsMaximal [P.IsMaximal] :
    S ⧸ P ≃+* Sₚ ⧸ P.map (algebraMap S Sₚ) :=
  .trans
    (Ideal.quotEquivOfEq (by
      rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), ← RingHom.comap_ker, Quotient.algebraMap_eq,
        mk_ker, comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top]))
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ _))
      fun x ↦ exists_algebraMap_quot_eq_of_mem_quot p Sₚ P x)

@[simp]
/-
**IsLocalization.AtPrime.equivQuotientMapOfIsMaximal_apply_mk** 是 Mathlib 中的一个定理
，位于命名空间 `IsLocalization.AtPrime`。
形式化陈述：equivQuotientMapOfIsMaximal_apply_mk [P.IsMaximal] (x : S) : equivQuotient
MapOfIsMaximal p Sₚ P (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk _ (algebraMap
 S Sₚ x))
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem equivQuotientMapOfIsMaximal_apply_mk [P.IsMaximal] (x : S) :
    equivQuotientMapOfIsMaximal p Sₚ P (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap S Sₚ x)) := rfl

@[simp]
/-
**IsLocalization.AtPrime.equivQuotientMapOfIsMaximal_symm_apply_mk** 是 Mathlib 中
的一个定理，位于命名空间 `IsLocalization.AtPrime`。
形式化陈述：equivQuotientMapOfIsMaximal_symm_apply_mk [P.IsMaximal] (x : S) (s : algeb
raMapSubmonoid S p.primeCompl) : (equivQuotientMapOfIsMaximal p Sₚ P).symm (Idea
l.Quotient.mk _ (mk' _ x s)) = (Ideal.Quotient.mk _ x) * (Ideal.Quotient.mk _ s.
val)⁻¹
参数：x : S；s : algebraMapSubmonoid S p.primeCompl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.isPrime_map_of_liesOver`：isPrime_map_of_liesOver 
[P.IsPrime] [P.LiesOver p] : (P.map (algebraMap S Sₚ)).IsPrime
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Ideal.disjoint_primeCompl_of_liesOver`：disjoint_primeCompl_of_liesOver [
p.IsPrime] [hPp : 𝔓.LiesOver p] : Disjoint ((Algebra.algebraMapSubmonoid C p.pri
meCompl) : Set C) (𝔓 : Set …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.map_ne_zero_iff`：map_ne_zero_iff : f x != 0 ↔ x != 0
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `RingEquiv.symm_apply_eq`：symm_apply_eq (e : R ≃+* S) {x : S} {y : R} : e
.symm x = y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 34 条，此处仅展示前 30 条）
-/
theorem equivQuotientMapOfIsMaximal_symm_apply_mk [P.IsMaximal] (x : S)
    (s : algebraMapSubmonoid S p.primeCompl) :
    (equivQuotientMapOfIsMaximal p Sₚ P).symm (Ideal.Quotient.mk _ (mk' _ x s)) =
      (Ideal.Quotient.mk _ x) * (Ideal.Quotient.mk _ s.val)⁻¹ := by
  have : (Ideal.map (algebraMap S Sₚ) P).IsPrime := isPrime_map_of_liesOver S p Sₚ P
  have h₁ : Ideal.Quotient.mk P ↑s ≠ 0 :=
    Quotient.eq_zero_iff_mem.not.mpr <|
      (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver P p) s.prop
  have h₂ : equivQuotientMapOfIsMaximal p Sₚ P (Ideal.Quotient.mk P ↑s) ≠ 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq, ← mul_left_inj' h₂, map_mul, mul_assoc, ← map_mul,
    inv_mul_cancel₀ h₁, map_one, mul_one, equivQuotientMapOfIsMaximal_apply_mk,
    ← map_mul, mk'_spec, Quotient.mk_algebraMap, equivQuotientMapOfIsMaximal_apply_mk,
    Quotient.mk_algebraMap]

variable [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]

/--
The following diagram where the vertical maps are the algebra maps and the horizontal maps are
`Localization.AtPrime.equivQuotMaximalIdeal.symm` and
`Localization.AtPrime.equivQuotientMapOfIsMaximal.symm` commutes:
```
Rₚ ⧸ 𝓂 ──▶ R ⧸ p
  │         │
Sₚ ⧸ 𝒫 ──▶ S ⧸ P
```
Here, `𝓂` denotes the maximal ideal of `Rₚ` and `𝒫` the image of `P` in `Sₚ`.
Note that result is stated in that direction since this is the formulation needed for the proof
of `Localization.AtPrime.inertiaDeg_map_eq_inertiaDeg`.
-/
/-
**IsLocalization.AtPrime.algebraMap_equivQuotMaximalIdeal_symm_apply** 是 Mathlib
 中的一个定理，位于命名空间 `IsLocalization.AtPrime`。
形式化陈述：algebraMap_equivQuotMaximalIdeal_symm_apply [p.IsMaximal] [P.IsMaximal] [(
P.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ)] (x : Rₚ ⧸ maximalIdeal Rₚ) 
: algebraMap (R ⧸ p) (S ⧸ P) ((equivQuotMaximalIdeal p Rₚ).symm x) = (equivQuoti
entMapOfIsMaximal p Sₚ P).symm (algebraMap (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ P.map (a
lgebraMap S Sₚ)) x)
参数：P.map (algebraMap S Sₚ)；maximalIdeal Rₚ；x : Rₚ ⧸ maximalIdeal Rₚ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.AtPrime.equivQuotMaximalIdeal_symm_apply_mk`：equivQuotMax
imalIdeal_symm_apply_mk (x : R) (s : p.primeCompl) : (equivQuotMaximalIdeal p Rₚ
).symm (Ideal.Quotient.mk _ (IsLocalization.mk' …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.mem_algebraMapSubmonoid_of_mem`：mem_algebraMapSubmonoid_of_mem {
M : Submonoid R} (x : M) : algebraMap R S x in algebraMapSubmonoid S M
· 使用定理 `IsLocalization.algebraMap_mk'`：IsLocalization.algebraMap_mk' (x : R) (y 
: M) : algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ x y) = IsLocalization.mk' Sₘ (alg
ebraMap R S x) ⟨alg…
· 使用定理 `IsLocalization.AtPrime.equivQuotientMapOfIsMaximal_symm_apply_mk`：equivQ
uotientMapOfIsMaximal_symm_apply_mk [P.IsMaximal] (x : S) (s : algebraMapSubmono
id S p.primeCompl) : (equivQuotientMapOfIsMaximal p Sₚ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The following diagram where the vertical maps are the algebra maps and the horiz
ontal maps are
`Localization.AtPrime.equivQuotMaximalIdeal.symm` and
`Localization.AtPrime.equivQuotientMapOfIsMaximal.symm` commutes:
```
Rₚ ⧸ 𝓂 ──▶ R ⧸ p
  │         │
Sₚ ⧸ 𝒫 ──▶ S ⧸ P
```
Here, `𝓂` denotes the maximal ideal of `Rₚ` and `𝒫` the image of `P` in `Sₚ`.
Note that result is stated in that direction since this is the formulation neede
d for the proof
of `Localization.AtPrime.inertiaDeg_map_eq_inertiaDeg`.
-/
theorem algebraMap_equivQuotMaximalIdeal_symm_apply [p.IsMaximal] [P.IsMaximal]
    [(P.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ)] (x : Rₚ ⧸ maximalIdeal Rₚ) :
    algebraMap (R ⧸ p) (S ⧸ P) ((equivQuotMaximalIdeal p Rₚ).symm x) =
    (equivQuotientMapOfIsMaximal p Sₚ P).symm
      (algebraMap (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ P.map (algebraMap S Sₚ)) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := mk'_surjective p.primeCompl x
  simp [equivQuotMaximalIdeal_symm_apply_mk, map_mul, Quotient.algebraMap_mk_of_liesOver,
    IsLocalization.algebraMap_mk' S Rₚ Sₚ]

-- Lean thinks that the instance [p.IsPrime] is not necessary here, but it is needed
-- for the definition of `Rₚ`.
set_option linter.unusedSectionVars false in
@[simp]
/-
**IsLocalization.AtPrime.equivQuotientMapMaximalIdeal_apply_mk** 是 Mathlib 中的一个定
理，位于命名空间 `IsLocalization.AtPrime`。
形式化陈述：equivQuotientMapMaximalIdeal_apply_mk [p.IsMaximal] (x : S) : equivQuotien
tMapMaximalIdeal S p Rₚ Sₚ (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk _ (algeb
raMap S Sₚ x))
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem equivQuotientMapMaximalIdeal_apply_mk [p.IsMaximal] (x : S) :
    equivQuotientMapMaximalIdeal S p Rₚ Sₚ (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap S Sₚ x)) := rfl
/-
**IsLocalization.AtPrime.inertiaDeg_map_eq_inertiaDeg** 是 Mathlib 中的一个定理，位于命名空间 
`IsLocalization.AtPrime`。
形式化陈述：inertiaDeg_map_eq_inertiaDeg [p.IsMaximal] [P.IsMaximal] [(Ideal.map (alge
braMap S Sₚ) P).LiesOver (maximalIdeal Rₚ)] : (maximalIdeal Rₚ).inertiaDeg' (P.m
ap (algebraMap S Sₚ)) = p.inertiaDeg' P
参数：Ideal.map (algebraMap S Sₚ) P；maximalIdeal Rₚ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg'_algebraMap`：∀ {R : Type u} [inst : CommRing R] {S : Ty
pe v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)  
 [inst_3 : P.LiesO…
· 使用定理 `Algebra.finrank_eq_of_equiv_equiv`：finrank_eq_of_equiv_equiv {R₀ S₀ : Ty
pe*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀] {R₁ S₁ : Type*} [CommSemiri
ng R₁] [Semiring S₁] [A…
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `IsLocalization.AtPrime.algebraMap_equivQuotMaximalIdeal_symm_apply`：alge
braMap_equivQuotMaximalIdeal_symm_apply [p.IsMaximal] [P.IsMaximal] [(P.map (alg
ebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ)] (x : Rₚ ⧸ max…
-/
theorem inertiaDeg_map_eq_inertiaDeg [p.IsMaximal] [P.IsMaximal]
    [(Ideal.map (algebraMap S Sₚ) P).LiesOver (maximalIdeal Rₚ)] :
    (maximalIdeal Rₚ).inertiaDeg' (P.map (algebraMap S Sₚ)) = p.inertiaDeg' P := by
  rw [inertiaDeg'_algebraMap, inertiaDeg'_algebraMap]
  refine Algebra.finrank_eq_of_equiv_equiv (equivQuotMaximalIdeal p Rₚ).symm
    (equivQuotientMapOfIsMaximal p Sₚ P).symm ?_
  ext x
  exact algebraMap_equivQuotMaximalIdeal_symm_apply p Rₚ Sₚ P x

include p in
/-
**IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx** 是 Mathlib 中的一个
定理，位于命名空间 `IsLocalization.AtPrime`。
形式化陈述：ramificationIdx_map_eq_ramificationIdx [P.IsPrime] : (P.map (algebraMap S 
Sₚ)).ramificationIdx Rₚ = P.ramificationIdx R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.liesOver_map_of_liesOver`：liesOver_map_of_liesOve
r [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] [P.IsPrime] : (P
.map (algebraMap S Sₚ)).LiesOver (IsL…
· 使用定理 `IsLocalization.liesOver_map_of_isPrime_disjoint`：liesOver_map_of_isPrime
_disjoint {I : Ideal R} [I.IsPrime] (hM : Disjoint (M : Set R) I) : (I.map (alge
braMap R S)).LiesOver I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_image_left`：disjoint_image_left {f : α -> β} {s : Set α} {t
 : Set β} : Disjoint (f '' s) t ↔ Disjoint s (f ⁻¹' t)
· 使用引理 `Set.disjoint_compl_left_iff_subset`：disjoint_compl_left_iff_subset : Dis
joint sᶜ t ↔ t subseteq s
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `IsLocalization.AtPrime.isPrime_map_of_liesOver`：isPrime_map_of_liesOver 
[P.IsPrime] [P.LiesOver p] : (P.map (algebraMap S Sₚ)).IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdx_eq`：ramificationIdx_eq [q.LiesOver p] [q.IsPrime] 
: letI Sq
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`：isL
ocalization_isLocalization_atPrime_isLocalization (p : Ideal S) [Hp : p.IsPrime]
 [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `IsLocalization.AtPrime.map_eq_maximalIdeal`：map_eq_maximalIdeal : p.map 
(algebraMap R Rₚ) = maximalIdeal Rₚ
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Ideal.comap_map_of_bijective`：comap_map_of_bijective : (I.map f).comap f
 = I
· 使用引理 `Module.length_quotient`：Module.length_quotient {N : Submodule R M} : Mod
ule.length R (M ⧸ N) = Order.coheight N
· 使用定理 `Ideal.coheight_comap_of_surjective`：coheight_comap_of_surjective (hf : F
unction.Surjective f) (I : Ideal S) : Order.coheight (I.comap f) = Order.coheigh
t I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ramificationIdx_map_eq_ramificationIdx [P.IsPrime] :
    (P.map (algebraMap S Sₚ)).ramificationIdx Rₚ = P.ramificationIdx R := by
  have := liesOver_map_of_liesOver p Rₚ Sₚ P
  have := IsLocalization.liesOver_map_of_isPrime_disjoint (algebraMapSubmonoid S p.primeCompl) Sₚ
    (Set.disjoint_image_left.mpr (Set.disjoint_compl_left_iff_subset.mpr hPp.over.ge))
  have := isPrime_map_of_liesOver S p Sₚ P
  rw [ramificationIdx_eq (maximalIdeal Rₚ) (P.map (algebraMap S Sₚ)), ramificationIdx_eq p P]
  let R₁ := Localization.AtPrime (P.map (algebraMap S Sₚ))
  let R₂ := Localization.AtPrime P
  let : Algebra R₂ R₁ := Localization.AtPrime.algebraOfLiesOver P (P.map (algebraMap S Sₚ))
  have : IsLocalization.AtPrime R₁ P := by
    convert isLocalization_isLocalization_atPrime_isLocalization
      (algebraMapSubmonoid S p.primeCompl) R₁ (P.map (algebraMap S Sₚ))
    rw [← Ideal.under_def, ← Ideal.over_def (P.map (algebraMap S Sₚ)) P]
  have h : Function.Bijective (algebraMap R₂ R₁) :=
    (Localization.algEquiv P.primeCompl R₁).bijective
  have key : p.map (algebraMap R R₂) =
      ((maximalIdeal Rₚ).map (algebraMap Rₚ R₁)).comap (algebraMap R₂ R₁) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, p.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R R₂ R₁, ← p.map_map, comap_map_of_bijective _ h]
  rw [Module.length_quotient, Module.length_quotient, key, coheight_comap_of_surjective _ h.2]

end IsLocalization.AtPrime

namespace IsDedekindDomain

open IsLocalization AtPrime

variable [IsDomain R] [IsDedekindDomain S] [IsTorsionFree R S] [Algebra R Sₚ] [IsScalarTower R S Sₚ]
  [IsScalarTower R Rₚ Sₚ]

set_option backward.isDefEq.respectTransparency.types false in
/--
For `R ⊆ S` an extension of Dedekind domains and `p` a prime ideal of `R`, the bijection
between the primes of `S` over `p` and the primes over the maximal ideal of `Rₚ` in `Sₚ` where
`Rₚ` and `Sₚ` are resp. the localizations of `R` and `S` at the complement of `p`.
-/
/-
**IsDedekindDomain.primesOverEquivPrimesOver** 是 Mathlib 中的一个定义，位于命名空间 `IsDedeki
ndDomain`。
形式化陈述：primesOverEquivPrimesOver (hp : p != ⊥) : p.primesOver S ≃o (maximalIdeal 
Rₚ).primesOver Sₚ where toFun P
参数：hp : p != ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `R ⊆ S` an extension of Dedekind domains and `p` a prime ideal of `R`, the b
ijection
between the primes of `S` over `p` and the primes over the maximal ideal of `Rₚ`
 in `Sₚ` where
`Rₚ` and `Sₚ` are resp. the localizations of `R` and `S` at the complement of `p
`.
-/
noncomputable def primesOverEquivPrimesOver (hp : p ≠ ⊥) :
    p.primesOver S ≃o (maximalIdeal Rₚ).primesOver Sₚ where
  toFun P := ⟨map (algebraMap S Sₚ) P.1, isPrime_map_of_liesOver S p Sₚ P.1,
    liesOver_map_of_liesOver p Rₚ Sₚ P.1⟩
  map_rel_iff' {Q Q'} := by
    refine ⟨fun h ↦ ?_, fun h ↦ map_mono h⟩
    have : Q'.1.IsMaximal :=
      (primesOver.isPrime p Q').isMaximal (ne_bot_of_mem_primesOver hp Q'.prop)
    simpa [under_map_of_isMaximal S p] using le_comap_of_map_le h
  invFun Q := ⟨comap (algebraMap S Sₚ) Q.1, IsPrime.under S Q.1,
    liesOver_comap_of_liesOver p Rₚ Q.1⟩
  left_inv P := by
    have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
      (ne_bot_of_mem_primesOver hp P.prop) (primesOver.isPrime p P)
    exact SetCoe.ext <| IsLocalization.AtPrime.under_map_of_isMaximal S p Sₚ P.1
  right_inv Q := SetCoe.ext <| map_under (algebraMapSubmonoid S p.primeCompl) Sₚ Q

@[simp]
/-
**IsDedekindDomain.primesOverEquivPrimesOver_apply** 是 Mathlib 中的一个定理，位于命名空间 `Is
DedekindDomain`。
形式化陈述：primesOverEquivPrimesOver_apply (hp : p != ⊥) (P : p.primesOver S) : prime
sOverEquivPrimesOver p Rₚ Sₚ hp P = Ideal.map (algebraMap S Sₚ) P
参数：hp : p != ⊥；P : p.primesOver S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem primesOverEquivPrimesOver_apply (hp : p ≠ ⊥) (P : p.primesOver S) :
    primesOverEquivPrimesOver p Rₚ Sₚ hp P = Ideal.map (algebraMap S Sₚ) P := rfl

@[simp]
/-
**IsDedekindDomain.primesOverEquivPrimesOver_symm_apply** 是 Mathlib 中的一个定理，位于命名空
间 `IsDedekindDomain`。
形式化陈述：primesOverEquivPrimesOver_symm_apply (hp : p != ⊥) (Q : (maximalIdeal Rₚ).
primesOver Sₚ) : ((primesOverEquivPrimesOver p Rₚ Sₚ hp).symm Q).1 = Ideal.comap
 (algebraMap S Sₚ) Q
参数：hp : p != ⊥；Q : (maximalIdeal Rₚ).primesOver Sₚ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem primesOverEquivPrimesOver_symm_apply (hp : p ≠ ⊥) (Q : (maximalIdeal Rₚ).primesOver Sₚ) :
    ((primesOverEquivPrimesOver p Rₚ Sₚ hp).symm Q).1 = Ideal.comap (algebraMap S Sₚ) Q := rfl
/-
**IsDedekindDomain.primesOverEquivPrimesOver_inertiagDeg_eq** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain`。
形式化陈述：primesOverEquivPrimesOver_inertiagDeg_eq [p.IsMaximal] (hp : p != ⊥) (P : 
p.primesOver S) : (maximalIdeal Rₚ).inertiaDeg' (primesOverEquivPrimesOver p Rₚ 
Sₚ hp P : Ideal Sₚ) = p.inertiaDeg' P.val
参数：hp : p != ⊥；P : p.primesOver S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.DimensionLEOne.maximalOfPrime`：∀ {R : Type u_1} {inst : CommRing R}
 [self : Ring.DimensionLEOne R] {p : Ideal R}, p ≠ ⊥ → p.IsPrime → p.IsMaximal
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.ne_bot_of_mem_primesOver`：ne_bot_of_mem_primesOver [FaithfulSMul A
 B] (hp : p != ⊥) {P : Ideal B} (hP : P in p.primesOver B) : P != ⊥
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Ideal.primesOver.isPrime`：∀ {A : Type u_2} [inst : CommSemiring A] (p : 
Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.
primesOver B))…
· 使用定理 `IsLocalization.AtPrime.liesOver_map_of_liesOver`：liesOver_map_of_liesOve
r [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] [P.IsPrime] : (P
.map (algebraMap S Sₚ)).LiesOver (IsL…
· 使用定理 `Ideal.primesOver.liesOver`：∀ {A : Type u_2} [inst : CommSemiring A] (p :
 Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p
.primesOver B))…
· 使用定理 `IsLocalization.AtPrime.inertiaDeg_map_eq_inertiaDeg`：inertiaDeg_map_eq_i
nertiaDeg [p.IsMaximal] [P.IsMaximal] [(Ideal.map (algebraMap S Sₚ) P).LiesOver 
(maximalIdeal Rₚ)] : (maximalIdeal Rₚ).in…
-/
theorem primesOverEquivPrimesOver_inertiagDeg_eq [p.IsMaximal] (hp : p ≠ ⊥) (P : p.primesOver S) :
    (maximalIdeal Rₚ).inertiaDeg' (primesOverEquivPrimesOver p Rₚ Sₚ hp P : Ideal Sₚ) =
      p.inertiaDeg' P.val := by
  have : NeZero p := ⟨hp⟩
  have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
    (ne_bot_of_mem_primesOver (NeZero.ne _) P.prop) inferInstance
  have : (P.1.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ) := liesOver_map_of_liesOver p _ _ _
  exact inertiaDeg_map_eq_inertiaDeg p _ _ _
/-
**IsDedekindDomain.primesOverEquivPrimesOver_ramificationIdx_eq** 是 Mathlib 中的一个
定理，位于命名空间 `IsDedekindDomain`。
形式化陈述：primesOverEquivPrimesOver_ramificationIdx_eq (hp : p != ⊥) (P : p.primesOv
er S) : (primesOverEquivPrimesOver p Rₚ Sₚ hp P : Ideal Sₚ).ramificationIdx Rₚ =
 P.val.ramificationIdx R
参数：hp : p != ⊥；P : p.primesOver S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx`：ramificat
ionIdx_map_eq_ramificationIdx [P.IsPrime] : (P.map (algebraMap S Sₚ)).ramificati
onIdx Rₚ = P.ramificationIdx R
· 使用定理 `Ideal.primesOver.liesOver`：∀ {A : Type u_2} [inst : CommSemiring A] (p :
 Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p
.primesOver B))…
· 使用定理 `Ideal.primesOver.isPrime`：∀ {A : Type u_2} [inst : CommSemiring A] (p : 
Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.
primesOver B))…
-/
theorem primesOverEquivPrimesOver_ramificationIdx_eq (hp : p ≠ ⊥) (P : p.primesOver S) :
    (primesOverEquivPrimesOver p Rₚ Sₚ hp P : Ideal Sₚ).ramificationIdx Rₚ =
      P.val.ramificationIdx R :=
  ramificationIdx_map_eq_ramificationIdx p _ _ _

end IsDedekindDomain

