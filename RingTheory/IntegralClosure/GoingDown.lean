/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal

/-!

# Going down for integrally closed domains

In this file, we provide the instance that any integral extension of `R ⊆ S` satisfies going down
if `R` is integrally closed.

-/

public section

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-
**Polynomial.coeff_mem_radical_span_coeff_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Polynomial.coeff_mem_radical_span_coeff_of_dvd (p : R[X]) (q : R[X]) (hp :
 p.Monic) (hq : q.Monic) (H : q ∣ p) (i : Nat) (hi : i != q.natDegree) : q.coeff
 i in (Ideal.span { p.coeff i | i < p.natDegree }).radical
参数：p : R[X]；q : R[X]；hp : p.Monic；hq : q.Monic；H : q ∣ p；i : Nat；hi : i != q.nat
Degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
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
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dvd_prime_pow`：dvd_prime_pow [CommMonoidWithZero M] [IsCancelMulZero M] 
{p q : M} (hp : Prime p) (n : Nat) : q ∣ p ^ n ↔ exists i <= n, Associated q (p 
^ i…
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
（共 48 条，此处仅展示前 30 条）
-/
lemma Polynomial.coeff_mem_radical_span_coeff_of_dvd
    (p : R[X]) (q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (H : q ∣ p) (i : ℕ) (hi : i ≠ q.natDegree) :
    q.coeff i ∈ (Ideal.span { p.coeff i | i < p.natDegree }).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hPJ, hP⟩
  have : p.map (Ideal.Quotient.mk P) = X ^ p.natDegree := by
    ext i
    obtain hi | rfl | hi := lt_trichotomy i p.natDegree
    · simpa [hi.ne, Ideal.Quotient.eq_zero_iff_mem] using hPJ (Ideal.subset_span ⟨_, hi, rfl⟩)
    · simp [hp]
    · simp [coeff_eq_zero_of_natDegree_lt hi, hi.ne']
  obtain ⟨j, hj, a, ha⟩ :=
    (dvd_prime_pow (prime_X (R := R ⧸ P)) _).mp (this ▸ map_dvd (Ideal.Quotient.mk P) H)
  obtain ⟨r, hr, e⟩ := isUnit_iff.mp a⁻¹.isUnit
  rw [← Units.eq_mul_inv_iff_mul_eq, ← e] at ha
  obtain rfl : j = q.natDegree := by
    simpa [hq.natDegree_map, hr.ne_zero] using congr(($ha).natDegree).symm
  simpa [hi, Ideal.Quotient.eq_zero_iff_mem] using congr(($ha).coeff i)

@[stacks 00H8]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R] :
    Algebra.HasGoingDown R S := by
  have := (FaithfulSMul.algebraMap_injective R S).isDomain
  constructor
  intro p _ Q _ hpQ
  let SQ := Localization.AtPrime Q
  suffices (p.map (algebraMap _ SQ)).comap (algebraMap _ SQ) ≤ p by
    obtain ⟨P, hP, e⟩ :=
      (Ideal.comap_map_eq_self_iff_of_isPrime _).mp (this.antisymm Ideal.le_comap_map)
    refine ⟨P.under S, ?_, inferInstance, ⟨by rw [Ideal.under_under, ← e]⟩⟩
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime P)).trans_eq
      Localization.AtPrime.under_maximalIdeal
  intro x hx
  obtain ⟨a, ha, haQ⟩ : ∃ a, x • a ∈ Ideal.map (algebraMap R S) p ∧ a ∉ Q := by
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_eq R S SQ, ← Ideal.map_map,
      IsLocalization.mem_map_algebraMap_iff Q.primeCompl, ← map_mul] using hx
  obtain ⟨f, hfm, hfa, hf⟩ := exists_monic_aeval_eq_zero_forall_mem_of_mem_map ha
  obtain ⟨i, hi, hip⟩ : ∃ i ≠ (minpoly R a).natDegree, (minpoly R a).coeff i ∉ p := by
    set g := minpoly R a
    by_contra! H
    have : g.map (Ideal.Quotient.mk p) = X ^ g.natDegree := by
      ext i
      obtain hi | rfl | hi := lt_trichotomy i g.natDegree
      · simpa [hi.ne, Ideal.Quotient.eq_zero_iff_mem] using H _ hi.ne
      · simp [g, minpoly.monic (Algebra.IsIntegral.isIntegral _)]
      · simp [coeff_eq_zero_of_natDegree_lt hi, hi.ne']
    have : Ideal.Quotient.mk (Ideal.map (algebraMap R S) p) (a ^ (minpoly R a).natDegree) = 0 := by
      simpa [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply, g] using
        congr(aeval (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p) a) $this).symm
    exact haQ (‹Q.IsPrime›.mem_of_pow_mem _
      (Ideal.map_le_iff_le_comap.mpr hpQ.le (Ideal.Quotient.eq_zero_iff_mem.mp this)))
  by_cases hx0 : x = 0; · simp [hx0]
  have := Polynomial.coeff_mem_radical_span_coeff_of_dvd _ _ hfm
    (minpoly.monic (Algebra.IsIntegral.isIntegral _))
    (minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral _) hfa)
  simp only [IsIntegrallyClosed.minpoly_smul hx0 (Algebra.IsIntegral.isIntegral _),
    natDegree_scaleRoots, coeff_scaleRoots, Ideal.radical_eq_sInf, Submodule.mem_sInf,
    Set.mem_ofPred_eq, and_imp] at this
  refine ‹p.IsPrime›.mem_of_pow_mem _ ((‹p.IsPrime›.mem_or_mem
    (this i hi p ?_ inferInstance)).resolve_left hip)
  simp +contextual [Ideal.span_le, Set.subset_def, LT.lt.ne, hf]
