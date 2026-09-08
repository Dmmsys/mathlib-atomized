/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!

# Krull dimension and non-zero-divisors

## Main results
- `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`: If `r` is not a zero divisor, then
  `dim R/r + 1 ≤ dim R`.
- `ringKrullDim_succ_le_ringKrullDim_polynomial`: `dim R + 1 ≤ dim R[X]`.
- `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial`: `dim R + #σ ≤ dim R[σ]`.
-/

public section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S]

/-
**ringKrullDim_quotient** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_quotient (I : Ideal R) : ringKrullDim (R ⧸ I) = Order.krullDi
m (PrimeSpectrum.zeroLocus (R
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ringKrullDim.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R], ringKrullDi
m R = Order.krullDim (PrimeSpectrum R)
· 使用引理 `Order.krullDim_eq_of_orderIso`：krullDim_eq_of_orderIso (f : α ≃o β) : kr
ullDim α = krullDim β
-/
lemma ringKrullDim_quotient (I : Ideal R) :
    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]

set_option backward.isDefEq.respectTransparency false in
/-
**ringKrullDim_quotient_succ_le_of_nonZeroDivisor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_quotient_succ_le_of_nonZeroDivisor {r : R} (hr : r in R⁰) : r
ingKrullDim (R ⧸ Ideal.span {r}) + 1 <= ringKrullDim R
参数：hr : r in R⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ringKrullDim_eq_bot_of_subsingleton`：ringKrullDim_eq_bot_of_subsingleton
 [Subsingleton R] : ringKrullDim R = ⊥
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `PrimeSpectrum.zeroLocus_empty_iff_eq_top`：zeroLocus_empty_iff_eq_top {I 
: Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.nontrivial_iff`：∀ {R : Type u_3} [inst : Ring R] {I : Ide
al R}, Nontrivial (R ⧸ I) ↔ I ≠ ⊤
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `ringKrullDim_quotient`：ringKrullDim_quotient (I : Ideal R) : ringKrullDi
m (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R
· 使用引理 `Order.krullDim_eq_iSup_length`：krullDim_eq_iSup_length [Nonempty α] : kr
ullDim α = ⨆ (p : LTSeries α), (p.length : Nat∞)
· 使用定理 `ringKrullDim.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R], ringKrullDi
m R = Order.krullDim (PrimeSpectrum R)
· 使用定理 `PrimeSpectrum.instNonemptyOfNontrivial`：∀ {R : Type u} [inst : CommSemir
ing R] [Nontrivial R], Nonempty (PrimeSpectrum R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_one`：∀ {α : Type u} [inst : One α], ↑1 = 1
· 使用定理 `WithBot.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用引理 `ENat.iSup_add`：iSup_add [Nonempty ι] (f : ι -> Nat∞) : (⨆ i, f i) + a = 
⨆ i, f i + a
· 使用定理 `RelSeries.instNonempty`：∀ {α : Type u_1} (r : SetRel α α) [Nonempty α], 
Nonempty (RelSeries r)
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
（共 42 条，此处仅展示前 30 条）
-/
lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    {r : R} (hr : r ∈ R⁰) :
    ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R := by
  by_cases hr' : Ideal.span {r} = ⊤
  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {r})) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial_iff.mpr hr'
  have := (Ideal.Quotient.mk (Ideal.span {r})).domain_nontrivial
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le (J := l.head.1.asIdeal) bot_le
  let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
  have hp' : p' < l.head := lt_of_le_of_ne hp' fun h ↦ Set.disjoint_iff.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp)
    ⟨show r ∈ p by simpa [← h] using l.head.2, hr⟩
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ ↦ id)).cons p' hp'))
  simp

/-- If `R →+* S` is surjective whose kernel contains a nonzero divisor, then `dim S + 1 ≤ dim R`. -/
/-
**ringKrullDim_succ_le_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_succ_le_of_surjective (f : R ->+* S) (hf : Function.Surjectiv
e f) {r : R} (hr : r in R⁰) (hr' : f r = 0) : ringKrullDim S + 1 <= ringKrullDim
 R
参数：f : R ->+* S；hf : Function.Surjective f；hr : r in R⁰；hr' : f r = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ringKrullDim_le_of_surjective`：ringKrullDim_le_of_surjective (f : R ->+*
 S) (hf : Function.Surjective f) : ringKrullDim S <= ringKrullDim R
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Ideal.Quotient.lift_surjective_of_surjective`：lift_surjective_of_surject
ive {f : R ->+* S} (H : forall a : R, a in I -> f a = 0) (hf : Function.Surjecti
ve f) : Function.Surjective (Ideal…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`：ringKrullDim_quotient_s
ucc_le_of_nonZeroDivisor {r : R} (hr : r in R⁰) : ringKrullDim (R ⧸ Ideal.span {
r}) + 1 <= ringKrullDim R

--- 原说明 ---
If `R →+* S` is surjective whose kernel contains a nonzero divisor, then `dim S 
+ 1 ≤ dim R`.
-/
lemma ringKrullDim_succ_le_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    {r : R} (hr : r ∈ R⁰) (hr' : f r = 0) : ringKrullDim S + 1 ≤ ringKrullDim R := by
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ f (RingHom.ker f
    |>.span_singleton_le_iff_mem.mpr hr')) (Ideal.Quotient.lift_surjective_of_surjective _ _ hf)

open Polynomial in
/-
**ringKrullDim_succ_le_ringKrullDim_polynomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_succ_le_ringKrullDim_polynomial : ringKrullDim R + 1 <= ringK
rullDim R[X]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ringKrullDim_succ_le_of_surjective`：ringKrullDim_succ_le_of_surjective (
f : R ->+* S) (hf : Function.Surjective f) {r : R} (hr : r in R⁰) (hr' : f r = 0
) : ringKrullDim S + 1 <…
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用引理 `Polynomial.X_mem_nonzeroDivisors`：X_mem_nonzeroDivisors : X in R[X]⁰
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
-/
lemma ringKrullDim_succ_le_ringKrullDim_polynomial :
    ringKrullDim R + 1 ≤ ringKrullDim R[X] :=
  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, coeff_C_zero⟩)
    X_mem_nonzeroDivisors coeff_X_zero

open MvPolynomial in
@[simp]
/-
**ringKrullDim_mvPolynomial_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_mvPolynomial_of_isEmpty (σ : Type*) [IsEmpty σ] : ringKrullDi
m (MvPolynomial σ R) = ringKrullDim R
参数：σ : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ringKrullDim_eq_of_ringEquiv`：ringKrullDim_eq_of_ringEquiv (e : R ≃+* S)
 : ringKrullDim R = ringKrullDim S
-/
lemma ringKrullDim_mvPolynomial_of_isEmpty (σ : Type*) [IsEmpty σ] :
    ringKrullDim (MvPolynomial σ R) = ringKrullDim R :=
  ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv _ _)

open MvPolynomial in
/-
**ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (σ : Type*) [Finite 
σ] : ringKrullDim R + Nat.card σ <= ringKrullDim (MvPolynomial σ R)
参数：σ : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `ringKrullDim_eq_of_ringEquiv`：ringKrullDim_eq_of_ringEquiv (e : R ≃+* S)
 : ringKrullDim R = ringKrullDim S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `ringKrullDim_mvPolynomial_of_isEmpty`：ringKrullDim_mvPolynomial_of_isEmp
ty (σ : Type*) [IsEmpty σ] : ringKrullDim (MvPolynomial σ R) = ringKrullDim R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_option`：Fintype.card_option {α : Type*} [Fintype α] : Finty
pe.card (Option α) = Fintype.card α + 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `ringKrullDim_succ_le_ringKrullDim_polynomial`：ringKrullDim_succ_le_ringK
rullDim_polynomial : ringKrullDim R + 1 <= ringKrullDim R[X]
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
lemma ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (σ : Type*) [Finite σ] :
    ringKrullDim R + Nat.card σ ≤ ringKrullDim (MvPolynomial σ R) := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    convert! ← H using 1
    · rw [Nat.card_congr e]
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    grw [IH, ringKrullDim_succ_le_ringKrullDim_polynomial]
    exact (ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv).ge

open MvPolynomial in
/-
**ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial (σ : Type*) : ringK
rullDim R + ENat.card σ <= ringKrullDim (MvPolynomial σ R)
参数：σ : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ringKrullDim_eq_bot_of_subsingleton`：ringKrullDim_eq_bot_of_subsingleton
 [Subsingleton R] : ringKrullDim R = ⊥
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用引理 `ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial`：ringKrullDim_add_
natCard_le_ringKrullDim_mvPolynomial (σ : Type*) [Finite σ] : ringKrullDim R + N
at.card σ <= ringKrullDim (MvPolynomial σ R…
· 使用定理 `ENat.card_eq_top_of_infinite`：card_eq_top_of_infinite [Infinite α] : car
d α = ⊤
· 使用引理 `ENat.WithBot.eq_top_iff_forall_ge`：eq_top_iff_forall_ge {n : WithBot Nat
∞} : n = ⊤ ↔ forall m : Nat, m <= n
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.invFun_surjective`：invFun_surjective (hf : Injective f) : Surje
ctive (invFun f)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
（共 42 条，此处仅展示前 30 条）
-/
lemma ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial (σ : Type*) :
    ringKrullDim R + ENat.card σ ≤ ringKrullDim (MvPolynomial σ R) := by
  nontriviality R
  cases finite_or_infinite σ
  · rw [ENat.card_eq_coe_natCard]
    push_cast
    exact ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _
  · simp only [ENat.card_eq_top_of_infinite, WithBot.coe_top]
    suffices ringKrullDim (MvPolynomial σ R) = ⊤ by simp_all
    rw [ENat.WithBot.eq_top_iff_forall_ge]
    intro n
    let ι := Infinite.natEmbedding σ ∘ Fin.val (n := n + 1)
    have := Function.invFun_surjective (f := ι) ((Infinite.natEmbedding σ).2.comp Fin.val_injective)
    refine le_trans ?_ (ringKrullDim_le_of_surjective
      (rename (R := R) _).toRingHom (rename_surjective _ this))
    refine le_trans ?_ (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _)
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    trans n + 1
    · norm_cast
      simp
    · exact WithBot.le_add_self Order.bot_lt_krullDim.ne' _

open PowerSeries in
/-
**ringKrullDim_succ_le_ringKrullDim_powerseries** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_succ_le_ringKrullDim_powerseries : ringKrullDim R + 1 <= ring
KrullDim (PowerSeries R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ringKrullDim_succ_le_of_surjective`：ringKrullDim_succ_le_of_surjective (
f : R ->+* S) (hf : Function.Surjective f) {r : R} (hr : r in R⁰) (hr' : f r = 0
) : ringKrullDim S + 1 <…
· 使用引理 `MvPowerSeries.X_mem_nonzeroDivisors`：X_mem_nonzeroDivisors {i : σ} : X i
 in (MvPowerSeries σ R)⁰
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
-/
lemma ringKrullDim_succ_le_ringKrullDim_powerseries :
    ringKrullDim R + 1 ≤ ringKrullDim (PowerSeries R) :=
  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, rfl⟩)
    MvPowerSeries.X_mem_nonzeroDivisors constantCoeff_X
