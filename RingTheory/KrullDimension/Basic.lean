/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic  -- shake: keep (used in `proof_wanted` only)
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Krull dimensions of (commutative) rings

Given a commutative ring, its ring-theoretic Krull dimension is the order-theoretic Krull dimension
of its prime spectrum. Unfolding this definition, it is the length of the longest sequence(s) of
prime ideals ordered by strict inclusion.
-/

@[expose] public section

open Order

/--
The ring-theoretic Krull dimension is the Krull dimension of its spectrum ordered by inclusion.
-/
/-
**ringKrullDim** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ringKrullDim (R : Type*) [CommSemiring R] : WithBot Nat∞
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring-theoretic Krull dimension is the Krull dimension of its spectrum ordere
d by inclusion.
-/
noncomputable def ringKrullDim (R : Type*) [CommSemiring R] : WithBot ℕ∞ :=
  krullDim (PrimeSpectrum R)

/-- Type class for rings with krull dimension at most `n`. -/
/-
**Ring.KrullDimLE** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE (n : Nat) (R : Type*) [CommSemiring R] : Prop
参数：n : Nat；R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for rings with krull dimension at most `n`.
-/
abbrev Ring.KrullDimLE (n : ℕ) (R : Type*) [CommSemiring R] : Prop :=
  Order.KrullDimLE n (PrimeSpectrum R)

variable {R S : Type*} [CommSemiring R] [CommSemiring S]
/-
**Ring.krullDimLE_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.krullDimLE_iff {n : Nat} : KrullDimLE n R ↔ ringKrullDim R <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.krullDimLE_iff`：∀ (n : ℕ) (α : Type u_1) [inst : Preorder α], Orde
r.KrullDimLE n α ↔ Order.krullDim α ≤ ↑n
-/
lemma Ring.krullDimLE_iff {n : ℕ} :
    KrullDimLE n R ↔ ringKrullDim R ≤ n := Order.krullDimLE_iff n (PrimeSpectrum R)

@[nontriviality]
/-
**ringKrullDim_eq_bot_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] : ringKrullDim R = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_eq_bot`：krullDim_eq_bot [IsEmpty α] : krullDim α = ⊥
· 使用定理 `PrimeSpectrum.instIsEmptyOfSubsingleton`：∀ {R : Type u} [inst : CommSemi
ring R] [Subsingleton R], IsEmpty (PrimeSpectrum R)
-/
lemma ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] :
    ringKrullDim R = ⊥ :=
  krullDim_eq_bot
/-
**ringKrullDim_nonneg_of_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_nonneg_of_nontrivial [Nontrivial R] : 0 <= ringKrullDim R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_nonneg`：krullDim_nonneg [Nonempty α] : 0 <= krullDim α
· 使用定理 `PrimeSpectrum.instNonemptyOfNontrivial`：∀ {R : Type u} [inst : CommSemir
ing R] [Nontrivial R], Nonempty (PrimeSpectrum R)
-/
lemma ringKrullDim_nonneg_of_nontrivial [Nontrivial R] :
    0 ≤ ringKrullDim R :=
  krullDim_nonneg

/-- If `f : R →+* S` is surjective, then `ringKrullDim S ≤ ringKrullDim R`. -/
/-
**ringKrullDim_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ringKrullDim_le_of_surjective (f : R ->+* S) (hf : Function.Surjective f) 
: ringKrullDim S <= ringKrullDim R
参数：f : R ->+* S；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_le_of_strictMono`：krullDim_le_of_strictMono (f : α -> β) 
(hf : StrictMono f) : krullDim α <= krullDim β
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.ext_iff`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : P
rimeSpectrum R}, x = y ↔ x.asIdeal = y.asIdeal
· 使用定理 `Ideal.comap_injective_of_surjective`：comap_injective_of_surjective : Inj
ective (comap f)
· 使用定理 `PrimeSpectrum.mk.injEq`：∀ {R : Type u_1} [inst : CommSemiring R] (asIdea
l : Ideal R) (isPrime : asIdeal.IsPrime) (asIdeal_1 : Ideal R)   (isPrime_1 : as
Ideal_1.IsPr…

--- 原说明 ---
If `f : R →+* S` is surjective, then `ringKrullDim S ≤ ringKrullDim R`.
-/
theorem ringKrullDim_le_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    ringKrullDim S ≤ ringKrullDim R :=
  krullDim_le_of_strictMono (fun I ↦ ⟨Ideal.comap f I.asIdeal, inferInstance⟩)
    (Monotone.strictMono_of_injective (fun _ _ hab ↦ Ideal.comap_mono hab)
      (fun _ _ h => PrimeSpectrum.ext_iff.mpr <| Ideal.comap_injective_of_surjective f hf <| by
        simpa using h))

/-- If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`. -/
/-
**ringKrullDim_quotient_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ringKrullDim_quotient_le {R : Type*} [CommRing R] (I : Ideal R) : ringKrul
lDim (R ⧸ I) <= ringKrullDim R
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ringKrullDim_le_of_surjective`：ringKrullDim_le_of_surjective (f : R ->+*
 S) (hf : Function.Surjective f) : ringKrullDim S <= ringKrullDim R
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)

--- 原说明 ---
If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`.
-/
theorem ringKrullDim_quotient_le {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim R :=
  ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective

/-- If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`. -/
/-
**ringKrullDim_eq_of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) : ringKrullDim R = ringKrullDim
 S
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ringKrullDim_le_of_surjective`：ringKrullDim_le_of_surjective (f : R ->+*
 S) (hf : Function.Surjective f) : ringKrullDim S <= ringKrullDim R
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e

--- 原说明 ---
If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`.
-/
theorem ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (ringKrullDim_le_of_surjective e.symm e.symm.surjective)
    (ringKrullDim_le_of_surjective e e.surjective)

alias RingEquiv.ringKrullDim := ringKrullDim_eq_of_ringEquiv

/-- A ring has finite Krull dimension if its `PrimeSpectrum` is
finite-dimensional (and non-empty). -/
/-
**FiniteRingKrullDim** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FiniteRingKrullDim (R : Type*) [CommSemiring R]
参数：R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring has finite Krull dimension if its `PrimeSpectrum` is
finite-dimensional (and non-empty).
-/
abbrev FiniteRingKrullDim (R : Type*) [CommSemiring R] :=
  FiniteDimensionalOrder (PrimeSpectrum R)
/-
**ringKrullDim_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_ne_top [FiniteRingKrullDim R] : ringKrullDim R != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_ne_top_of_finiteDimensionalOrder`：krullDim_ne_top_of_fini
teDimensionalOrder [FiniteDimensionalOrder α] : krullDim α != ⊤
-/
lemma ringKrullDim_ne_top [FiniteRingKrullDim R] :
    ringKrullDim R ≠ ⊤ := krullDim_ne_top_of_finiteDimensionalOrder
/-
**ringKrullDim_lt_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_lt_top [FiniteRingKrullDim R] : ringKrullDim R < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用引理 `ringKrullDim_ne_top`：ringKrullDim_ne_top [FiniteRingKrullDim R] : ringKr
ullDim R != ⊤
-/
lemma ringKrullDim_lt_top [FiniteRingKrullDim R] :
    ringKrullDim R < ⊤ := ringKrullDim_ne_top.lt_top
/-
**ringKrullDim_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_ne_bot [FiniteRingKrullDim R] : ringKrullDim R != ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_ne_bot_of_finiteDimensionalOrder`：krullDim_ne_bot_of_fini
teDimensionalOrder [FiniteDimensionalOrder α] : krullDim α != ⊥
-/
lemma ringKrullDim_ne_bot [FiniteRingKrullDim R] :
    ringKrullDim R ≠ ⊥ := krullDim_ne_bot_of_finiteDimensionalOrder
/-
**finiteRingKrullDim_iff_ne_bot_and_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finiteRingKrullDim_iff_ne_bot_and_top : FiniteRingKrullDim R ↔ (ringKrullD
im R != ⊥ ∧ ringKrullDim R != ⊤)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top`：finiteDimensio
nalOrder_iff_krullDim_ne_bot_and_top : FiniteDimensionalOrder α ↔ krullDim α != 
⊥ ∧ krullDim α != ⊤
-/
lemma finiteRingKrullDim_iff_ne_bot_and_top :
    FiniteRingKrullDim R ↔ (ringKrullDim R ≠ ⊥ ∧ ringKrullDim R ≠ ⊤) :=
  (Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top (α := PrimeSpectrum R))
/-
**Nontrivial.of_finiteRingKrullDim** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nontrivial.of_finiteRingKrullDim [FiniteRingKrullDim R] : Nontrivial R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimeSpectrum.nonempty_iff_nontrivial`：nonempty_iff_nontrivial : Nonempt
y (PrimeSpectrum R) ↔ Nontrivial R
· 使用引理 `LTSeries.nonempty_of_finiteDimensionalOrder`：nonempty_of_finiteDimension
alOrder [FiniteDimensionalOrder α] : Nonempty α
-/
lemma Nontrivial.of_finiteRingKrullDim [FiniteRingKrullDim R] : Nontrivial R := by
  rw [← PrimeSpectrum.nonempty_iff_nontrivial]
  exact LTSeries.nonempty_of_finiteDimensionalOrder _

proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
    [IsNoetherianRing R] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n

section Zero

-- See `Mathlib/RingTheory/KrullDimension/Zero.lean` for further results.

/-
**Ring.krullDimLE_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.krullDimLE_zero_iff : Ring.KrullDimLE 0 R ↔ forall I : Ideal R, I.IsP
rime -> I.IsMaximal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ring.krullDimLE_zero_iff : Ring.KrullDimLE 0 R ↔ ∀ I : Ideal R, I.IsPrime → I.IsMaximal := by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_zero,
    Order.krullDim_nonpos_iff_forall_isMax,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall, PrimeSpectrum.isMax_iff]
  rfl

/-- A ring has krull dimension at most zero if and only if all minimal primes are maximal. -/
/-
**Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal : Ring.KrullDimLE 
0 R ↔ forall I in minimalPrimes R, I.IsMaximal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Ring.krullDimLE_zero_iff`：Ring.krullDimLE_zero_iff : Ring.KrullDimLE 0 R
 ↔ forall I : Ideal R, I.IsPrime -> I.IsMaximal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤

--- 原说明 ---
A ring has krull dimension at most zero if and only if all minimal primes are ma
ximal.
-/
theorem Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal :
    Ring.KrullDimLE 0 R ↔ ∀ I ∈ minimalPrimes R, I.IsMaximal := by
  refine Ring.krullDimLE_zero_iff.trans ⟨fun h I hI ↦ h I hI.1.1, fun h I hI ↦ ?_⟩
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_minimalPrimes_le bot_le (J := I)
  exact (h J hJ).eq_of_le hI.ne_top hle ▸ h J hJ
/-
**Ring.KrullDimLE.mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ring.KrullDimLE.mk₀ (H : ∀ I : Ideal R, I.IsPrime → I.IsMaximal) : Ring.KrullDimLE 0 R := by
  rwa [Ring.krullDimLE_zero_iff]
/-
**Ideal.isMaximal_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.isMaximal_of_isPrime [Ring.KrullDimLE 0 R] (I : Ideal R) [I.IsPrime]
 : I.IsMaximal
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Ring.krullDimLE_zero_iff`：Ring.krullDimLE_zero_iff : Ring.KrullDimLE 0 R
 ↔ forall I : Ideal R, I.IsPrime -> I.IsMaximal
-/
lemma Ideal.isMaximal_of_isPrime [Ring.KrullDimLE 0 R] (I : Ideal R) [I.IsPrime] : I.IsMaximal :=
  Ring.krullDimLE_zero_iff.mp ‹_› I ‹_›

/-- Also see `Ideal.IsPrime.isMaximal` for the analogous statement for Dedekind domains. -/
/-
**Ideal.IsPrime.isMaximal'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.IsPrime.isMaximal' [Ring.KrullDimLE 0 R] {I : Ideal R} (hI : I.IsPri
me) : I.IsMaximal
参数：hI : I.IsPrime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.isMaximal_of_isPrime`：Ideal.isMaximal_of_isPrime [Ring.KrullDimLE 
0 R] (I : Ideal R) [I.IsPrime] : I.IsMaximal

--- 原说明 ---
Also see `Ideal.IsPrime.isMaximal` for the analogous statement for Dedekind doma
ins.
-/
lemma Ideal.IsPrime.isMaximal' [Ring.KrullDimLE 0 R] {I : Ideal R} (hI : I.IsPrime) : I.IsMaximal :=
  I.isMaximal_of_isPrime
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (I : Ideal R) [I.IsPrime] [Ring.KrullDimLE 0 R] : I.IsMaximal :=
  I.isMaximal_of_isPrime
/-
**Ideal.isMaximal_iff_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.isMaximal_iff_isPrime [Ring.KrullDimLE 0 R] {I : Ideal R} : I.IsMaxi
mal ↔ I.IsPrime
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `instIsMaximalOfIsPrimeOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : Com
mSemiring R] (I : Ideal R) [I.IsPrime] [Ring.KrullDimLE 0 R], I.IsMaximal
-/
lemma Ideal.isMaximal_iff_isPrime [Ring.KrullDimLE 0 R] {I : Ideal R} : I.IsMaximal ↔ I.IsPrime :=
  ⟨IsMaximal.isPrime, fun _ ↦ inferInstance⟩
/-
**Ideal.mem_minimalPrimes_of_krullDimLE_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.mem_minimalPrimes_of_krullDimLE_zero [Ring.KrullDimLE 0 R] (I : Idea
l R) [I.IsPrime] : I in minimalPrimes R
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `instIsMaximalOfIsPrimeOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : Com
mSemiring R] (I : Ideal R) [I.IsPrime] [Ring.KrullDimLE 0 R], I.IsMaximal
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `minimalPrimes_eq_minimals`：minimalPrimes_eq_minimals : minimalPrimes R =
 {x | Minimal Ideal.IsPrime x}
-/
lemma Ideal.mem_minimalPrimes_of_krullDimLE_zero [Ring.KrullDimLE 0 R]
    (I : Ideal R) [I.IsPrime] : I ∈ minimalPrimes R :=
  minimalPrimes_eq_minimals (R := R) ▸
    ⟨‹_›, fun J hJ hJI ↦ (IsMaximal.eq_of_le inferInstance IsPrime.ne_top' hJI).ge⟩
/-
**Ideal.mem_minimalPrimes_iff_isPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.mem_minimalPrimes_iff_isPrime [Ring.KrullDimLE 0 R] {I : Ideal R} : 
I in minimalPrimes R ↔ I.IsPrime
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Ideal.mem_minimalPrimes_of_krullDimLE_zero`：Ideal.mem_minimalPrimes_of_k
rullDimLE_zero [Ring.KrullDimLE 0 R] (I : Ideal R) [I.IsPrime] : I in minimalPri
mes R
-/
lemma Ideal.mem_minimalPrimes_iff_isPrime [Ring.KrullDimLE 0 R] {I : Ideal R} :
    I ∈ minimalPrimes R ↔ I.IsPrime :=
  ⟨(·.1.1), fun _ ↦ I.mem_minimalPrimes_of_krullDimLE_zero⟩
/-
**nilradical_le_jacobson** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nilradical_le_jacobson (R) [CommRing R] : nilradical R <= Ring.jacobson R
参数：R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nilradical_eq_sInf`：nilradical_eq_sInf (R : Type*) [CommSemiring R] : ni
lradical R = sInf { J : Ideal R | J.IsPrime }
-/
theorem nilradical_le_jacobson (R) [CommRing R] : nilradical R ≤ Ring.jacobson R :=
  nilradical_eq_sInf R ▸ le_sInf fun _I hI ↦ sInf_le (Ideal.IsMaximal.isPrime ⟨hI⟩)
/-
**Ring.jacobson_eq_nilradical_of_krullDimLE_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.jacobson_eq_nilradical_of_krullDimLE_zero (R) [CommRing R] [KrullDimL
E 0 R] : jacobson R = nilradical R
参数：R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `nilradical_le_jacobson`：nilradical_le_jacobson (R) [CommRing R] : nilrad
ical R <= Ring.jacobson R
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `instIsMaximalOfIsPrimeOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : Com
mSemiring R] (I : Ideal R) [I.IsPrime] [Ring.KrullDimLE 0 R], I.IsMaximal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nilradical_eq_sInf`：nilradical_eq_sInf (R : Type*) [CommSemiring R] : ni
lradical R = sInf { J : Ideal R | J.IsPrime }
-/
theorem Ring.jacobson_eq_nilradical_of_krullDimLE_zero (R) [CommRing R] [KrullDimLE 0 R] :
    jacobson R = nilradical R :=
  (nilradical_le_jacobson R).antisymm' <| nilradical_eq_sInf R ▸ le_sInf fun I (_ : I.IsPrime) ↦
    sInf_le Ideal.IsMaximal.out

end Zero

section One

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring.KrullDimLE 0 R] : Ring.KrullDimLE 1 R := .mono zero_le_one _
/-
**Ring.krullDimLE_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.krullDimLE_one_iff : Ring.KrullDimLE 1 R ↔ forall I : Ideal R, I.IsPr
ime -> I in minimalPrimes R ∨ I.IsMaximal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ring.krullDimLE_one_iff : Ring.KrullDimLE 1 R ↔
    ∀ I : Ideal R, I.IsPrime → I ∈ minimalPrimes R ∨ I.IsMaximal := by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, PrimeSpectrum.isMin_iff]
  rfl
/-
**Ring.KrullDimLE.mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ring.KrullDimLE.mk₁ (H : ∀ I : Ideal R, I.IsPrime → I ∈ minimalPrimes R ∨ I.IsMaximal) :
    Ring.KrullDimLE 1 R := by
  rwa [Ring.krullDimLE_one_iff]
/-
**Ring.krullDimLE_one_iff_of_isPrime_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.krullDimLE_one_iff_of_isPrime_bot [(⊥ : Ideal R).IsPrime] : Ring.Krul
lDimLE 1 R ↔ forall I : Ideal R, I != ⊥ -> I.IsPrime -> I.IsMaximal
参数：⊥ : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ring.krullDimLE_one_iff_of_isPrime_bot [(⊥ : Ideal R).IsPrime] :
    Ring.KrullDimLE 1 R ↔ ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal := by
  let : OrderBot (PrimeSpectrum R) := { bot := ⟨⊥, ‹_›⟩, bot_le I := bot_le (a := I.1) }
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff_forall_isMax, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, forall_comm (α := _ ≠ ⊥),
    ne_eq, PrimeSpectrum.ext_iff]
  rfl
/-
**Ring.krullDimLE_one_iff_of_noZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.krullDimLE_one_iff_of_noZeroDivisors [NoZeroDivisors R] : Ring.KrullD
imLE 1 R ↔ forall I : Ideal R, I != ⊥ -> I.IsPrime -> I.IsMaximal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `instKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : CommSemiring R] [Ring.K
rullDimLE 0 R], Ring.KrullDimLE 1 R
· 使用定理 `Order.instKrullDimLEOfNatNatOfSubsingleton`：∀ {α : Type u_1} [inst : Pre
order α] [Subsingleton α], Order.KrullDimLE 0 α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `PrimeSpectrum.instIsEmptyOfSubsingleton`：∀ {R : Type u} [inst : CommSemi
ring R] [Subsingleton R], IsEmpty (PrimeSpectrum R)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `Ring.krullDimLE_one_iff_of_isPrime_bot`：Ring.krullDimLE_one_iff_of_isPri
me_bot [(⊥ : Ideal R).IsPrime] : Ring.KrullDimLE 1 R ↔ forall I : Ideal R, I != 
⊥ -> I.IsPrime -> I.IsMaxima…
-/
lemma Ring.krullDimLE_one_iff_of_noZeroDivisors [NoZeroDivisors R] :
    Ring.KrullDimLE 1 R ↔ ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal := by
  cases subsingleton_or_nontrivial R
  · exact iff_of_true inferInstance fun I h ↦ (h <| Subsingleton.elim ..).elim
  exact Ring.krullDimLE_one_iff_of_isPrime_bot
/-
**Ideal.IsPrime.isMaximal_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.IsPrime.isMaximal_of_ne_bot [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
 {I : Ideal R} (hI : I.IsPrime) (hI' : I != ⊥) : I.IsMaximal
参数：hI : I.IsPrime；hI' : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Ring.krullDimLE_one_iff_of_noZeroDivisors`：Ring.krullDimLE_one_iff_of_no
ZeroDivisors [NoZeroDivisors R] : Ring.KrullDimLE 1 R ↔ forall I : Ideal R, I !=
 ⊥ -> I.IsPrime -> I.IsMaximal
-/
lemma Ideal.IsPrime.isMaximal_of_ne_bot [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
    {I : Ideal R} (hI : I.IsPrime) (hI' : I ≠ ⊥) :
    I.IsMaximal :=
  Ring.krullDimLE_one_iff_of_noZeroDivisors.mp ‹_› _ hI' hI
/-
**Ideal.isMaximal_of_isPrime_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.isMaximal_of_isPrime_of_ne_bot [NoZeroDivisors R] [Ring.KrullDimLE 1
 R] (I : Ideal R) [I.IsPrime] (hI' : I != ⊥) : I.IsMaximal
参数：I : Ideal R；hI' : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.IsPrime.isMaximal_of_ne_bot`：Ideal.IsPrime.isMaximal_of_ne_bot [No
ZeroDivisors R] [Ring.KrullDimLE 1 R] {I : Ideal R} (hI : I.IsPrime) (hI' : I !=
 ⊥) : I.IsMaximal
-/
lemma Ideal.isMaximal_of_isPrime_of_ne_bot [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
    (I : Ideal R) [I.IsPrime] (hI' : I ≠ ⊥) :
    I.IsMaximal :=
  Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hI'

/-- Alternative constructor for `Ring.KrullDimLE 1`, convenient for domains. -/
/-
**Ring.KrullDimLE.mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative constructor for `Ring.KrullDimLE 1`, convenient for domains.
-/
lemma Ring.KrullDimLE.mk₁' (H : ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal) :
    Ring.KrullDimLE 1 R := by
  by_cases hR : (⊥ : Ideal R).IsPrime
  · rwa [Ring.krullDimLE_one_iff_of_isPrime_bot]
  suffices Ring.KrullDimLE 0 R from inferInstance
  exact .mk₀ fun I hI ↦ H I (fun e ↦ hR (e ▸ hI)) hI
/-
**Prime.isMaximal_span_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prime.isMaximal_span_singleton [NoZeroDivisors R] [Ring.KrullDimLE 1 R] {a
 : R} (ha : Prime a) : (Ideal.span {a}).IsMaximal
参数：ha : Prime a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.IsPrime.isMaximal_of_ne_bot`：Ideal.IsPrime.isMaximal_of_ne_bot [No
ZeroDivisors R] [Ring.KrullDimLE 1 R] {I : Ideal R} (hI : I.IsPrime) (hI' : I !=
 ⊥) : I.IsMaximal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma Prime.isMaximal_span_singleton [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
    {a : R} (ha : Prime a) : (Ideal.span {a}).IsMaximal :=
  ((Ideal.span_singleton_prime ha.ne_zero).mpr ha).isMaximal_of_ne_bot (by simpa using ha.ne_zero)
/-
**Ideal.liesOver_span_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.liesOver_span_iff [NoZeroDivisors R] [Ring.KrullDimLE 1 R] [Algebra 
R S] {P : Ideal S} {p : R} (hP : P != ⊤) (hp : Prime p) : P.LiesOver (.span {p})
 ↔ algebraMap R S p in P
参数：hP : P != ⊤；hp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_ne_top`：comap_ne_top [RingHomClass F R S] (hK : K != ⊤) : co
map f K != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsMaximal.eq_iff_le`：∀ {α : Type u} [inst : Semiring α] {I J : Ide
al α}, I.IsMaximal → J ≠ ⊤ → (I = J ↔ I ≤ J)
· 使用引理 `Prime.isMaximal_span_singleton`：Prime.isMaximal_span_singleton [NoZeroDi
visors R] [Ring.KrullDimLE 1 R] {a : R} (ha : Prime a) : (Ideal.span {a}).IsMaxi
mal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Ideal.liesOver_span_iff [NoZeroDivisors R] [Ring.KrullDimLE 1 R] [Algebra R S]
    {P : Ideal S} {p : R} (hP : P ≠ ⊤) (hp : Prime p) :
      P.LiesOver (.span {p}) ↔ algebraMap R S p ∈ P := by
  have hP : P.under R ≠ ⊤ := Ideal.comap_ne_top _ hP
  simp [Ideal.liesOver_iff, Ideal.IsMaximal.eq_iff_le hp.isMaximal_span_singleton hP]

end One

