/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# Zero-dimensional rings

We provide further API for zero-dimensional rings.
Basic definitions and lemmas are provided in `Mathlib/RingTheory/KrullDimension/Basic.lean`.

-/

public section

section CommSemiring

variable {R : Type*} [CommSemiring R] [Ring.KrullDimLE 0 R] (I : Ideal R)

/-
**Ring.KrullDimLE.mem_minimalPrimes_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.mem_minimalPrimes_iff {I J : Ideal R} : I in J.minimalPrim
es ↔ I.IsPrime ∧ J <= I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用引理 `Ideal.IsPrime.isMaximal'`：Ideal.IsPrime.isMaximal' [Ring.KrullDimLE 0 R]
 {I : Ideal R} (hI : I.IsPrime) : I.IsMaximal
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
lemma Ring.KrullDimLE.mem_minimalPrimes_iff {I J : Ideal R} :
    I ∈ J.minimalPrimes ↔ I.IsPrime ∧ J ≤ I :=
  ⟨fun H ↦ H.1, fun H ↦ ⟨H, fun _ h e ↦ (h.1.isMaximal'.eq_of_le H.1.ne_top e).ge⟩⟩
/-
**Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime {I J : Ideal R} [I.IsP
rime] : I in J.minimalPrimes ↔ J <= I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ring.KrullDimLE.mem_minimalPrimes_iff`：Ring.KrullDimLE.mem_minimalPrimes
_iff {I J : Ideal R} : I in J.minimalPrimes ↔ I.IsPrime ∧ J <= I
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime {I J : Ideal R} [I.IsPrime] :
    I ∈ J.minimalPrimes ↔ J ≤ I := by
  rwa [mem_minimalPrimes_iff, and_iff_right]

variable (R) in
/-
**Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime : minimalPrimes R = { I
 | I.IsPrime }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Ideal.mem_minimalPrimes_iff_isPrime`：Ideal.mem_minimalPrimes_iff_isPrime
 [Ring.KrullDimLE 0 R] {I : Ideal R} : I in minimalPrimes R ↔ I.IsPrime
-/
lemma Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime :
    minimalPrimes R = { I | I.IsPrime } := by
  ext
  exact Ideal.mem_minimalPrimes_iff_isPrime

@[deprecated (since := "2026-07-09")]
alias Ring.KrullDimLE.minimalPrimes_eq_setOf_isPrime :=
  Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime

variable (R) in
/-
**Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal : minimalPrimes R = {
 I | I.IsMaximal }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime`：Ring.KrullDimLE.mini
malPrimes_eq_setOfPred_isPrime : minimalPrimes R = { I | I.IsPrime }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal :
    minimalPrimes R = { I | I.IsMaximal } := by
  ext; simp [minimalPrimes_eq_setOfPred_isPrime, Ideal.isMaximal_iff_isPrime]

@[deprecated (since := "2026-07-09")]
alias Ring.KrullDimLE.minimalPrimes_eq_setOf_isMaximal :=
  Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal

/-- Note that the `ringKrullDim` of the trivial ring is `⊥` and not `0`. -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that the `ringKrullDim` of the trivial ring is `⊥` and not `0`.
-/
example [Subsingleton R] : Ring.KrullDimLE 0 R := inferInstance
/-
**Ring.KrullDimLE.isField_of_isDomain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.isField_of_isDomain [IsDomain R] : IsField R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ring.not_isField_iff_exists_prime`：not_isField_iff_exists_prime [Nontriv
ial R] : ¬IsField R ↔ exists p : Ideal R, p != ⊥ ∧ p.IsPrime
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用引理 `Ideal.IsPrime.isMaximal'`：Ideal.IsPrime.isMaximal' [Ring.KrullDimLE 0 R]
 {I : Ideal R} (hI : I.IsPrime) : I.IsMaximal
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma Ring.KrullDimLE.isField_of_isDomain [IsDomain R] : IsField R := by
  by_contra h
  obtain ⟨p, hp, h⟩ := Ring.not_isField_iff_exists_prime.mp h
  exact hp.symm (Ideal.isPrime_bot.isMaximal'.eq_of_le h.ne_top bot_le)

omit [Ring.KrullDimLE 0 R] in
/-
**ringKrullDimZero_iff_ringKrullDim_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] : Ring.KrullDimLE
 0 R ↔ ringKrullDim R = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.KrullDimLE.eq_1`：∀ (n : ℕ) (R : Type u_1) [inst : CommSemiring R], 
Ring.KrullDimLE n R = Order.KrullDimLE n (PrimeSpectrum R)
· 使用定理 `Order.krullDimLE_iff`：∀ (n : ℕ) (α : Type u_1) [inst : Preorder α], Orde
r.KrullDimLE n α ↔ Order.krullDim α ≤ ↑n
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ringKrullDim.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R], ringKrullDi
m R = Order.krullDim (PrimeSpectrum R)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `iff_self_and`：∀ {p q : Prop}, (p ↔ p ∧ q) ↔ p → q
· 使用引理 `ringKrullDim_nonneg_of_nontrivial`：ringKrullDim_nonneg_of_nontrivial [No
ntrivial R] : 0 <= ringKrullDim R
-/
lemma ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] :
    Ring.KrullDimLE 0 R ↔ ringKrullDim R = 0 := by
  rw [Ring.KrullDimLE, Order.krullDimLE_iff, le_antisymm_iff, ← ringKrullDim, Nat.cast_zero,
    iff_self_and]
  exact fun _ ↦ ringKrullDim_nonneg_of_nontrivial

/-- A quotient `R ⧸ I` has krull dimension at most zero if and only if all minimal primes over `I`
are maximal. -/
/-
**Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal {R : Typ
e*} [CommRing R] {I : Ideal R} : Ring.KrullDimLE 0 (R ⧸ I) ↔ forall J in I.minim
alPrimes, J.IsMaximal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal`：Ring.krullDimLE
_zero_iff_forall_minimalPrimes_isMaximal : Ring.KrullDimLE 0 R ↔ forall I in min
imalPrimes R, I.IsMaximal
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.minimalPrimes_eq_comap`：Ideal.minimalPrimes_eq_comap : I.minimalPr
imes = Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (R ⧸ I)
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Ideal.comap_isMaximal_of_surjective`：comap_isMaximal_of_surjective (hf :
 Function.Surjective f) {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.map_eq_top_or_isMaximal_of_surjective`：map_eq_top_or_isMaximal_of_
surjective (hf : Function.Surjective f) {I : Ideal R} (H : IsMaximal I) : map f 
I = ⊤ ∨ IsMaximal (map f I)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A quotient `R ⧸ I` has krull dimension at most zero if and only if all minimal p
rimes over `I`
are maximal.
-/
theorem Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal
    {R : Type*} [CommRing R] {I : Ideal R} :
    Ring.KrullDimLE 0 (R ⧸ I) ↔ ∀ J ∈ I.minimalPrimes, J.IsMaximal := by
  rw [Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal, minimalPrimes_eq_comap,
    Set.forall_mem_image]
  refine forall₂_congr fun J hJ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact comap_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective
  · have := map_eq_top_or_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective h
    rw [map_comap_of_surjective (Quotient.mk I) Quotient.mk_surjective] at this
    exact this.resolve_left hJ.1.1.ne_top

section IsLocalRing

omit [Ring.KrullDimLE 0 R] in
variable (R) in
/-
**Ring.krullDimLE_zero_and_isLocalRing_tfae** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.krullDimLE_zero_and_isLocalRing_tfae : List.TFAE [ Ring.KrullDimLE 0 
R ∧ IsLocalRing R, exists! I : Ideal R, I.IsPrime, forall x : R, IsNilpotent x ↔
 ¬ IsUnit x, (nilradical R).IsMaximal ]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nilradical.eq_1`：∀ (R : Type u_3) [inst : CommSemiring R], nilradical R 
= Ideal.radical 0
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `sInf_singleton`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {a : 
α}, sInf {a} = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `IsNilpotent.zero`：∀ {R : Type u_3} [inst : MonoidWithZero R], IsNilpoten
t 0
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `nilradical_le_prime`：nilradical_le_prime (J : Ideal R) [H : J.IsPrime] :
 nilradical R <= J
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用引理 `Ring.KrullDimLE.mk₀`：Ring.KrullDimLE.mk₀ (H : forall I : Ideal R, I.IsPr
ime -> I.IsMaximal) : Ring.KrullDimLE 0 R
· 使用定理 `IsLocalRing.of_unique_max_ideal`：of_unique_max_ideal (h : exists! I : Id
eal R, I.IsMaximal) : IsLocalRing R
（共 31 条，此处仅展示前 30 条）
-/
lemma Ring.krullDimLE_zero_and_isLocalRing_tfae :
    List.TFAE
    [ Ring.KrullDimLE 0 R ∧ IsLocalRing R,
      ∃! I : Ideal R, I.IsPrime,
      ∀ x : R, IsNilpotent x ↔ ¬ IsUnit x,
      (nilradical R).IsMaximal ] := by
  tfae_have 1 → 3 := by
    intro ⟨h₁, h₂⟩ x
    change x ∈ nilradical R ↔ x ∈ IsLocalRing.maximalIdeal R
    rw [nilradical, Ideal.radical_eq_sInf]
    simp [← Ideal.isMaximal_iff_isPrime, IsLocalRing.isMaximal_iff]
  tfae_have 3 → 4 := by
    refine fun H ↦ ⟨fun e ↦ ?_, fun I hI ↦ ?_⟩
    · obtain ⟨n, hn⟩ := (Ideal.eq_top_iff_one _).mp e
      exact (H 0).mp .zero ((show (1 : R) = 0 by simpa using hn) ▸ isUnit_one)
    · obtain ⟨x, hx, hx'⟩ := (SetLike.lt_iff_le_and_exists.mp hI).2
      exact Ideal.eq_top_of_isUnit_mem _ hx (not_not.mp ((H x).not.mp hx'))
  tfae_have 4 → 2 := fun H ↦ ⟨_, H.isPrime, fun p (hp : p.IsPrime) ↦
      (H.eq_of_le hp.ne_top (nilradical_le_prime p)).symm⟩
  tfae_have 2 → 1 := by
    rintro ⟨P, hP₁, hP₂⟩
    obtain ⟨P, hP₃, -⟩ := P.exists_le_maximal hP₁.ne_top
    obtain rfl := hP₂ P hP₃.isPrime
    exact ⟨.mk₀ fun Q h ↦ hP₂ Q h ▸ hP₃, .of_unique_max_ideal ⟨P, hP₃, fun Q h ↦ hP₂ Q h.isPrime⟩⟩
  tfae_finish

@[simp]
/-
**le_isUnit_iff_zero_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_isUnit_iff_zero_notMem [IsLocalRing R] {M : Submonoid R} : M <= IsUnit.
submonoid R ↔ 0 ∉ M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Ring.krullDimLE_zero_and_isLocalRing_tfae`：Ring.krullDimLE_zero_and_isLo
calRing_tfae : List.TFAE [ Ring.KrullDimLE 0 R ∧ IsLocalRing R, exists! I : Idea
l R, I.IsPrime, forall x : R, I…
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
lemma le_isUnit_iff_zero_notMem [IsLocalRing R]
    {M : Submonoid R} : M ≤ IsUnit.submonoid R ↔ 0 ∉ M := by
  have := ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2 rfl rfl).mp ⟨‹_›, ‹_›⟩
  exact ⟨fun h₁ h₂ ↦ not_isUnit_zero (h₁ h₂),
    fun H x hx ↦ (this x).not_left.mp fun ⟨n, hn⟩ ↦ H (hn ▸ pow_mem hx n)⟩

variable (R) in
/-
**Ring.KrullDimLE.existsUnique_isPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.existsUnique_isPrime [IsLocalRing R] : exists! I : Ideal R
, I.IsPrime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Ring.krullDimLE_zero_and_isLocalRing_tfae`：Ring.krullDimLE_zero_and_isLo
calRing_tfae : List.TFAE [ Ring.KrullDimLE 0 R ∧ IsLocalRing R, exists! I : Idea
l R, I.IsPrime, forall x : R, I…
-/
theorem Ring.KrullDimLE.existsUnique_isPrime [IsLocalRing R] :
    ∃! I : Ideal R, I.IsPrime :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1 rfl rfl).mp ⟨‹_›, ‹_›⟩
/-
**Ring.KrullDimLE.eq_maximalIdeal_of_isPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.eq_maximalIdeal_of_isPrime [IsLocalRing R] (J : Ideal R) [
J.IsPrime] : J = IsLocalRing.maximalIdeal R
参数：J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Ring.krullDimLE_zero_and_isLocalRing_tfae`：Ring.krullDimLE_zero_and_isLo
calRing_tfae : List.TFAE [ Ring.KrullDimLE 0 R ∧ IsLocalRing R, exists! I : Idea
l R, I.IsPrime, forall x : R, I…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
theorem Ring.KrullDimLE.eq_maximalIdeal_of_isPrime [IsLocalRing R] (J : Ideal R) [J.IsPrime] :
    J = IsLocalRing.maximalIdeal R :=
  (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1 rfl rfl).mp ⟨‹_›, ‹_›⟩).unique
    ‹_› inferInstance
/-
**Ring.KrullDimLE.radical_eq_maximalIdeal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.radical_eq_maximalIdeal [IsLocalRing R] (I : Ideal R) (hI 
: I != ⊤) : I.radical = IsLocalRing.maximalIdeal R
参数：I : Ideal R；hI : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ring.KrullDimLE.eq_maximalIdeal_of_isPrime`：Ring.KrullDimLE.eq_maximalId
eal_of_isPrime [IsLocalRing R] (J : Ideal R) [J.IsPrime] : J = IsLocalRing.maxim
alIdeal R
-/
lemma Ring.KrullDimLE.radical_eq_maximalIdeal [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    I.radical = IsLocalRing.maximalIdeal R := by
  rw [Ideal.radical_eq_sInf]
  refine (sInf_le ?_).antisymm (le_sInf ?_)
  · exact ⟨IsLocalRing.le_maximalIdeal hI, inferInstance⟩
  · rintro J ⟨h₁, h₂⟩
    exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime J).ge

variable (R) in
/-
**Ring.KrullDimLE.subsingleton_primeSpectrum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.subsingleton_primeSpectrum [IsLocalRing R] : Subsingleton 
(PrimeSpectrum R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ring.KrullDimLE.eq_maximalIdeal_of_isPrime`：Ring.KrullDimLE.eq_maximalId
eal_of_isPrime [IsLocalRing R] (J : Ideal R) [J.IsPrime] : J = IsLocalRing.maxim
alIdeal R
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Ring.KrullDimLE.subsingleton_primeSpectrum [IsLocalRing R] :
    Subsingleton (PrimeSpectrum R) :=
  ⟨fun x y ↦ PrimeSpectrum.ext <|
    (eq_maximalIdeal_of_isPrime x.1).trans (eq_maximalIdeal_of_isPrime y.1).symm⟩
/-
**Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal [IsLocalRing R] {x} : IsN
ilpotent x ↔ x in IsLocalRing.maximalIdeal R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Ring.krullDimLE_zero_and_isLocalRing_tfae`：Ring.krullDimLE_zero_and_isLo
calRing_tfae : List.TFAE [ Ring.KrullDimLE 0 R ∧ IsLocalRing R, exists! I : Idea
l R, I.IsPrime, forall x : R, I…
-/
theorem Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal [IsLocalRing R] {x} :
    IsNilpotent x ↔ x ∈ IsLocalRing.maximalIdeal R :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2 rfl rfl).mp ⟨‹_›, ‹_›⟩ x
/-
**Ring.KrullDimLE.isNilpotent_iff_mem_nonunits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.isNilpotent_iff_mem_nonunits [IsLocalRing R] {x} : IsNilpo
tent x ↔ x in nonunits R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal`：Ring.KrullDimLE.isNilp
otent_iff_mem_maximalIdeal [IsLocalRing R] {x} : IsNilpotent x ↔ x in IsLocalRin
g.maximalIdeal R
-/
theorem Ring.KrullDimLE.isNilpotent_iff_mem_nonunits [IsLocalRing R] {x} :
    IsNilpotent x ↔ x ∈ nonunits R :=
  isNilpotent_iff_mem_maximalIdeal

variable (R) in
/-
**Ring.KrullDimLE.nilradical_eq_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.nilradical_eq_maximalIdeal [IsLocalRing R] : nilradical R 
= IsLocalRing.maximalIdeal R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal`：Ring.KrullDimLE.isNilp
otent_iff_mem_maximalIdeal [IsLocalRing R] {x} : IsNilpotent x ↔ x in IsLocalRin
g.maximalIdeal R
-/
theorem Ring.KrullDimLE.nilradical_eq_maximalIdeal [IsLocalRing R] :
    nilradical R = IsLocalRing.maximalIdeal R :=
  Ideal.ext fun _ ↦ isNilpotent_iff_mem_maximalIdeal

omit [Ring.KrullDimLE 0 R] in
variable (R) in
/-
**IsLocalRing.of_isMaximal_nilradical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalRing.of_isMaximal_nilradical [(nilradical R).IsMaximal] : IsLocalRi
ng R
参数：nilradical R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Ring.krullDimLE_zero_and_isLocalRing_tfae`：Ring.krullDimLE_zero_and_isLo
calRing_tfae : List.TFAE [ Ring.KrullDimLE 0 R ∧ IsLocalRing R, exists! I : Idea
l R, I.IsPrime, forall x : R, I…
-/
theorem IsLocalRing.of_isMaximal_nilradical [(nilradical R).IsMaximal] :
    IsLocalRing R :=
  (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 3 0 rfl rfl).mp ‹_›).2

omit [Ring.KrullDimLE 0 R] in
variable (R) in
/-
**Ring.KrullDimLE.of_isMaximal_nilradical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.of_isMaximal_nilradical [(nilradical R).IsMaximal] : Ring.
KrullDimLE 0 R
参数：nilradical R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Ring.krullDimLE_zero_and_isLocalRing_tfae`：Ring.krullDimLE_zero_and_isLo
calRing_tfae : List.TFAE [ Ring.KrullDimLE 0 R ∧ IsLocalRing R, exists! I : Idea
l R, I.IsPrime, forall x : R, I…
-/
theorem Ring.KrullDimLE.of_isMaximal_nilradical [(nilradical R).IsMaximal] :
    Ring.KrullDimLE 0 R :=
  (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 3 0 rfl rfl).mp ‹_›).1

omit [Ring.KrullDimLE 0 R] in
/-
**Ring.KrullDimLE.of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.of_isLocalization (p : Ideal R) (hp : p in minimalPrimes R
) (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p (hp
参数：p : Ideal R；hp : p in minimalPrimes R；S : Type*。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes`：IsLocali
zation.subsingleton_primeSpectrum_of_mem_minimalPrimes {R : Type*} [CommSemiring
 R] (p : Ideal R) (hp : p in minimalPrimes R) (S : T…
· 使用引理 `Order.krullDim_nonpos_of_subsingleton`：krullDim_nonpos_of_subsingleton [
Subsingleton α] : krullDim α <= 0
-/
lemma Ring.KrullDimLE.of_isLocalization (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    Ring.KrullDimLE 0 S :=
  have := IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p hp S
  ⟨Order.krullDim_nonpos_of_subsingleton⟩
/-
**Ring.KrullDimLE.isField_of_isReduced** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.KrullDimLE.isField_of_isReduced [IsReduced R] [IsLocalRing R] : IsFie
ld R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.isField_iff_maximalIdeal_eq`：isField_iff_maximalIdeal_eq : I
sField R ↔ maximalIdeal R = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.KrullDimLE.nilradical_eq_maximalIdeal`：Ring.KrullDimLE.nilradical_e
q_maximalIdeal [IsLocalRing R] : nilradical R = IsLocalRing.maximalIdeal R
· 使用定理 `nilradical_eq_zero`：nilradical_eq_zero (R : Type*) [CommSemiring R] [IsR
educed R] : nilradical R = 0
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
-/
lemma Ring.KrullDimLE.isField_of_isReduced [IsReduced R] [IsLocalRing R] : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← nilradical_eq_maximalIdeal,
    nilradical_eq_zero, Ideal.zero_eq_bot]
/-
**PrimeSpectrum.unique_of_ringKrullDimLE_zero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PrimeSpectrum.unique_of_ringKrullDimLE_zero [IsLocalRing R] : Unique (Prim
eSpectrum R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PrimeSpectrum.unique_of_ringKrullDimLE_zero [IsLocalRing R] : Unique (PrimeSpectrum R) :=
  ⟨⟨IsLocalRing.closedPoint _⟩,
    fun _ ↦ PrimeSpectrum.ext (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime _)⟩
/-
**PrimeSpectrum.subsingleton_iff_isField_of_isReduced** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：PrimeSpectrum.subsingleton_iff_isField_of_isReduced {R : Type*} [CommRing 
R] [IsReduced R] [Nontrivial R] : Subsingleton (PrimeSpectrum R) ↔ IsField R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `MaximalSpectrum.toPrimeSpectrum_injective`：toPrimeSpectrum_injective : (
@toPrimeSpectrum R _).Injective
· 使用定理 `IsLocalRing.of_singleton_maximalSpectrum`：of_singleton_maximalSpectrum [
Subsingleton (MaximalSpectrum R)] [Nonempty (MaximalSpectrum R)] : IsLocalRing R
· 使用定理 `MaximalSpectrum.instNonemptyOfNontrivial`：∀ {R : Type u_1} [inst : CommS
emiring R] [Nontrivial R], Nonempty (MaximalSpectrum R)
· 使用引理 `Ring.KrullDimLE.isField_of_isReduced`：Ring.KrullDimLE.isField_of_isReduc
ed [IsReduced R] [IsLocalRing R] : IsField R
· 使用定理 `Order.instKrullDimLEOfNatNatOfSubsingleton`：∀ {α : Type u_1} [inst : Pre
order α] [Subsingleton α], Order.KrullDimLE 0 α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma PrimeSpectrum.subsingleton_iff_isField_of_isReduced
    {R : Type*} [CommRing R] [IsReduced R] [Nontrivial R] :
    Subsingleton (PrimeSpectrum R) ↔ IsField R := by
  refine ⟨fun H ↦ ?_, fun H ↦ letI := H.toField; inferInstance⟩
  have : Subsingleton (MaximalSpectrum R) := MaximalSpectrum.toPrimeSpectrum_injective.subsingleton
  have : IsLocalRing R := .of_singleton_maximalSpectrum
  exact Ring.KrullDimLE.isField_of_isReduced

end IsLocalRing

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (I : Ideal R)

/-
**Ideal.jacobson_eq_radical** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.jacobson_eq_radical [Ring.KrullDimLE 0 R] : I.jacobson = I.radical
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ideal.jacobson_eq_radical [Ring.KrullDimLE 0 R] : I.jacobson = I.radical := by
  simp [jacobson, radical_eq_sInf, Ideal.isMaximal_iff_isPrime]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Ring.KrullDimLE 0 R] : IsJacobsonRing R :=
  ⟨fun I hI ↦ by rw [I.jacobson_eq_radical, hI.radical]⟩

end CommRing

