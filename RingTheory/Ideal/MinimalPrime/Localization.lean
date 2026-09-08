/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!

# Minimal primes and localization

We provide various results concerning the minimal primes above an ideal that require the theory
of localizations.

## Main results
- `Ideal.exists_minimalPrimes_comap_eq` If `p` is a minimal prime over `f ⁻¹ I`, then it is the
  preimage of some minimal prime over `I`.
- `Ideal.minimalPrimes_eq_comap`: The minimal primes over `I` are precisely the preimages of
  minimal primes of `R ⧸ I`.
- `IsLocalization.minimalPrimes_comap`: If `A` is a localization of `R` with respect to the
  submonoid `S`, `J` is an ideal of `A`, then the minimal primes over the preimage of `J`
  (under `R →+* A`) are exactly the preimages of the minimal primes over `J`.
- `IsLocalization.minimalPrimes_map`: If `A` is a localization of `R` with respect to the
  submonoid `S`, `J` is an ideal of `R`, then the minimal primes over the span of the image of `J`
  (under `R →+* A`) are exactly the ideals of `A` such that the preimage of which is a minimal prime
  over `J`.
- `Localization.AtPrime.prime_unique_of_minimal`: When localizing at a minimal prime ideal `I`,
  the resulting ring only has a single prime ideal.
-/

public section


section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {I J : Ideal R}

/-
**Ideal.iUnion_minimalPrimes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.iUnion_minimalPrimes : ⋃ p in I.minimalPrimes, p = { x | exists y ∉ 
I.radical, x * y in I.radical }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `le_sInf_iff`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set
 α} {a : α}, a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `IsLocalization.mem_map_algebraMap_iff`：mem_map_algebraMap_iff {I : Ideal
 R} {z} : z in Ideal.map (algebraMap R S) I ↔ exists x : I × M, z * algebraMap R
 S x.2 = algebraMap R S x.1
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.IsPrime.radical_le_iff`：∀ {R : Type u} [inst : CommSemiring R] {I 
J : Ideal R}, J.IsPrime → (I.radical ≤ J ↔ I ≤ J)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 53 条，此处仅展示前 30 条）
-/
theorem Ideal.iUnion_minimalPrimes :
    ⋃ p ∈ I.minimalPrimes, p = { x | ∃ y ∉ I.radical, x * y ∈ I.radical } := by
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, ⟨⟨hp₁, hp₂⟩, hp₃⟩, hxp⟩
    have : p.map (algebraMap R (Localization.AtPrime p)) ≤ (I.map (algebraMap _ _)).radical := by
      rw [Ideal.radical_eq_sInf, le_sInf_iff]
      rintro q ⟨hq', hq⟩
      obtain ⟨h₁, h₂⟩ := ((IsLocalization.AtPrime.orderIsoOfPrime _ p) ⟨q, hq⟩).2
      rw [Ideal.map_le_iff_le_comap] at hq' ⊢
      exact hp₃ ⟨h₁, hq'⟩ h₂
    obtain ⟨n, hn⟩ := this (Ideal.mem_map_of_mem _ hxp)
    rw [IsLocalization.mem_map_algebraMap_iff (M := p.primeCompl)] at hn
    obtain ⟨⟨a, b⟩, hn⟩ := hn
    rw [← map_pow, ← map_mul, IsLocalization.eq_iff_exists p.primeCompl] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨t * b, fun h ↦ (t * b).2 (hp₁.radical_le_iff.mpr hp₂ h), n + 1, ?_⟩
    simp only at ht
    have : (x * (t.1 * b.1)) ^ (n + 1) = (t.1 ^ n * b.1 ^ n * x * t.1) * a := by
      rw [mul_assoc, ← ht]; ring
    rw [this]
    exact I.mul_mem_left _ a.2
  · rintro ⟨y, hy, hx⟩
    obtain ⟨p, hp, hyp⟩ : ∃ p ∈ I.minimalPrimes, y ∉ p := by
      simpa [← Ideal.sInf_minimalPrimes] using hy
    refine ⟨p, hp, (hp.isPrime.mem_or_mem ?_).resolve_right hyp⟩
    exact hp.isPrime.radical_le_iff.mpr hp.le hx
/-
**Ideal.exists_mul_mem_of_mem_minimalPrimes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.exists_mul_mem_of_mem_minimalPrimes {p : Ideal R} (hp : p in I.minim
alPrimes) {x : R} (hx : x in p) : exists y ∉ I, x * y in I
参数：hp : p in I.minimalPrimes；hx : x in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Ideal.iUnion_minimalPrimes`：Ideal.iUnion_minimalPrimes : ⋃ p in I.minima
lPrimes, p = { x | exists y ∉ I.radical, x * y in I.radical }
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Nat.sub_one_lt`：∀ {n : ℕ}, n ≠ 0 → n - 1 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
theorem Ideal.exists_mul_mem_of_mem_minimalPrimes
    {p : Ideal R} (hp : p ∈ I.minimalPrimes) {x : R} (hx : x ∈ p) :
    ∃ y ∉ I, x * y ∈ I := by
  classical
  obtain ⟨y, hy, n, hx⟩ := Ideal.iUnion_minimalPrimes.subset (Set.mem_biUnion hp hx)
  have H : ∃ m, x ^ m * y ^ n ∈ I := ⟨n, mul_pow x y n ▸ hx⟩
  have : Nat.find H ≠ 0 :=
    fun h ↦ hy ⟨n, by simpa only [h, pow_zero, one_mul] using Nat.find_spec H⟩
  refine ⟨x ^ (Nat.find H - 1) * y ^ n, Nat.find_min H (Nat.sub_one_lt this), ?_⟩
  rw [← mul_assoc, ← pow_succ', tsub_add_cancel_of_le (Nat.one_le_iff_ne_zero.mpr this)]
  exact Nat.find_spec H
/-
**IsSMulRegular.notMem_of_mem_minimalPrimes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSMulRegular.notMem_of_mem_minimalPrimes {M : Type*} [AddCommMonoid M] [M
odule R M] {x : R} (reg : IsSMulRegular M x) {p : Ideal R} (hp : p in (Module.an
nihilator R M).minimalPrimes) : x ∉ p
参数：reg : IsSMulRegular M x；hp : p in (Module.annihilator R M).minimalPrimes。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_mul_mem_of_mem_minimalPrimes`：Ideal.exists_mul_mem_of_mem_m
inimalPrimes {p : Ideal R} (hp : p in I.minimalPrimes) {x : R} (hx : x in p) : e
xists y ∉ I, x * y in I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Module.mem_annihilator`：Module.mem_annihilator {r} : r in Module.annihil
ator R M ↔ forall m : M, r • m = 0
· 使用定理 `IsSMulRegular.right_eq_zero_of_smul`：∀ {R : Type u_1} {M : Type u_3} [in
st : Zero M] [inst_1 : SMulZeroClass R M] {r : R} {x : M},   IsSMulRegular M r →
 r • x = 0 → x = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
theorem IsSMulRegular.notMem_of_mem_minimalPrimes
    {M : Type*} [AddCommMonoid M] [Module R M] {x : R} (reg : IsSMulRegular M x)
    {p : Ideal R} (hp : p ∈ (Module.annihilator R M).minimalPrimes) : x ∉ p := by
  intro hx
  rcases Ideal.exists_mul_mem_of_mem_minimalPrimes hp hx with ⟨y, hy, hxy⟩
  rcases not_forall.mp (Module.mem_annihilator.not.mp hy) with ⟨m, hm⟩
  exact hm (reg.right_eq_zero_of_smul ((smul_smul x y m).trans (Module.mem_annihilator.mp hxy m)))

/-- Minimal primes are contained in zero divisors. -/
/-
**Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes {p : Ideal R} (hp : p 
in minimalPrimes R) : Disjoint (p : Set R) (nonZeroDivisors R)
参数：hp : p in minimalPrimes R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.exists_mul_mem_of_mem_minimalPrimes`：Ideal.exists_mul_mem_of_mem_m
inimalPrimes {p : Ideal R} (hp : p in I.minimalPrimes) {x : R} (hx : x in p) : e
xists y ∉ I, x * y in I

--- 原说明 ---
Minimal primes are contained in zero divisors.
-/
lemma Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    Disjoint (p : Set R) (nonZeroDivisors R) := by
  simp_rw [Set.disjoint_left, SetLike.mem_coe, mem_nonZeroDivisors_iff_right, not_forall,
    exists_prop, @and_comm (_ * _ = _), ← mul_comm]
  exact fun _ ↦ Ideal.exists_mul_mem_of_mem_minimalPrimes hp

/-- An element of a minimal prime is a zero divisor. -/
/-
**notMem_nonZeroDivisors_of_mem_mem_minimalPrimes** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：notMem_nonZeroDivisors_of_mem_mem_minimalPrimes {x : R} {q : Ideal R} (hx 
: x in q) (hq : q in minimalPrimes R) : x ∉ nonZeroDivisors R
参数：hx : x in q；hq : q in minimalPrimes R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用引理 `Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes`：Ideal.disjoint_nonZ
eroDivisors_of_mem_minimalPrimes {p : Ideal R} (hp : p in minimalPrimes R) : Dis
joint (p : Set R) (nonZeroDivisors R)

--- 原说明 ---
An element of a minimal prime is a zero divisor.
-/
lemma notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    {x : R} {q : Ideal R} (hx : x ∈ q) (hq : q ∈ minimalPrimes R) :
    x ∉ nonZeroDivisors R :=
  Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) hx
/-
**Ideal.exists_comap_eq_of_mem_minimalPrimes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.exists_comap_eq_of_mem_minimalPrimes {I : Ideal S} (f : R ->+* S) (p
) (H : p in (I.comap f).minimalPrimes) : exists p' : Ideal S, p'.IsPrime ∧ I <= 
p' ∧ p'.comap f = p
参数：f : R ->+* S；p；H : p in (I.comap f).minimalPrimes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用引理 `Ideal.exists_ideal_comap_le_prime`：exists_ideal_comap_le_prime {S} [Comm
Semiring S] [FunLike F R S] [RingHomClass F R S] {f : F} (P : Ideal R) [P.IsPrim
e] (I : Ideal S) (le : …
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
-/
theorem Ideal.exists_comap_eq_of_mem_minimalPrimes {I : Ideal S} (f : R →+* S) (p)
    (H : p ∈ (I.comap f).minimalPrimes) : ∃ p' : Ideal S, p'.IsPrime ∧ I ≤ p' ∧ p'.comap f = p :=
  have := H.isPrime
  have ⟨p', hIp', hp', le⟩ := exists_ideal_comap_le_prime p I H.le
  ⟨p', hp', hIp', le.antisymm (H.2 ⟨inferInstance, comap_mono hIp'⟩ le)⟩
/-
**Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective** 是 Mathlib 中的一个定理，位于命
名空间 `Ideal`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring S] {f : R →+* S},   Function.Injective ⇑f → ∀ p ∈ minimalPrimes R, ∃ p', p'
.IsPrime ∧ Ideal.comap f p' = p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_comap_eq_of_mem_minimalPrimes`：Ideal.exists_comap_eq_of_mem
_minimalPrimes {I : Ideal S} (f : R ->+* S) (p) (H : p in (I.comap f).minimalPri
mes) : exists p' : Ideal S, p'.I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_bot_of_injective`：comap_bot_of_injective (hf : Function.Inje
ctive f) : Ideal.comap f ⊥ = ⊥
-/
@[stacks 00FK] theorem Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective {f : R →+* S}
    (hf : Function.Injective f) (p) (H : p ∈ minimalPrimes R) :
    ∃ p' : Ideal S, p'.IsPrime ∧ p'.comap f = p :=
  have ⟨p', hp', _, eq⟩ := exists_comap_eq_of_mem_minimalPrimes f (I := ⊥) p <| by
    rwa [comap_bot_of_injective f hf]
  ⟨p', hp', eq⟩
/-
**Ideal.exists_minimalPrimes_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.exists_minimalPrimes_comap_eq {I : Ideal S} (f : R ->+* S) (p) (H : 
p in (I.comap f).minimalPrimes) : exists p' in I.minimalPrimes, Ideal.comap f p'
 = p
参数：f : R ->+* S；p；H : p in (I.comap f).minimalPrimes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_comap_eq_of_mem_minimalPrimes`：Ideal.exists_comap_eq_of_mem
_minimalPrimes {I : Ideal S} (f : R ->+* S) (p) (H : p in (I.comap f).minimalPri
mes) : exists p' : Ideal S, p'.I…
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
-/
theorem Ideal.exists_minimalPrimes_comap_eq {I : Ideal S} (f : R →+* S) (p)
    (H : p ∈ (I.comap f).minimalPrimes) : ∃ p' ∈ I.minimalPrimes, Ideal.comap f p' = p := by
  obtain ⟨p', h₁, h₂, h₃⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f p H
  obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le h₂
  refine ⟨q, hq, Eq.symm ?_⟩
  have := hq.isPrime
  have := (Ideal.comap_mono hq').trans_eq h₃
  exact (H.2 ⟨inferInstance, Ideal.comap_mono hq.le⟩ this).antisymm this
/-
**Ideal.minimalPrimes_comap_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.minimalPrimes_comap_subset (f : R ->+* S) (J : Ideal S) : (J.comap f
).minimalPrimes subseteq Ideal.comap f '' J.minimalPrimes
参数：f : R ->+* S；J : Ideal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_minimalPrimes_comap_eq`：Ideal.exists_minimalPrimes_comap_eq
 {I : Ideal S} (f : R ->+* S) (p) (H : p in (I.comap f).minimalPrimes) : exists 
p' in I.minimalPrimes, Id…
-/
theorem Ideal.minimalPrimes_comap_subset (f : R →+* S) (J : Ideal S) :
    (J.comap f).minimalPrimes ⊆ Ideal.comap f '' J.minimalPrimes :=
  fun p hp ↦ Ideal.exists_minimalPrimes_comap_eq f p hp

end

section

variable {R S : Type*} [CommRing R] [CommRing S] {I J : Ideal R}

/-
**Ideal.minimalPrimes_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.minimalPrimes_comap_of_surjective {f : R ->+* S} (hf : Function.Surj
ective f) {I J : Ideal S} (h : J in I.minimalPrimes) : J.comap f in (I.comap f).
minimalPrimes
参数：hf : Function.Surjective f；h : J in I.minimalPrimes。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.map_isPrime_of_surjective`：map_isPrime_of_surjective {f : F} (hf :
 Function.Surjective f) {I : Ideal R} [H : IsPrime I] (hk : RingHom.ker f <= I) 
: IsPrime (map f I)
· 使用定理 `Ideal.le_map_of_comap_le_of_surjective`：le_map_of_comap_le_of_surjective
 : comap f K <= I -> K <= map f I
· 使用定理 `Ideal.map_le_of_le_comap`：map_le_of_le_comap : I <= K.comap f -> I.map f
 <= K
-/
theorem Ideal.minimalPrimes_comap_of_surjective {f : R →+* S} (hf : Function.Surjective f)
    {I J : Ideal S} (h : J ∈ I.minimalPrimes) : J.comap f ∈ (I.comap f).minimalPrimes := by
  have := h.isPrime
  refine ⟨⟨inferInstance, Ideal.comap_mono h.le⟩, ?_⟩
  rintro K ⟨hK, e₁⟩ e₂
  have : RingHom.ker f ≤ K := (Ideal.comap_mono bot_le).trans e₁
  rw [← sup_eq_left.mpr this, RingHom.ker_eq_comap_bot, ← Ideal.comap_map_of_surjective f hf]
  apply Ideal.comap_mono _
  apply h.2 _ _
  · exact ⟨Ideal.map_isPrime_of_surjective hf this, Ideal.le_map_of_comap_le_of_surjective f hf e₁⟩
  · exact Ideal.map_le_of_le_comap e₂

@[deprecated (since := "2026-04-01")] alias Ideal.minimal_primes_comap_of_surjective :=
    Ideal.minimalPrimes_comap_of_surjective
/-
**Ideal.comap_minimalPrimes_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.comap_minimalPrimes_eq_of_surjective {f : R ->+* S} (hf : Function.S
urjective f) (I : Ideal S) : (I.comap f).minimalPrimes = Ideal.comap f '' I.mini
malPrimes
参数：hf : Function.Surjective f；I : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ideal.exists_minimalPrimes_comap_eq`：Ideal.exists_minimalPrimes_comap_eq
 {I : Ideal S} (f : R ->+* S) (p) (H : p in (I.comap f).minimalPrimes) : exists 
p' in I.minimalPrimes, Id…
· 使用定理 `Ideal.minimalPrimes_comap_of_surjective`：Ideal.minimalPrimes_comap_of_su
rjective {f : R ->+* S} (hf : Function.Surjective f) {I J : Ideal S} (h : J in I
.minimalPrimes) : J.comap f i…
-/
theorem Ideal.comap_minimalPrimes_eq_of_surjective {f : R →+* S} (hf : Function.Surjective f)
    (I : Ideal S) : (I.comap f).minimalPrimes = Ideal.comap f '' I.minimalPrimes := by
  ext J
  constructor
  · intro H
    obtain ⟨p, h, rfl⟩ := Ideal.exists_minimalPrimes_comap_eq f J H
    exact ⟨p, h, rfl⟩
  · rintro ⟨J, hJ, rfl⟩
    exact Ideal.minimalPrimes_comap_of_surjective hf hJ
/-
**Ideal.minimalPrimes_map_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.minimalPrimes_map_of_surjective {S : Type*} [CommRing S] {f : R ->+*
 S} (hf : Function.Surjective f) (I : Ideal R) : (I.map f).minimalPrimes = Ideal
.map f '' (I ⊔ (RingHom.ker f)).minimalPrimes
参数：hf : Function.Surjective f；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `Ideal.comap_injective_of_surjective`：comap_injective_of_surjective : Inj
ective (comap f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_minimalPrimes_eq_of_surjective`：Ideal.comap_minimalPrimes_eq
_of_surjective {f : R ->+* S} (hf : Function.Surjective f) (I : Ideal S) : (I.co
map f).minimalPrimes = Ideal.com…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `RingHom.ker.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Sem
iring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F 
R S] (…
-/
lemma Ideal.minimalPrimes_map_of_surjective {S : Type*} [CommRing S] {f : R →+* S}
    (hf : Function.Surjective f) (I : Ideal R) :
    (I.map f).minimalPrimes = Ideal.map f '' (I ⊔ (RingHom.ker f)).minimalPrimes := by
  apply Set.image_injective.mpr (Ideal.comap_injective_of_surjective f hf)
  rw [← Ideal.comap_minimalPrimes_eq_of_surjective hf, ← Set.image_comp,
    Ideal.comap_map_of_surjective f hf, Set.image_congr, Set.image_id, RingHom.ker]
  intro x hx
  exact (Ideal.comap_map_of_surjective f hf _).trans (sup_eq_left.mpr <| le_sup_right.trans hx.le)
/-
**Ideal.minimalPrimes_eq_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.minimalPrimes_eq_comap : I.minimalPrimes = Ideal.comap (Ideal.Quotie
nt.mk I) '' minimalPrimes (R ⧸ I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minimalPrimes.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R], minimalPri
mes R = {p | IsMinimalPrime p}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_minimalPrimes_eq_of_surjective`：Ideal.comap_minimalPrimes_eq
_of_surjective {f : R ->+* S} (hf : Function.Surjective f) (I : Ideal S) : (I.co
map f).minimalPrimes = Ideal.com…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
-/
theorem Ideal.minimalPrimes_eq_comap :
    I.minimalPrimes = Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (R ⧸ I) := by
  rw [minimalPrimes, ← Ideal.comap_minimalPrimes_eq_of_surjective Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

end

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A]

/-
**IsLocalization.minimalPrimes_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.minimalPrimes_map [IsLocalization S A] (J : Ideal R) : (J.m
ap (algebraMap R A)).minimalPrimes = Ideal.under R ⁻¹' J.minimalPrimes
参数：J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
· 使用引理 `Set.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subseteq u
) (d : Disjoint s u) : Disjoint s t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsLocalization.isPrime_iff_isPrime_disjoint`：isPrime_iff_isPrime_disjoin
t (J : Ideal S) : J.IsPrime ↔ (J.under R).IsPrime ∧ Disjoint (M : Set R) (J.unde
r R)
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.disjoint_under_iff`：disjoint_under_iff (J : Ideal S) : Di
sjoint (M : Set R) (J.under R) ↔ J != ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
-/
theorem IsLocalization.minimalPrimes_map [IsLocalization S A] (J : Ideal R) :
    (J.map (algebraMap R A)).minimalPrimes = Ideal.under R ⁻¹' J.minimalPrimes := by
  ext p
  constructor
  · intro hp
    have := hp.isPrime
    refine ⟨⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hp.le⟩, ?_⟩
    rintro I hI e
    have hI' : Disjoint (S : Set R) I := Set.disjoint_of_subset_right e
      ((IsLocalization.isPrime_iff_isPrime_disjoint S A _).mp hp.isPrime).2
    refine (Ideal.comap_mono <|
      hp.2 ⟨?_, Ideal.map_mono hI.2⟩ (Ideal.map_le_iff_le_comap.mpr e)).trans_eq ?_
    · exact IsLocalization.isPrime_of_isPrime_disjoint S A I hI.1 hI'
    · exact IsLocalization.under_map_of_isPrime_disjoint S A hI.1 hI'
  · intro hp
    refine ⟨⟨?_, Ideal.map_le_iff_le_comap.mpr hp.le⟩, ?_⟩
    · rw [IsLocalization.isPrime_iff_isPrime_disjoint S A, IsLocalization.disjoint_under_iff S]
      refine ⟨hp.isPrime, ?_⟩
      rintro rfl
      exact hp.isPrime.ne_top rfl
    · intro I hI e
      rw [← IsLocalization.map_under S A I, ← IsLocalization.map_under S A p]
      exact Ideal.map_mono (hp.2 ⟨hI.1.comap _, Ideal.map_le_iff_le_comap.mp hI.2⟩
        (Ideal.comap_mono e))
/-
**IsLocalization.minimalPrimes_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.minimalPrimes_comap [IsLocalization S A] (J : Ideal A) : (J
.comap (algebraMap R A)).minimalPrimes = Ideal.comap (algebraMap R A) '' J.minim
alPrimes
参数：J : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
· 使用定理 `IsLocalization.minimalPrimes_map`：IsLocalization.minimalPrimes_map [IsLo
calization S A] (J : Ideal R) : (J.map (algebraMap R A)).minimalPrimes = Ideal.u
nder R ⁻¹' J.minimalPr…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Ideal.minimalPrimes_comap_subset`：Ideal.minimalPrimes_comap_subset (f : 
R ->+* S) (J : Ideal S) : (J.comap f).minimalPrimes subseteq Ideal.comap f '' J.
minimalPrimes
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
-/
theorem IsLocalization.minimalPrimes_comap [IsLocalization S A] (J : Ideal A) :
    (J.comap (algebraMap R A)).minimalPrimes = Ideal.comap (algebraMap R A) '' J.minimalPrimes := by
  conv_rhs => rw [← map_under S A J, minimalPrimes_map S]
  refine (Set.image_preimage_eq_iff.mpr ?_).symm
  exact subset_trans (Ideal.minimalPrimes_comap_subset (algebraMap R A) J) (by simp)
/-
**IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (q : Ideal R) [hqp
 : q.IsPrime] [IsLocalization.AtPrime A q] (I : Ideal R) (hIq : q in I.minimalPr
imes) : (I.map (algebraMap R A)).radical = q.map (algebraMap R A)
参数：q : Ideal R；I : Ideal R；hIq : q in I.minimalPrimes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.sInf_minimalPrimes`：Ideal.sInf_minimalPrimes : sInf I.minimalPrime
s = I.radical
· 使用定理 `IsLocalization.minimalPrimes_map`：IsLocalization.minimalPrimes_map [IsLo
calization S A] (J : Ideal R) : (J.map (algebraMap R A)).minimalPrimes = Ideal.u
nder R ⁻¹' J.minimalPr…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `IsLocalization.AtPrime.map_eq_maximalIdeal`：map_eq_maximalIdeal : p.map 
(algebraMap R Rₚ) = maximalIdeal Rₚ
· 使用定理 `IsLocalization.AtPrime.under_maximalIdeal`：under_maximalIdeal (h : IsLoc
alRing S
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `IsLocalization.under_le_under_iff`：under_le_under_iff {I J : Ideal S} : 
I.under R <= J.under R ↔ I <= J
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.disjoint_compl_left_iff_subset`：disjoint_compl_left_iff_subset : Dis
joint sᶜ t ↔ t subseteq s
· 使用定理 `IsLocalization.disjoint_under_iff`：disjoint_under_iff (J : Ideal S) : Di
sjoint (M : Set R) (J.under R) ↔ J != ⊤
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.comap_eq_top_iff`：comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔
 I = ⊤
-/
theorem IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (q : Ideal R) [hqp : q.IsPrime] [IsLocalization.AtPrime A q]
    (I : Ideal R) (hIq : q ∈ I.minimalPrimes) :
    (I.map (algebraMap R A)).radical = q.map (algebraMap R A) := by
  have : IsLocalRing A := AtPrime.isLocalRing A q
  rw [← Ideal.sInf_minimalPrimes, IsLocalization.minimalPrimes_map q.primeCompl A I]
  refine le_antisymm (sInf_le ?_) (le_sInf fun J hJ ↦ ?_)
  · rwa [Set.mem_preimage, map_eq_maximalIdeal q A, under_maximalIdeal A q]
  · rw [← IsLocalization.under_le_under_iff q.primeCompl A,
      AtPrime.map_eq_maximalIdeal q A, AtPrime.under_maximalIdeal A q]
    apply hIq.2 hJ.1
    have := hJ.isPrime.ne_top
    rw [ne_eq, Ideal.comap_eq_top_iff, ← ne_eq, ← disjoint_under_iff q.primeCompl A J] at this
    exact Set.disjoint_compl_left_iff_subset.mp this

end

