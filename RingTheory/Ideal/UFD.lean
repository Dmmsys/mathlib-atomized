/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# UFD criteria via height `1` prime ideals and localization

## Main results
* `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one` : Let `R` be a
  Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is principal.

* `UniqueFactorizationMonoid.iff_localizationAway_of_prime` : Let `R` be a Noetherian domain,
  `x ∈ R` be a prime element. Then `R` is a UFD if and only if `Rₓ` is a UFD.
-/

public section

variable {R : Type*} [CommRing R] [IsDomain R]

namespace Ideal

variable [WfDvdMonoid R] {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)

include hx hxp

/-
**Ideal.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime** 是 Mathlib 中的一个定
理，位于命名空间 `Ideal`。
形式化陈述：isPrincipal_of_isPrincipal_isLocalizationAway_of_prime (S : Type*) [CommRi
ng S] [Algebra R S] [IsLocalization.Away x S] (hp : (map (algebraMap R S) p).IsP
rincipal) : p.IsPrincipal
参数：S : Type*；hp : (map (algebraMap R S) p).IsPrincipal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.disjoint_powers_iff_notMem_of_isPrime`：disjoint_powers_iff_notMem_
of_isPrime [I.IsPrime] (y : R) : Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ 
I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `powers_le_nonZeroDivisors_of_noZeroDivisors`：powers_le_nonZeroDivisors_o
f_noZeroDivisors (hx : x != 0) : Submonoid.powers x <= M₀⁰
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `exists_reduced_fraction'`：exists_reduced_fraction' {b : B} (hb : b != 0)
 (hx : Irreducible x) : exists (a : R) (n : Int), ¬x ∣ a ∧ selfZPow x B n * alge
braMap R B a =…
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `selfZPow_mul_neg`：selfZPow_mul_neg (d : Int) : selfZPow x B d * selfZPow
 x B (-d) = 1
· 使用引理 `Ideal.eq_of_map_algebraMap_le`：Ideal.eq_of_map_algebraMap_le (heq : I.ma
p (algebraMap R S) = J.map (algebraMap R S)) (hxI : forall y : R, x * y in I -> 
y in I) (hxJ : fora…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_mul_left_unit`：span_singleton_mul_left_unit {a : α}
 (h2 : IsUnit a) (x : α) : span ({a * x} : Set α) = span {x}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.IsPrime.mul_mem_left_iff`：∀ {α : Type u} [inst : Semiring α] {I : 
Ideal α} [I.IsTwoSided] [I.IsPrime] {x y : α}, x ∉ I → (x * y ∈ I ↔ y ∈ I)
（共 35 条，此处仅展示前 30 条）
-/
theorem isPrincipal_of_isPrincipal_isLocalizationAway_of_prime
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S]
    (hp : (map (algebraMap R S) p).IsPrincipal) : p.IsPrincipal := by
  have := (disjoint_powers_iff_notMem_of_isPrime x).mpr hxp
  by_cases hpbot : p = ⊥
  · simp [hpbot, bot_isPrincipal]
  · have hi := IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    have hpb : map (algebraMap R S) p ≠ ⊥ := by simp [Ideal.map_eq_bot_iff_of_injective hi, hpbot]
    obtain ⟨g, hg⟩ := hp
    have hg0 : g ≠ 0 := fun hg0 ↦ hpb <| by simp [hg0, hg]
    obtain ⟨a, n, hxa, hag⟩ := exists_reduced_fraction' x S hg0 hx.irreducible
    have hu : IsUnit (selfZPow x S n) :=
      IsUnit.of_mul_eq_one (selfZPow x S (- n)) (selfZPow_mul_neg x S n)
    refine ⟨a, Ideal.eq_of_map_algebraMap_le S x ?_ (by simp [IsPrime.mul_mem_left_iff hxp]) ?_⟩
    · simp [hg, map_span, ← span_singleton_mul_left_unit hu (algebraMap R S a), hag]
    · intro y hy
      rw [mem_span_singleton] at hy ⊢
      exact (hx.left_dvd_or_dvd_right_of_dvd_mul hy).resolve_left hxa
/-
**Ideal.isPrincipal_of_isPrincipal_localizationAway_of_prime** 是 Mathlib 中的一个定理，
位于命名空间 `Ideal`。
形式化陈述：isPrincipal_of_isPrincipal_localizationAway_of_prime (hp : (map (algebraMa
p R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal
参数：hp : (map (algebraMap R (Localization.Away x)) p).IsPrincipal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime`：isPrincipa
l_of_isPrincipal_isLocalizationAway_of_prime (S : Type*) [CommRing S] [Algebra R
 S] [IsLocalization.Away x S] (hp : (map (algebraM…
-/
theorem isPrincipal_of_isPrincipal_localizationAway_of_prime
    (hp : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal :=
  p.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime hx hxp (Localization.Away x) hp

end Ideal

namespace UniqueFactorizationMonoid

/-
**UniqueFactorizationMonoid.isPrincipal_of_height_eq_one** 是 Mathlib 中的一个定理，位于命名
空间 `UniqueFactorizationMonoid`。
形式化陈述：isPrincipal_of_height_eq_one [UniqueFactorizationMonoid R] {p : Ideal R} [
p.IsPrime] (hph : p.height = 1) : p.IsPrincipal
参数：hph : p.height = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ne_bot_of_height_eq_one`：Ideal.ne_bot_of_height_eq_one [IsDomain R
] {I : Ideal R} (h : I.height = 1) : I != ⊥
· 使用定理 `Ideal.IsPrime.exists_mem_prime_of_ne_bot`：Ideal.IsPrime.exists_mem_prime
_of_ne_bot {R : Type*} [CommSemiring R] [UniqueFactorizationMonoid R] {I : Ideal
 R} (hI₂ : I.IsPrime) (hI : I …
· 使用引理 `Ideal.eq_span_singleton_of_height_eq_one`：Ideal.eq_span_singleton_of_hei
ght_eq_one [IsDomain R] {p : Ideal R} [p.IsPrime] (h1 : p.height = 1) {x : R} (h
x : x in p) (hxp : Prime x) : …
-/
theorem isPrincipal_of_height_eq_one [UniqueFactorizationMonoid R]
    {p : Ideal R} [p.IsPrime] (hph : p.height = 1) : p.IsPrincipal := by
  have hpn : p ≠ ⊥ := p.ne_bot_of_height_eq_one hph
  obtain ⟨x, hxmem, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹_› hpn
  exact ⟨x, p.eq_span_singleton_of_height_eq_one hph hxmem hxp⟩

variable [IsNoetherianRing R]
/-
**UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one** 是 Mathlib 中
的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：of_forall_isPrincipal_of_height_eq_one (h : forall (p : Ideal R) [p.IsPrim
e], p.height = 1 -> p.IsPrincipal) : UniqueFactorizationMonoid R
参数：h : forall (p : Ideal R) [p.IsPrime], p.height = 1 -> p.IsPrincipal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime`：∀ {R : Type u
_1} [inst : CommSemiring R] [IsDomain R],   UniqueFactorizationMonoid R ↔ ∀ (I :
 Ideal R), I ≠ ⊥ → I.IsPrime → ∃ x ∈ I, Prime x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用引理 `Ideal.IsMinimalPrime.isPrime`：Ideal.IsMinimalPrime.isPrime {p : Ideal R}
 (h : I.IsMinimalPrime p) : p.IsPrime
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Ideal.IsMinimalPrime.le`：Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.Is
MinimalPrime p) : I <= p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`：Ideal.height_le
_one_of_isPrincipal_of_mem_minimalPrimes (I : Ideal R) [I.IsPrincipal] (p : Idea
l R) (hp : p in I.minimalPrimes) : p.height <…
· 使用定理 `instIsPrincipalSpanSingletonSet`：∀ {R : Type u_1} [inst : Semiring R] {x
 : R}, Submodule.IsPrincipal (Ideal.span {x})
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Submodule.IsPrincipal.generator_mem`：generator_mem (S : Submodule R M) [
S.IsPrincipal] : generator S in S
· 使用定理 `Submodule.IsPrincipal.prime_generator_of_isPrime`：prime_generator_of_isP
rime (S : Ideal R) [S.IsPrincipal] [is_prime : S.IsPrime] (ne_bot : S != ⊥) : Pr
ime (generator S)
-/
theorem of_forall_isPrincipal_of_height_eq_one
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → p.IsPrincipal) :
    UniqueFactorizationMonoid R := by
  rw [iff_exists_prime_mem_of_isPrime]
  intro I hIn _
  rcases I.ne_bot_iff.mp hIn with ⟨x, hxI, hx0⟩
  rcases Ideal.exists_minimalPrimes_le (I.span_singleton_le_iff_mem.mpr hxI) with ⟨p, hpmin, hpl⟩
  have : p.IsPrime := hpmin.isPrime
  have hpn : p ≠ ⊥ := fun hpb ↦ hx0 <|
    Ideal.span_singleton_eq_bot.mp <| bot_unique (hpmin.le.trans_eq hpb)
  have hpp : p.IsPrincipal := h p <| le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hpmin)
      (by simpa [Order.one_le_iff_ne_zero])
  exact ⟨hpp.generator p, hpl (hpp.generator_mem p), hpp.prime_generator_of_isPrime p hpn⟩

/-- Let `R` be a Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is
  principal. -/
@[stacks 0AFT]
/-
**UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one** 是 Mathlib 
中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：iff_forall_isPrincipal_of_height_eq_one : UniqueFactorizationMonoid R ↔ fo
rall (p : Ideal R) [p.IsPrime], p.height = 1 -> p.IsPrincipal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.isPrincipal_of_height_eq_one`：isPrincipal_of_h
eight_eq_one [UniqueFactorizationMonoid R] {p : Ideal R} [p.IsPrime] (hph : p.he
ight = 1) : p.IsPrincipal
· 使用定理 `UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one`：of_for
all_isPrincipal_of_height_eq_one (h : forall (p : Ideal R) [p.IsPrime], p.height
 = 1 -> p.IsPrincipal) : UniqueFactorizationMonoid R

--- 原说明 ---
Let `R` be a Noetherian domain. Then `R` is a UFD if and only if every height `1
` prime ideal is
  principal.
-/
theorem iff_forall_isPrincipal_of_height_eq_one :
    UniqueFactorizationMonoid R ↔ ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → p.IsPrincipal :=
  ⟨fun _ _ _ ↦ isPrincipal_of_height_eq_one, of_forall_isPrincipal_of_height_eq_one⟩
/-
**UniqueFactorizationMonoid.iff_of_isLocalizationAway_of_prime** 是 Mathlib 中的一个定
理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：iff_of_isLocalizationAway_of_prime {x : R} (hx : Prime x) (S : Type*) [Com
mRing S] [Algebra R S] [IsLocalization.Away x S] : UniqueFactorizationMonoid R ↔
 UniqueFactorizationMonoid S
参数：hx : Prime x；S : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.Away.isDomain`：isDomain [IsDomain R] {x : R} (hx : x != 0
) [IsLocalization.Away x S] : IsDomain S
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `UniqueFactorizationMonoid.of_isLocalization`：UniqueFactorizationMonoid.o
f_isLocalization (N : Type*) [CommSemiring N] [Algebra M N] [IsLocalization S N]
 [UniqueFactorizationMonoid M] : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`：iff_f
orall_isPrincipal_of_height_eq_one : UniqueFactorizationMonoid R ↔ forall (p : I
deal R) [p.IsPrime], p.height = 1 -> p.IsPrincipal
· 使用引理 `Ideal.eq_span_singleton_of_height_eq_one`：Ideal.eq_span_singleton_of_hei
ght_eq_one [IsDomain R] {p : Ideal R} [p.IsPrime] (h1 : p.height = 1) {x : R} (h
x : x in p) (hxp : Prime x) : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.disjoint_powers_iff_notMem_of_isPrime`：disjoint_powers_iff_notMem_
of_isPrime [I.IsPrime] (y : R) : Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ 
I
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
· 使用定理 `Ideal.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime`：isPrincipa
l_of_isPrincipal_isLocalizationAway_of_prime (S : Type*) [CommRing S] [Algebra R
 S] [IsLocalization.Away x S] (hp : (map (algebraM…
· 使用定理 `IsNoetherianRing.wfDvdMonoid`：∀ {R : Type u_1} [inst : CommSemiring R] [
IsDomain R] [h : IsNoetherianRing R], WfDvdMonoid R
· 使用定理 `UniqueFactorizationMonoid.isPrincipal_of_height_eq_one`：isPrincipal_of_h
eight_eq_one [UniqueFactorizationMonoid R] {p : Ideal R} [p.IsPrime] (hph : p.he
ight = 1) : p.IsPrincipal
· 使用定理 `IsLocalization.height_under`：IsLocalization.height_under (S : Submonoid 
R) {A : Type*} [CommRing A] [Algebra R A] [IsLocalization S A] (J : Ideal A) : (
J.under R).height…
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
-/
theorem iff_of_isLocalizationAway_of_prime {x : R} (hx : Prime x)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S] :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid S := by
  have : IsDomain S := IsLocalization.Away.isDomain S hx.ne_zero
  refine ⟨fun _ ↦ of_isLocalization (Submonoid.powers x) S, fun _ ↦ ?_⟩
  rw [iff_forall_isPrincipal_of_height_eq_one]
  intro p hp h1
  by_cases hxp : x ∈ p
  · exact ⟨x, p.eq_span_singleton_of_height_eq_one h1 hxp hx⟩
  · have hd := by rwa [← Ideal.disjoint_powers_iff_notMem_of_isPrime x] at hxp
    have := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) S p hp hd
    refine p.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime hx hxp S
      (isPrincipal_of_height_eq_one ?_)
    rw [← IsLocalization.height_under (Submonoid.powers x),
      IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) S hp hd, h1]

/-- Let `R` be a Noetherian domain, `x ∈ R` be a prime element. Then `R` is a UFD if and only if
  `Rₓ` is a UFD. -/
/-
**UniqueFactorizationMonoid.iff_localizationAway_of_prime** 是 Mathlib 中的一个定理，位于命
名空间 `UniqueFactorizationMonoid`。
形式化陈述：iff_localizationAway_of_prime {x : R} (hx : Prime x) : UniqueFactorization
Monoid R ↔ UniqueFactorizationMonoid (Localization.Away x)
参数：hx : Prime x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.iff_of_isLocalizationAway_of_prime`：iff_of_isL
ocalizationAway_of_prime {x : R} (hx : Prime x) (S : Type*) [CommRing S] [Algebr
a R S] [IsLocalization.Away x S] : UniqueFactoriza…

--- 原说明 ---
Let `R` be a Noetherian domain, `x ∈ R` be a prime element. Then `R` is a UFD if
 and only if
  `Rₓ` is a UFD.
-/
theorem iff_localizationAway_of_prime {x : R} (hx : Prime x) :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid (Localization.Away x) :=
  iff_of_isLocalizationAway_of_prime hx (Localization.Away x)

end UniqueFactorizationMonoid

