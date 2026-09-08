/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Multiplicative maps on unique factorization domains

## Main results
* `UniqueFactorizationMonoid.induction_on_coprime`: if `P` holds for `0`, units and powers of
  primes, and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`, then `P` holds on all `a : α`.
* `UniqueFactorizationMonoid.multiplicative_of_coprime`: if `f` maps `p ^ i` to `(f p) ^ i` for
  primes `p`, and `f` is multiplicative on coprime elements, then `f` is multiplicative everywhere.
-/

public section

assert_not_exists Field

variable {α : Type*}

namespace UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

section Multiplicative

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
variable {β : Type*} [CommMonoidWithZero β]

/-
**UniqueFactorizationMonoid.prime_pow_coprime_prod_of_coprime_insert** 是 Mathlib
 中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：prime_pow_coprime_prod_of_coprime_insert [DecidableEq α] {s : Finset α} (i
 : α -> Nat) (p : α) (hps : p ∉ s) (is_prime : forall q in insert p s, Prime q) 
(is_coprime : forallᵉ (q in insert p s) (q' in insert p s), q ∣ q' -> q = q') : 
IsRelPrime (p ^ i p) (∏ p' in s, p' ^ i p')
参数：i : α -> Nat；p : α；hps : p ∉ s；is_prime : forall q in insert p s, Prime q；is_
coprime : forallᵉ (q in insert p s) (q' in insert p s), q ∣ q' -> q = q'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors`：isRelPrime_if
f_no_prime_factors {a b : R} (ha : a != 0) : IsRelPrime a b ↔ forall ⦃d⦄, d ∣ a 
-> d ∣ b -> ¬Prime d
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `Prime.dvd_of_dvd_pow`：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) :
 p ∣ a
· 使用定理 `Prime.exists_mem_multiset_dvd`：exists_mem_multiset_dvd (hp : Prime p) {s
 : Multiset M₀} : p ∣ s.prod -> exists a in s, p ∣ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Irreducible.dvd_symm`：Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Ir
reducible p) (hq : Irreducible q) : p ∣ q -> q ∣ p
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_val`：mem_val {a : α} {s : Finset α} : (a in s.1) = (a in s)
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prime_pow_coprime_prod_of_coprime_insert [DecidableEq α] {s : Finset α} (i : α → ℕ) (p : α)
    (hps : p ∉ s) (is_prime : ∀ q ∈ insert p s, Prime q)
    (is_coprime : ∀ᵉ (q ∈ insert p s) (q' ∈ insert p s), q ∣ q' → q = q') :
    IsRelPrime (p ^ i p) (∏ p' ∈ s, p' ^ i p') := by
  have hp := is_prime _ (Finset.mem_insert_self _ _)
  refine (isRelPrime_iff_no_prime_factors <| pow_ne_zero _ hp.ne_zero).mpr ?_
  intro d hdp hdprod hd
  apply hps
  replace hdp := hd.dvd_of_dvd_pow hdp
  obtain ⟨q, q_mem', hdq⟩ := hd.exists_mem_multiset_dvd hdprod
  obtain ⟨q, q_mem, rfl⟩ := Multiset.mem_map.mp q_mem'
  replace hdq := hd.dvd_of_dvd_pow hdq
  have : p ∣ q := dvd_trans (hd.irreducible.dvd_symm hp.irreducible hdp) hdq
  convert! q_mem using 0
  rw [Finset.mem_val,
    is_coprime _ (Finset.mem_insert_self p s) _ (Finset.mem_insert_of_mem q_mem) this]

/-- If `P` holds for units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on a product of powers of distinct primes. -/
@[elab_as_elim]
/-
**UniqueFactorizationMonoid.induction_on_prime_power** 是 Mathlib 中的一个定理，位于命名空间 `
UniqueFactorizationMonoid`。
形式化陈述：induction_on_prime_power {P : α -> Prop} (s : Finset α) (i : α -> Nat) (is
_prime : forall p in s, Prime p) (is_coprime : forallᵉ (p in s) (q in s), p ∣ q 
-> p = q) (h1 : forall {x}, IsUnit x -> P x) (hpr : forall {p} (i : Nat), Prime 
p -> P (p ^ i)) (hcp : forall {x y}, IsRelPrime x y -> P x -> P y -> P (x * y)) 
: P (∏ p in s, p ^ i p)
参数：s : Finset α；i : α -> Nat；is_prime : forall p in s, Prime p；is_coprime : fora
llᵉ (p in s) (q in s), p ∣ q -> p = q；h1 : forall {x}, IsUnit x -> P x；hpr : for
all {p} (i : Nat), Prime p -> P (p ^ i)；hcp : forall {x y}, IsRelPrime x y -> P 
x -> P y -> P (x * y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `UniqueFactorizationMonoid.prime_pow_coprime_prod_of_coprime_insert`：prim
e_pow_coprime_prod_of_coprime_insert [DecidableEq α] {s : Finset α} (i : α -> Na
t) (p : α) (hps : p ∉ s) (is_prime : forall q in insert …
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
If `P` holds for units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on a product of powers of distinct primes.
-/
theorem induction_on_prime_power {P : α → Prop} (s : Finset α) (i : α → ℕ)
    (is_prime : ∀ p ∈ s, Prime p) (is_coprime : ∀ᵉ (p ∈ s) (q ∈ s), p ∣ q → p = q)
    (h1 : ∀ {x}, IsUnit x → P x) (hpr : ∀ {p} (i : ℕ), Prime p → P (p ^ i))
    (hcp : ∀ {x y}, IsRelPrime x y → P x → P y → P (x * y)) :
    P (∏ p ∈ s, p ^ i p) := by
  let := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simpa using h1 isUnit_one
  | insert p f' hpf' ih =>
    rw [Finset.prod_insert hpf']
    exact
      hcp (prime_pow_coprime_prod_of_coprime_insert i p hpf' is_prime is_coprime)
        (hpr (i p) (is_prime _ (Finset.mem_insert_self _ _)))
        (ih (fun q hq => is_prime _ (Finset.mem_insert_of_mem hq)) fun q hq q' hq' =>
          is_coprime _ (Finset.mem_insert_of_mem hq) _ (Finset.mem_insert_of_mem hq'))

/-- If `P` holds for `0`, units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on all `a : α`. -/
@[elab_as_elim]
/-
**UniqueFactorizationMonoid.induction_on_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Uniq
ueFactorizationMonoid`。
形式化陈述：induction_on_coprime {P : α -> Prop} (a : α) (h0 : P 0) (h1 : forall {x}, 
IsUnit x -> P x) (hpr : forall {p} (i : Nat), Prime p -> P (p ^ i)) (hcp : foral
l {x y}, IsRelPrime x y -> P x -> P y -> P (x * y)) : P a
参数：a : α；h0 : P 0；h1 : forall {x}, IsUnit x -> P x；hpr : forall {p} (i : Nat), P
rime p -> P (p ^ i)；hcp : forall {x y}, IsRelPrime x y -> P x -> P y -> P (x * y
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
· 使用定理 `Finset.prod_multiset_map_count`：prod_multiset_map_count [DecidableEq ι] 
(s : Multiset ι) {M : Type*} [CommMonoid M] (f : ι -> M) : (s.map f).prod = ∏ m 
in s.toFinset, f m ^…
· 使用定理 `UniqueFactorizationMonoid.induction_on_prime_power`：induction_on_prime_p
ower {P : α -> Prop} (s : Finset α) (i : α -> Nat) (is_prime : forall p in s, Pr
ime p) (is_coprime : forallᵉ (p in s) (q…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_eq_of_dvd`：normalizedFactors
_eq_of_dvd (a : α) : forallᵉ (p in normalizedFactors a) (q in normalizedFactors 
a), p ∣ q -> p = q

--- 原说明 ---
If `P` holds for `0`, units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on all `a : α`.
-/
theorem induction_on_coprime {P : α → Prop} (a : α) (h0 : P 0) (h1 : ∀ {x}, IsUnit x → P x)
    (hpr : ∀ {p} (i : ℕ), Prime p → P (p ^ i))
    (hcp : ∀ {x y}, IsRelPrime x y → P x → P y → P (x * y)) : P a := by
  let := Classical.decEq α
  have P_of_associated : ∀ {x y}, Associated x y → P x → P y := by
    rintro x y ⟨u, rfl⟩ hx
    exact hcp (fun p _ hpx => isUnit_of_dvd_unit hpx u.isUnit) hx (h1 u.isUnit)
  by_cases ha0 : a = 0
  · rwa [ha0]
  have : Nontrivial α := ⟨⟨_, _, ha0⟩⟩
  let : StrongNormalizationMonoid α := UniqueFactorizationMonoid.strongNormalizationMonoid
  refine P_of_associated (prod_normalizedFactors ha0) ?_
  rw [← (normalizedFactors a).map_id, Finset.prod_multiset_map_count]
  refine induction_on_prime_power _ _ ?_ ?_ @h1 @hpr @hcp <;> simp only [Multiset.mem_toFinset]
  · apply prime_of_normalized_factor
  · apply normalizedFactors_eq_of_dvd

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative on all products of primes. -/
/-
**UniqueFactorizationMonoid.multiplicative_prime_power** 是 Mathlib 中的一个定理，位于命名空间
 `UniqueFactorizationMonoid`。
形式化陈述：multiplicative_prime_power {f : α -> β} (s : Finset α) (i j : α -> Nat) (i
s_prime : forall p in s, Prime p) (is_coprime : forallᵉ (p in s) (q in s), p ∣ q
 -> p = q) (h1 : forall {x y}, IsUnit y -> f (x * y) = f x * f y) (hpr : forall 
{p} (i : Nat), Prime p -> f (p ^ i) = f p ^ i) (hcp : forall {x y}, IsRelPrime x
 y -> f (x * y) = f x * f y) : f (∏ p in s, p ^ (i p + j p)) = f (∏ p in s, p ^ 
i p) * f (∏ p in s, p ^ j p)
参数：s : Finset α；i j : α -> Nat；is_prime : forall p in s, Prime p；is_coprime : fo
rallᵉ (p in s) (q in s), p ∣ q -> p = q；h1 : forall {x y}, IsUnit y -> f (x * y)
 = f x * f y；hpr : forall {p} (i : Nat), Prime p -> f (p ^ i) = f p ^ i；hcp : fo
rall {x y}, IsRelPrime x y -> f (x * y) = f x * f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `UniqueFactorizationMonoid.prime_pow_coprime_prod_of_coprime_insert`：prim
e_pow_coprime_prod_of_coprime_insert [DecidableEq α] {s : Finset α} (i : α -> Na
t) (p : α) (hps : p ∉ s) (is_prime : forall q in insert …
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)

--- 原说明 ---
If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative on all product
s of primes.
-/
theorem multiplicative_prime_power {f : α → β} (s : Finset α) (i j : α → ℕ)
    (is_prime : ∀ p ∈ s, Prime p) (is_coprime : ∀ᵉ (p ∈ s) (q ∈ s), p ∣ q → p = q)
    (h1 : ∀ {x y}, IsUnit y → f (x * y) = f x * f y)
    (hpr : ∀ {p} (i : ℕ), Prime p → f (p ^ i) = f p ^ i)
    (hcp : ∀ {x y}, IsRelPrime x y → f (x * y) = f x * f y) :
    f (∏ p ∈ s, p ^ (i p + j p)) = f (∏ p ∈ s, p ^ i p) * f (∏ p ∈ s, p ^ j p) := by
  let := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simpa using h1 isUnit_one
  | insert p s hps ih =>
    have hpr_p := is_prime _ (Finset.mem_insert_self _ _)
    have hpr_s : ∀ p ∈ s, Prime p := fun p hp => is_prime _ (Finset.mem_insert_of_mem hp)
    have hcp_p := fun i => prime_pow_coprime_prod_of_coprime_insert i p hps is_prime is_coprime
    have hcp_s : ∀ᵉ (p ∈ s) (q ∈ s), p ∣ q → p = q := fun p hp q hq =>
      is_coprime p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps, Finset.prod_insert hps, Finset.prod_insert hps, hcp (hcp_p _),
      hpr _ hpr_p, hcp (hcp_p _), hpr _ hpr_p, hcp (hcp_p (fun p => i p + j p)), hpr _ hpr_p,
      ih hpr_s hcp_s, pow_add, mul_assoc, mul_left_comm (f p ^ j p), mul_assoc]

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative everywhere. -/
/-
**UniqueFactorizationMonoid.multiplicative_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 
`UniqueFactorizationMonoid`。
形式化陈述：multiplicative_of_coprime (f : α -> β) (a b : α) (h0 : f 0 = 0) (h1 : fora
ll {x y}, IsUnit y -> f (x * y) = f x * f y) (hpr : forall {p} (i : Nat), Prime 
p -> f (p ^ i) = f p ^ i) (hcp : forall {x y}, IsRelPrime x y -> f (x * y) = f x
 * f y) : f (a * b) = f a * f b
参数：f : α -> β；a b : α；h0 : f 0 = 0；h1 : forall {x y}, IsUnit y -> f (x * y) = f 
x * f y；hpr : forall {p} (i : Nat), Prime p -> f (p ^ i) = f p ^ i；hcp : forall 
{x y}, IsRelPrime x y -> f (x * y) = f x * f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `UniqueFactorizationMonoid.multiplicative_prime_power`：multiplicative_pri
me_power {f : α -> β} (s : Finset α) (i j : α -> Nat) (is_prime : forall p in s,
 Prime p) (is_coprime : forallᵉ (p in s) (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.normalize_normalized_factor`：normalize_normali
zed_factor {a : α} : forall x : α, x in normalizedFactors a -> normalize x = x
· 使用定理 `normalize_eq_normalize`：normalize_eq_normalize {a b : α} (hab : a ∣ b) (
hba : b ∣ a) : normalize a = normalize b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Irreducible.dvd_symm`：Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Ir
reducible p) (hq : Irreducible q) : p ∣ q -> q ∣ p
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
· 使用定理 `Finset.prod_multiset_map_count`：prod_multiset_map_count [DecidableEq ι] 
(s : Multiset ι) {M : Type*} [CommMonoid M] (f : ι -> M) : (s.map f).prod = ∏ m 
in s.toFinset, f m ^…
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative everywhere.
-/
theorem multiplicative_of_coprime (f : α → β) (a b : α) (h0 : f 0 = 0)
    (h1 : ∀ {x y}, IsUnit y → f (x * y) = f x * f y)
    (hpr : ∀ {p} (i : ℕ), Prime p → f (p ^ i) = f p ^ i)
    (hcp : ∀ {x y}, IsRelPrime x y → f (x * y) = f x * f y) :
    f (a * b) = f a * f b := by
  let := Classical.decEq α
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul, h0, zero_mul]
  by_cases hb0 : b = 0
  · rw [hb0, mul_zero, h0, mul_zero]
  by_cases hf1 : f 1 = 0
  · calc
      f (a * b) = f (a * b * 1) := by rw [mul_one]
      _ = 0 := by simp only [h1 isUnit_one, hf1, mul_zero]
      _ = f a * f (b * 1) := by simp only [h1 isUnit_one, hf1, mul_zero]
      _ = f a * f b := by rw [mul_one]
  have : Nontrivial α := ⟨⟨_, _, ha0⟩⟩
  let : StrongNormalizationMonoid α := UniqueFactorizationMonoid.strongNormalizationMonoid
  suffices
      f (∏ p ∈ (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
        p ^ ((normalizedFactors a).count p + (normalizedFactors b).count p)) =
      f (∏ p ∈ (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
        p ^ (normalizedFactors a).count p) *
      f (∏ p ∈ (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
        p ^ (normalizedFactors b).count p) by
    obtain ⟨ua, a_eq⟩ := prod_normalizedFactors ha0
    obtain ⟨ub, b_eq⟩ := prod_normalizedFactors hb0
    rw [← a_eq, ← b_eq, mul_right_comm (Multiset.prod (normalizedFactors a)) ua
        (Multiset.prod (normalizedFactors b) * ub), h1 ua.isUnit, h1 ub.isUnit, h1 ua.isUnit, ←
      mul_assoc, h1 ub.isUnit, mul_right_comm _ (f ua), ← mul_assoc]
    congr
    rw [← (normalizedFactors a).map_id, ← (normalizedFactors b).map_id,
      Finset.prod_multiset_map_count, Finset.prod_multiset_map_count,
      Finset.prod_subset (Finset.subset_union_left (s₂ := (normalizedFactors b).toFinset)),
      Finset.prod_subset (Finset.subset_union_right (s₂ := (normalizedFactors b).toFinset)), ←
      Finset.prod_mul_distrib]
    · simp_rw [id, ← pow_add, this]
    all_goals simp only [Multiset.mem_toFinset]
    · intro p _ hpb
      simp [hpb]
    · intro p _ hpa
      simp [hpa]
  refine multiplicative_prime_power _ _ _ ?_ ?_ @h1 @hpr @hcp
  all_goals simp only [Multiset.mem_toFinset, Finset.mem_union]
  · rintro p (hpa | hpb) <;> apply prime_of_normalized_factor <;> assumption
  · rintro p (hp | hp) q (hq | hq) hdvd <;>
      rw [← normalize_normalized_factor _ hp, ← normalize_normalized_factor _ hq] <;>
      exact
        normalize_eq_normalize hdvd
          ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
            (prime_of_normalized_factor _ hq).irreducible hdvd)

end Multiplicative

end UniqueFactorizationMonoid

