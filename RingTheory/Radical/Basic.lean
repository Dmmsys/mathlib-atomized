/-
Copyright (c) 2024 Jineon Baek, Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee, Bhavik Mehta, Arend Mellendijk
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Radical of an element of a unique factorization normalization monoid

This file defines the radical of an element `a` in a unique factorization normalization
monoid as the product of normalized prime factors of `a` without duplication.
This is different from the radical of an ideal.

Lemmas relating to natural numbers and integers are in `Mathlib.RingTheory.Radical.NatInt`.

## Main declarations

- `radical`: The radical of an element `a` in a unique factorization monoid is the product of
  its prime factors.
- `radical_eq_of_associated`: If `a` and `b` are associates, i.e. `a * u = b` for some unit `u`,
  then `radical a = radical b`.
- `radical_mul_of_isUnit_left`: Multiplying by a unit does not change the radical.
- `radical_dvd_self`: `radical a` divides `a`.
- `radical_pow`: `radical (a ^ n) = radical a` for any `n ≥ 1`.
- `radical_of_prime`: Radical of a prime element is equal to its normalization.
- `radical_pow_of_prime`: Radical of a power of a prime element is equal to its normalization.
- `radical_mul`, `radical_prod`: Radical is multiplicative for (pairwise) relatively prime elements.
- `radical_mul_dvd`, `radical_prod_dvd`: Radical of a product divides the product of radicals.

### For Euclidean domains

- `EuclideanDomain.divRadical`: For an element `a` in a Euclidean domain, `a / radical a`.
- `EuclideanDomain.divRadical_mul`: `divRadical` of a product is the product of `divRadical`s.
- `IsCoprime.divRadical`: `divRadical` of coprime elements are coprime.

## TODO

- Connect this notion with `Ideal.radical`. Particularly, for a principal ideal,
  `Ideal.radical (Ideal.span {a}) = Ideal.span {radical a}`.
-/

@[expose] public noncomputable section

namespace UniqueFactorizationMonoid

variable {M : Type*} [CommMonoidWithZero M] [NormalizationMonoid M]
  [UniqueFactorizationMonoid M] {a b u : M}

open scoped Classical in
/-- The finite set of prime factors of an element in a unique factorization monoid. -/
/-
**UniqueFactorizationMonoid.primeFactors** 是 Mathlib 中的一个定义，位于命名空间 `UniqueFactor
izationMonoid`。
形式化陈述：primeFactors (a : M) : Finset M
参数：a : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite set of prime factors of an element in a unique factorization monoid.
-/
def primeFactors (a : M) : Finset M :=
  (normalizedFactors a).toFinset

@[simp]
/-
**UniqueFactorizationMonoid.toFinset_normalizedFactors** 是 Mathlib 中的一个定理，位于命名空间
 `UniqueFactorizationMonoid`。
形式化陈述：toFinset_normalizedFactors [DecidableEq M] : (normalizedFactors a).toFinse
t = primeFactors a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
theorem toFinset_normalizedFactors [DecidableEq M] :
    (normalizedFactors a).toFinset = primeFactors a := by
  unfold primeFactors
  convert rfl
/-
**UniqueFactorizationMonoid.mem_primeFactors** 是 Mathlib 中的一个引理，位于命名空间 `UniqueFa
ctorizationMonoid`。
形式化陈述：mem_primeFactors : a in primeFactors b ↔ a in normalizedFactors b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_primeFactors : a ∈ primeFactors b ↔ a ∈ normalizedFactors b := by
  simp only [primeFactors, Multiset.mem_toFinset]
/-
**UniqueFactorizationMonoid._root_.Associated.primeFactors_eq** 是 Mathlib 中的一个定理
，位于命名空间 `UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Associated.primeFactors_eq {a b : M} (h : Associated a b) :
    primeFactors a = primeFactors b := by
  unfold primeFactors
  rw [h.normalizedFactors_eq]
/-
**UniqueFactorizationMonoid.primeFactors_zero** 是 Mathlib 中的一个定理，位于命名空间 `UniqueF
actorizationMonoid`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [inst_1 : NormalizationMono
id M] [inst_2 : UniqueFactorizationMonoid M],   UniqueFactorizationMonoid.primeF
actors 0 = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma primeFactors_zero : primeFactors (0 : M) = ∅ := by simp [primeFactors]
/-
**UniqueFactorizationMonoid.primeFactors_one** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFa
ctorizationMonoid`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [inst_1 : NormalizationMono
id M] [inst_2 : UniqueFactorizationMonoid M],   UniqueFactorizationMonoid.primeF
actors 1 = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_one`：normalizedFactors_one :
 normalizedFactors (1 : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma primeFactors_one : primeFactors (1 : M) = ∅ := by simp [primeFactors]
/-
**UniqueFactorizationMonoid.pairwise_primeFactors_isRelPrime** 是 Mathlib 中的一个引理，
位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：pairwise_primeFactors_isRelPrime : Set.Pairwise (primeFactors a : Set M) I
sRelPrime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.primeFactors_zero`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M],   UniqueFactorizatio…
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Irreducible.isRelPrime_iff_not_dvd`：Irreducible.isRelPrime_iff_not_dvd [
Monoid M] {p n : M} (hp : Irreducible p) : IsRelPrime p n ↔ ¬ p ∣ n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `UniqueFactorizationMonoid.mem_normalizedFactors_iff'`：mem_normalizedFact
ors_iff' {p x : α} (h : x != 0) : p in normalizedFactors x ↔ Irreducible p ∧ nor
malize p = p ∧ p ∣ x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Irreducible.associated_of_dvd`：Irreducible.associated_of_dvd [Monoid M] 
{p q : M} (p_irr : Irreducible p) (q_irr : Irreducible q) (dvd : p ∣ q) : Associ
ated p q
· 使用定理 `Associated.eq_of_normalized`：Associated.eq_of_normalized {a b : α} (h : 
Associated a b) (ha : normalize a = a) (hb : normalize b = b) : a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma pairwise_primeFactors_isRelPrime :
    Set.Pairwise (primeFactors a : Set M) IsRelPrime := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  intro x hx y hy hxy
  simp only [Finset.mem_coe, mem_primeFactors, mem_normalizedFactors_iff' ha₀] at hx hy
  rw [hx.1.isRelPrime_iff_not_dvd]
  contrapose hxy
  have : Associated x y := hx.1.associated_of_dvd hy.1 hxy
  exact this.eq_of_normalized hx.2.1 hy.2.1
/-
**UniqueFactorizationMonoid.primeFactors_pow** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFa
ctorizationMonoid`。
形式化陈述：primeFactors_pow (a : M) {n : Nat} (hn : n != 0) : primeFactors (a ^ n) = 
primeFactors a
参数：a : M；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_pow`：normalizedFactors_pow {
x : α} (n : Nat) : normalizedFactors (x ^ n) = n • normalizedFactors x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.toFinset_nsmul`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Mu
ltiset α) (n : ℕ), n ≠ 0 → (n • s).toFinset = s.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem primeFactors_pow (a : M) {n : ℕ} (hn : n ≠ 0) : primeFactors (a ^ n) = primeFactors a := by
  simp_rw [primeFactors, normalizedFactors_pow, Multiset.toFinset_nsmul _ _ hn]

@[simp]
/-
**UniqueFactorizationMonoid.primeFactors_pow'** 是 Mathlib 中的一个定理，位于命名空间 `UniqueF
actorizationMonoid`。
形式化陈述：primeFactors_pow' (a : M) {n : Nat} [NeZero n] : primeFactors (a ^ n) = pr
imeFactors a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.primeFactors_pow`：primeFactors_pow (a : M) {n 
: Nat} (hn : n != 0) : primeFactors (a ^ n) = primeFactors a
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
theorem primeFactors_pow' (a : M) {n : ℕ} [NeZero n] : primeFactors (a ^ n) = primeFactors a :=
  primeFactors_pow a NeZero.out
/-
**UniqueFactorizationMonoid.normalizedFactors_nodup** 是 Mathlib 中的一个引理，位于命名空间 `U
niqueFactorizationMonoid`。
形式化陈述：normalizedFactors_nodup (ha : IsRadical a) : (normalizedFactors a).Nodup
参数：ha : IsRadical a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`：square
free_iff_nodup_normalizedFactors [NormalizationMonoid R] {x : R} (x0 : x != 0) :
 Squarefree x ↔ Multiset.Nodup (normalizedFactors x)
· 使用定理 `isRadical_iff_squarefree_of_ne_zero`：isRadical_iff_squarefree_of_ne_zero
 (h : x != 0) : IsRadical x ↔ Squarefree x
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `instIsGCDMonoidOfUniqueFactorizationMonoid`：∀ (α : Type u_2) [inst : Com
mMonoidWithZero α] [UniqueFactorizationMonoid α], IsGCDMonoid α
-/
lemma normalizedFactors_nodup (ha : IsRadical a) : (normalizedFactors a).Nodup := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rwa [← squarefree_iff_nodup_normalizedFactors ha₀, ← isRadical_iff_squarefree_of_ne_zero ha₀]

/--
If `x` is a unit, then the finset of prime factors of `x` is empty.
The converse is true with a nonzero assumption, see `primeFactors_eq_empty_iff`.
-/
/-
**UniqueFactorizationMonoid.primeFactors_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Un
iqueFactorizationMonoid`。
形式化陈述：primeFactors_of_isUnit (h : IsUnit a) : primeFactors a = ∅
参数：h : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.primeFactors.eq_1`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M]   (a : M), UniqueFact…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_of_isUnit`：normalizedFactors
_of_isUnit {x : α} (hx : IsUnit x) : normalizedFactors x = 0
· 使用定理 `Multiset.toFinset_zero`：toFinset_zero : toFinset (0 : Multiset α) = ∅

--- 原说明 ---
If `x` is a unit, then the finset of prime factors of `x` is empty.
The converse is true with a nonzero assumption, see `primeFactors_eq_empty_iff`.
-/
lemma primeFactors_of_isUnit (h : IsUnit a) : primeFactors a = ∅ := by
  classical
  rw [primeFactors, normalizedFactors_of_isUnit h, Multiset.toFinset_zero]

/--
The finset of prime factors of `x` is empty if and only if `x` is a unit.
The converse is true without the nonzero assumption, see `primeFactors_of_isUnit`.
-/
/-
**UniqueFactorizationMonoid.primeFactors_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 
`UniqueFactorizationMonoid`。
形式化陈述：primeFactors_eq_empty_iff (ha : a != 0) : primeFactors a = ∅ ↔ IsUnit a
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.primeFactors.eq_1`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M]   (a : M), UniqueFact…
· 使用定理 `Multiset.toFinset_eq_empty`：toFinset_eq_empty {m : Multiset α} : m.toFin
set = ∅ ↔ m = 0
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_eq_zero_iff`：normalizedFacto
rs_eq_zero_iff {x : α} (hx : x != 0) : normalizedFactors x = 0 ↔ IsUnit x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The finset of prime factors of `x` is empty if and only if `x` is a unit.
The converse is true without the nonzero assumption, see `primeFactors_of_isUnit
`.
-/
theorem primeFactors_eq_empty_iff (ha : a ≠ 0) : primeFactors a = ∅ ↔ IsUnit a := by
  classical
  rw [primeFactors, Multiset.toFinset_eq_empty, normalizedFactors_eq_zero_iff ha]
/-
**UniqueFactorizationMonoid.primeFactors_val_eq_normalizedFactors** 是 Mathlib 中的
一个引理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：primeFactors_val_eq_normalizedFactors (ha : IsRadical a) : (primeFactors a
).val = normalizedFactors a
参数：ha : IsRadical a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.primeFactors.eq_1`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M]   (a : M), UniqueFact…
· 使用定理 `Multiset.toFinset_val`：toFinset_val (s : Multiset α) : s.toFinset.1 = s.
dedup
· 使用定理 `Multiset.dedup_eq_self`：dedup_eq_self {s : Multiset α} : dedup s = s ↔ N
odup s
· 使用引理 `UniqueFactorizationMonoid.normalizedFactors_nodup`：normalizedFactors_nod
up (ha : IsRadical a) : (normalizedFactors a).Nodup
-/
lemma primeFactors_val_eq_normalizedFactors (ha : IsRadical a) :
    (primeFactors a).val = normalizedFactors a := by
  classical
  rw [primeFactors, Multiset.toFinset_val, Multiset.dedup_eq_self]
  exact normalizedFactors_nodup ha

-- Note that the non-zero assumptions are necessary here.
/-
**UniqueFactorizationMonoid.primeFactors_mul_eq_union** 是 Mathlib 中的一个定理，位于命名空间 
`UniqueFactorizationMonoid`。
形式化陈述：primeFactors_mul_eq_union [DecidableEq M] (ha : a != 0) (hb : b != 0) : pr
imeFactors (a * b) = primeFactors a union primeFactors b
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_mul`：normalizedFactors_mul {
x y : α} (hx : x != 0) (hy : y != 0) : normalizedFactors (x * y) = normalizedFac
tors x + normalizedFactors y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem primeFactors_mul_eq_union [DecidableEq M] (ha : a ≠ 0) (hb : b ≠ 0) :
    primeFactors (a * b) = primeFactors a ∪ primeFactors b := by
  ext p
  simp [mem_normalizedFactors_iff', mem_primeFactors, ha, hb]

/-- Relatively prime elements have disjoint prime factors (as finsets). -/
/-
**UniqueFactorizationMonoid.disjoint_primeFactors** 是 Mathlib 中的一个定理，位于命名空间 `Uni
queFactorizationMonoid`。
形式化陈述：disjoint_primeFactors (hc : IsRelPrime a b) : Disjoint (primeFactors a) (p
rimeFactors b)
参数：hc : IsRelPrime a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.disjoint_toFinset`：disjoint_toFinset {m1 m2 : Multiset α} : _ro
ot_.Disjoint m1.toFinset m2.toFinset ↔ Disjoint m1 m2
· 使用定理 `UniqueFactorizationMonoid.disjoint_normalizedFactors`：disjoint_normalize
dFactors {a b : α} (hc : IsRelPrime a b) : Disjoint (normalizedFactors a) (norma
lizedFactors b)

--- 原说明 ---
Relatively prime elements have disjoint prime factors (as finsets).
-/
theorem disjoint_primeFactors (hc : IsRelPrime a b) :
    Disjoint (primeFactors a) (primeFactors b) := by
  classical
  exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors hc)
/-
**UniqueFactorizationMonoid.primeFactors_mul_eq_disjUnion** 是 Mathlib 中的一个定理，位于命
名空间 `UniqueFactorizationMonoid`。
形式化陈述：primeFactors_mul_eq_disjUnion (hc : IsRelPrime a b) : primeFactors (a * b)
 = (primeFactors a).disjUnion (primeFactors b) (disjoint_primeFactors hc)
参数：hc : IsRelPrime a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.disjoint_primeFactors`：disjoint_primeFactors (
hc : IsRelPrime a b) : Disjoint (primeFactors a) (primeFactors b)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.primeFactors.congr_simp`：∀ {M : Type u_1} [ins
t : CommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFacto
rizationMonoid M]   (a a_1 : M), a = a_…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `UniqueFactorizationMonoid.primeFactors_zero`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M],   UniqueFactorizatio…
· 使用引理 `UniqueFactorizationMonoid.primeFactors_of_isUnit`：primeFactors_of_isUnit
 (h : IsUnit a) : primeFactors a = ∅
· 使用定理 `isRelPrime_zero_left`：isRelPrime_zero_left : IsRelPrime 0 x ↔ IsUnit x
· 使用定理 `Finset.disjUnion.congr_simp`：∀ {α : Type u_2} (s s_1 : Finset α) (e_s : 
s = s_1) (t t_1 : Finset α) (e_t : t = t_1) (h : Disjoint s t),   s.disjUnion t 
h = s_1.disjUnion…
· 使用定理 `Finset.empty_disjUnion`：empty_disjUnion (t : Finset α) (h : Disjoint ∅ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `isRelPrime_zero_right`：isRelPrime_zero_right : IsRelPrime x 0 ↔ IsUnit x
· 使用定理 `Finset.disjUnion_empty`：disjUnion_empty (s : Finset α) (h : Disjoint s ∅
· 使用定理 `Finset.disjUnion_eq_union`：disjUnion_eq_union (s t h) : @disjUnion α s t
 h = s union t
· 使用定理 `UniqueFactorizationMonoid.primeFactors_mul_eq_union`：primeFactors_mul_eq
_union [DecidableEq M] (ha : a != 0) (hb : b != 0) : primeFactors (a * b) = prim
eFactors a union primeFactors b
-/
theorem primeFactors_mul_eq_disjUnion (hc : IsRelPrime a b) :
    primeFactors (a * b) =
      (primeFactors a).disjUnion (primeFactors b) (disjoint_primeFactors hc) := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [isRelPrime_zero_left] at hc
    simp only [zero_mul, primeFactors_zero, Finset.empty_disjUnion, primeFactors_of_isUnit hc]
  obtain rfl | hb := eq_or_ne b 0
  · rw [isRelPrime_zero_right] at hc
    simp only [mul_zero, primeFactors_zero, primeFactors_of_isUnit hc, Finset.disjUnion_empty]
  classical
  rw [Finset.disjUnion_eq_union, primeFactors_mul_eq_union ha hb]

/-- The radical of an element `a` in a unique factorization monoid is the product of
the prime factors of `a`. -/
/-
**UniqueFactorizationMonoid.radical** 是 Mathlib 中的一个定义，位于命名空间 `UniqueFactorizati
onMonoid`。
形式化陈述：radical (a : M) : M
参数：a : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The radical of an element `a` in a unique factorization monoid is the product of
the prime factors of `a`.
-/
def radical (a : M) : M :=
  (primeFactors a).prod id
/-
**UniqueFactorizationMonoid.radical_zero** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactor
izationMonoid`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [inst_1 : NormalizationMono
id M] [inst_2 : UniqueFactorizationMonoid M],   UniqueFactorizationMonoid.radica
l 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `UniqueFactorizationMonoid.primeFactors_zero`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M],   UniqueFactorizatio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem radical_zero : radical (0 : M) = 1 := by simp [radical]
/-
**UniqueFactorizationMonoid.radical_one** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactori
zationMonoid`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [inst_1 : NormalizationMono
id M] [inst_2 : UniqueFactorizationMonoid M],   UniqueFactorizationMonoid.radica
l 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `UniqueFactorizationMonoid.primeFactors_one`：∀ {M : Type u_1} [inst : Com
mMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizatio
nMonoid M],   UniqueFactorizatio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem radical_one : radical (1 : M) = 1 := by simp [radical]
/-
**UniqueFactorizationMonoid.radical_eq_of_associated** 是 Mathlib 中的一个定理，位于命名空间 `
UniqueFactorizationMonoid`。
形式化陈述：radical_eq_of_associated (h : Associated a b) : radical a = radical b
参数：h : Associated a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical.eq_1`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M]   (a : M), UniqueFact…
· 使用定理 `Associated.primeFactors_eq`：∀ {M : Type u_1} [inst : CommMonoidWithZero 
M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMonoid M]   {a 
b : M}, Associat…
-/
theorem radical_eq_of_associated (h : Associated a b) : radical a = radical b := by
  rw [radical, radical, Associated.primeFactors_eq h]
/-
**UniqueFactorizationMonoid.radical_associated** 是 Mathlib 中的一个引理，位于命名空间 `Unique
FactorizationMonoid`。
形式化陈述：radical_associated (ha : IsRadical a) (ha' : a != 0) : Associated (radical
 a) a
参数：ha : IsRadical a；ha' : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical.eq_1`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M]   (a : M), UniqueFact…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_val`：prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.p
rod id
· 使用引理 `UniqueFactorizationMonoid.primeFactors_val_eq_normalizedFactors`：primeFa
ctors_val_eq_normalizedFactors (ha : IsRadical a) : (primeFactors a).val = norma
lizedFactors a
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
-/
lemma radical_associated (ha : IsRadical a) (ha' : a ≠ 0) :
    Associated (radical a) a := by
  rw [radical, ← Finset.prod_val, primeFactors_val_eq_normalizedFactors ha]
  exact prod_normalizedFactors ha'

/-- If `a` is a radical element, then it divides its radical. -/
/-
**UniqueFactorizationMonoid._root_.IsRadical.dvd_radical** 是 Mathlib 中的一个引理，位于命名
空间 `UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a` is a radical element, then it divides its radical.
-/
lemma _root_.IsRadical.dvd_radical (ha : IsRadical a) (ha' : a ≠ 0) : a ∣ radical a :=
  (radical_associated ha ha').dvd'
/-
**UniqueFactorizationMonoid.radical_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `UniqueF
actorizationMonoid`。
形式化陈述：radical_of_isUnit (h : IsUnit a) : radical a = 1
参数：h : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniqueFactorizationMonoid.radical_eq_of_associated`：radical_eq_of_associ
ated (h : Associated a b) : radical a = radical b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `associated_one_iff_isUnit`：associated_one_iff_isUnit [Monoid M] {a : M} 
: (a : M) ~ᵤ 1 ↔ IsUnit a
· 使用定理 `UniqueFactorizationMonoid.radical_one`：∀ {M : Type u_1} [inst : CommMono
idWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMono
id M],   UniqueFactorizatio…
-/
theorem radical_of_isUnit (h : IsUnit a) : radical a = 1 :=
  (radical_eq_of_associated (associated_one_iff_isUnit.mpr h)).trans radical_one
/-
**UniqueFactorizationMonoid.radical_mul_of_isUnit_left** 是 Mathlib 中的一个定理，位于命名空间
 `UniqueFactorizationMonoid`。
形式化陈述：radical_mul_of_isUnit_left (h : IsUnit u) : radical (u * a) = radical a
参数：h : IsUnit u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.radical_eq_of_associated`：radical_eq_of_associ
ated (h : Associated a b) : radical a = radical b
· 使用定理 `associated_unit_mul_left`：associated_unit_mul_left {N : Type*} [CommMono
id N] (a u : N) (hu : IsUnit u) : Associated (u * a) a
-/
theorem radical_mul_of_isUnit_left (h : IsUnit u) : radical (u * a) = radical a :=
  radical_eq_of_associated (associated_unit_mul_left _ _ h)
/-
**UniqueFactorizationMonoid.radical_mul_of_isUnit_right** 是 Mathlib 中的一个定理，位于命名空
间 `UniqueFactorizationMonoid`。
形式化陈述：radical_mul_of_isUnit_right (h : IsUnit u) : radical (a * u) = radical a
参数：h : IsUnit u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.radical_eq_of_associated`：radical_eq_of_associ
ated (h : Associated a b) : radical a = radical b
· 使用定理 `associated_mul_unit_left`：associated_mul_unit_left {N : Type*} [Monoid N
] (a u : N) (hu : IsUnit u) : Associated (a * u) a
-/
theorem radical_mul_of_isUnit_right (h : IsUnit u) : radical (a * u) = radical a :=
  radical_eq_of_associated (associated_mul_unit_left _ _ h)
/-
**UniqueFactorizationMonoid.radical_pow** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactori
zationMonoid`。
形式化陈述：radical_pow (a : M) {n : Nat} (hn : n != 0) : radical (a ^ n) = radical a
参数：a : M；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `UniqueFactorizationMonoid.primeFactors_pow`：primeFactors_pow (a : M) {n 
: Nat} (hn : n != 0) : primeFactors (a ^ n) = primeFactors a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem radical_pow (a : M) {n : ℕ} (hn : n ≠ 0) : radical (a ^ n) = radical a := by
  simp_rw [radical, primeFactors_pow a hn]
/-
**UniqueFactorizationMonoid.radical_pow_dvd** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFac
torizationMonoid`。
形式化陈述：radical_pow_dvd {n : Nat} : radical (a ^ n) ∣ radical a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical.congr_simp`：∀ {M : Type u_1} [inst : C
ommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizat
ionMonoid M]   (a a_1 : M), a = a_…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `UniqueFactorizationMonoid.radical_one`：∀ {M : Type u_1} [inst : CommMono
idWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMono
id M],   UniqueFactorizatio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.radical_pow`：radical_pow (a : M) {n : Nat} (hn
 : n != 0) : radical (a ^ n) = radical a
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem radical_pow_dvd {n : ℕ} : radical (a ^ n) ∣ radical a := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [radical_pow _ hn]
/-
**UniqueFactorizationMonoid.radical_dvd_self** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFa
ctorizationMonoid`。
形式化陈述：radical_dvd_self : radical a ∣ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `UniqueFactorizationMonoid.radical.eq_1`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M]   (a : M), UniqueFact…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_val`：prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.p
rod id
· 使用定理 `Associated.dvd_iff_dvd_right`：Associated.dvd_iff_dvd_right [Monoid M] {a
 b c : M} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `Multiset.prod_dvd_prod_of_le`：prod_dvd_prod_of_le (h : s <= t) : s.prod 
∣ t.prod
· 使用定理 `UniqueFactorizationMonoid.primeFactors.eq_1`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M]   (a : M), UniqueFact…
· 使用定理 `Multiset.toFinset_val`：toFinset_val (s : Multiset α) : s.toFinset.1 = s.
dedup
· 使用定理 `Multiset.dedup_le`：dedup_le (s : Multiset α) : dedup s <= s
-/
theorem radical_dvd_self : radical a ∣ a := by
  classical
  by_cases ha : a = 0
  · rw [ha]
    apply dvd_zero
  · rw [radical, ← Finset.prod_val, ← (prod_normalizedFactors ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors, Multiset.toFinset_val]
    apply Multiset.dedup_le
/-
**UniqueFactorizationMonoid.radical_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFa
ctorizationMonoid`。
形式化陈述：radical_of_prime (ha : Prime a) : radical a = normalize a
参数：ha : Prime a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical.eq_1`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M]   (a : M), UniqueFact…
· 使用定理 `UniqueFactorizationMonoid.primeFactors.eq_1`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M]   (a : M), UniqueFact…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_irreducible`：normalizedFacto
rs_irreducible {a : α} (ha : Irreducible a) : normalizedFactors a = {normalize a
}
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Multiset.toFinset_singleton`：toFinset_singleton (a : α) : toFinset ({a} 
: Multiset α) = {a}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem radical_of_prime (ha : Prime a) : radical a = normalize a := by
  rw [radical, primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]
/-
**UniqueFactorizationMonoid.radical_pow_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `Uniq
ueFactorizationMonoid`。
形式化陈述：radical_pow_of_prime (ha : Prime a) {n : Nat} (hn : n != 0) : radical (a ^
 n) = normalize a
参数：ha : Prime a；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical_pow`：radical_pow (a : M) {n : Nat} (hn
 : n != 0) : radical (a ^ n) = radical a
· 使用定理 `UniqueFactorizationMonoid.radical_of_prime`：radical_of_prime (ha : Prime
 a) : radical a = normalize a
-/
theorem radical_pow_of_prime (ha : Prime a) {n : ℕ} (hn : n ≠ 0) :
    radical (a ^ n) = normalize a := by
  rw [radical_pow a hn]
  exact radical_of_prime ha
/-
**UniqueFactorizationMonoid.radical_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFac
torizationMonoid`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [inst_1 : NormalizationMono
id M] [inst_2 : UniqueFactorizationMonoid M]   {a : M} [Nontrivial M], UniqueFac
torizationMonoid.radical a ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical.eq_1`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M]   (a : M), UniqueFact…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_val`：prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.p
rod id
· 使用引理 `Multiset.prod_ne_zero`：prod_ne_zero (h : (0 : M₀) ∉ s) : s.prod != 0
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `UniqueFactorizationMonoid.primeFactors.eq_1`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M]   (a : M), UniqueFact…
· 使用定理 `UniqueFactorizationMonoid.zero_notMem_normalizedFactors`：zero_notMem_nor
malizedFactors (x : α) : (0 : α) ∉ normalizedFactors x
-/
@[simp] theorem radical_ne_zero [Nontrivial M] : radical a ≠ 0 := by
  rw [radical, ← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [primeFactors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_notMem_normalizedFactors _

/--
An irreducible `a` divides the radical of `b` if and only if it divides `b` itself.
Note this generalises to radical elements `a`, see `UniqueFactorizationMonoid.dvd_radical_iff`.
-/
/-
**UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible** 是 Mathlib 中的一个引理，位于
命名空间 `UniqueFactorizationMonoid`。
形式化陈述：dvd_radical_iff_of_irreducible (ha : Irreducible a) (hb : b != 0) : a ∣ ra
dical b ↔ a ∣ b
参数：ha : Irreducible a；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `UniqueFactorizationMonoid.radical_dvd_self`：radical_dvd_self : radical a
 ∣ a
· 使用定理 `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd`：exists_me
m_normalizedFactors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a
 -> exists q in normalizedFactors a, p ~ᵤ q
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i

--- 原说明 ---
An irreducible `a` divides the radical of `b` if and only if it divides `b` itse
lf.
Note this generalises to radical elements `a`, see `UniqueFactorizationMonoid.dv
d_radical_iff`.
-/
lemma dvd_radical_iff_of_irreducible (ha : Irreducible a) (hb : b ≠ 0) :
    a ∣ radical b ↔ a ∣ b := by
  constructor
  · intro ha
    exact ha.trans radical_dvd_self
  · intro ha'
    obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd hb ha ha'
    exact hc'.dvd.trans (Finset.dvd_prod_of_mem _ (by simpa [mem_primeFactors] using hc))
/-
**UniqueFactorizationMonoid.isRadical_radical** 是 Mathlib 中的一个引理，位于命名空间 `UniqueF
actorizationMonoid`。
形式化陈述：isRadical_radical : IsRadical (radical a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical.eq_1`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M]   (a : M), UniqueFact…
· 使用定理 `Finset.prod_dvd_of_isRelPrime`：Finset.prod_dvd_of_isRelPrime : (t : Set 
I).Pairwise (IsRelPrime on s) -> (forall i in t, s i ∣ z) -> (∏ x in t, s x) ∣ z
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `instIsGCDMonoidOfUniqueFactorizationMonoid`：∀ (α : Type u_2) [inst : Com
mMonoidWithZero α] [UniqueFactorizationMonoid α], IsGCDMonoid α
· 使用引理 `UniqueFactorizationMonoid.pairwise_primeFactors_isRelPrime`：pairwise_pri
meFactors_isRelPrime : Set.Pairwise (primeFactors a : Set M) IsRelPrime
· 使用引理 `UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible`：dvd_radical_if
f_of_irreducible (ha : Irreducible a) (hb : b != 0) : a ∣ radical b ↔ a ∣ b
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `Prime.isRadical`：Prime.isRadical [CommMonoidWithZero R] {y : R} (hy : Pr
ime y) : IsRadical y
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
-/
lemma isRadical_radical : IsRadical (radical a) := by
  intro n p ha
  rw [radical]
  apply Finset.prod_dvd_of_isRelPrime
  · exact pairwise_primeFactors_isRelPrime
  intro i hi
  simp only [mem_primeFactors] at hi
  have : i ∣ radical a := by
    rw [dvd_radical_iff_of_irreducible]
    · exact dvd_of_mem_normalizedFactors hi
    · exact irreducible_of_normalized_factor i hi
    · rintro rfl
      simp only [normalizedFactors_zero, Multiset.notMem_zero] at hi
  exact (prime_of_normalized_factor i hi).isRadical n p (this.trans ha)
/-
**UniqueFactorizationMonoid.squarefree_radical** 是 Mathlib 中的一个引理，位于命名空间 `Unique
FactorizationMonoid`。
形式化陈述：squarefree_radical : Squarefree (radical a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IsRadical.squarefree`：IsRadical.squarefree (h0 : x != 0) (h : IsRadical 
x) : Squarefree x
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `UniqueFactorizationMonoid.isRadical_radical`：isRadical_radical : IsRadic
al (radical a)
-/
lemma squarefree_radical : Squarefree (radical a) := by
  nontriviality M
  exact isRadical_radical.squarefree (by simp [radical_ne_zero])
/-
**UniqueFactorizationMonoid.primeFactors_radical** 是 Mathlib 中的一个定理，位于命名空间 `Uniq
ueFactorizationMonoid`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [inst_1 : NormalizationMono
id M] [inst_2 : UniqueFactorizationMonoid M]   {a : M},   UniqueFactorizationMon
oid.primeFactors (UniqueFactorizationMonoid.radical a) =     UniqueFactorization
Monoid.primeFactors a
参数：UniqueFactorizationMonoid.radical a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors.congr_simp`：∀ {α : Type u_1}
 [inst : CommMonoidWithZero α] [inst_1 : NormalizationMonoid α] [inst_2 : Unique
FactorizationMonoid α]   (a a_1 : α), a = a_…
· 使用定理 `UniqueFactorizationMonoid.radical_zero`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M],   UniqueFactorizatio…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_one`：normalizedFactors_one :
 normalizedFactors (1 : α) = 0
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma primeFactors_radical : primeFactors (radical a) = primeFactors a := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [primeFactors]
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  ext p
  simp +contextual [mem_primeFactors, mem_normalizedFactors_iff',
    dvd_radical_iff_of_irreducible, ha₀]
/-
**UniqueFactorizationMonoid.radical_eq_iff_primeFactors_eq** 是 Mathlib 中的一个引理，位于
命名空间 `UniqueFactorizationMonoid`。
形式化陈述：radical_eq_iff_primeFactors_eq : radical a = radical b ↔ primeFactors a = 
primeFactors b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.primeFactors_radical`：∀ {M : Type u_1} [inst :
 CommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactoriz
ationMonoid M]   {a : M},   UniqueFa…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma radical_eq_iff_primeFactors_eq :
    radical a = radical b ↔ primeFactors a = primeFactors b :=
  ⟨fun h => by rw [← primeFactors_radical, h]; exact primeFactors_radical,
    fun h => by simp [radical, h]⟩
/-
**UniqueFactorizationMonoid.radical_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Unique
FactorizationMonoid`。
形式化陈述：radical_eq_one_iff : radical a = 1 ↔ a = 0 ∨ IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.primeFactors_radical`：∀ {M : Type u_1} [inst :
 CommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactoriz
ationMonoid M]   {a : M},   UniqueFa…
· 使用定理 `UniqueFactorizationMonoid.primeFactors_one`：∀ {M : Type u_1} [inst : Com
mMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizatio
nMonoid M],   UniqueFactorizatio…
· 使用定理 `UniqueFactorizationMonoid.primeFactors_eq_empty_iff`：primeFactors_eq_emp
ty_iff (ha : a != 0) : primeFactors a = ∅ ↔ IsUnit a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UniqueFactorizationMonoid.radical.congr_simp`：∀ {M : Type u_1} [inst : C
ommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizat
ionMonoid M]   (a a_1 : M), a = a_…
· 使用定理 `UniqueFactorizationMonoid.radical_zero`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M],   UniqueFactorizatio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `UniqueFactorizationMonoid.radical_of_isUnit`：radical_of_isUnit (h : IsUn
it a) : radical a = 1
-/
theorem radical_eq_one_iff : radical a = 1 ↔ a = 0 ∨ IsUnit a := by
  refine ⟨?_, (Or.elim · (by simp +contextual) radical_of_isUnit)⟩
  intro h
  rw [or_iff_not_imp_left]
  intro ha
  have : primeFactors a = ∅ := by rw [← primeFactors_radical, h, primeFactors_one]
  rwa [primeFactors_eq_empty_iff ha] at this

@[simp]
/-
**UniqueFactorizationMonoid.radical_radical** 是 Mathlib 中的一个引理，位于命名空间 `UniqueFac
torizationMonoid`。
形式化陈述：radical_radical : radical (radical a) = radical a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `UniqueFactorizationMonoid.radical_eq_iff_primeFactors_eq`：radical_eq_iff
_primeFactors_eq : radical a = radical b ↔ primeFactors a = primeFactors b
· 使用定理 `UniqueFactorizationMonoid.primeFactors_radical`：∀ {M : Type u_1} [inst :
 CommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactoriz
ationMonoid M]   {a : M},   UniqueFa…
-/
lemma radical_radical : radical (radical a) = radical a :=
  radical_eq_iff_primeFactors_eq.mpr primeFactors_radical
/-
**UniqueFactorizationMonoid.radical_dvd_radical_iff_normalizedFactors_subset_nor
malizedFactors** 是 Mathlib 中的一个引理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors : radic
al a ∣ radical b ↔ normalizedFactors a subseteq normalizedFactors b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UniqueFactorizationMonoid.radical_zero`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M],   UniqueFactorizatio…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
`：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y
 != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y
· 使用定理 `UniqueFactorizationMonoid.radical_ne_zero`：∀ {M : Type u_1} [inst : Comm
MonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorization
Monoid M]   {a : M} [Nontrivial…
· 使用定理 `Multiset.le_iff_subset`：le_iff_subset {s t : Multiset α} : Nodup s -> (s
 <= t ↔ s subseteq t)
· 使用引理 `UniqueFactorizationMonoid.normalizedFactors_nodup`：normalizedFactors_nod
up (ha : IsRadical a) : (normalizedFactors a).Nodup
· 使用引理 `UniqueFactorizationMonoid.isRadical_radical`：isRadical_radical : IsRadic
al (radical a)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `UniqueFactorizationMonoid.primeFactors_radical`：∀ {M : Type u_1} [inst :
 CommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactoriz
ationMonoid M]   {a : M},   UniqueFa…
-/
lemma radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors :
    radical a ∣ radical b ↔ normalizedFactors a ⊆ normalizedFactors b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  rw [dvd_iff_normalizedFactors_le_normalizedFactors radical_ne_zero radical_ne_zero,
    Multiset.le_iff_subset (normalizedFactors_nodup isRadical_radical)]
  simp only [Multiset.subset_iff, ← mem_primeFactors, primeFactors_radical]
/-
**UniqueFactorizationMonoid.radical_dvd_radical_iff_primeFactors_subset_primeFac
tors** 是 Mathlib 中的一个引理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：radical_dvd_radical_iff_primeFactors_subset_primeFactors : radical a ∣ rad
ical b ↔ primeFactors a subseteq primeFactors b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UniqueFactorizationMonoid.radical_dvd_radical_iff_normalizedFactors_subs
et_normalizedFactors`：radical_dvd_radical_iff_normalizedFactors_subset_normalize
dFactors : radical a ∣ radical b ↔ normalizedFactors a subseteq normalizedFactor
s …
· 使用定理 `UniqueFactorizationMonoid.primeFactors.eq_1`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M]   (a : M), UniqueFact…
· 使用定理 `Multiset.toFinset_subset`：toFinset_subset : s.toFinset subseteq t.toFins
et ↔ s subseteq t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma radical_dvd_radical_iff_primeFactors_subset_primeFactors :
    radical a ∣ radical b ↔ primeFactors a ⊆ primeFactors b := by
  classical
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors, primeFactors,
    primeFactors, Multiset.toFinset_subset]

/-- If `a` divides `b`, then the radical of `a` divides the radical of `b`. The theorem requires
that `b ≠ 0`, since `radical 0 = 1` but `a ∣ 0` holds for every `a`. -/
/-
**UniqueFactorizationMonoid.radical_dvd_radical** 是 Mathlib 中的一个引理，位于命名空间 `Uniqu
eFactorizationMonoid`。
形式化陈述：radical_dvd_radical (h : a ∣ b) (hb₀ : b != 0) : radical a ∣ radical b
参数：h : a ∣ b；hb₀ : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical_zero`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M],   UniqueFactorizatio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `UniqueFactorizationMonoid.radical_dvd_radical_iff_normalizedFactors_subs
et_normalizedFactors`：radical_dvd_radical_iff_normalizedFactors_subset_normalize
dFactors : radical a ∣ radical b ↔ normalizedFactors a subseteq normalizedFactor
s …
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
`：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y
 != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y

--- 原说明 ---
If `a` divides `b`, then the radical of `a` divides the radical of `b`. The theo
rem requires
that `b ≠ 0`, since `radical 0 = 1` but `a ∣ 0` holds for every `a`.
-/
lemma radical_dvd_radical (h : a ∣ b) (hb₀ : b ≠ 0) : radical a ∣ radical b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha₀ hb₀] at h
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors]
  exact Multiset.subset_of_le h

/--
If `a` is a radical element, then `a` divides the radical of `b` if and only if it divides `b`.
Note the forward implication holds without the `b ≠ 0` assumption via `radical_dvd_self`.
-/
/-
**UniqueFactorizationMonoid.dvd_radical_iff** 是 Mathlib 中的一个引理，位于命名空间 `UniqueFac
torizationMonoid`。
形式化陈述：dvd_radical_iff (ha : IsRadical a) (hb₀ : b != 0) : a ∣ radical b ↔ a ∣ b
参数：ha : IsRadical a；hb₀ : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `UniqueFactorizationMonoid.radical_dvd_self`：radical_dvd_self : radical a
 ∣ a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsRadical.dvd_radical`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [i
nst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMonoid M]   {a : M},
 IsRadical …
· 使用引理 `UniqueFactorizationMonoid.radical_dvd_radical`：radical_dvd_radical (h : 
a ∣ b) (hb₀ : b != 0) : radical a ∣ radical b

--- 原说明 ---
If `a` is a radical element, then `a` divides the radical of `b` if and only if 
it divides `b`.
Note the forward implication holds without the `b ≠ 0` assumption via `radical_d
vd_self`.
-/
lemma dvd_radical_iff (ha : IsRadical a) (hb₀ : b ≠ 0) : a ∣ radical b ↔ a ∣ b := by
  refine ⟨fun ha' ↦ ha'.trans radical_dvd_self, fun hab ↦ ?_⟩
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  · exact (ha.dvd_radical ha₀).trans (radical_dvd_radical hab hb₀)
/-
**UniqueFactorizationMonoid.radical_dvd_iff_primeFactors_subset** 是 Mathlib 中的一个
定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：radical_dvd_iff_primeFactors_subset (hb : b != 0) : radical a ∣ b ↔ primeF
actors a subseteq primeFactors b
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `UniqueFactorizationMonoid.dvd_radical_iff`：dvd_radical_iff (ha : IsRadic
al a) (hb₀ : b != 0) : a ∣ radical b ↔ a ∣ b
· 使用引理 `UniqueFactorizationMonoid.isRadical_radical`：isRadical_radical : IsRadic
al (radical a)
· 使用引理 `UniqueFactorizationMonoid.radical_dvd_radical_iff_primeFactors_subset_pr
imeFactors`：radical_dvd_radical_iff_primeFactors_subset_primeFactors : radical a
 ∣ radical b ↔ primeFactors a subseteq primeFactors b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem radical_dvd_iff_primeFactors_subset (hb : b ≠ 0) :
    radical a ∣ b ↔ primeFactors a ⊆ primeFactors b := by
  rw [← dvd_radical_iff isRadical_radical hb,
    radical_dvd_radical_iff_primeFactors_subset_primeFactors]
/-
**UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd** 是 Mathlib 中的一个定理，位于
命名空间 `UniqueFactorizationMonoid`。
形式化陈述：exists_dvd_pow_iff_radical_dvd (ha : a != 0) : (exists n, a ∣ b ^ n) ↔ rad
ical a ∣ b
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UniqueFactorizationMonoid.radical_of_isUnit`：radical_of_isUnit (h : IsUn
it a) : radical a = 1
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransDvd`：∀ {α : Type u_1} [inst : Semigroup α], IsTrans α Dvd.dvd
· 使用引理 `UniqueFactorizationMonoid.radical_dvd_radical`：radical_dvd_radical (h : 
a ∣ b) (hb₀ : b != 0) : radical a ∣ radical b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `UniqueFactorizationMonoid.radical_pow`：radical_pow (a : M) {n : Nat} (hn
 : n != 0) : radical (a ^ n) = radical a
· 使用定理 `UniqueFactorizationMonoid.radical_dvd_self`：radical_dvd_self : radical a
 ∣ a
· 使用定理 `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
`：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y
 != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_pow`：normalizedFactors_pow {
x : α} (n : Nat) : normalizedFactors (x ^ n) = n • normalizedFactors x
· 使用定理 `Multiset.le_card_smul_iff_subset`：le_card_smul_iff_subset {s t : Multise
t α} : s <= s.card • t ↔ s subseteq t
· 使用定理 `Multiset.toFinset_subset`：toFinset_subset : s.toFinset subseteq t.toFins
et ↔ s subseteq t
· 使用定理 `UniqueFactorizationMonoid.toFinset_normalizedFactors`：toFinset_normalize
dFactors [DecidableEq M] : (normalizedFactors a).toFinset = primeFactors a
· 使用定理 `UniqueFactorizationMonoid.radical_dvd_iff_primeFactors_subset`：radical_d
vd_iff_primeFactors_subset (hb : b != 0) : radical a ∣ b ↔ primeFactors a subset
eq primeFactors b
-/
theorem exists_dvd_pow_iff_radical_dvd (ha : a ≠ 0) : (∃ n, a ∣ b ^ n) ↔ radical a ∣ b := by
  rcases eq_or_ne b 0 with (rfl | hb)
  · exact ⟨by simp, fun _ ↦ ⟨1, by simp⟩⟩
  refine ⟨fun ⟨n, hdvd⟩ ↦ ?_, fun h ↦ ⟨normalizedFactors a |>.card, ?_⟩⟩
  · rcases eq_or_ne n 0 with (rfl | hn)
    · simp [radical_of_isUnit <| isUnit_of_dvd_one <| pow_zero b ▸ hdvd]
    grw [radical_dvd_radical hdvd <| pow_ne_zero _ hb, radical_pow b hn, radical_dvd_self]
  · classical
    rwa [dvd_iff_normalizedFactors_le_normalizedFactors ha <| pow_ne_zero _ hb,
      normalizedFactors_pow, Multiset.le_card_smul_iff_subset, ← Multiset.toFinset_subset,
      toFinset_normalizedFactors, toFinset_normalizedFactors,
      ← radical_dvd_iff_primeFactors_subset hb]
/-
**UniqueFactorizationMonoid.exists_dvd_radical_self_pow** 是 Mathlib 中的一个定理，位于命名空
间 `UniqueFactorizationMonoid`。
形式化陈述：exists_dvd_radical_self_pow (ha : a != 0) : exists n, a ∣ radical a ^ n
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd`：exists_dvd_pow
_iff_radical_dvd (ha : a != 0) : (exists n, a ∣ b ^ n) ↔ radical a ∣ b
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem exists_dvd_radical_self_pow (ha : a ≠ 0) : ∃ n, a ∣ radical a ^ n := by
  rw [exists_dvd_pow_iff_radical_dvd ha]

/-- Radical is multiplicative for relatively prime elements. -/
/-
**UniqueFactorizationMonoid.radical_mul** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactori
zationMonoid`。
形式化陈述：radical_mul (hc : IsRelPrime a b) : radical (a * b) = radical a * radical 
b
参数：hc : IsRelPrime a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.disjoint_primeFactors`：disjoint_primeFactors (
hc : IsRelPrime a b) : Disjoint (primeFactors a) (primeFactors b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.primeFactors_mul_eq_disjUnion`：primeFactors_mu
l_eq_disjUnion (hc : IsRelPrime a b) : primeFactors (a * b) = (primeFactors a).d
isjUnion (primeFactors b) (disjoint_primeFact…
· 使用定理 `Finset.prod_disjUnion`：prod_disjUnion (h) : ∏ x in s₁.disjUnion s₂ h, f 
x = (∏ x in s₁, f x) * ∏ x in s₂, f x

--- 原说明 ---
Radical is multiplicative for relatively prime elements.
-/
theorem radical_mul (hc : IsRelPrime a b) :
    radical (a * b) = radical a * radical b := by
  simp_rw [radical]
  rw [primeFactors_mul_eq_disjUnion hc, Finset.prod_disjUnion (disjoint_primeFactors hc)]
/-
**UniqueFactorizationMonoid.radical_prod** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactor
izationMonoid`。
形式化陈述：radical_prod {ι : Type*} {f : ι -> M} (s : Finset ι) (h : Set.Pairwise (s 
: Set ι) (Function.onFun IsRelPrime f)) : radical (∏ i in s, f i) = ∏ i in s, ra
dical (f i)
参数：s : Finset ι；h : Set.Pairwise (s : Set ι) (Function.onFun IsRelPrime f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical_one`：∀ {M : Type u_1} [inst : CommMono
idWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMono
id M],   UniqueFactorizatio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UniqueFactorizationMonoid.radical.congr_simp`：∀ {M : Type u_1} [inst : C
ommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizat
ionMonoid M]   (a a_1 : M), a = a_…
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `UniqueFactorizationMonoid.radical_mul`：radical_mul (hc : IsRelPrime a b)
 : radical (a * b) = radical a * radical b
· 使用定理 `IsRelPrime.prod_right`：IsRelPrime.prod_right : (forall i in t, IsRelPrim
e x (s i)) -> IsRelPrime x (∏ i in t, s i)
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `instIsGCDMonoidOfUniqueFactorizationMonoid`：∀ (α : Type u_2) [inst : Com
mMonoidWithZero α] [UniqueFactorizationMonoid α], IsGCDMonoid α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.pairwise_insert_of_symm_of_notMem`：pairwise_insert_of_symm_of_notMem
 [Std.Symm r] (ha : a ∉ s) : (insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b i
n s, r a b
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem radical_prod {ι : Type*} {f : ι → M} (s : Finset ι)
    (h : Set.Pairwise (s : Set ι) (Function.onFun IsRelPrime f)) :
    radical (∏ i ∈ s, f i) = ∏ i ∈ s, radical (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ih =>
    simp only [Finset.prod_cons]
    rw [Finset.coe_cons, Set.pairwise_insert_of_symm_of_notMem <| by simpa] at h
    rw [radical_mul, ih h.1]
    exact IsRelPrime.prod_right h.2
/-
**UniqueFactorizationMonoid.radical_mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFac
torizationMonoid`。
形式化陈述：radical_mul_dvd : radical (a * b) ∣ radical a * radical b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical.congr_simp`：∀ {M : Type u_1} [inst : C
ommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizat
ionMonoid M]   (a a_1 : M), a = a_…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `UniqueFactorizationMonoid.radical_zero`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M],   UniqueFactorizatio…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `UniqueFactorizationMonoid.primeFactors_mul_eq_union`：primeFactors_mul_eq
_union [DecidableEq M] (ha : a != 0) (hb : b != 0) : primeFactors (a * b) = prim
eFactors a union primeFactors b
· 使用定理 `UniqueFactorizationMonoid.primeFactors_radical`：∀ {M : Type u_1} [inst :
 CommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactoriz
ationMonoid M]   {a : M},   UniqueFa…
-/
theorem radical_mul_dvd : radical (a * b) ∣ radical a * radical b := by
  classical
  obtain rfl | ha := eq_or_ne a 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  nontriviality M
  simp [radical_dvd_iff_primeFactors_subset, primeFactors_mul_eq_union,
    primeFactors_mul_eq_union ha hb, primeFactors_radical]
/-
**UniqueFactorizationMonoid.radical_prod_dvd** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFa
ctorizationMonoid`。
形式化陈述：radical_prod_dvd {ι : Type*} {s : Finset ι} {f : ι -> M} : radical (∏ i in
 s, f i) ∣ ∏ i in s, radical (f i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical_one`：∀ {M : Type u_1} [inst : CommMono
idWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMono
id M],   UniqueFactorizatio…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UniqueFactorizationMonoid.radical.congr_simp`：∀ {M : Type u_1} [inst : C
ommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizat
ionMonoid M]   (a a_1 : M), a = a_…
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `UniqueFactorizationMonoid.radical_mul_dvd`：radical_mul_dvd : radical (a 
* b) ∣ radical a * radical b
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
-/
theorem radical_prod_dvd {ι : Type*} {s : Finset ι} {f : ι → M} :
    radical (∏ i ∈ s, f i) ∣ ∏ i ∈ s, radical (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s h ih =>
    simp only [Finset.prod_cons]
    exact radical_mul_dvd.trans (mul_dvd_mul_left _ ih)

end UniqueFactorizationMonoid

open UniqueFactorizationMonoid

/-! Theorems for UFDs -/
namespace UniqueFactorizationDomain

variable {R : Type*} [CommRing R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R] {a b : R}

@[simp]
/-
**UniqueFactorizationDomain.radical_neg** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactori
zationDomain`。
形式化陈述：radical_neg : radical (-a) = radical a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.radical_eq_of_associated`：radical_eq_of_associ
ated (h : Associated a b) : radical a = radical b
· 使用引理 `Associated.neg_left`：neg_left (h : Associated a b) : Associated (-a) b
· 使用定理 `Associated.rfl`：∀ {M : Type u_1} [inst : Monoid M] {x : M}, Associated x
 x
-/
theorem radical_neg : radical (-a) = radical a :=
  radical_eq_of_associated Associated.rfl.neg_left
/-
**UniqueFactorizationDomain.radical_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFac
torizationDomain`。
形式化陈述：radical_neg_one : radical (-1 : R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationDomain.radical_neg`：radical_neg : radical (-a) = radi
cal a
· 使用定理 `UniqueFactorizationMonoid.radical_one`：∀ {M : Type u_1} [inst : CommMono
idWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMono
id M],   UniqueFactorizatio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem radical_neg_one : radical (-1 : R) = 1 := by simp

end UniqueFactorizationDomain

open UniqueFactorizationDomain
namespace EuclideanDomain

variable {E : Type*} [EuclideanDomain E] [NormalizationMonoid E] [UniqueFactorizationMonoid E]
  {a b u x : E}

/-- Division of an element by its radical in a Euclidean domain. -/
/-
**EuclideanDomain.divRadical** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanDomain`。
形式化陈述：divRadical (a : E) : E
参数：a : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Division of an element by its radical in a Euclidean domain.
-/
def divRadical (a : E) : E := a / radical a
/-
**EuclideanDomain.radical_mul_divRadical** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDom
ain`。
形式化陈述：radical_mul_divRadical : radical a * divRadical a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.divRadical.eq_1`：∀ {E : Type u_1} [inst : EuclideanDomai
n E] [inst_1 : NormalizationMonoid E] [inst_2 : UniqueFactorizationMonoid E]   (
a : E), EuclideanDoma…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.mul_div_assoc`：mul_div_assoc (x : R) {y z : R} (h : z ∣ 
y) : x * y / z = x * (y / z)
· 使用定理 `UniqueFactorizationMonoid.radical_dvd_self`：radical_dvd_self : radical a
 ∣ a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `UniqueFactorizationMonoid.radical_ne_zero`：∀ {M : Type u_1} [inst : Comm
MonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorization
Monoid M]   {a : M} [Nontrivial…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
theorem radical_mul_divRadical : radical a * divRadical a = a := by
  rw [divRadical, ← EuclideanDomain.mul_div_assoc _ radical_dvd_self,
    mul_div_cancel_left₀ _ radical_ne_zero]
/-
**EuclideanDomain.divRadical_mul_radical** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDom
ain`。
形式化陈述：divRadical_mul_radical : divRadical a * radical a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanDomain.radical_mul_divRadical`：radical_mul_divRadical : radical
 a * divRadical a = a
-/
theorem divRadical_mul_radical : divRadical a * radical a = a := by
  rw [mul_comm]
  exact radical_mul_divRadical
/-
**EuclideanDomain.divRadical_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`
。
形式化陈述：divRadical_ne_zero (ha : a != 0) : divRadical a != 0
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.radical_mul_divRadical`：radical_mul_divRadical : radical
 a * divRadical a = a
-/
theorem divRadical_ne_zero (ha : a ≠ 0) : divRadical a ≠ 0 := by
  rw [← radical_mul_divRadical (a := a)] at ha
  exact right_ne_zero_of_mul ha
/-
**EuclideanDomain.divRadical_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：divRadical_isUnit (hu : IsUnit u) : IsUnit (divRadical u)
参数：hu : IsUnit u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.divRadical.eq_1`：∀ {E : Type u_1} [inst : EuclideanDomai
n E] [inst_1 : NormalizationMonoid E] [inst_2 : UniqueFactorizationMonoid E]   (
a : E), EuclideanDoma…
· 使用定理 `UniqueFactorizationMonoid.radical_of_isUnit`：radical_of_isUnit (h : IsUn
it a) : radical a = 1
· 使用定理 `EuclideanDomain.div_one`：div_one (p : R) : p / 1 = p
-/
theorem divRadical_isUnit (hu : IsUnit u) : IsUnit (divRadical u) := by
  rwa [divRadical, radical_of_isUnit hu, EuclideanDomain.div_one]
/-
**EuclideanDomain.eq_divRadical** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：eq_divRadical (h : radical a * x = a) : x = divRadical a
参数：h : radical a * x = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_left`：eq_div_of_mul_eq_left {a b c : R}
 (hb : b != 0) (h : a * b = c) : a = c / b
· 使用定理 `UniqueFactorizationMonoid.radical_ne_zero`：∀ {M : Type u_1} [inst : Comm
MonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorization
Monoid M]   {a : M} [Nontrivial…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem eq_divRadical (h : radical a * x = a) : x = divRadical a := by
  apply EuclideanDomain.eq_div_of_mul_eq_left radical_ne_zero
  rwa [mul_comm]
/-
**EuclideanDomain.divRadical_mul** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：divRadical_mul (hab : IsCoprime a b) : divRadical (a * b) = divRadical a *
 divRadical b
参数：hab : IsCoprime a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.eq_divRadical`：eq_divRadical (h : radical a * x = a) : x
 = divRadical a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical_mul`：radical_mul (hc : IsRelPrime a b)
 : radical (a * b) = radical a * radical b
· 使用定理 `IsCoprime.isRelPrime`：IsCoprime.isRelPrime {a b : R} (h : IsCoprime a b)
 : IsRelPrime a b
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `EuclideanDomain.radical_mul_divRadical`：radical_mul_divRadical : radical
 a * divRadical a = a
-/
theorem divRadical_mul (hab : IsCoprime a b) :
    divRadical (a * b) = divRadical a * divRadical b := by
  symm; apply eq_divRadical
  rw [UniqueFactorizationMonoid.radical_mul hab.isRelPrime]
  rw [mul_mul_mul_comm, radical_mul_divRadical, radical_mul_divRadical]
/-
**EuclideanDomain.divRadical_dvd_self** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain
`。
形式化陈述：divRadical_dvd_self (a : E) : divRadical a ∣ a
参数：a : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.divRadical_mul_radical`：divRadical_mul_radical : divRadi
cal a * radical a = a
-/
theorem divRadical_dvd_self (a : E) : divRadical a ∣ a :=
  ⟨radical a, divRadical_mul_radical.symm⟩
/-
**EuclideanDomain._root_.IsCoprime.divRadical** 是 Mathlib 中的一个定理，位于命名空间 `Euclide
anDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsCoprime.divRadical {a b : E} (h : IsCoprime a b) :
    IsCoprime (divRadical a) (divRadical b) := by
  rw [← radical_mul_divRadical (a := a)] at h
  rw [← radical_mul_divRadical (a := b)] at h
  exact h.of_mul_left_right.of_mul_right_right

end EuclideanDomain

