/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
module

public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Basic lemmas on prime factorizations
-/

public section

open Finset List Finsupp

namespace Nat
variable {a b m n p : ℕ}

/-! ### Basic facts about factorization -/

/-! ## Lemmas characterising when `n.factorization p = 0` -/


/-
**Nat.factorization_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_zero_of_lt {n p : Nat} (h : n < p) : n.factorization p = 
0
参数：h : n < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `Nat.le_of_mem_primeFactors`：le_of_mem_primeFactors (h : p in n.primeFact
ors) : p <= n
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a

--- 原说明 ---
## Lemmas characterising when `n.factorization p = 0`
-/
theorem factorization_eq_zero_of_lt {n p : ℕ} (h : n < p) : n.factorization p = 0 :=
  Finsupp.notMem_support_iff.mp (mt le_of_mem_primeFactors (not_le_of_gt h))
/-
**Nat.dvd_of_factorization_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_of_factorization_pos {n p : Nat} (hn : n.factorization p != 0) : p ∣ n
参数：hn : n.factorization p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_of_mem_primeFactorsList`：dvd_of_mem_primeFactorsList {n p : Nat}
 (h : p in n.primeFactorsList) : p ∣ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.mem_primeFactors_iff_mem_primeFactorsList`：mem_primeFactors_iff_mem_
primeFactorsList : p in n.primeFactors ↔ p in n.primeFactorsList
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
-/
theorem dvd_of_factorization_pos {n p : ℕ} (hn : n.factorization p ≠ 0) : p ∣ n :=
  dvd_of_mem_primeFactorsList <| mem_primeFactors_iff_mem_primeFactorsList.1 <| mem_support_iff.2 hn
/-
**Nat.factorization_eq_zero_iff_remainder** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_zero_iff_remainder {p r : Nat} (i : Nat) (pp : p.Prime) (
hr0 : r != 0) : ¬p ∣ r ↔ (p * i + r).factorization p = 0
参数：i : Nat；pp : p.Prime；hr0 : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorization_eq_zero_of_remainder`：factorization_eq_zero_of_remaind
er {p r : Nat} (i : Nat) (hr : ¬p ∣ r) : (p * i + r).factorization p = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_add_iff_right`：∀ {k m n : ℕ}, k ∣ m → (k ∣ n ↔ k ∣ m + n)
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.factorization_eq_zero_iff`：factorization_eq_zero_iff (n p : Nat) : n
.factorization p = 0 ↔ ¬p.Prime ∨ ¬p ∣ n ∨ n = 0
-/
theorem factorization_eq_zero_iff_remainder {p r : ℕ} (i : ℕ) (pp : p.Prime) (hr0 : r ≠ 0) :
    ¬p ∣ r ↔ (p * i + r).factorization p = 0 := by
  refine ⟨factorization_eq_zero_of_remainder i, fun h => ?_⟩
  rw [factorization_eq_zero_iff] at h
  contrapose! h
  refine ⟨pp, ?_, ?_⟩
  · rwa [← Nat.dvd_add_iff_right (dvd_mul_right p i)]
  · contrapose hr0
    exact (add_eq_zero.1 hr0).2

/-- The only numbers with empty prime factorization are `0` and `1` -/
/-
**Nat.factorization_eq_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_zero_iff' (n : Nat) : n.factorization = 0 ↔ n = 0 ∨ n = 1
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_eq_primeFactorsList_multiset`：factorization_eq_primeFa
ctorsList_multiset (n : Nat) : n.factorization = Multiset.toFinsupp (n.primeFact
orsList : Multiset Nat)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The only numbers with empty prime factorization are `0` and `1`
-/
theorem factorization_eq_zero_iff' (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 := by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp [Multiset.coe_eq_zero]

/-! ## Lemmas about factorizations of products and powers -/

/-- Modified version of `factorization_prod` that accounts for inputs. -/
/-
**Nat.factorization_prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_prod_apply {α : Type*} {p : Nat} {S : Finset α} {g : α -> Na
t} (hS : forall x in S, g x != 0) : (S.prod g).factorization p = S.sum fun x => 
(g x).factorization p
参数：hS : forall x in S, g x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_prod`：factorization_prod {α : Type*} {S : Finset α} {g
 : α -> Nat} (hS : forall x in S, g x != 0) : (S.prod g).factorization = S.sum f
un x => (g x…
· 使用定理 `Finsupp.finsetSum_apply`：finsetSum_apply [AddCommMonoid N] (S : Finset ι
) (f : ι -> α ->₀ N) (a : α) : (∑ i in S, f i) a = ∑ i in S, f i a

--- 原说明 ---
Modified version of `factorization_prod` that accounts for inputs.
-/
theorem factorization_prod_apply {α : Type*} {p : ℕ}
    {S : Finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) :
    (S.prod g).factorization p = S.sum fun x => (g x).factorization p := by
  rw [factorization_prod hS, finsetSum_apply]

/-- A product over `n.factorization` can be written as a product over `n.primeFactors`; -/
/-
**Nat.prod_factorization_eq_prod_primeFactors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prod_factorization_eq_prod_primeFactors {β : Type*} [CommMonoid β] (f : Na
t -> Nat -> β) : n.factorization.prod f = ∏ p in n.primeFactors, f p (n.factoriz
ation p)
参数：f : Nat -> Nat -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product over `n.factorization` can be written as a product over `n.primeFactor
s`;
-/
lemma prod_factorization_eq_prod_primeFactors {β : Type*} [CommMonoid β] (f : ℕ → ℕ → β) :
    n.factorization.prod f = ∏ p ∈ n.primeFactors, f p (n.factorization p) := rfl

/-- A product over `n.primeFactors` can be written as a product over `n.factorization`; -/
/-
**Nat.prod_primeFactors_prod_factorization** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prod_primeFactors_prod_factorization {β : Type*} [CommMonoid β] (f : Nat -
> β) : ∏ p in n.primeFactors, f p = n.factorization.prod (fun p _ => f p)
参数：f : Nat -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product over `n.primeFactors` can be written as a product over `n.factorizatio
n`;
-/
lemma prod_primeFactors_prod_factorization {β : Type*} [CommMonoid β] (f : ℕ → β) :
    ∏ p ∈ n.primeFactors, f p = n.factorization.prod (fun p _ ↦ f p) := rfl

/-! ## Lemmas about factorizations of primes and prime powers -/

/-- The multiplicity of prime `p` in `p` is `1` -/
/-
**Nat.Prime.factorization_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p.factorization p = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.factorization`：∀ {p : ℕ}, Nat.Prime p → p.factorization = fun₀
 | p => 1
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The multiplicity of prime `p` in `p` is `1`
-/
theorem Prime.factorization_self {p : ℕ} (hp : Prime p) : p.factorization p = 1 := by simp [hp]
/-
**Nat.factorization_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_pow_self {p n : Nat} (hp : p.Prime) : (p ^ n).factorization 
p = n
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_pow`：factorization_pow (n k : Nat) : factorization (n 
^ k) = k • n.factorization
· 使用定理 `Nat.Prime.factorization_self`：∀ {p : ℕ}, Nat.Prime p → p.factorization p
 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorization_pow_self {p n : ℕ} (hp : p.Prime) : (p ^ n).factorization p = n := by
  simp [factorization_pow, Prime.factorization_self hp]

/-- If the factorization of `n` contains just one number `p` then `n` is a power of `p` -/
/-
**Nat.eq_pow_of_factorization_eq_single** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_pow_of_factorization_eq_single {n p k : Nat} (hn : n != 0) (h : n.facto
rization = Finsupp.single p k) : n = p ^ k
参数：hn : n != 0；h : n.factorization = Finsupp.single p k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the factorization of `n` contains just one number `p` then `n` is a power of 
`p`
-/
theorem eq_pow_of_factorization_eq_single {n p k : ℕ} (hn : n ≠ 0)
    (h : n.factorization = Finsupp.single p k) : n = p ^ k := by
  rw [← Nat.prod_factorization_pow_eq_self hn, h]
  simp

/-- The only prime factor of prime `p` is `p` itself. -/
/-
**Nat.Prime.eq_of_factorization_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p q : ℕ}, Nat.Prime p → p.factorization q ≠ 0 → p = q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.factorization`：∀ {p : ℕ}, Nat.Prime p → p.factorization = fun₀
 | p => 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
The only prime factor of prime `p` is `p` itself.
-/
theorem Prime.eq_of_factorization_pos {p q : ℕ} (hp : Prime p) (h : p.factorization q ≠ 0) :
    p = q := by simpa [hp.factorization, single_apply] using h

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/


@[deprecated factorizationEquiv_symm_apply_coe (since := "2026-03-18")]
/-
**Nat.factorizationEquiv_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorizationEquiv_inv_apply {f : Nat ->₀ Nat} (hf : forall p in f.support
, Prime p) : (factorizationEquiv.symm ⟨f, hf⟩).1 = f.prod (· ^ ·)
参数：hf : forall p in f.support, Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorizationEquiv_symm_apply_coe`：∀ (x : { f // ∀ p ∈ f.support, Na
t.Prime p }), ↑(Nat.factorizationEquiv.symm x) = (↑x).prod fun x1 x2 => x1 ^ x2

--- 原说明 ---
### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes.
-/
theorem factorizationEquiv_inv_apply {f : ℕ →₀ ℕ} (hf : ∀ p ∈ f.support, Prime p) :
    (factorizationEquiv.symm ⟨f, hf⟩).1 = f.prod (· ^ ·) :=
  factorizationEquiv_symm_apply_coe ⟨f, hf⟩
/-
**Nat.ordProj_of_not_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordProj_of_not_prime (n p : Nat) (hp : ¬p.Prime) : ordProj[p] n = 1
参数：n p : Nat；hp : ¬p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordProj_of_not_prime (n p : ℕ) (hp : ¬p.Prime) : ordProj[p] n = 1 := by
  simp [hp]
/-
**Nat.ordCompl_of_not_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_of_not_prime (n p : Nat) (hp : ¬p.Prime) : ordCompl[p] n = n
参数：n p : Nat；hp : ¬p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordCompl_of_not_prime (n p : ℕ) (hp : ¬p.Prime) : ordCompl[p] n = n := by
  simp [hp]
/-
**Nat.ordCompl_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_dvd (n p : Nat) : ordCompl[p] n ∣ n
参数：n p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_dvd_of_dvd`：∀ {n m : ℕ}, n ∣ m → m / n ∣ m
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
-/
theorem ordCompl_dvd (n p : ℕ) : ordCompl[p] n ∣ n :=
  div_dvd_of_dvd (ordProj_dvd n p)
/-
**Nat.ordProj_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordProj_pos (n p : Nat) : 0 < ordProj[p] n
参数：n p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordProj_pos (n p : ℕ) : 0 < ordProj[p] n := by
  if pp : p.Prime then simp [Nat.pow_pos pp.pos] else simp [pp]
/-
**Nat.ordProj_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordProj_le {n : Nat} (p : Nat) (hn : n != 0) : ordProj[p] n <= n
参数：p : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
-/
theorem ordProj_le {n : ℕ} (p : ℕ) (hn : n ≠ 0) : ordProj[p] n ≤ n :=
  le_of_dvd hn.bot_lt (Nat.ordProj_dvd n p)
/-
**Nat.ordCompl_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_pos {n : Nat} (p : Nat) (hn : n != 0) : 0 < ordCompl[p] n
参数：p : Nat；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Nat.ordProj_le`：ordProj_le {n : Nat} (p : Nat) (hn : n != 0) : ordProj[p
] n <= n
· 使用定理 `Nat.ordProj_pos`：ordProj_pos (n p : Nat) : 0 < ordProj[p] n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem ordCompl_pos {n : ℕ} (p : ℕ) (hn : n ≠ 0) : 0 < ordCompl[p] n := by
  if pp : p.Prime then
    exact Nat.div_pos (ordProj_le p hn) (ordProj_pos n p)
  else
    simpa [Nat.factorization_eq_zero_of_not_prime n pp] using hn.bot_lt
/-
**Nat.ordCompl_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_le (n p : Nat) : ordCompl[p] n <= n
参数：n p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_le_self`：∀ (n k : ℕ), n / k ≤ n
-/
theorem ordCompl_le (n p : ℕ) : ordCompl[p] n ≤ n :=
  Nat.div_le_self _ _
/-
**Nat.ordProj_mul_ordCompl_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordProj_mul_ordCompl_eq_self (n p : Nat) : ordProj[p] n * ordCompl[p] n = 
n
参数：n p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
-/
theorem ordProj_mul_ordCompl_eq_self (n p : ℕ) : ordProj[p] n * ordCompl[p] n = n :=
  Nat.mul_div_cancel' (ordProj_dvd n p)
/-
**Nat.ordProj_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordProj_mul {a b : Nat} (p : Nat) (ha : a != 0) (hb : b != 0) : ordProj[p]
 (a * b) = ordProj[p] a * ordProj[p] b
参数：p : Nat；ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordProj_mul {a b : ℕ} (p : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ordProj[p] (a * b) = ordProj[p] a * ordProj[p] b := by
  simp [factorization_mul ha hb, pow_add]
/-
**Nat.ordCompl_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_mul (a b p : Nat) : ordCompl[p] (a * b) = ordCompl[p] a * ordComp
l[p] b
参数：a b p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.ordProj_mul`：ordProj_mul {a b : Nat} (p : Nat) (ha : a != 0) (hb : b
 != 0) : ordProj[p] (a * b) = ordProj[p] a * ordProj[p] b
· 使用定理 `Nat.div_mul_div_comm`：∀ {a b c d : ℕ}, b ∣ a → d ∣ c → a / b * (c / d) =
 a * c / (b * d)
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
-/
theorem ordCompl_mul (a b p : ℕ) : ordCompl[p] (a * b) = ordCompl[p] a * ordCompl[p] b := by
  if ha : a = 0 then simp [ha] else
  if hb : b = 0 then simp [hb] else
  simp only [ordProj_mul p ha hb]
  rw [div_mul_div_comm (ordProj_dvd a p) (ordProj_dvd b p)]

/-! ### Factorization and divisibility -/

/-- A crude upper bound on `n.factorization p` -/
/-
**Nat.factorization_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_lt {n : Nat} (p : Nat) (hn : n != 0) : n.factorization p < n
参数：p : Nat；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pow_lt_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n < a ^ m ↔ n < m)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.ordProj_le`：ordProj_le {n : Nat} (p : Nat) (hn : n != 0) : ordProj[p
] n <= n
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a

--- 原说明 ---
A crude upper bound on `n.factorization p`
-/
theorem factorization_lt {n : ℕ} (p : ℕ) (hn : n ≠ 0) : n.factorization p < n := by
  by_cases pp : p.Prime
  · exact (Nat.pow_lt_pow_iff_right pp.one_lt).1 <| (ordProj_le p hn).trans_lt <|
      Nat.lt_pow_self pp.one_lt
  · simpa only [factorization_eq_zero_of_not_prime n pp] using! hn.bot_lt

/-- An upper bound on `n.factorization p` -/
/-
**Nat.factorization_le_of_le_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_le_of_le_pow {n p b : Nat} (hb : n <= p ^ b) : n.factorizati
on p <= b
参数：hb : n <= p ^ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pow_le_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n ≤ a ^ m ↔ n ≤ m)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.ordProj_le`：ordProj_le {n : Nat} (p : Nat) (hn : n != 0) : ordProj[p
] n <= n
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0

--- 原说明 ---
An upper bound on `n.factorization p`
-/
theorem factorization_le_of_le_pow {n p b : ℕ} (hb : n ≤ p ^ b) : n.factorization p ≤ b := by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then
    exact (Nat.pow_le_pow_iff_right pp.one_lt).1 ((ordProj_le p hn).trans hb)
  else
    simp [factorization_eq_zero_of_not_prime n pp]
/-
**Nat.factorization_prime_le_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_prime_le_iff_dvd {d n : Nat} (hd : d != 0) (hn : n != 0) : (
forall p : Nat, p.Prime -> d.factorization p <= n.factorization p) ↔ d ∣ n
参数：hd : d != 0；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem factorization_prime_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    (∀ p : ℕ, p.Prime → d.factorization p ≤ n.factorization p) ↔ d ∣ n := by
  rw [← factorization_le_iff_dvd hd hn]
  refine ⟨fun h p => (em p.Prime).elim (h p) fun hp => ?_, fun h p _ => h p⟩
  simp_rw [factorization_eq_zero_of_not_prime _ hp]
  rfl
/-
**Nat.factorization_le_factorization_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_le_factorization_mul_left {a b : Nat} (hb : b != 0) : a.fact
orization <= (a * b).factorization
参数：hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
-/
theorem factorization_le_factorization_mul_left {a b : ℕ} (hb : b ≠ 0) :
    a.factorization ≤ (a * b).factorization := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  rw [factorization_le_iff_dvd ha <| mul_ne_zero ha hb]
  exact Dvd.intro b rfl
/-
**Nat.factorization_le_factorization_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_le_factorization_mul_right {a b : Nat} (ha : a != 0) : b.fac
torization <= (a * b).factorization
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.factorization_le_factorization_mul_left`：factorization_le_factorizat
ion_mul_left {a b : Nat} (hb : b != 0) : a.factorization <= (a * b).factorizatio
n
-/
theorem factorization_le_factorization_mul_right {a b : ℕ} (ha : a ≠ 0) :
    b.factorization ≤ (a * b).factorization := by
  rw [mul_comm]
  apply factorization_le_factorization_mul_left ha
/-
**Nat.Prime.pow_dvd_iff_le_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p k n : ℕ}, Nat.Prime p → n ≠ 0 → (p ^ k ∣ n ↔ k ≤ n.factorization p)
参数：p ^ k ∣ n ↔ k ≤ n.factorization p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Nat.Prime.factorization_pow`：∀ {p k : ℕ}, Nat.Prime p → (p ^ k).factoriz
ation = fun₀ | p => k
· 使用定理 `Finsupp.single_le_iff`：single_le_iff {i : ι} {x : α} {f : ι ->₀ α} : sin
gle i x <= f ↔ x <= f i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Prime.pow_dvd_iff_le_factorization {p k n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ n.factorization p := by
  rw [← factorization_le_iff_dvd (Nat.pow_pos pp.pos).ne' hn, pp.factorization_pow, single_le_iff]
/-
**Nat.Prime.pow_dvd_iff_dvd_ordProj** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p k n : ℕ}, Nat.Prime p → n ≠ 0 → (p ^ k ∣ n ↔ p ^ k ∣ p ^ n.factorizat
ion p)
参数：p ^ k ∣ n ↔ p ^ k ∣ p ^ n.factorization p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_dvd_pow_iff_le_right`：∀ {x k l : ℕ}, 1 < x → (x ^ k ∣ x ^ l ↔ k 
≤ l)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Nat.Prime.pow_dvd_iff_le_factorization`：∀ {p k n : ℕ}, Nat.Prime p → n ≠
 0 → (p ^ k ∣ n ↔ k ≤ n.factorization p)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Prime.pow_dvd_iff_dvd_ordProj {p k n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ p ^ k ∣ ordProj[p] n := by
  rw [pow_dvd_pow_iff_le_right pp.one_lt, pp.pow_dvd_iff_le_factorization hn]
/-
**Nat.Prime.dvd_iff_one_le_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p n : ℕ}, Nat.Prime p → n ≠ 0 → (p ∣ n ↔ 1 ≤ n.factorization p)
参数：p ∣ n ↔ 1 ≤ n.factorization p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.Prime.pow_dvd_iff_le_factorization`：∀ {p k n : ℕ}, Nat.Prime p → n ≠
 0 → (p ^ k ∣ n ↔ k ≤ n.factorization p)
-/
theorem Prime.dvd_iff_one_le_factorization {p n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ∣ n ↔ 1 ≤ n.factorization p :=
  Iff.trans (by simp) (pp.pow_dvd_iff_le_factorization hn)
/-
**Nat.exists_factorization_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_factorization_lt_of_lt {a b : Nat} (ha : a != 0) (hab : a < b) : ex
ists p : Nat, a.factorization p < b.factorization p
参数：ha : a != 0；hab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.le_def`：le_def : f <= g ↔ forall i, f i <= g i
-/
theorem exists_factorization_lt_of_lt {a b : ℕ} (ha : a ≠ 0) (hab : a < b) :
    ∃ p : ℕ, a.factorization p < b.factorization p := by
  have hb : b ≠ 0 := (ha.bot_lt.trans hab).ne'
  contrapose! hab
  rw [← Finsupp.le_def, factorization_le_iff_dvd hb ha] at hab
  exact le_of_dvd ha.bot_lt hab

@[simp]
/-
**Nat.factorization_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_div {d n : Nat} (h : d ∣ n) : (n / d).factorization = n.fact
orization - d.factorization
参数：h : d ∣ n。
该定理/引理给出了一组等式。
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 34 条，此处仅展示前 30 条）
-/
theorem factorization_div {d n : ℕ} (h : d ∣ n) :
    (n / d).factorization = n.factorization - d.factorization := by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [zero_dvd_iff.mp h]
  rcases eq_or_ne n 0 with (rfl | hn); · simp [tsub_eq_zero_of_le]
  apply add_left_injective d.factorization
  simp only
  rw [tsub_add_cancel_of_le <| (Nat.factorization_le_iff_dvd hd hn).mpr h, ←
    Nat.factorization_mul (Nat.div_pos (Nat.le_of_dvd hn.bot_lt h) hd.bot_lt).ne' hd,
    Nat.div_mul_cancel h]
/-
**Nat.dvd_ordProj_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_ordProj_of_dvd {n p : Nat} (hn : n != 0) (pp : p.Prime) (h : p ∣ n) : 
p ∣ ordProj[p] n
参数：hn : n != 0；pp : p.Prime；h : p ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.Prime.factorization_pos_of_dvd`：∀ {n p : ℕ}, Nat.Prime p → n ≠ 0 → p
 ∣ n → 0 < n.factorization p
-/
theorem dvd_ordProj_of_dvd {n p : ℕ} (hn : n ≠ 0) (pp : p.Prime) (h : p ∣ n) : p ∣ ordProj[p] n :=
  dvd_pow_self p (Prime.factorization_pos_of_dvd pp hn h).ne'
/-
**Nat.not_dvd_ordCompl** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_dvd_ordCompl {n p : Nat} (hp : Prime p) (hn : n != 0) : ¬p ∣ ordCompl[
p] n
参数：hp : Prime p；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.dvd_iff_one_le_factorization`：∀ {p n : ℕ}, Nat.Prime p → n ≠ 0
 → (p ∣ n ↔ 1 ≤ n.factorization p)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.ordCompl_pos`：ordCompl_pos {n : Nat} (p : Nat) (hn : n != 0) : 0 < o
rdCompl[p] n
· 使用定理 `Nat.factorization_div`：factorization_div {d n : Nat} (h : d ∣ n) : (n / 
d).factorization = n.factorization - d.factorization
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_pow`：factorization_pow (n k : Nat) : factorization (n 
^ k) = k • n.factorization
· 使用定理 `Nat.Prime.factorization`：∀ {p : ℕ}, Nat.Prime p → p.factorization = fun₀
 | p => 1
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_dvd_ordCompl {n p : ℕ} (hp : Prime p) (hn : n ≠ 0) : ¬p ∣ ordCompl[p] n := by
  rw [Nat.Prime.dvd_iff_one_le_factorization hp (ordCompl_pos p hn).ne']
  rw [Nat.factorization_div (Nat.ordProj_dvd n p)]
  simp [hp.factorization]
/-
**Nat.coprime_ordCompl** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_ordCompl {n p : Nat} (hp : Prime p) (hn : n != 0) : Coprime p (ord
Compl[p] n)
参数：hp : Prime p；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Nat.not_dvd_ordCompl`：not_dvd_ordCompl {n p : Nat} (hp : Prime p) (hn : 
n != 0) : ¬p ∣ ordCompl[p] n
· 使用定理 `Nat.coprime_or_dvd_of_prime`：coprime_or_dvd_of_prime {p} (pp : Prime p) 
(i : Nat) : Coprime p i ∨ p ∣ i
-/
theorem coprime_ordCompl {n p : ℕ} (hp : Prime p) (hn : n ≠ 0) : Coprime p (ordCompl[p] n) :=
  (or_iff_left (not_dvd_ordCompl hp hn)).mp <| coprime_or_dvd_of_prime hp _
/-
**Nat.factorization_ordCompl** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_ordCompl (n p : Nat) : (ordCompl[p] n).factorization = n.fac
torization.erase p
参数：n p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `Finsupp.erase_of_notMem_support`：erase_of_notMem_support {f : α ->₀ M} {
a} (haf : a ∉ f.support) : erase a f = f
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Finsupp.erase_same`：erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.not_dvd_ordCompl`：not_dvd_ordCompl {n p : Nat} (hp : Prime p) (hn : 
n != 0) : ¬p ∣ ordCompl[p] n
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `Nat.factorization_div`：factorization_div {d n : Nat} (h : d ∣ n) : (n / 
d).factorization = n.factorization - d.factorization
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
· 使用定理 `Nat.factorization_pow`：factorization_pow (n k : Nat) : factorization (n 
^ k) = k • n.factorization
· 使用定理 `Nat.Prime.factorization`：∀ {p : ℕ}, Nat.Prime p → p.factorization = fun₀
 | p => 1
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem factorization_ordCompl (n p : ℕ) :
    (ordCompl[p] n).factorization = n.factorization.erase p := by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then ?_ else
    simp [pp]
  ext q
  rcases eq_or_ne q p with (rfl | hqp)
  · simp only [Finsupp.erase_same, factorization_eq_zero_iff, not_dvd_ordCompl pp hn]
    simp
  · rw [Finsupp.erase_ne hqp, factorization_div (ordProj_dvd n p)]
    simp [pp.factorization, hqp.symm]
/-
**Nat.ordProj_self_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordProj_self_pow {p k : Nat} (hp : Prime p) : ordProj[p] (p ^ k) = p ^ k
参数：hp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_pow`：factorization_pow (n k : Nat) : factorization (n 
^ k) = k • n.factorization
· 使用定理 `Nat.Prime.factorization`：∀ {p : ℕ}, Nat.Prime p → p.factorization = fun₀
 | p => 1
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordProj_self_pow {p k : ℕ} (hp : Prime p) : ordProj[p] (p ^ k) = p ^ k := by
  simp [hp]
/-
**Nat.ordCompl_self_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_self_pow {p k : Nat} (hp : Prime p) : ordCompl[p] (p ^ k) = 1
参数：hp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_of_factorization_eq`：eq_of_factorization_eq {a b : Nat} (ha : a !
= 0) (hb : b != 0) (h : forall p : Nat, a.factorization p = b.factorization p) :
 a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.ordCompl_pos`：ordCompl_pos {n : Nat} (p : Nat) (hn : n != 0) : 0 < o
rdCompl[p] n
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Prime.factorization_pow`：∀ {p k : ℕ}, Nat.Prime p → (p ^ k).factoriz
ation = fun₀ | p => k
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Nat.factorization_div`：factorization_div {d n : Nat} (h : d ∣ n) : (n / 
d).factorization = n.factorization - d.factorization
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.factorization_one`：factorization_one : factorization 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ordCompl_self_pow {p k : ℕ} (hp : Prime p) : ordCompl[p] (p ^ k) = 1 := by
  apply Nat.eq_of_factorization_eq
  · exact pos_iff_ne_zero.mp (ordCompl_pos p (pow_ne_zero k hp.ne_zero))
  · exact one_ne_zero
  · simp [Prime.factorization_pow hp]
/-
**Nat.ordCompl_self_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_self_pow_mul (n k : Nat) {p : Nat} (hp : Prime p) : ordCompl[p] (
p ^ k * n) = ordCompl[p] n
参数：n k : Nat；hp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ordCompl_mul`：ordCompl_mul (a b p : Nat) : ordCompl[p] (a * b) = ord
Compl[p] a * ordCompl[p] b
· 使用定理 `Nat.ordCompl_self_pow`：ordCompl_self_pow {p k : Nat} (hp : Prime p) : or
dCompl[p] (p ^ k) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem ordCompl_self_pow_mul (n k : ℕ) {p : ℕ} (hp : Prime p) :
    ordCompl[p] (p ^ k * n) = ordCompl[p] n := by
  rw [ordCompl_mul, ordCompl_self_pow hp, one_mul]
/-
**Nat.ordCompl_eq_self_iff_zero_or_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_eq_self_iff_zero_or_not_dvd (n : Nat) {p : Nat} (hp : Prime p) : 
ordCompl[p] n = n ↔ n = 0 ∨ ¬p ∣ n
参数：n : Nat；hp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.not_dvd_ordCompl`：not_dvd_ordCompl {n p : Nat} (hp : Prime p) (hn : 
n != 0) : ¬p ∣ ordCompl[p] n
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `Nat.factorization_eq_zero_of_not_dvd`：factorization_eq_zero_of_not_dvd {
n p : Nat} (h : ¬p ∣ n) : n.factorization p = 0
-/
theorem ordCompl_eq_self_iff_zero_or_not_dvd (n : ℕ) {p : ℕ} (hp : Prime p) :
    ordCompl[p] n = n ↔ n = 0 ∨ ¬p ∣ n := by
  constructor
  · intro h
    by_cases n_zero : n = 0
    · simp [n_zero]
    · right
      rw [← h]
      exact not_dvd_ordCompl hp n_zero
  · rintro (n_eq_zero | not_dvd)
    · simp [n_eq_zero]
    · simp [Nat.factorization_eq_zero_of_not_dvd not_dvd]
/-
**Nat.ordCompl_pow_mul_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_pow_mul_of_not_dvd {m : Nat} (k : Nat) {p : Nat} (hp : p.Prime) (
hm : ¬p ∣ m) : ordCompl[p] (p ^ k * m) = m
参数：k : Nat；hp : p.Prime；hm : ¬p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ordCompl_self_pow_mul`：ordCompl_self_pow_mul (n k : Nat) {p : Nat} (
hp : Prime p) : ordCompl[p] (p ^ k * n) = ordCompl[p] n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ordCompl_eq_self_iff_zero_or_not_dvd`：ordCompl_eq_self_iff_zero_or_n
ot_dvd (n : Nat) {p : Nat} (hp : Prime p) : ordCompl[p] n = n ↔ n = 0 ∨ ¬p ∣ n
-/
theorem ordCompl_pow_mul_of_not_dvd {m : ℕ} (k : ℕ) {p : ℕ} (hp : p.Prime) (hm : ¬p ∣ m) :
    ordCompl[p] (p ^ k * m) = m := by
  rw [ordCompl_self_pow_mul m k hp]
  exact (ordCompl_eq_self_iff_zero_or_not_dvd m hp).mpr (Or.inr hm)
/-
**Nat.ordCompl_pow_mul_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_pow_mul_eq_self_iff (k m : Nat) {p : Nat} (hp : p.Prime) : ordCom
pl[p] (p ^ k * m) = m ↔ m = 0 ∨ ¬p ∣ m
参数：k m : Nat；hp : p.Prime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ordCompl_self_pow_mul`：ordCompl_self_pow_mul (n k : Nat) {p : Nat} (
hp : Prime p) : ordCompl[p] (p ^ k * n) = ordCompl[p] n
· 使用定理 `Nat.ordCompl_eq_self_iff_zero_or_not_dvd`：ordCompl_eq_self_iff_zero_or_n
ot_dvd (n : Nat) {p : Nat} (hp : Prime p) : ordCompl[p] n = n ↔ n = 0 ∨ ¬p ∣ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ordCompl_pow_mul_eq_self_iff (k m : ℕ) {p : ℕ} (hp : p.Prime) :
    ordCompl[p] (p ^ k * m) = m ↔ m = 0 ∨ ¬p ∣ m := by
  rw [ordCompl_self_pow_mul m k hp, ordCompl_eq_self_iff_zero_or_not_dvd m hp]
/-
**Nat.ordCompl_div_pow_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_div_pow_of_dvd (k : Nat) {x p : Nat} (hp : p.Prime) (hx : p ^ k ∣
 x) : ordCompl[p] (x / p ^ k) = ordCompl[p] x
参数：k : Nat；hp : p.Prime；hx : p ^ k ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ordCompl_self_pow_mul`：ordCompl_self_pow_mul (n k : Nat) {p : Nat} (
hp : Prime p) : ordCompl[p] (p ^ k * n) = ordCompl[p] n
-/
theorem ordCompl_div_pow_of_dvd (k : ℕ) {x p : ℕ} (hp : p.Prime) (hx : p ^ k ∣ x) :
    ordCompl[p] (x / p ^ k) = ordCompl[p] x := by
  obtain ⟨m, rfl⟩ := hx
  rw [Nat.mul_div_cancel_left m (pow_pos hp.pos k), ← ordCompl_self_pow_mul m k hp]
/-
**Nat.ordCompl_div_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_div_of_dvd {x : Nat} {p : Nat} (hp : p.Prime) (hx : p ∣ x) : ordC
ompl[p] (x / p) = ordCompl[p] x
参数：hp : p.Prime；hx : p ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.ordCompl_div_pow_of_dvd`：ordCompl_div_pow_of_dvd (k : Nat) {x p : Na
t} (hp : p.Prime) (hx : p ^ k ∣ x) : ordCompl[p] (x / p ^ k) = ordCompl[p] x
-/
theorem ordCompl_div_of_dvd {x : ℕ} {p : ℕ} (hp : p.Prime) (hx : p ∣ x) :
    ordCompl[p] (x / p) = ordCompl[p] x := by
  simpa [pow_one] using ordCompl_div_pow_of_dvd 1 hp (show p ^ 1 ∣ x by simpa)

-- `ordCompl[p] n` is the largest divisor of `n` not divisible by `p`.
/-
**Nat.dvd_ordCompl_of_dvd_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_ordCompl_of_dvd_not_dvd {p d n : Nat} (hdn : d ∣ n) (hpd : ¬p ∣ d) : d
 ∣ ordCompl[p] n
参数：hdn : d ∣ n；hpd : ¬p ∣ d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.ordCompl_pos`：ordCompl_pos {n : Nat} (p : Nat) (hn : n != 0) : 0 < o
rdCompl[p] n
· 使用定理 `Nat.factorization_ordCompl`：factorization_ordCompl (n p : Nat) : (ordCom
pl[p] n).factorization = n.factorization.erase p
· 使用定理 `Finsupp.erase_same`：erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem dvd_ordCompl_of_dvd_not_dvd {p d n : ℕ} (hdn : d ∣ n) (hpd : ¬p ∣ d) :
    d ∣ ordCompl[p] n := by
  if hn0 : n = 0 then simp [hn0] else
  if hd0 : d = 0 then simp [hd0] at hpd else
  rw [← factorization_le_iff_dvd hd0 (ordCompl_pos p hn0).ne', factorization_ordCompl]
  intro q
  if hqp : q = p then
    simp [factorization_eq_zero_iff, hqp, hpd]
  else
    simp [hqp, (factorization_le_iff_dvd hd0 hn0).2 hdn q]

/-- If `n` is a nonzero natural number and `p ≠ 1`, then there are natural numbers `e`
and `n'` such that `n'` is not divisible by `p` and `n = p^e * n'`. -/
/-
**Nat.exists_eq_pow_mul_and_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_eq_pow_mul_and_not_dvd {n : Nat} (hn : n != 0) (p : Nat) (hp : p !=
 1) : exists e n' : Nat, ¬p ∣ n' ∧ n = p ^ e * n'
参数：hn : n != 0；p : Nat；hp : p != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd`：FiniteMultiplicity.exi
sts_eq_pow_mul_and_not_dvd (hfin : FiniteMultiplicity a b) : exists c : α, b = a
 ^ multiplicity a b * c ∧ ¬a ∣ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n

--- 原说明 ---
If `n` is a nonzero natural number and `p ≠ 1`, then there are natural numbers `
e`
and `n'` such that `n'` is not divisible by `p` and `n = p^e * n'`.
-/
theorem exists_eq_pow_mul_and_not_dvd {n : ℕ} (hn : n ≠ 0) (p : ℕ) (hp : p ≠ 1) :
    ∃ e n' : ℕ, ¬p ∣ n' ∧ n = p ^ e * n' :=
  let ⟨a', h₁, h₂⟩ :=
    (Nat.finiteMultiplicity_iff.mpr ⟨hp, Nat.pos_of_ne_zero hn⟩).exists_eq_pow_mul_and_not_dvd
  ⟨_, a', h₂, h₁⟩

/-- Any nonzero natural number is the product of an odd part `m` and a power of
two `2 ^ k`. -/
/-
**Nat.exists_eq_two_pow_mul_odd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_eq_two_pow_mul_odd {n : Nat} (hn : n != 0) : exists k m : Nat, Odd 
m ∧ n = 2 ^ k * m
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_pow_mul_and_not_dvd`：exists_eq_pow_mul_and_not_dvd {n : Na
t} (hn : n != 0) (p : Nat) (hp : p != 1) : exists e n' : Nat, ¬p ∣ n' ∧ n = p ^ 
e * n'
· 使用定理 `Nat.succ_ne_self`：∀ (n : ℕ), n.succ ≠ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Even.two_dvd`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → 2 ∣
 a

--- 原说明 ---
Any nonzero natural number is the product of an odd part `m` and a power of
two `2 ^ k`.
-/
theorem exists_eq_two_pow_mul_odd {n : ℕ} (hn : n ≠ 0) :
    ∃ k m : ℕ, Odd m ∧ n = 2 ^ k * m :=
  let ⟨k, m, hm, hn⟩ := exists_eq_pow_mul_and_not_dvd hn 2 (succ_ne_self 1)
  ⟨k, m, not_even_iff_odd.1 (mt Even.two_dvd hm), hn⟩
/-
**Nat.dvd_iff_div_factorization_eq_tsub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_iff_div_factorization_eq_tsub {d n : Nat} (hd : d != 0) (hdn : d <= n)
 : d ∣ n ↔ (n / d).factorization = n.factorization - d.factorization
参数：hd : d != 0；hdn : d <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorization_div`：factorization_div {d n : Nat} (h : d ∣ n) : (n / 
d).factorization = n.factorization - d.factorization
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.dvd_iff_le_div_mul`：∀ (n d : ℕ), d ∣ n ↔ n ≤ n / d * d
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.exists_factorization_lt_of_lt`：exists_factorization_lt_of_lt {a b : 
Nat} (ha : a != 0) (hab : a < b) : exists p : Nat, a.factorization p < b.factori
zation p
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用定理 `Finsupp.tsub_apply`：tsub_apply (f g : ι ->₀ α) (a : ι) : (f - g) a = f a
 - g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_tsub_iff_right`：lt_tsub_iff_right : a < b - c ↔ a + c < b
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
-/
theorem dvd_iff_div_factorization_eq_tsub {d n : ℕ} (hd : d ≠ 0) (hdn : d ≤ n) :
    d ∣ n ↔ (n / d).factorization = n.factorization - d.factorization := by
  refine ⟨factorization_div, ?_⟩
  rcases eq_or_lt_of_le hdn with (rfl | hd_lt_n); · simp
  have h1 : n / d ≠ 0 := by simp [*]
  intro h
  rw [dvd_iff_le_div_mul n d]
  by_contra h2
  obtain ⟨p, hp⟩ := exists_factorization_lt_of_lt (mul_ne_zero h1 hd) (not_le.mp h2)
  rwa [factorization_mul h1 hd, add_apply, ← lt_tsub_iff_right, h, tsub_apply,
    lt_self_iff_false] at hp
/-
**Nat.ordProj_dvd_ordProj_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordProj_dvd_ordProj_of_dvd {a b : Nat} (hb0 : b != 0) (hab : a ∣ b) (p : N
at) : ordProj[p] a ∣ ordProj[p] b
参数：hb0 : b != 0；hab : a ∣ b；p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pow_dvd_pow_iff_le_right`：∀ {x k l : ℕ}, 1 < x → (x ^ k ∣ x ^ l ↔ k 
≤ l)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
-/
theorem ordProj_dvd_ordProj_of_dvd {a b : ℕ} (hb0 : b ≠ 0) (hab : a ∣ b) (p : ℕ) :
    ordProj[p] a ∣ ordProj[p] b := by
  rcases em' p.Prime with (pp | pp); · simp [pp]
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  rw [pow_dvd_pow_iff_le_right pp.one_lt]
  exact (factorization_le_iff_dvd ha0 hb0).2 hab p
/-
**Nat.ordCompl_dvd_ordCompl_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_dvd_ordCompl_of_dvd {a b : Nat} (hab : a ∣ b) (p : Nat) : ordComp
l[p] a ∣ ordCompl[p] b
参数：hab : a ∣ b；p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Nat.ordProj_le`：ordProj_le {n : Nat} (p : Nat) (hn : n != 0) : ordProj[p
] n <= n
· 使用定理 `Nat.ordProj_pos`：ordProj_pos (n p : Nat) : 0 < ordProj[p] n
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `Nat.factorization_ordCompl`：factorization_ordCompl (n p : Nat) : (ordCom
pl[p] n).factorization = n.factorization.erase p
· 使用定理 `Finsupp.erase_same`：erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem ordCompl_dvd_ordCompl_of_dvd {a b : ℕ} (hab : a ∣ b) (p : ℕ) :
    ordCompl[p] a ∣ ordCompl[p] b := by
  rcases em' p.Prime with (pp | pp)
  · simp [pp, hab]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  rcases eq_or_ne a 0 with (rfl | ha0)
  · cases hb0 (zero_dvd_iff.1 hab)
  have ha := (Nat.div_pos (ordProj_le p ha0) (ordProj_pos a p)).ne'
  have hb := (Nat.div_pos (ordProj_le p hb0) (ordProj_pos b p)).ne'
  rw [← factorization_le_iff_dvd ha hb, factorization_ordCompl a p, factorization_ordCompl b p]
  intro q
  rcases eq_or_ne q p with (rfl | hqp)
  · simp
  simp_rw [erase_ne hqp]
  exact (factorization_le_iff_dvd ha0 hb0).2 hab q
/-
**Nat.ordCompl_dvd_ordCompl_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordCompl_dvd_ordCompl_iff_dvd (a b : Nat) : (forall p : Nat, ordCompl[p] a
 ∣ ordCompl[p] b) ↔ a ∣ b
参数：a b : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Nat.mul_dvd_mul_iff_left`：∀ {a b c : ℕ}, 0 < a → (a * b ∣ a * c ↔ b ∣ c)
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Prime.factorization`：∀ {p : ℕ}, Nat.Prime p → p.factorization = fun₀
 | p => 1
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `Nat.Prime.factorization_self`：∀ {p : ℕ}, Nat.Prime p → p.factorization p
 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `Nat.ordCompl_dvd_ordCompl_of_dvd`：ordCompl_dvd_ordCompl_of_dvd {a b : Na
t} (hab : a ∣ b) (p : Nat) : ordCompl[p] a ∣ ordCompl[p] b
-/
theorem ordCompl_dvd_ordCompl_iff_dvd (a b : ℕ) :
    (∀ p : ℕ, ordCompl[p] a ∣ ordCompl[p] b) ↔ a ∣ b := by
  refine ⟨fun h => ?_, fun hab p => ordCompl_dvd_ordCompl_of_dvd hab p⟩
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  if pa : a.Prime then ?_ else simpa [pa] using h a
  if pb : b.Prime then ?_ else simpa [pb] using h b
  rw [prime_dvd_prime_iff_eq pa pb]
  by_contra hab
  apply pa.ne_one
  rw [← Nat.dvd_one, ← Nat.mul_dvd_mul_iff_left hb0.bot_lt, mul_one]
  simpa [Prime.factorization_self pb, Prime.factorization pa, hab] using h b
/-
**Nat.dvd_iff_prime_pow_dvd_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_iff_prime_pow_dvd_dvd (n d : Nat) : d ∣ n ↔ forall p k : Nat, Prime p 
-> p ^ k ∣ d -> p ^ k ∣ n
参数：n d : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.lt_two_pow_self`：∀ {n : ℕ}, n < 2 ^ n
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Nat.factorization_prime_le_iff_dvd`：factorization_prime_le_iff_dvd {d n 
: Nat} (hd : d != 0) (hn : n != 0) : (forall p : Nat, p.Prime -> d.factorization
 p <= n.factorization p)…
· 使用定理 `Nat.Prime.pow_dvd_iff_le_factorization`：∀ {p k n : ℕ}, Nat.Prime p → n ≠
 0 → (p ^ k ∣ n ↔ k ≤ n.factorization p)
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
-/
theorem dvd_iff_prime_pow_dvd_dvd (n d : ℕ) :
    d ∣ n ↔ ∀ p k : ℕ, Prime p → p ^ k ∣ d → p ^ k ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases eq_or_ne d 0 with (rfl | hd)
  · simp only [zero_dvd_iff, hn, false_iff, not_forall]
    exact ⟨2, n, prime_two, dvd_zero _, mt (le_of_dvd hn.bot_lt) (n.lt_two_pow_self).not_ge⟩
  refine ⟨fun h p k _ hpkd => dvd_trans hpkd h, ?_⟩
  rw [← factorization_prime_le_iff_dvd hd hn]
  intro h p pp
  simp_rw [← pp.pow_dvd_iff_le_factorization hn]
  exact h p _ pp (ordProj_dvd _ _)
/-
**Nat.prod_primeFactors_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_primeFactors_dvd (n : Nat) : ∏ p in n.primeFactors, p ∣ n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.primeFactors_zero`：Nat.primeFactors 0 = ∅
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `Multiset.toFinset_prod_dvd_prod`：toFinset_prod_dvd_prod [DecidableEq M] 
[CommMonoid M] (S : Multiset M) : S.toFinset.prod id ∣ S.prod
-/
theorem prod_primeFactors_dvd (n : ℕ) : ∏ p ∈ n.primeFactors, p ∣ n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · simpa [prod_primeFactorsList hn] using (n.primeFactorsList : Multiset ℕ).toFinset_prod_dvd_prod
/-
**Nat.factorization_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_gcd {a b : Nat} (ha_pos : a != 0) (hb_pos : b != 0) : (gcd a
 b).factorization = a.factorization ⊓ b.factorization
参数：ha_pos : a != 0；hb_pos : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd_greatest`：gcd_greatest {a b d : Nat} (hda : d ∣ a) (hdb : d ∣ b)
 (hd : forall e : Nat, e ∣ a -> e ∣ b -> e ∣ d) : d = a.gcd b
· 使用定理 `Nat.prod_pow_dvd_of_le_factorization`：prod_pow_dvd_of_le_factorization (
hf : f <= n.factorization) : f.prod (· ^ ·) ∣ n
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_prod_pow_of_factorization_le`：dvd_prod_pow_of_factorization_le (
hn : n != 0) (hf : n.factorization <= f) : n ∣ f.prod (· ^ ·)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.factorization_prod_pow_eq_self_of_le_factorization`：factorization_pr
od_pow_eq_self_of_le_factorization (hf : f <= n.factorization) : (f.prod (· ^ ·)
).factorization = f
-/
theorem factorization_gcd {a b : ℕ} (ha_pos : a ≠ 0) (hb_pos : b ≠ 0) :
    (gcd a b).factorization = a.factorization ⊓ b.factorization := by
  suffices (a.factorization ⊓ b.factorization).prod (· ^ ·) = gcd a b by
    rw [← this, factorization_prod_pow_eq_self_of_le_factorization inf_le_left]
  apply gcd_greatest
  · exact prod_pow_dvd_of_le_factorization inf_le_left
  · exact prod_pow_dvd_of_le_factorization inf_le_right
  · intro e hea heb
    rcases eq_or_ne e 0 with (rfl | he_pos)
    · exact absurd (zero_dvd_iff.mp hea) ha_pos
    apply dvd_prod_pow_of_factorization_le he_pos
    have hea' := (factorization_le_iff_dvd he_pos ha_pos).mpr hea
    have heb' := (factorization_le_iff_dvd he_pos hb_pos).mpr heb
    simp [hea', heb']
/-
**Nat.factorization_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_lcm {a b : Nat} (ha : a != 0) (hb : b != 0) : (a.lcm b).fact
orization = a.factorization ⊔ b.factorization
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.gcd_eq_zero_iff`：∀ {i j : ℕ}, i.gcd j = 0 ↔ i = 0 ∧ j = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.lcm_ne_zero`：∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.lcm n ≠ 0
· 使用定理 `Nat.gcd_mul_lcm`：∀ (m n : ℕ), m.gcd n * m.lcm n = m * n
· 使用定理 `Nat.factorization_gcd`：factorization_gcd {a b : Nat} (ha_pos : a != 0) (
hb_pos : b != 0) : (gcd a b).factorization = a.factorization ⊓ b.factorization
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `min_add_max`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : AddCommSe
migroup α] (a b : α), min a b + max a b = a + b
-/
theorem factorization_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.lcm b).factorization = a.factorization ⊔ b.factorization := by
  rw [← add_right_inj (a.gcd b).factorization, ←
    factorization_mul (mt gcd_eq_zero_iff.1 fun h => ha h.1) (lcm_ne_zero ha hb), gcd_mul_lcm,
    factorization_gcd ha hb, factorization_mul ha hb]
  ext1
  exact (min_add_max _ _).symm

@[to_additive sum_primeFactors_gcd_add_sum_primeFactors_mul]
/-
**Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul** 是 Mathlib 中的一个定理，位于命名空间 
`Nat`。
形式化陈述：prod_primeFactors_gcd_mul_prod_primeFactors_mul {β : Type*} [CommMonoid β]
 (m n : Nat) (f : Nat -> β) : (m.gcd n).primeFactors.prod f * (m * n).primeFacto
rs.prod f = m.primeFactors.prod f * n.primeFactors.prod f
参数：m n : Nat；f : Nat -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.primeFactors_zero`：Nat.primeFactors 0 = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_zero_right`：∀ (n : ℕ), n.gcd 0 = n
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Nat.primeFactors_mul`：primeFactors_mul (ha : a != 0) (hb : b != 0) : (a 
* b).primeFactors = a.primeFactors union b.primeFactors
· 使用引理 `Nat.primeFactors_gcd`：primeFactors_gcd (ha : a != 0) (hb : b != 0) : (a.
gcd b).primeFactors = a.primeFactors inter b.primeFactors
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_union_inter`：prod_union_inter [DecidableEq ι] : (∏ x in s₁ u
nion s₂, f x) * ∏ x in s₁ inter s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
-/
theorem prod_primeFactors_gcd_mul_prod_primeFactors_mul {β : Type*} [CommMonoid β] (m n : ℕ)
    (f : ℕ → β) :
    (m.gcd n).primeFactors.prod f * (m * n).primeFactors.prod f =
      m.primeFactors.prod f * n.primeFactors.prod f := by
  obtain rfl | hm₀ := eq_or_ne m 0
  · simp
  obtain rfl | hn₀ := eq_or_ne n 0
  · simp
  · rw [primeFactors_mul hm₀ hn₀, primeFactors_gcd hm₀ hn₀, mul_comm, Finset.prod_union_inter]
/-
**Nat.setOfPred_pow_dvd_eq_Icc_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：setOfPred_pow_dvd_eq_Icc_factorization {n p : Nat} (pp : p.Prime) (hn : n 
!= 0) : { i : Nat | i != 0 ∧ p ^ i ∣ n } = Set.Icc 1 (n.factorization p)
参数：pp : p.Prime；hn : n != 0。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.Prime.pow_dvd_iff_le_factorization`：∀ {p k n : ℕ}, Nat.Prime p → n ≠
 0 → (p ^ k ∣ n ↔ k ≤ n.factorization p)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem setOfPred_pow_dvd_eq_Icc_factorization {n p : ℕ} (pp : p.Prime) (hn : n ≠ 0) :
    { i : ℕ | i ≠ 0 ∧ p ^ i ∣ n } = Set.Icc 1 (n.factorization p) := by
  ext
  simp [one_le_iff_ne_zero, pp.pow_dvd_iff_le_factorization hn]

@[deprecated (since := "2026-07-09")]
alias setOf_pow_dvd_eq_Icc_factorization := setOfPred_pow_dvd_eq_Icc_factorization

/-- The set of positive powers of prime `p` that divide `n` is exactly the set of
positive natural numbers up to `n.factorization p`. -/
/-
**Nat.Icc_factorization_eq_pow_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Icc_factorization_eq_pow_dvd (n : Nat) {p : Nat} (pp : Prime p) : Icc 1 (n
.factorization p) = {i in Ico 1 n | p ^ i ∣ n}
参数：n : Nat；pp : Prime p。
该定理/引理给出了一组等式。
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
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `Finset.Icc_eq_empty_of_lt`：Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_true`：∀ {α : Type u_1} {h : DecidablePred fun x => True} (
s : Finset α), {x ∈ s | True} = s
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Nat.Prime.pow_dvd_iff_le_factorization`：∀ {p k n : ℕ}, Nat.Prime p → n ≠
 0 → (p ^ k ∣ n ↔ k ≤ n.factorization p)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.factorization_lt`：factorization_lt {n : Nat} (p : Nat) (hn : n != 0)
 : n.factorization p < n

--- 原说明 ---
The set of positive powers of prime `p` that divide `n` is exactly the set of
positive natural numbers up to `n.factorization p`.
-/
theorem Icc_factorization_eq_pow_dvd (n : ℕ) {p : ℕ} (pp : Prime p) :
    Icc 1 (n.factorization p) = {i ∈ Ico 1 n | p ^ i ∣ n} := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  ext x
  simp only [mem_Icc, Finset.mem_filter, mem_Ico, and_assoc, and_congr_right_iff,
    pp.pow_dvd_iff_le_factorization hn, iff_and_self]
  exact fun _ H => lt_of_le_of_lt H (factorization_lt p hn)
/-
**Nat.factorization_eq_card_pow_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_card_pow_dvd (n : Nat) {p : Nat} (pp : p.Prime) : n.facto
rization p = #{i in Ico 1 n | p ^ i ∣ n}
参数：n : Nat；pp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Icc_factorization_eq_pow_dvd`：Icc_factorization_eq_pow_dvd (n : Nat)
 {p : Nat} (pp : Prime p) : Icc 1 (n.factorization p) = {i in Ico 1 n | p ^ i ∣ 
n}
· 使用定理 `Nat.card_Icc`：∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorization_eq_card_pow_dvd (n : ℕ) {p : ℕ} (pp : p.Prime) :
    n.factorization p = #{i ∈ Ico 1 n | p ^ i ∣ n} := by
  simp [← Icc_factorization_eq_pow_dvd n pp]
/-
**Nat.Ico_filter_pow_dvd_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_filter_pow_dvd_eq {n p b : Nat} (pp : p.Prime) (hn : n != 0) (hb : n <
= p ^ b) : {i in Ico 1 n | p ^ i ∣ n} = {i in Icc 1 b | p ^ i ∣ n}
参数：pp : p.Prime；hn : n != 0；hb : n <= p ^ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `Nat.lt_of_pow_dvd_right`：∀ {b a n : ℕ}, b ≠ 0 → 2 ≤ a → a ^ n ∣ b → n < 
b
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pow_le_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n ≤ a ^ m ↔ n ≤ m)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem Ico_filter_pow_dvd_eq {n p b : ℕ} (pp : p.Prime) (hn : n ≠ 0) (hb : n ≤ p ^ b) :
    {i ∈ Ico 1 n | p ^ i ∣ n} = {i ∈ Icc 1 b | p ^ i ∣ n} := by
  ext x
  simp only [Finset.mem_filter, mem_Ico, mem_Icc, and_congr_left_iff, and_congr_right_iff]
  rintro h1 -
  exact iff_of_true (lt_of_pow_dvd_right hn pp.two_le h1) <|
    (Nat.pow_le_pow_iff_right pp.one_lt).1 <| (le_of_dvd hn.bot_lt h1).trans hb
/-
**Nat.Ico_pow_dvd_eq_Ico_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_pow_dvd_eq_Ico_of_lt {n p b : Nat} (pp : p.Prime) (hn : n != 0) (hb : 
n < p ^ b) : {i in Ico 1 n | p ^ i ∣ n} = {i in Ico 1 b | p ^ i ∣ n}
参数：pp : p.Prime；hn : n != 0；hb : n < p ^ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pow_lt_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n < a ^ m ↔ n < m)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `Nat.lt_of_pow_dvd_right`：∀ {b a n : ℕ}, b ≠ 0 → 2 ≤ a → a ^ n ∣ b → n < 
b
-/
theorem Ico_pow_dvd_eq_Ico_of_lt {n p b : ℕ} (pp : p.Prime) (hn : n ≠ 0) (hb : n < p ^ b) :
    {i ∈ Ico 1 n | p ^ i ∣ n} = {i ∈ Ico 1 b | p ^ i ∣ n} := by
  ext i
  simp only [Finset.mem_filter, mem_Ico, and_congr_left_iff, and_congr_right_iff]
  refine fun h1 h2 ↦ ⟨fun h ↦ ?_, fun h ↦ lt_of_pow_dvd_right hn (Prime.one_lt pp) h1⟩
  rcases p with - | p
  · rw [zero_pow (by lia), zero_dvd_iff] at h1
    exact (hn h1).elim
  · rw [← Nat.pow_lt_pow_iff_right (Prime.one_lt pp)]
    apply lt_of_le_of_lt (le_of_dvd (Nat.zero_lt_of_ne_zero hn) h1) hb

/-- The factorization of `m` in `n` is the number of positive natural numbers `i` such that `m ^ i`
divides `n`. Note `m` is prime. This set is expressed by filtering `Ico 1 b` where `b` is any bound
greater than `log m n`. -/
/-
**Nat.factorization_eq_card_pow_dvd_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_card_pow_dvd_of_lt (hm : m.Prime) (hn : 0 < n) (hb : n < 
m ^ b) : n.factorization m = #{i in Ico 1 b | m ^ i ∣ n}
参数：hm : m.Prime；hn : 0 < n；hb : n < m ^ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_eq_card_pow_dvd`：factorization_eq_card_pow_dvd (n : Na
t) {p : Nat} (pp : p.Prime) : n.factorization p = #{i in Ico 1 n | p ^ i ∣ n}
· 使用定理 `Nat.Ico_pow_dvd_eq_Ico_of_lt`：Ico_pow_dvd_eq_Ico_of_lt {n p b : Nat} (pp
 : p.Prime) (hn : n != 0) (hb : n < p ^ b) : {i in Ico 1 n | p ^ i ∣ n} = {i in 
Ico 1 b | p ^ i ∣ …

--- 原说明 ---
The factorization of `m` in `n` is the number of positive natural numbers `i` su
ch that `m ^ i`
divides `n`. Note `m` is prime. This set is expressed by filtering `Ico 1 b` whe
re `b` is any bound
greater than `log m n`.
-/
theorem factorization_eq_card_pow_dvd_of_lt (hm : m.Prime) (hn : 0 < n) (hb : n < m ^ b) :
    n.factorization m = #{i ∈ Ico 1 b | m ^ i ∣ n} := by
  rwa [factorization_eq_card_pow_dvd n hm, Ico_pow_dvd_eq_Ico_of_lt hm (by lia)]

/-! ### Factorization and coprimes -/


/-- If `p` is a prime factor of `a` then the power of `p` in `a` is the same that in `a * b`,
for any `b` coprime to `a`. -/
/-
**Nat.factorization_eq_of_coprime_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_of_coprime_left {p a b : Nat} (hab : Coprime a b) (hpa : 
p in a.primeFactorsList) : (a * b).factorization p = a.factorization p
参数：hab : Coprime a b；hpa : p in a.primeFactorsList。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_mul_apply_of_coprime`：factorization_mul_apply_of_copri
me {p a b : Nat} (hab : Coprime a b) : (a * b).factorization p = a.factorization
 p + b.factorization p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.primeFactorsList_count_eq`：primeFactorsList_count_eq {n p : Nat} : n
.primeFactorsList.count p = n.factorization p
· 使用定理 `List.count_eq_zero_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBE
q α] {a : α} {l : List α}, a ∉ l → List.count a l = 0
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `Nat.coprime_primeFactorsList_disjoint`：coprime_primeFactorsList_disjoint
 {a b : Nat} (hab : a.Coprime b) : List.Disjoint a.primeFactorsList b.primeFacto
rsList
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
If `p` is a prime factor of `a` then the power of `p` in `a` is the same that in
 `a * b`,
for any `b` coprime to `a`.
-/
theorem factorization_eq_of_coprime_left {p a b : ℕ} (hab : Coprime a b)
    (hpa : p ∈ a.primeFactorsList) : (a * b).factorization p = a.factorization p := by
  rw [factorization_mul_apply_of_coprime hab, ← primeFactorsList_count_eq,
    ← primeFactorsList_count_eq,
    count_eq_zero_of_not_mem (coprime_primeFactorsList_disjoint hab hpa), add_zero]

/-- If `p` is a prime factor of `b` then the power of `p` in `b` is the same that in `a * b`,
for any `a` coprime to `b`. -/
/-
**Nat.factorization_eq_of_coprime_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_of_coprime_right {p a b : Nat} (hab : Coprime a b) (hpb :
 p in b.primeFactorsList) : (a * b).factorization p = b.factorization p
参数：hab : Coprime a b；hpb : p in b.primeFactorsList。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.factorization_eq_of_coprime_left`：factorization_eq_of_coprime_left {
p a b : Nat} (hab : Coprime a b) (hpa : p in a.primeFactorsList) : (a * b).facto
rization p = a.factorizati…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.coprime_comm`：∀ {n m : ℕ}, n.Coprime m ↔ m.Coprime n

--- 原说明 ---
If `p` is a prime factor of `b` then the power of `p` in `b` is the same that in
 `a * b`,
for any `a` coprime to `b`.
-/
theorem factorization_eq_of_coprime_right {p a b : ℕ} (hab : Coprime a b)
    (hpb : p ∈ b.primeFactorsList) : (a * b).factorization p = b.factorization p := by
  rw [mul_comm]
  exact factorization_eq_of_coprime_left (coprime_comm.mp hab) hpb

/-- Two positive naturals are equal if their prime padic valuations are equal -/
/-
**Nat.eq_iff_prime_padicValNat_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_iff_prime_padicValNat_eq (a b : Nat) (ha : a != 0) (hb : b != 0) : a = 
b ↔ forall p : Nat, p.Prime -> padicValNat p a = padicValNat p b
参数：a b : Nat；ha : a != 0；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.eq_of_factorization_eq`：eq_of_factorization_eq {a b : Nat} (ha : a !
= 0) (hb : b != 0) (h : forall p : Nat, a.factorization p = b.factorization p) :
 a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_def`：factorization_def (n : Nat) {p : Nat} (pp : p.Pri
me) : n.factorization p = padicValNat p n
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Two positive naturals are equal if their prime padic valuations are equal
-/
theorem eq_iff_prime_padicValNat_eq (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a = b ↔ ∀ p : ℕ, p.Prime → padicValNat p a = padicValNat p b := by
  constructor
  · rintro rfl
    simp
  · intro h
    refine eq_of_factorization_eq ha hb fun p => ?_
    by_cases pp : p.Prime
    · simp [factorization_def, pp, h p pp]
    · simp [factorization_eq_zero_of_not_prime, pp]
/-
**Nat.prod_pow_prime_padicValNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_pow_prime_padicValNat (n : Nat) (hn : n != 0) (m : Nat) (pr : n < m) 
: ∏ p in range m with p.Prime, p ^ padicValNat p n = n
参数：n : Nat；hn : n != 0；m : Nat；pr : n < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.prod_subset_one_on_sdiff`：prod_subset_one_on_sdiff [DecidableEq ι
] (h : s₁ subseteq s₂) (hg : forall x in s₂ \ s₁, g x = 1) (hfg : forall x in s₁
, f x = g x) : ∏ i in…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用引理 `Nat.le_of_mem_primeFactors`：le_of_mem_primeFactors (h : p in n.primeFact
ors) : p <= n
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `Nat.factorization_def`：factorization_def (n : Nat) {p : Nat} (pp : p.Pri
me) : n.factorization p = padicValNat p n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_pow_prime_padicValNat (n : Nat) (hn : n ≠ 0) (m : Nat) (pr : n < m) :
    ∏ p ∈ range m with p.Prime, p ^ padicValNat p n = n := by
  nth_rw 2 [← prod_factorization_pow_eq_self hn]
  rw [eq_comm]
  apply Finset.prod_subset_one_on_sdiff
  · exact fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_range.2 <| pr.trans_le' <|
      le_of_mem_primeFactors hp, prime_of_mem_primeFactors hp⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
    rw [← factorization_def n (Finset.mem_filter.mp hp1).2]
    simp [Finsupp.notMem_support_iff.mp hp2]
  · intro p hp
    simp [factorization_def n (prime_of_mem_primeFactors hp)]
/-
**Nat.prod_primeFactors_pow_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_primeFactors_pow_factorization (hn : n != 0) : n = ∏ p in n.primeFact
ors, p ^ n.factorization p
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用引理 `Nat.prod_factorization_eq_prod_primeFactors`：prod_factorization_eq_prod_
primeFactors {β : Type*} [CommMonoid β] (f : Nat -> Nat -> β) : n.factorization.
prod f = ∏ p in n.primeFactors, f…
-/
theorem prod_primeFactors_pow_factorization (hn : n ≠ 0) :
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
  prod_factorization_pow_eq_self hn |>.symm.trans <| prod_factorization_eq_prod_primeFactors _
/-
**Nat.prod_primeFactors_coe_pow_factorization** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prod_primeFactors_coe_pow_factorization (hn : n != 0) : n = ∏ (p : n.prime
Factors), (p : Nat) ^ (n.factorization p)
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.prod_attach_index`：prod_attach_index [CommMonoid N] {s : Finset 
α} (f : α -> M) {h : α -> M -> N} : ∏ x in s.attach, h x (f x) = ∏ x in s, h x (
f x)
· 使用定理 `Nat.prod_primeFactors_pow_factorization`：prod_primeFactors_pow_factoriza
tion (hn : n != 0) : n = ∏ p in n.primeFactors, p ^ n.factorization p
-/
lemma prod_primeFactors_coe_pow_factorization (hn : n ≠ 0) :
    n = ∏ (p : n.primeFactors), (p : ℕ) ^ (n.factorization p) := by
  simpa using prod_primeFactors_pow_factorization hn

@[deprecated (since := "2026-06-24")]
alias prod_pow_primeFactors_factorization := prod_primeFactors_coe_pow_factorization
/-
**Nat.pairwise_coprime_pow_primeFactors_factorization** 是 Mathlib 中的一个引理，位于命名空间 
`Nat`。
形式化陈述：pairwise_coprime_pow_primeFactors_factorization : Pairwise (Function.onFun
 Nat.Coprime fun (p : n.primeFactors) => p ^ n.factorization p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.pow`：∀ {k l : ℕ} (m n : ℕ), k.Coprime l → (k ^ m).Coprime (l
 ^ n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_primes`：coprime_primes {p q : Nat} (pp : Prime p) (pq : Prim
e q) : Coprime p q ↔ p != q
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
-/
lemma pairwise_coprime_pow_primeFactors_factorization :
    Pairwise (Function.onFun Nat.Coprime fun (p : n.primeFactors) ↦ p ^ n.factorization p) := by
  intro p1 p2 hp
  refine Nat.Coprime.pow (n.factorization p1) (n.factorization p2) ?_
  refine (Nat.coprime_primes ?_ ?_).mpr <| Subtype.coe_ne_coe.mpr hp
  · exact Nat.prime_of_mem_primeFactors p1.2
  · exact Nat.prime_of_mem_primeFactors p2.2
/-
**Nat.dvd_prod_primeFactors_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_prod_primeFactors_pow_self {n : Nat} (hn : n != 0) : n ∣ (∏ p in n.pri
meFactors, p) ^ n
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_pow`：prod_pow (s : Finset ι) (n : Nat) (f : ι -> M) : ∏ x in
 s, f x ^ n = (∏ x in s, f x) ^ n
· 使用定理 `Nat.prod_primeFactors_pow_factorization`：prod_primeFactors_pow_factoriza
tion (hn : n != 0) : n = ∏ p in n.primeFactors, p ^ n.factorization p
· 使用引理 `Finset.prod_dvd_prod_of_dvd`：prod_dvd_prod_of_dvd (f g : ι -> M) (h : fo
rall i in s, f i ∣ g i) : ∏ i in s, f i ∣ ∏ i in s, g i
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Nat.factorization_def`：factorization_def (n : Nat) {p : Nat} (pp : p.Pri
me) : n.factorization p = padicValNat p n
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Nat.padicValNat_le_self`：padicValNat_le_self {p : Nat} (n : Nat) : padic
ValNat p n <= n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem dvd_prod_primeFactors_pow_self {n : ℕ} (hn : n ≠ 0) :
    n ∣ (∏ p ∈ n.primeFactors, p) ^ n := by
  nth_rw 1 [← Finset.prod_pow, prod_primeFactors_pow_factorization hn]
  refine prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow i ?_
  grw [n.factorization_def <| prime_of_mem_primeFactors hi, padicValNat_le_self]
/-
**Nat.dvd_pow_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_pow_self_iff {n k : Nat} (hn : n != 0) (hk : k != 0) : n ∣ k ^ n ↔ n.p
rimeFactors subseteq k.primeFactors
参数：hn : n != 0；hk : k != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.primeFactors_pow`：primeFactors_pow (n : Nat) (hk : k != 0) : (n ^ k)
.primeFactors = n.primeFactors
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Nat.primeFactors_mono`：primeFactors_mono (hmn : m ∣ n) (hn : n != 0) : p
rimeFactors m subseteq primeFactors n
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransDvd`：∀ {α : Type u_1} [inst : Semigroup α], IsTrans α Dvd.dvd
· 使用定理 `Nat.dvd_prod_primeFactors_pow_self`：dvd_prod_primeFactors_pow_self {n : 
Nat} (hn : n != 0) : n ∣ (∏ p in n.primeFactors, p) ^ n
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用引理 `pow_dvd_pow_of_dvd_of_le`：pow_dvd_pow_of_dvd_of_le {m n : Nat} (hab : a 
∣ b) (hmn : m <= n) : a ^ m ∣ b ^ n
· 使用定理 `Finset.prod_dvd_prod_of_subset`：prod_dvd_prod_of_subset {ι M : Type*} [C
ommMonoid M] (s t : Finset ι) (f : ι -> M) (h : s subseteq t) : (∏ i in s, f i) 
∣ ∏ i in t, f i
· 使用定理 `Nat.prod_primeFactors_dvd`：prod_primeFactors_dvd (n : Nat) : ∏ p in n.pr
imeFactors, p ∣ n
-/
theorem dvd_pow_self_iff {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    n ∣ k ^ n ↔ n.primeFactors ⊆ k.primeFactors := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · grw [← Nat.primeFactors_pow k hn, Nat.primeFactors_mono h <| pow_ne_zero n hk]
  · grw [dvd_prod_primeFactors_pow_self hn, prod_dvd_prod_of_subset _ _ _ h, prod_primeFactors_dvd]
/-
**Nat.exists_dvd_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_dvd_pow_iff {n k : Nat} (hn : n != 0) (hk : k != 0) : (exists m, n 
∣ k ^ m) ↔ n.primeFactors subseteq k.primeFactors
参数：hn : n != 0；hk : k != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.primeFactors_one`：Nat.primeFactors 1 = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.primeFactors_pow`：primeFactors_pow (n : Nat) (hk : k != 0) : (n ^ k)
.primeFactors = n.primeFactors
· 使用引理 `Nat.primeFactors_mono`：primeFactors_mono (hmn : m ∣ n) (hn : n != 0) : p
rimeFactors m subseteq primeFactors n
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.dvd_pow_self_iff`：dvd_pow_self_iff {n k : Nat} (hn : n != 0) (hk : k
 != 0) : n ∣ k ^ n ↔ n.primeFactors subseteq k.primeFactors
-/
theorem exists_dvd_pow_iff {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (∃ m, n ∣ k ^ m) ↔ n.primeFactors ⊆ k.primeFactors := by
  refine ⟨fun ⟨m, h⟩ ↦ ?_, fun h ↦ ⟨n, dvd_pow_self_iff hn hk |>.mpr h⟩⟩
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp_all
  rw [← Nat.primeFactors_pow k hm]
  exact Nat.primeFactors_mono h <| pow_ne_zero m hk

/-! ### Lemmas about factorizations of particular functions -/

/-- Exactly `n / p` naturals in `[1, n]` are multiples of `p`.
See `Nat.card_multiples'` for an alternative spelling of the statement. -/
/-
**Nat.card_multiples** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_multiples (n p : Nat) : #{e in range n | p ∣ e + 1} = n / p
参数：n p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.succ_div`：∀ {a b : ℕ}, (a + 1) / b = a / b + if b ∣ a + 1 then 1 els
e 0
· 使用定理 `add_ite`：∀ {α : Type u_2} (P : Prop) [inst : Decidable P] [inst_1 : Add 
α] (a b c : α),   (a + if P then b else c) = if P then a + b else a + c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
Exactly `n / p` naturals in `[1, n]` are multiples of `p`.
See `Nat.card_multiples'` for an alternative spelling of the statement.
-/
theorem card_multiples (n p : ℕ) : #{e ∈ range n | p ∣ e + 1} = n / p := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp [Nat.succ_div, add_ite, add_zero, Finset.range_add_one, filter_insert, apply_ite card,
      card_insert_of_notMem, hn]

/-- Exactly `n / p` naturals in `(0, n]` are multiples of `p`. -/
/-
**Nat.Ioc_filter_dvd_card_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ioc_filter_dvd_card_eq_div (n p : Nat) : #{x in Ioc 0 n | p ∣ x} = n / p
参数：n p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.Ioc_eq_empty_of_le`：Ioc_eq_empty_of_le (h : b <= a) : Ioc a b = ∅
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.succ_div`：∀ {a b : ℕ}, (a + 1) / b = a / b + if b ∣ a + 1 then 1 els
e 0
· 使用定理 `add_ite`：∀ {α : Type u_2} (P : Prop) [inst : Decidable P] [inst_1 : Add 
α] (a b c : α),   (a + if P then b else c) = if P then a + b else a + c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
Exactly `n / p` naturals in `(0, n]` are multiples of `p`.
-/
theorem Ioc_filter_dvd_card_eq_div (n p : ℕ) : #{x ∈ Ioc 0 n | p ∣ x} = n / p := by
  induction n <;> simp [Nat.succ_div, add_ite, ← insert_Ioc_right_eq_Ioc_add_one, filter_insert,
    apply_ite card, *]

/-- There are exactly `⌊N/n⌋` positive multiples of `n` that are `≤ N`.
See `Nat.card_multiples` for a "shifted-by-one" version. -/
/-
**Nat.card_multiples'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：card_multiples' (N n : Nat) : #{k in range N.succ | k != 0 ∧ n ∣ k} = N / 
n
参数：N n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_false_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (∀ x ∈ s, ¬p x) → Finset.filter p s = ∅
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Nat.succ_div_of_dvd`：∀ {a b : ℕ}, b ∣ a + 1 → (a + 1) / b = a / b + 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.succ_div_of_not_dvd`：∀ {a b : ℕ}, ¬b ∣ a + 1 → (a + 1) / b = a / b

--- 原说明 ---
There are exactly `⌊N/n⌋` positive multiples of `n` that are `≤ N`.
See `Nat.card_multiples` for a "shifted-by-one" version.
-/
lemma card_multiples' (N n : ℕ) : #{k ∈ range N.succ | k ≠ 0 ∧ n ∣ k} = N / n := by
  induction N with
  | zero => simp [Finset.filter_false_of_mem]
  | succ N ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : n ∣ N.succ
    · simp [h, succ_div_of_dvd, ih]
    · simp [h, succ_div_of_not_dvd, ih]
/-
**Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 
`Nat`。
形式化陈述：exists_eq_pow_of_exponent_coprime_of_pow_eq_pow {a b m n : Nat} (hmn : m.C
oprime n) (h : a ^ m = b ^ n) : exists c, a = c ^ n ∧ b = c ^ m
参数：hmn : m.Coprime n；h : a ^ m = b ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `Nat.eq_of_factorization_eq`：eq_of_factorization_eq {a b : Nat} (ha : a !
= 0) (hb : b != 0) (h : forall p : Nat, a.factorization p = b.factorization p) :
 a = b
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.factorization_zero_right`：factorization_zero_right (n : Nat) : n.fac
torization 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `Finsupp.support_mapRange`：support_mapRange {f : M -> N} {hf : f 0 = 0} {
g : α ->₀ M} : (mapRange f hf g).support subseteq g.support
· 使用定理 `Nat.factorization_pow`：factorization_pow (n k : Nat) : factorization (n 
^ k) = k • n.factorization
· 使用定理 `Nat.prod_pow_factorization_eq_self`：prod_pow_factorization_eq_self (hf :
 forall p in f.support, Prime p) : (f.prod (· ^ ·)).factorization = f
（共 35 条，此处仅展示前 30 条）
-/
theorem exists_eq_pow_of_exponent_coprime_of_pow_eq_pow
    {a b m n : ℕ} (hmn : m.Coprime n) (h : a ^ m = b ^ n) :
    ∃ c, a = c ^ n ∧ b = c ^ m := by
  by_cases ha0 : a = 0
  · symm at h
    by_cases hm0 : m = 0
    · simp_all
    · use 0
      simp_all
  by_cases hn0 : n = 0
  · use b
    simp_all
  let factors := a.factorization.mapRange (· / n) (Nat.zero_div n)
  set c := factors.prod (· ^ ·) with hc
  use c
  suffices ha : a = c ^ n by
    refine ⟨ha, ?_⟩
    apply Nat.pow_left_injective hn0
    simp [← h, ha, Nat.pow_right_comm]
  apply eq_of_factorization_eq ha0 (by simp [c, factors])
  intro p
  have foo (p) (hp : p ∈ factors.support) : Prime p :=
    prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  rw [factorization_pow, hc, prod_pow_factorization_eq_self foo]
  suffices n ∣ a.factorization p by
    simp [factors, Nat.mul_div_cancel' this]
  refine hmn.symm.dvd_of_dvd_mul_left ⟨b.factorization p, ?_⟩
  simpa using congr(factorization $h p)
/-
**Nat.exists_eq_pow_of_pow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_eq_pow_of_pow_eq_pow {a b m n : Nat} (hmn : m != 0 ∨ n != 0) (h : a
 ^ m = b ^ n) : letI g
参数：hmn : m != 0 ∨ n != 0；h : a ^ m = b ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_div_gcd_div_gcd_of_pos_left`：∀ {n m : ℕ}, 0 < n → (n / n.gcd m).
gcd (m / n.gcd m) = 1
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `Nat.gcd_div_gcd_div_gcd_of_pos_right`：∀ {n m : ℕ}, 0 < m → (n / n.gcd m)
.gcd (m / n.gcd m) = 1
· 使用定理 `Nat.gcd_ne_zero_left`：∀ {m n : ℕ}, m ≠ 0 → m.gcd n ≠ 0
· 使用定理 `Nat.gcd_ne_zero_right`：∀ {n m : ℕ}, n ≠ 0 → m.gcd n ≠ 0
· 使用引理 `Nat.pow_left_injective`：pow_left_injective (hn : n != 0) : Injective (fu
n a : Nat => a ^ n)
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow`：exists_eq_pow_of_ex
ponent_coprime_of_pow_eq_pow {a b m n : Nat} (hmn : m.Coprime n) (h : a ^ m = b 
^ n) : exists c, a = c ^ n ∧ b = c ^ m
-/
theorem exists_eq_pow_of_pow_eq_pow
    {a b m n : ℕ} (hmn : m ≠ 0 ∨ n ≠ 0) (h : a ^ m = b ^ n) :
    letI g := gcd m n; ∃ c, a = c ^ (n / g) ∧ b = c ^ (m / g) := by
  set g := gcd m n
  let m' := m / gcd m n
  let n' := n / gcd m n
  have coprime : m'.Coprime n' := by
    rcases hmn with hm | hn
    · exact gcd_div_gcd_div_gcd_of_pos_left (zero_lt_of_ne_zero hm)
    · exact gcd_div_gcd_div_gcd_of_pos_right (zero_lt_of_ne_zero hn)
  have pow_eq : a ^ m' = b ^ n' := by
    conv_lhs at h => rw [show m = m' * g from (Nat.div_mul_cancel (gcd_dvd_left m n)).symm]
    conv_rhs at h => rw [show n = n' * g from (Nat.div_mul_cancel (gcd_dvd_right m n)).symm]
    rw [pow_mul, pow_mul] at h
    have : g ≠ 0 := by
      rcases hmn with hm | hn
      · exact gcd_ne_zero_left hm
      · exact gcd_ne_zero_right hn
    exact Nat.pow_left_injective this h
  exact exists_eq_pow_of_exponent_coprime_of_pow_eq_pow coprime pow_eq

end Nat

