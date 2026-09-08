/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
module

public import Batteries.Data.List.Count
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# Prime factorizations

`n.factorization` is the finitely supported function `ℕ →₀ ℕ`
mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
* `factorization 2000 2` is 4
* `factorization 2000 5` is 3
* `factorization 2000 k` is 0 for all other `k : ℕ`.

## TODO

* As discussed in this Zulip thread:
  https://leanprover.zulipchat.com/#narrow/stream/217875/topic/Multiplicity.20in.20the.20naturals
  We have lots of disparate ways of talking about the multiplicity of a prime
  in a natural number, including `factors.count`, `padicValNat`, `multiplicity`,
  and the material in `Data/PNat/Factors`.  Move some of this material to this file,
  prove results about the relationships between these definitions,
  and (where appropriate) choose a uniform canonical way of expressing these ideas.

* Moreover, the results here should be generalised to an arbitrary unique factorization monoid
  with a normalization function, and then deduplicated.  The basics of this have been started in
  `Mathlib/RingTheory/UniqueFactorizationDomain/`.

* Extend the inductions to any `NormalizationMonoid` with unique factorization.

-/

@[expose] public section

open Nat Finset List Finsupp

namespace Nat
variable {a b m n p : ℕ}

/-- `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
mapping each prime factor of `n` to its multiplicity in `n`. -/
/-
**Nat.factorization** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：factorization (n : Nat) : Nat ->₀ Nat where support
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n.factorization` is the finitely supported function `ℕ →₀ ℕ`
mapping each prime factor of `n` to its multiplicity in `n`.
-/
def factorization (n : ℕ) : ℕ →₀ ℕ where
  support := n.primeFactors
  toFun p := if p.Prime then padicValNat p n else 0
  mem_support_toFun := by simp [not_or]; aesop

/-- The support of `n.factorization` is exactly `n.primeFactors`. -/
/-
**Nat.support_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), n.factorization.support = n.primeFactors
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of `n.factorization` is exactly `n.primeFactors`.
-/
@[simp] lemma support_factorization (n : ℕ) : (factorization n).support = n.primeFactors := rfl
/-
**Nat.factorization_def** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_def (n : Nat) {p : Nat} (pp : p.Prime) : n.factorization p =
 padicValNat p n
参数：n : Nat；pp : p.Prime。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of `n.factorization` is exactly `n.primeFactors`.
-/
theorem factorization_def (n : ℕ) {p : ℕ} (pp : p.Prime) : n.factorization p = padicValNat p n := by
  simpa [factorization] using absurd pp

/-- We can write both `n.factorization p` and `n.factors.count p` to represent the power
of `p` in the factorization of `n`: we declare the former to be the simp-normal form. -/
@[simp]
/-
**Nat.primeFactorsList_count_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_count_eq {n p : Nat} : n.primeFactorsList.count p = n.fac
torization p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Nat.primeFactors_zero`：Nat.primeFactors 0 = ∅
· 使用定理 `Finsupp.mk.congr_simp`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero M] 
(support support_1 : Finset α) (e_support : support = support_1)   (toFun toFun_
1 : α → M) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_def`：factorization_def (n : Nat) {p : Nat} (pp : p.Pri
me) : n.factorization p = padicValNat p n
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_padicValNat_iff_replicate_subperm_primeFactorsList`：le_padicValNat_if
f_replicate_subperm_primeFactorsList {a b : Nat} {n : Nat} (ha : a.Prime) (hb : 
b != 0) : n <= padicValNat a b ↔ replicate …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.replicate_sublist_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α
] {n : ℕ} {a : α} {l : List α},   (List.replicate n a).Sublist l ↔ n ≤ List.coun
t a l
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `List.Subperm.count_le`：∀ {α : Type u_1} [inst : BEq α] {l₁ l₂ : List α},
 l₁.Subperm l₂ → ∀ (a : α), List.count a l₁ ≤ List.count a l₂
· 使用定理 `List.count_replicate_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α]
 {a : α} {n : ℕ}, List.count a (List.replicate n a) = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
We can write both `n.factorization p` and `n.factors.count p` to represent the p
ower
of `p` in the factorization of `n`: we declare the former to be the simp-normal 
form.
-/
theorem primeFactorsList_count_eq {n p : ℕ} : n.primeFactorsList.count p = n.factorization p := by
  rcases n.eq_zero_or_pos with (rfl | hn0)
  · simp [factorization, count]
  if pp : p.Prime then ?_ else
    rw [count_eq_zero_of_not_mem (mt prime_of_mem_primeFactorsList pp)]
    simp [factorization, pp]
  simp only [factorization_def _ pp]
  apply _root_.le_antisymm
  · rw [le_padicValNat_iff_replicate_subperm_primeFactorsList pp hn0.ne']
    exact List.replicate_sublist_iff.mpr le_rfl |>.subperm
  · rw [← Nat.lt_add_one_iff, lt_iff_not_ge,
      le_padicValNat_iff_replicate_subperm_primeFactorsList pp hn0.ne']
    intro h
    have := h.count_le p
    simp at this
/-
**Nat.factorization_eq_primeFactorsList_multiset** 是 Mathlib 中的一个定理，位于命名空间 `Nat`
。
形式化陈述：factorization_eq_primeFactorsList_multiset (n : Nat) : n.factorization = M
ultiset.toFinsupp (n.primeFactorsList : Multiset Nat)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `Nat.primeFactorsList_count_eq`：primeFactorsList_count_eq {n p : Nat} : n
.primeFactorsList.count p = n.factorization p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorization_eq_primeFactorsList_multiset (n : ℕ) :
    n.factorization = Multiset.toFinsupp (n.primeFactorsList : Multiset ℕ) := by
  ext p
  simp
/-
**Nat.Prime.factorization_pos_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {n p : ℕ}, Nat.Prime p → n ≠ 0 → p ∣ n → 0 < n.factorization p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.primeFactorsList_count_eq`：primeFactorsList_count_eq {n p : Nat} : n
.primeFactorsList.count p = n.factorization p
· 使用定理 `List.count_pos_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, 0 < List.count a l ↔ a ∈ l
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `Nat.mem_primeFactorsList_iff_dvd`：mem_primeFactorsList_iff_dvd {n p : Na
t} (hn : n != 0) (hp : Prime p) : p in primeFactorsList n ↔ p ∣ n where mp h
-/
theorem Prime.factorization_pos_of_dvd {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ∣ n) :
    0 < n.factorization p := by
  rwa [← primeFactorsList_count_eq, count_pos_iff, mem_primeFactorsList_iff_dvd hn hp]
/-
**Nat.multiplicity_eq_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multiplicity_eq_factorization {n p : Nat} (pp : p.Prime) (hn : n != 0) : m
ultiplicity p n = n.factorization p
参数：pp : p.Prime；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `padicValNat_def'`：padicValNat_def' {n : Nat} (hp : p != 1) (hn : n != 0)
 : padicValNat p n = multiplicity p n
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem multiplicity_eq_factorization {n p : ℕ} (pp : p.Prime) (hn : n ≠ 0) :
    multiplicity p n = n.factorization p := by
  simp [factorization, pp, padicValNat_def' pp.ne_one hn]

/-! ### Basic facts about factorization -/


@[simp]
/-
**Nat.prod_factorization_pow_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_factorization_pow_eq_self {n : Nat} (hn : n != 0) : n.factorization.p
rod (· ^ ·) = n
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_eq_primeFactorsList_multiset`：factorization_eq_primeFa
ctorsList_multiset (n : Nat) : n.factorization = Multiset.toFinsupp (n.primeFact
orsList : Multiset Nat)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.toFinsupp_toMultiset`：toFinsupp_toMultiset (s : Multiset α) : F
insupp.toMultiset (toFinsupp s) = s
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m

--- 原说明 ---
### Basic facts about factorization
-/
theorem prod_factorization_pow_eq_self {n : ℕ} (hn : n ≠ 0) : n.factorization.prod (· ^ ·) = n := by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp only [← prod_toMultiset, Multiset.prod_coe, Multiset.toFinsupp_toMultiset]
  exact prod_primeFactorsList hn

@[deprecated (since := "2026-03-19")]
alias factorization_prod_pow_eq_self := prod_factorization_pow_eq_self
/-
**Nat.eq_of_factorization_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_of_factorization_eq {a b : Nat} (ha : a != 0) (hb : b != 0) (h : forall
 p : Nat, a.factorization p = b.factorization p) : a = b
参数：ha : a != 0；hb : b != 0；h : forall p : Nat, a.factorization p = b.factorizati
on p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_of_perm_primeFactorsList`：eq_of_perm_primeFactorsList {a b : Nat}
 (ha : a != 0) (hb : b != 0) (h : a.primeFactorsList ~ b.primeFactorsList) : a =
 b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_count_eq`：primeFactorsList_count_eq {n p : Nat} : n
.primeFactorsList.count p = n.factorization p
-/
theorem eq_of_factorization_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, a.factorization p = b.factorization p) : a = b :=
  eq_of_perm_primeFactorsList ha hb
    (by simpa only [List.perm_iff_count, primeFactorsList_count_eq] using h)
/-
**Nat.eq_of_factorization_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_of_factorization_eq' {a b : Nat} (ha : a != 0) (hb : b != 0) (h : a.fac
torization = b.factorization) : a = b
参数：ha : a != 0；hb : b != 0；h : a.factorization = b.factorization。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_of_factorization_eq`：eq_of_factorization_eq {a b : Nat} (ha : a !
= 0) (hb : b != 0) (h : forall p : Nat, a.factorization p = b.factorization p) :
 a = b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem eq_of_factorization_eq' {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.factorization = b.factorization) : a = b :=
  eq_of_factorization_eq ha hb (congrFun (congrArg DFunLike.coe h))


/-- Every nonzero natural number has a unique prime factorization -/
/-
**Nat.factorization_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_inj : Set.InjOn factorization { x : Nat | x != 0 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_of_factorization_eq`：eq_of_factorization_eq {a b : Nat} (ha : a !
= 0) (hb : b != 0) (h : forall p : Nat, a.factorization p = b.factorization p) :
 a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Every nonzero natural number has a unique prime factorization
-/
theorem factorization_inj : Set.InjOn factorization { x : ℕ | x ≠ 0 } := fun a ha b hb h =>
  eq_of_factorization_eq ha hb fun p => by simp [h]

@[simp]
/-
**Nat.factorization_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_zero : factorization 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Nat.primeFactors_zero`：Nat.primeFactors 0 = ∅
· 使用定理 `Finsupp.mk.congr_simp`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero M] 
(support support_1 : Finset α) (e_support : support = support_1)   (toFun toFun_
1 : α → M) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorization_zero : factorization 0 = 0 := by ext; simp [factorization]

@[simp]
/-
**Nat.factorization_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_one : factorization 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Nat.primeFactors_one`：Nat.primeFactors 1 = ∅
· 使用定理 `Finsupp.mk.congr_simp`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero M] 
(support support_1 : Finset α) (e_support : support = support_1)   (toFun toFun_
1 : α → M) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorization_one : factorization 1 = 0 := by ext; simp [factorization]

/-! ## Lemmas characterising when `n.factorization p = 0` -/

/-
**Nat.factorization_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_zero_iff (n p : Nat) : n.factorization p = 0 ↔ ¬p.Prime ∨
 ¬p ∣ n ∨ n = 0
参数：n p : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
## Lemmas characterising when `n.factorization p = 0`
-/
theorem factorization_eq_zero_iff (n p : ℕ) :
    n.factorization p = 0 ↔ ¬p.Prime ∨ ¬p ∣ n ∨ n = 0 := by
  simp_rw [← notMem_support_iff, support_factorization, mem_primeFactors, not_and_or, not_ne_iff]

@[simp]
/-
**Nat.factorization_eq_zero_of_not_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_zero_of_not_prime (n : Nat) {p : Nat} (hp : ¬p.Prime) : n
.factorization p = 0
参数：n : Nat；hp : ¬p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem factorization_eq_zero_of_not_prime (n : ℕ) {p : ℕ} (hp : ¬p.Prime) :
    n.factorization p = 0 := by simp [factorization_eq_zero_iff, hp]

@[simp]
/-
**Nat.factorization_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_zero_right (n : Nat) : n.factorization 0 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `Nat.not_prime_zero`：¬Nat.Prime 0
-/
theorem factorization_zero_right (n : ℕ) : n.factorization 0 = 0 :=
  factorization_eq_zero_of_not_prime _ not_prime_zero

@[simp]
/-
**Nat.factorization_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_one_right (n : Nat) : n.factorization 1 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `Nat.not_prime_one`：¬Nat.Prime 1
-/
theorem factorization_one_right (n : ℕ) : n.factorization 1 = 0 :=
  factorization_eq_zero_of_not_prime _ not_prime_one
/-
**Nat.factorization_eq_zero_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_zero_of_not_dvd {n p : Nat} (h : ¬p ∣ n) : n.factorizatio
n p = 0
参数：h : ¬p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem factorization_eq_zero_of_not_dvd {n p : ℕ} (h : ¬p ∣ n) : n.factorization p = 0 := by
  simp [factorization_eq_zero_iff, h]
/-
**Nat.factorization_eq_zero_of_remainder** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_zero_of_remainder {p r : Nat} (i : Nat) (hr : ¬p ∣ r) : (
p * i + r).factorization p = 0
参数：i : Nat；hr : ¬p ∣ r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorization_eq_zero_of_not_dvd`：factorization_eq_zero_of_not_dvd {
n p : Nat} (h : ¬p ∣ n) : n.factorization p = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_add_iff_right`：∀ {k m n : ℕ}, k ∣ m → (k ∣ n ↔ k ∣ m + n)
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
-/
theorem factorization_eq_zero_of_remainder {p r : ℕ} (i : ℕ) (hr : ¬p ∣ r) :
    (p * i + r).factorization p = 0 := by
  apply factorization_eq_zero_of_not_dvd
  rwa [← Nat.dvd_add_iff_right (Dvd.intro i rfl)]

/-! ## Lemmas about factorizations of products and powers -/

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp]
/-
**Nat.factorization_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_mul {a b : Nat} (ha : a != 0) (hb : b != 0) : (a * b).factor
ization = a.factorization + b.factorization
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.perm_iff_count`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l₁ l
₂ : List α},   l₁.Perm l₂ ↔ ∀ (a : α), List.count a l₁ = List.count a l₂
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `Nat.perm_primeFactorsList_mul`：perm_primeFactorsList_mul {a b : Nat} (ha
 : a != 0) (hb : b != 0) : (a * b).primeFactorsList ~ a.primeFactorsList ++ b.pr
imeFactorsList
· 使用定理 `List.count_append`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l₁ l₂ : List
 α}, List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in
 `a` and `b`
-/
theorem factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext p
  simp only [add_apply, ← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul ha hb) p, count_append]
/-
**Nat.factorization_le_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_le_iff_dvd {d n : Nat} (hd : d != 0) (hn : n != 0) : d.facto
rization <= n.factorization ↔ d ∣ n
参数：hd : d != 0；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `Finsupp.prod_dvd_prod_of_subset_of_dvd`：prod_dvd_prod_of_subset_of_dvd [
Zero M] [CommMonoid N] {f1 f2 : α ->₀ M} {g1 g2 : α -> M -> N} (h1 : f1.support 
subseteq f2.support) (h2 : f…
· 使用引理 `Finsupp.support_mono`：support_mono (hfg : f <= g) : f.support subseteq g
.support
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem factorization_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    d.factorization ≤ n.factorization ↔ d ∣ n := by
  refine ⟨fun hdn ↦ ?_, fun ⟨c, h⟩ ↦ ?_⟩
  · rw [← prod_factorization_pow_eq_self hn, ← prod_factorization_pow_eq_self hd]
    exact prod_dvd_prod_of_subset_of_dvd (support_mono hdn) fun a _ ↦ pow_dvd_pow a (hdn a)
  · subst h
    rw [factorization_mul hd <| right_ne_zero_of_mul hn]
    apply self_le_add_right

/-- For any `p : ℕ` and any function `g : α → ℕ` that's non-zero on `S : Finset α`,
the power of `p` in `S.prod g` equals the sum over `x ∈ S` of the powers of `p` in `g x`.
Generalises `factorization_mul`, which is the special case where `#S = 2` and `g = id`. -/
/-
**Nat.factorization_prod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_prod {α : Type*} {S : Finset α} {g : α -> Nat} (hS : forall 
x in S, g x != 0) : (S.prod g).factorization = S.sum fun x => (g x).factorizatio
n
参数：hS : forall x in S, g x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on'`：induction_on' {α : Type*} {motive : Finset α -> Pr
op} [DecidableEq α] (S : Finset α) (empty : motive ∅) (insert : forall (a s), a 
in S -> s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_one`：factorization_one : factorization 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…

--- 原说明 ---
For any `p : ℕ` and any function `g : α → ℕ` that's non-zero on `S : Finset α`,
the power of `p` in `S.prod g` equals the sum over `x ∈ S` of the powers of `p` 
in `g x`.
Generalises `factorization_mul`, which is the special case where `#S = 2` and `g
 = id`.
-/
theorem factorization_prod {α : Type*} {S : Finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) :
    (S.prod g).factorization = S.sum fun x => (g x).factorization := by
  classical
    refine Finset.induction_on' S ?_ ?_
    · simp
    · intro x T hxS hTS hxT IH
      have hT : T.prod g ≠ 0 := prod_ne_zero_iff.mpr fun x hx => hS x (hTS hx)
      simp [prod_insert hxT, sum_insert hxT, IH, factorization_mul (hS x hxS) hT]

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
@[simp]
/-
**Nat.factorization_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_pow (n k : Nat) : factorization (n ^ k) = k • n.factorizatio
n
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.factorization_one`：factorization_one : factorization 1 = 0
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
For any `p`, the power of `p` in `n^k` is `k` times the power in `n`
-/
theorem factorization_pow (n k : ℕ) : factorization (n ^ k) = k • n.factorization := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases eq_or_ne n 0 with (rfl | hn)
    · simp
    rw [Nat.pow_succ, mul_comm, factorization_mul hn (pow_ne_zero _ hn), ih,
      add_smul, one_smul, add_comm]

/-! ## Lemmas about factorizations of primes and prime powers -/


/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp]
/-
**Nat.Prime.factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p.factorization = fun₀ | p => 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.primeFactorsList_count_eq`：primeFactorsList_count_eq {n p : Nat} : n
.primeFactorsList.count p = n.factorization p
· 使用定理 `Nat.primeFactorsList_prime`：primeFactorsList_prime {p : Nat} (hp : Nat.P
rime p) : p.primeFactorsList = [p]
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `List.count_singleton'`：∀ {α : Type u_1} [inst : DecidableEq α] (a b : α)
, List.count a [b] = if b = a then 1 else 0
· 使用定理 `if_congr`：if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y
 = ite Q u v
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a

--- 原说明 ---
The only prime factor of prime `p` is `p` itself, with multiplicity `1`
-/
protected theorem Prime.factorization {p : ℕ} (hp : Prime p) : p.factorization = single p 1 := by
  ext q
  rw [← primeFactorsList_count_eq, primeFactorsList_prime hp, single_apply, count_singleton',
    if_congr eq_comm] <;> rfl

/-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
/-
**Nat.Prime.factorization_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p k : ℕ}, Nat.Prime p → (p ^ k).factorization = fun₀ | p => k
参数：p ^ k。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k`
-/
theorem Prime.factorization_pow {p k : ℕ} (hp : Prime p) : (p ^ k).factorization = single p k := by
  simp [hp]
/-
**Nat.pow_succ_factorization_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_succ_factorization_not_dvd {n p : Nat} (hn : n != 0) (hp : p.Prime) : 
¬p ^ (n.factorization p + 1) ∣ n
参数：hn : n != 0；hp : p.Prime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
-/
theorem pow_succ_factorization_not_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    ¬p ^ (n.factorization p + 1) ∣ n := by
  intro h
  rw [← factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) hn] at h
  simpa [hp.factorization] using h p
/-
**Nat.factorization_minFac_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factorization_minFac_ne_zero {n : Nat} (hn : 1 < n) : n.factorization n.mi
nFac != 0
参数：hn : 1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.factorization_eq_zero_iff`：factorization_eq_zero_iff (n p : Nat) : n
.factorization p = 0 ↔ ¬p.Prime ∨ ¬p ∣ n ∨ n = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
-/
lemma factorization_minFac_ne_zero {n : ℕ} (hn : 1 < n) :
    n.factorization n.minFac ≠ 0 := by
  refine mt (factorization_eq_zero_iff _ _).mp ?_
  push Not
  exact ⟨minFac_prime (by lia), minFac_dvd n, Nat.ne_zero_of_lt hn⟩

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/

variable {f : ℕ →₀ ℕ}

-- TODO: Rename to `factorization_prod_pow_eq_self`
/-- Any Finsupp `f : ℕ →₀ ℕ` whose support is in the primes is equal to the factorization of
the product `∏ (a : ℕ) ∈ f.support, a ^ f a`. -/
/-
**Nat.prod_pow_factorization_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_pow_factorization_eq_self (hf : forall p in f.support, Prime p) : (f.
prod (· ^ ·)).factorization = f
参数：hf : forall p in f.support, Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : CommMonoid N] (f : α →₀ M) (g : α → M → N),   f.prod g = ∏ 
a ∈ f.s…
· 使用定理 `Nat.factorization_prod`：factorization_prod {α : Type*} {S : Finset α} {g
 : α -> Nat} (hS : forall x in S, g x != 0) : (S.prod g).factorization = S.sum f
un x => (g x…
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.Prime.factorization_pow`：∀ {p k : ℕ}, Nat.Prime p → (p ^ k).factoriz
ation = fun₀ | p => k
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f

--- 原说明 ---
Any Finsupp `f : ℕ →₀ ℕ` whose support is in the primes is equal to the factoriz
ation of
the product `∏ (a : ℕ) ∈ f.support, a ^ f a`.
-/
theorem prod_pow_factorization_eq_self (hf : ∀ p ∈ f.support, Prime p) :
    (f.prod (· ^ ·)).factorization = f := by
  rw [Finsupp.prod, factorization_prod (pow_ne_zero _ <| hf · · |>.ne_zero),
    sum_congr rfl (hf · · |>.factorization_pow)]
  exact sum_single f
/-
**Nat.eq_factorization_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_factorization_iff (hn : n != 0) (hf : forall p in f.support, Prime p) :
 f = n.factorization ↔ f.prod (· ^ ·) = n
参数：hn : n != 0；hf : forall p in f.support, Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_pow_factorization_eq_self`：prod_pow_factorization_eq_self (hf :
 forall p in f.support, Prime p) : (f.prod (· ^ ·)).factorization = f
-/
theorem eq_factorization_iff (hn : n ≠ 0) (hf : ∀ p ∈ f.support, Prime p) :
    f = n.factorization ↔ f.prod (· ^ ·) = n := by
  constructor <;> rintro rfl
  exacts [prod_factorization_pow_eq_self hn, prod_pow_factorization_eq_self hf |>.symm]
/-
**Nat.factorization_prod_pow_eq_self_of_le_factorization** 是 Mathlib 中的一个定理，位于命名
空间 `Nat`。
形式化陈述：factorization_prod_pow_eq_self_of_le_factorization (hf : f <= n.factorizat
ion) : (f.prod (· ^ ·)).factorization = f
参数：hf : f <= n.factorization。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prod_pow_factorization_eq_self`：prod_pow_factorization_eq_self (hf :
 forall p in f.support, Prime p) : (f.prod (· ^ ·)).factorization = f
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用引理 `Finsupp.support_mono`：support_mono (hfg : f <= g) : f.support subseteq g
.support
-/
theorem factorization_prod_pow_eq_self_of_le_factorization (hf : f ≤ n.factorization) :
    (f.prod (· ^ ·)).factorization = f :=
  prod_pow_factorization_eq_self fun _ hp ↦ prime_of_mem_primeFactors <| support_mono hf hp
/-
**Nat.prod_pow_dvd_of_le_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_pow_dvd_of_le_factorization (hf : f <= n.factorization) : f.prod (· ^
 ·) ∣ n
参数：hf : f <= n.factorization。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finsupp.prod_ne_zero_iff`：prod_ne_zero_iff : f.prod g != 0 ↔ forall i in
 f.support, g i (f i) != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用引理 `Finsupp.support_mono`：support_mono (hfg : f <= g) : f.support subseteq g
.support
· 使用定理 `Nat.factorization_prod_pow_eq_self_of_le_factorization`：factorization_pr
od_pow_eq_self_of_le_factorization (hf : f <= n.factorization) : (f.prod (· ^ ·)
).factorization = f
-/
theorem prod_pow_dvd_of_le_factorization (hf : f ≤ n.factorization) : f.prod (· ^ ·) ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rwa [← factorization_le_iff_dvd ?_ hn, factorization_prod_pow_eq_self_of_le_factorization hf]
  refine f.prod_ne_zero_iff.mpr fun _ hp ↦ ?_
  exact pow_ne_zero _ (prime_of_mem_primeFactors <| support_mono hf hp).ne_zero
/-
**Nat.dvd_prod_pow_of_factorization_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_prod_pow_of_factorization_le (hn : n != 0) (hf : n.factorization <= f)
 : n ∣ f.prod (· ^ ·)
参数：hn : n != 0；hf : n.factorization <= f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finsupp.prod_add_index'`：prod_add_index' [AddZeroClass M] [CommMonoid N]
 {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a, h a 0 = 1) (h_add : foral
l a b₁ b₂, h …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.pow_add`：∀ (a m n : ℕ), a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `Nat.dvd_mul_right`：∀ (a b : ℕ), a ∣ a * b
-/
theorem dvd_prod_pow_of_factorization_le (hn : n ≠ 0) (hf : n.factorization ≤ f) :
    n ∣ f.prod (· ^ ·) := by
  rw [← add_tsub_cancel_of_le hf, Finsupp.prod_add_index' (by simp) Nat.pow_add,
    prod_factorization_pow_eq_self hn]
  apply n.dvd_mul_right
/-
**Nat.dvd_iff_exists_le_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_iff_exists_le_factorization {d : Nat} (hd : d != 0) (hn : n != 0) : d 
∣ n ↔ exists f <= n.factorization, d = f.prod (· ^ ·)
参数：hd : d != 0；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `Nat.factorization_prod_pow_eq_self_of_le_factorization`：factorization_pr
od_pow_eq_self_of_le_factorization (hf : f <= n.factorization) : (f.prod (· ^ ·)
).factorization = f
-/
theorem dvd_iff_exists_le_factorization {d : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    d ∣ n ↔ ∃ f ≤ n.factorization, d = f.prod (· ^ ·) := by
  rw [← factorization_le_iff_dvd hd hn]
  refine ⟨fun h ↦ ⟨_, h, prod_factorization_pow_eq_self hd |>.symm⟩, fun ⟨f, hle, hprod⟩ ↦ ?_⟩
  rwa [hprod, factorization_prod_pow_eq_self_of_le_factorization hle]

/-- The equiv between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/
@[simps]
/-
**Nat.factorizationEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：factorizationEquiv : Nat+ ≃ { f : Nat ->₀ Nat // forall p in f.support, Pr
ime p } where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime

--- 原说明 ---
The equiv between `ℕ+` and `ℕ →₀ ℕ` with support in the primes.
-/
def factorizationEquiv : ℕ+ ≃ { f : ℕ →₀ ℕ // ∀ p ∈ f.support, Prime p } where
  toFun := fun ⟨n, _⟩ => ⟨n.factorization, fun _ => prime_of_mem_primeFactors⟩
  invFun := fun ⟨f, hf⟩ =>
    ⟨f.prod _, prod_pow_pos_of_zero_notMem_support fun H => not_prime_zero (hf 0 H)⟩
  left_inv := fun ⟨_, hx⟩ => Subtype.ext <| prod_factorization_pow_eq_self hx.ne.symm
  right_inv := fun ⟨_, hf⟩ => Subtype.ext <| prod_pow_factorization_eq_self hf

/-! ### Factorization and coprimes -/


/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
/-
**Nat.factorization_mul_apply_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_mul_apply_of_coprime {p a b : Nat} (hab : Coprime a b) : (a 
* b).factorization p = a.factorization p + b.factorization p
参数：hab : Coprime a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.perm_iff_count`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l₁ l
₂ : List α},   l₁.Perm l₂ ↔ ∀ (a : α), List.count a l₁ = List.count a l₂
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `Nat.perm_primeFactorsList_mul_of_coprime`：perm_primeFactorsList_mul_of_c
oprime {a b : Nat} (hab : Coprime a b) : (a * b).primeFactorsList ~ a.primeFacto
rsList ++ b.primeFactorsList
· 使用定理 `List.count_append`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l₁ l₂ : List
 α}, List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in
 `a` and `b`
-/
theorem factorization_mul_apply_of_coprime {p a b : ℕ} (hab : Coprime a b) :
    (a * b).factorization p = a.factorization p + b.factorization p := by
  simp only [← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul_of_coprime hab), count_append]

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
/-
**Nat.factorization_mul_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_mul_of_coprime {a b : Nat} (hab : Coprime a b) : (a * b).fac
torization = a.factorization + b.factorization
参数：hab : Coprime a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a
· 使用定理 `Nat.factorization_mul_apply_of_coprime`：factorization_mul_apply_of_copri
me {p a b : Nat} (hab : Coprime a b) : (a * b).factorization p = a.factorization
 p + b.factorization p

--- 原说明 ---
For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in
 `a` and `b`
-/
theorem factorization_mul_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext q
  rw [Finsupp.add_apply, factorization_mul_apply_of_coprime hab]

/-! ### Generalisation of the "even part" and "odd part" of a natural number -/

/-- We introduce the notations `ordProj[p] n` for the largest power of the prime `p` that
divides `n` and `ordCompl[p] n` for the complementary part. The `ord` naming comes from
the $p$-adic order/valuation of a number, and `proj` and `compl` are for the projection and
complementary projection. The term `n.factorization p` is the $p$-adic order itself.
For example, `ordProj[2] n` is the even part of `n` and `ordCompl[2] n` is the odd part. -/
notation "ordProj[" p "] " n:arg => p ^ Nat.factorization n p

@[inherit_doc «termOrdProj[_]_»]
notation "ordCompl[" p "] " n:arg => n / ordProj[p] n

/-
**Nat.ordProj_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
参数：n p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.primeFactorsList_count_eq`：primeFactorsList_count_eq {n p : Nat} : n
.primeFactorsList.count p = n.factorization p
· 使用定理 `Nat.dvd_of_primeFactorsList_subperm`：dvd_of_primeFactorsList_subperm {a 
b : Nat} (ha : a != 0) (h : a.primeFactorsList <+~ b.primeFactorsList) : a ∣ b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Nat.Prime.primeFactorsList_pow`：∀ {p : ℕ}, Nat.Prime p → ∀ (n : ℕ), (p ^
 n).primeFactorsList = List.replicate n p
· 使用定理 `List.subperm_ext_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l₁ 
l₂ : List α},   l₁.Subperm l₂ ↔ ∀ x ∈ l₁, List.count x l₁ ≤ List.count x l₂
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.eq_of_mem_replicate`：∀ {α : Type u_1} {a b : α} {n : ℕ}, b ∈ List.r
eplicate n a → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.count_replicate_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α]
 {a : α} {n : ℕ}, List.count a (List.replicate n a) = n
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordProj_dvd (n p : ℕ) : ordProj[p] n ∣ n := by
  if hp : p.Prime then ?_ else simp [hp]
  rw [← primeFactorsList_count_eq]
  apply dvd_of_primeFactorsList_subperm (pow_ne_zero _ hp.ne_zero)
  rw [hp.primeFactorsList_pow, List.subperm_ext_iff]
  intro q hq
  simp [List.eq_of_mem_replicate hq]
/-
**Nat.ordProj_dvd_ordProj_iff_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ordProj_dvd_ordProj_iff_dvd (ha : a != 0) (hb : b != 0) : (forall p : Nat,
 ordProj[p] a ∣ ordProj[p] b) ↔ a ∣ b
参数：ha : a != 0；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用引理 `Finsupp.le_def`：le_def : f <= g ↔ forall i, f i <= g i
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.factorization_zero_right`：factorization_zero_right (n : Nat) : n.fac
torization 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.factorization_one_right`：factorization_one_right (n : Nat) : n.facto
rization 1 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma ordProj_dvd_ordProj_iff_dvd (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ p : ℕ, ordProj[p] a ∣ ordProj[p] b) ↔ a ∣ b := by
  rw [← factorization_le_iff_dvd ha hb, Finsupp.le_def]
  congr! 1 with p
  obtain _ | _ | p := p <;> simp [Nat.pow_dvd_pow_iff_le_right]

/-! ### Factorization LCM definitions -/


/-- If `a = ∏ pᵢ ^ nᵢ` and `b = ∏ pᵢ ^ mᵢ`, then `factorizationLCMLeft = ∏ pᵢ ^ kᵢ`, where
`kᵢ = nᵢ` if `mᵢ ≤ nᵢ` and `0` otherwise. Note that the product is over the divisors of `lcm a b`,
so if one of `a` or `b` is `0` then the result is `1`. -/
/-
**Nat.factorizationLCMLeft** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：factorizationLCMLeft (a b : Nat) : Nat
参数：a b : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a = ∏ pᵢ ^ nᵢ` and `b = ∏ pᵢ ^ mᵢ`, then `factorizationLCMLeft = ∏ pᵢ ^ kᵢ`,
 where
`kᵢ = nᵢ` if `mᵢ ≤ nᵢ` and `0` otherwise. Note that the product is over the divi
sors of `lcm a b`,
so if one of `a` or `b` is `0` then the result is `1`.
-/
def factorizationLCMLeft (a b : ℕ) : ℕ :=
  (Nat.lcm a b).factorization.prod fun p n ↦
    if b.factorization p ≤ a.factorization p then p ^ n else 1

/-- If `a = ∏ pᵢ ^ nᵢ` and `b = ∏ pᵢ ^ mᵢ`, then `factorizationLCMRight = ∏ pᵢ ^ kᵢ`, where
`kᵢ = mᵢ` if `nᵢ < mᵢ` and `0` otherwise. Note that the product is over the divisors of `lcm a b`,
so if one of `a` or `b` is `0` then the result is `1`.

Note that `factorizationLCMRight a b` is *not* `factorizationLCMLeft b a`: the difference is
that in `factorizationLCMLeft a b` there are the primes whose exponent in `a` is bigger or equal
than the exponent in `b`, while in `factorizationLCMRight a b` there are the primes whose
exponent in `b` is strictly bigger than in `a`. For example `factorizationLCMLeft 2 2 = 2`, but
`factorizationLCMRight 2 2 = 1`. -/
/-
**Nat.factorizationLCMRight** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：factorizationLCMRight (a b : Nat)
参数：a b : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a = ∏ pᵢ ^ nᵢ` and `b = ∏ pᵢ ^ mᵢ`, then `factorizationLCMRight = ∏ pᵢ ^ kᵢ`
, where
`kᵢ = mᵢ` if `nᵢ < mᵢ` and `0` otherwise. Note that the product is over the divi
sors of `lcm a b`,
so if one of `a` or `b` is `0` then the result is `1`.

Note that `factorizationLCMRight a b` is *not* `factorizationLCMLeft b a`: the d
ifference is
that in `factorizationLCMLeft a b` there are the primes whose exponent in `a` is
 bigger or equal
than the exponent in `b`, while in `factorizationLCMRight a b` there are the pri
mes whose
exponent in `b` is strictly bigger than in `a`. For example `factorizationLCMLef
t 2 2 = 2`, but
`factorizationLCMRight 2 2 = 1`.
-/
def factorizationLCMRight (a b : ℕ) :=
  (Nat.lcm a b).factorization.prod fun p n ↦
    if b.factorization p ≤ a.factorization p then 1 else p ^ n

end Nat

