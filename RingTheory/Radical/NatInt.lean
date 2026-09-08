/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Arend Mellendijk, Jeremy Tan
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Radical.Basic

/-!
# The radical in `ℕ` and `ℤ`

## Declarations for `ℕ`

- `UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors`: The prime factors of a natural number
  are the same as the prime factors defined in `Nat.primeFactors`.
- `Nat.radical_eq_prod_primeFactors`: The radical is computable for natural numbers.
- `Nat.radical_le_self_iff`: if `n ≠ 0`, `radical n ≤ n`.
- `Nat.two_le_radical_iff`: `2 ≤ n.radical` iff `2 ≤ n`.

## Declarations for `ℤ`

- `UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs`: The prime factors of an integer
  are the same as the prime factors of its absolute value.
- `Int.radical_eq_prod_primeFactors`: The radical is computable for integers.
-/

@[expose] public section

open UniqueFactorizationMonoid

/-! ### Lemmas about natural numbers -/

/-
**UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors : primeFactors =
 Nat.primeFactors
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.primeFactors.eq_1`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M]   (a : M), UniqueFact…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.factors_eq`：∀ (n : ℕ), UniqueFactorizationMonoid.normalizedFactors n
 = ↑n.primeFactorsList
· 使用定理 `Nat.primeFactors.eq_1`：∀ (n : ℕ), n.primeFactors = n.primeFactorsList.to
Finset
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `List.toFinset_coe`：toFinset_coe (l : List α) : (l : Multiset α).toFinset
 = l.toFinset

--- 原说明 ---
### Lemmas about natural numbers
-/
lemma UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors :
    primeFactors = Nat.primeFactors := by
  ext n : 1
  rw [primeFactors, Nat.factors_eq, Nat.primeFactors]
  -- this convert is necessary because of the different DecidableEq instances
  convert! List.toFinset_coe _

namespace Nat

variable {n : ℕ}

/-
**Nat.radical_eq_prod_primeFactors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：radical_eq_prod_primeFactors : radical n = ∏ p in n.primeFactors, p
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors`：UniqueFactori
zationMonoid.primeFactors_eq_natPrimeFactors : primeFactors = Nat.primeFactors
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma radical_eq_prod_primeFactors : radical n = ∏ p ∈ n.primeFactors, p := by
  simp [radical, primeFactors_eq_natPrimeFactors]
/-
**Nat.radical_pos** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：radical_pos (n) : 0 < radical n
参数：n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `UniqueFactorizationMonoid.radical_ne_zero`：∀ {M : Type u_1} [inst : Comm
MonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorization
Monoid M]   {a : M} [Nontrivial…
-/
lemma radical_pos (n) : 0 < radical n := pos_of_ne_zero radical_ne_zero
/-
**Nat.one_lt_radical_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, 1 < UniqueFactorizationMonoid.radical n ↔ 1 < n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.pos_of_mem_primeFactors`：pos_of_mem_primeFactors (hp : p in n.primeF
actors) : 0 < p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.radical_eq_prod_primeFactors`：radical_eq_prod_primeFactors : radical
 n = ∏ p in n.primeFactors, p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.nonempty_primeFactors`：nonempty_primeFactors {n : Nat} : n.primeFact
ors.Nonempty ↔ 1 < n
· 使用引理 `Finset.one_lt_prod_iff_of_one_le`：one_lt_prod_iff_of_one_le {ι : Type u_
1} {N : Type u_5} [CommMonoid N] [PartialOrder N] {f : ι -> N} {s : Finset ι} [M
ulLeftMono N] (hf : fo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
-/
@[simp] lemma one_lt_radical_iff : 1 < radical n ↔ 1 < n := by
  have pp (p) (h : p ∈ n.primeFactors) : 1 ≤ p := pos_of_mem_primeFactors h
  rw [radical_eq_prod_primeFactors, ← @nonempty_primeFactors n, Finset.one_lt_prod_iff_of_one_le pp]
  exact ⟨fun ⟨p, h⟩ ↦ ⟨p, h.1⟩, fun ⟨p, h⟩ ↦ ⟨p, h, (mem_primeFactors.mp h).1.one_lt⟩⟩
/-
**Nat.two_le_radical_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, 2 ≤ UniqueFactorizationMonoid.radical n ↔ 2 ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.one_lt_radical_iff`：∀ {n : ℕ}, 1 < UniqueFactorizationMonoid.radical
 n ↔ 1 < n
-/
@[simp] lemma two_le_radical_iff : 2 ≤ radical n ↔ 2 ≤ n := one_lt_radical_iff
/-
**Nat.radical_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, UniqueFactorizationMonoid.radical n ≤ 1 ↔ n ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.one_lt_radical_iff`：∀ {n : ℕ}, 1 < UniqueFactorizationMonoid.radical
 n ↔ 1 < n
-/
@[simp] lemma radical_le_one_iff : radical n ≤ 1 ↔ n ≤ 1 := by
  simpa only [not_lt] using one_lt_radical_iff.not
/-
**Nat.radical_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, UniqueFactorizationMonoid.radical n = 1 ↔ n ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.radical_le_one_iff`：∀ {n : ℕ}, UniqueFactorizationMonoid.radical n ≤
 1 ↔ n ≤ 1
-/
@[simp] lemma radical_eq_one_iff : radical n = 1 ↔ n ≤ 1 := by
  rw [← radical_le_one_iff]
  grind [radical_pos n]
/-
**Nat.radical_le_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, UniqueFactorizationMonoid.radical n ≤ n ↔ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.radical_zero`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M],   UniqueFactorizatio…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `UniqueFactorizationMonoid.radical_dvd_self`：radical_dvd_self : radical a
 ∣ a
-/
@[simp] lemma radical_le_self_iff : radical n ≤ n ↔ n ≠ 0 :=
  ⟨by aesop, fun h ↦ Nat.le_of_dvd (by lia) radical_dvd_self⟩
/-
**Nat.self_lt_radical_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n < UniqueFactorizationMonoid.radical n ↔ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.radical_le_self_iff`：∀ {n : ℕ}, UniqueFactorizationMonoid.radical n 
≤ n ↔ n ≠ 0
-/
@[simp] lemma self_lt_radical_iff : n < radical n ↔ n = 0 := by
  simpa only [not_le, not_not] using radical_le_self_iff.not
/-
**Nat.primeFactors_radical** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactors_radical (n : Nat) : (radical n).primeFactors = n.primeFactors
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.radical_eq_prod_primeFactors`：radical_eq_prod_primeFactors : radical
 n = ∏ p in n.primeFactors, p
· 使用定理 `Nat.primeFactors_prod_primeFactors`：primeFactors_prod_primeFactors (n : 
Nat) : (∏ p in n.primeFactors, p).primeFactors = n.primeFactors
-/
theorem primeFactors_radical (n : ℕ) : (radical n).primeFactors = n.primeFactors := by
  rw [radical_eq_prod_primeFactors, primeFactors_prod_primeFactors]
/-
**Nat.radical_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：radical_dvd_iff {n k : Nat} (hk : k != 0) : radical n ∣ k ↔ n.primeFactors
 subseteq k.primeFactors
参数：hk : k != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.radical_eq_prod_primeFactors`：radical_eq_prod_primeFactors : radical
 n = ∏ p in n.primeFactors, p
· 使用定理 `Nat.prod_primeFactors_dvd_iff`：prod_primeFactors_dvd_iff {n k : Nat} (hk
 : k != 0) : (∏ p in n.primeFactors, p) ∣ k ↔ n.primeFactors subseteq k.primeFac
tors
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem radical_dvd_iff {n k : ℕ} (hk : k ≠ 0) :
    radical n ∣ k ↔ n.primeFactors ⊆ k.primeFactors := by
  rw [radical_eq_prod_primeFactors, prod_primeFactors_dvd_iff hk]
/-
**Nat.dvd_radical_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_radical_pow_self {n : Nat} (hn : n != 0) : n ∣ radical n ^ n
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.radical_eq_prod_primeFactors`：radical_eq_prod_primeFactors : radical
 n = ∏ p in n.primeFactors, p
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransDvd`：∀ {α : Type u_1} [inst : Semigroup α], IsTrans α Dvd.dvd
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Nat.dvd_prod_primeFactors_pow_self`：dvd_prod_primeFactors_pow_self {n : 
Nat} (hn : n != 0) : n ∣ (∏ p in n.primeFactors, p) ^ n
-/
theorem dvd_radical_pow_self {n : ℕ} (hn : n ≠ 0) : n ∣ radical n ^ n := by
  grw [radical_eq_prod_primeFactors, ← dvd_prod_primeFactors_pow_self hn]

open Qq Lean Mathlib.Meta Finset

namespace Mathlib.Meta.Positivity
open Positivity

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for radical. Proves radicals are nonzero. -/
@[positivity UniqueFactorizationMonoid.radical _]
meta def evalRadical : PositivityExt where eval {u α} _ _ e := do
  match e with
  | ~q(@radical _ $inst $inst' $inst'' $n) =>
    have _ := ← synthInstanceQ q(Nontrivial $α)
    assertInstancesCommute
    return .nonzero q(radical_ne_zero)
  | _ => throwError "not radical"

/-
**Nat.Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Nat.Mathlib.Meta.Posit
ivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : 0 < radical 100 := by positivity

end Mathlib.Meta.Positivity

end Nat

/-! ### Lemmas about integers -/

variable {z : ℤ}

/-
**UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs : primeFacto
rs z = z.natAbs.primeFactors.map Nat.castEmbedding
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.primeFactors_zero`：∀ {M : Type u_1} [inst : Co
mmMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizati
onMonoid M],   UniqueFactorizatio…
· 使用定理 `Nat.primeFactors_zero`：Nat.primeFactors 0 = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用引理 `UniqueFactorizationMonoid.mem_primeFactors`：mem_primeFactors : a in prim
eFactors b ↔ a in normalizedFactors b
· 使用定理 `UniqueFactorizationMonoid.mem_normalizedFactors_iff'`：mem_normalizedFact
ors_iff' {p x : α} (h : x != 0) : p in normalizedFactors x ↔ Irreducible p ∧ nor
malize p = p ∧ p ∣ x
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `IsBezout.instIsGCDMonoidOfIsCancelMulZero`：∀ (R : Type u) [inst : CommRi
ng R] [IsBezout R] [IsCancelMulZero R], IsGCDMonoid R
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `Int.nonneg_iff_normalize_eq_self`：nonneg_iff_normalize_eq_self (z : Int)
 : normalize z = z ↔ 0 <= z
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用引理 `Int.natCast_dvd`：natCast_dvd {m : Nat} : (m : Int) ∣ n ↔ m ∣ n.natAbs
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 36 条，此处仅展示前 30 条）
-/
lemma UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs :
    primeFactors z = z.natAbs.primeFactors.map Nat.castEmbedding := by
  obtain rfl | hz := eq_or_ne z 0; · simp
  ext p
  rw [mem_primeFactors, mem_normalizedFactors_iff' hz, irreducible_iff_prime,
    Int.nonneg_iff_normalize_eq_self, Finset.mem_map, Function.Embedding.coeFn_mk]
  refine ⟨fun ⟨pp, nnp, dp⟩ ↦ ?_, fun h ↦ ?_⟩
  · lift p to ℕ using nnp
    rw [← Nat.prime_iff_prime_int] at pp
    rw [Int.natCast_dvd] at dp
    exact ⟨p, by simp_all, rfl⟩
  · simp_rw [Nat.mem_primeFactors, Function.Embedding.toFun_eq_coe, Nat.castEmbedding_apply] at h
    obtain ⟨n, ⟨pn, dn, -⟩, rfl⟩ := h
    rw [Int.natCast_dvd, ← Nat.prime_iff_prime_int]
    exact ⟨pn, by simp, dn⟩

namespace Int

/-
**Int.radical_natAbs_eq_radical** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {z : ℤ}, ↑(UniqueFactorizationMonoid.radical z.natAbs) = UniqueFactoriza
tionMonoid.radical z
参数：UniqueFactorizationMonoid.radical z.natAbs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.radical_eq_prod_primeFactors`：radical_eq_prod_primeFactors : radical
 n = ∏ p in n.primeFactors, p
· 使用定理 `UniqueFactorizationMonoid.radical.eq_1`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMon
oid M]   (a : M), UniqueFact…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.cast_prod`：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) 
: (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs`：UniqueFac
torizationMonoid.primeFactors_eq_primeFactors_natAbs : primeFactors z = z.natAbs
.primeFactors.map Nat.castEmbedding
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Nat.castEmbedding_apply`：∀ {R : Type u_2} [inst : AddMonoidWithOne R] [i
nst_1 : CharZero R] (a : ℕ), Nat.castEmbedding a = ↑a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma radical_natAbs_eq_radical : radical z.natAbs = radical z := by
  rw [Nat.radical_eq_prod_primeFactors, radical]
  simp [primeFactors_eq_primeFactors_natAbs]
/-
**Int.radical_eq_prod_primeFactors** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：radical_eq_prod_primeFactors : radical z = ∏ p in z.natAbs.primeFactors, p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.radical_natAbs_eq_radical`：∀ {z : ℤ}, ↑(UniqueFactorizationMonoid.ra
dical z.natAbs) = UniqueFactorizationMonoid.radical z
· 使用引理 `Nat.radical_eq_prod_primeFactors`：radical_eq_prod_primeFactors : radical
 n = ∏ p in n.primeFactors, p
-/
lemma radical_eq_prod_primeFactors : radical z = ∏ p ∈ z.natAbs.primeFactors, p := by
  rw [← radical_natAbs_eq_radical, Nat.radical_eq_prod_primeFactors]
/-
**Int.radical_pos** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：radical_pos (z : Int) : 0 < radical z
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.radical_natAbs_eq_radical`：∀ {z : ℤ}, ↑(UniqueFactorizationMonoid.ra
dical z.natAbs) = UniqueFactorizationMonoid.radical z
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用引理 `Nat.radical_pos`：radical_pos (n) : 0 < radical n
-/
lemma radical_pos (z : ℤ) : 0 < radical z := by
  rw [← radical_natAbs_eq_radical, natCast_pos]
  exact Nat.radical_pos _
/-
**Int.one_lt_radical_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {z : ℤ}, 1 < UniqueFactorizationMonoid.radical z ↔ 1 < z.natAbs
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.radical_natAbs_eq_radical`：∀ {z : ℤ}, ↑(UniqueFactorizationMonoid.ra
dical z.natAbs) = UniqueFactorizationMonoid.radical z
· 使用定理 `Nat.one_lt_cast`：one_lt_cast : 1 < (n : α) ↔ 1 < n
· 使用定理 `Nat.one_lt_radical_iff`：∀ {n : ℕ}, 1 < UniqueFactorizationMonoid.radical
 n ↔ 1 < n
-/
@[simp] lemma one_lt_radical_iff : 1 < radical z ↔ 1 < z.natAbs := by
  rw [← radical_natAbs_eq_radical, Nat.one_lt_cast]
  exact Nat.one_lt_radical_iff
/-
**Int.two_le_radical_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {z : ℤ}, 2 ≤ UniqueFactorizationMonoid.radical z ↔ 2 ≤ z.natAbs
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.one_lt_radical_iff`：∀ {z : ℤ}, 1 < UniqueFactorizationMonoid.radical
 z ↔ 1 < z.natAbs
-/
@[simp] lemma two_le_radical_iff : 2 ≤ radical z ↔ 2 ≤ z.natAbs := one_lt_radical_iff
/-
**Int.radical_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {z : ℤ}, UniqueFactorizationMonoid.radical z ≤ 1 ↔ z.natAbs ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Int.one_lt_radical_iff`：∀ {z : ℤ}, 1 < UniqueFactorizationMonoid.radical
 z ↔ 1 < z.natAbs
-/
@[simp] lemma radical_le_one_iff : radical z ≤ 1 ↔ z.natAbs ≤ 1 := by
  simpa only [not_lt] using one_lt_radical_iff.not
/-
**Int.radical_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {z : ℤ}, UniqueFactorizationMonoid.radical z = 1 ↔ z.natAbs ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.radical_le_one_iff`：∀ {z : ℤ}, UniqueFactorizationMonoid.radical z ≤
 1 ↔ z.natAbs ≤ 1
-/
@[simp] lemma radical_eq_one_iff : radical z = 1 ↔ z.natAbs ≤ 1 := by
  rw [← radical_le_one_iff]
  grind [radical_pos z]
/-
**Int.radical_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℕ}, UniqueFactorizationMonoid.radical ↑n = ↑(UniqueFactorizationMon
oid.radical n)
参数：UniqueFactorizationMonoid.radical n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.radical_eq_prod_primeFactors`：radical_eq_prod_primeFactors : radical
 z = ∏ p in z.natAbs.primeFactors, p
· 使用引理 `Nat.cast_prod`：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) 
: (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用引理 `Nat.radical_eq_prod_primeFactors`：radical_eq_prod_primeFactors : radical
 n = ∏ p in n.primeFactors, p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] lemma radical_natCast {n : ℕ} : radical (n : ℤ) = radical n := by
  simp [Int.radical_eq_prod_primeFactors, Nat.radical_eq_prod_primeFactors]

end Int

