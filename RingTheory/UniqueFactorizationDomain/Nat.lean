/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Unique factorization of natural numbers

## Main definitions

* `Nat.instUniqueFactorizationMonoid`: the natural numbers have unique factorization
-/

public section

assert_not_exists Field

namespace Nat

/-
**Nat.instWfDvdMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instWfDvdMonoid : WfDvdMonoid Nat where wf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} {F : Type u_5} [inst : FunLike F α β]   [RelHomClass F r 
s] (f : F), W…
· 使用定理 `RelHom.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r →r s) r s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dvd_and_not_dvd_iff`：dvd_and_not_dvd_iff [CommMonoidWithZero α] [IsCance
lMulZero α] {x y : α} : x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
（共 36 条，此处仅展示前 30 条）
-/
instance instWfDvdMonoid : WfDvdMonoid ℕ where
  wf := by
    refine RelHomClass.wellFounded
      (⟨fun x : ℕ => if x = 0 then (⊤ : ℕ∞) else x, ?_⟩ : DvdNotUnit →r (· < ·)) wellFounded_lt
    intro a b h
    rcases a with - | a
    · exfalso
      revert h
      simp [DvdNotUnit]
    cases b
    · simp
    obtain ⟨h1, h2⟩ := dvd_and_not_dvd_iff.2 h
    simp only [succ_ne_zero, cast_lt, if_false]
    refine lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h1) fun con => h2 ?_
    rw [con]
/-
**Nat.instUniqueFactorizationMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instUniqueFactorizationMonoid : UniqueFactorizationMonoid Nat where irredu
cible_iff_prime
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.irreducible_iff_prime`：irreducible_iff_prime {p : Nat} : Irreducible
 p ↔ _root_.Prime p
-/
instance instUniqueFactorizationMonoid : UniqueFactorizationMonoid ℕ where
  irreducible_iff_prime := Nat.irreducible_iff_prime

open UniqueFactorizationMonoid
/-
**Nat.factors_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), UniqueFactorizationMonoid.normalizedFactors n = ↑n.primeFactors
List
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.rel_eq`：rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t
· 使用定理 `associated_eq_eq`：associated_eq_eq : (Associated : M -> M -> Prop) = Eq
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `Nat.irreducible_iff_prime`：irreducible_iff_prime {p : Nat} : Irreducible
 p ↔ _root_.Prime p
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
-/
lemma factors_eq : ∀ n : ℕ, normalizedFactors n = n.primeFactorsList
  | 0 => by simp
  | n + 1 => by
    rw [← Multiset.rel_eq, ← associated_eq_eq]
    apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor _
    · rw [Multiset.prod_coe, Nat.prod_primeFactorsList n.succ_ne_zero]
      exact prod_normalizedFactors n.succ_ne_zero
    · intro x hx
      rw [Nat.irreducible_iff_prime, ← Nat.prime_iff]
      exact Nat.prime_of_mem_primeFactorsList hx
/-
**Nat.factors_multiset_prod_of_irreducible** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factors_multiset_prod_of_irreducible {s : Multiset Nat} (h : forall x : Na
t, x in s -> Irreducible x) : normalizedFactors s.prod = s
参数：h : forall x : Nat, x in s -> Irreducible x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.rel_eq`：rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t
· 使用定理 `associated_eq_eq`：associated_eq_eq : (Associated : M -> M -> Prop) = Eq
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Multiset.prod_eq_zero_iff`：∀ {M₀ : Type u_3} [inst : CommMonoidWithZero 
M₀] [NoZeroDivisors M₀] [Nontrivial M₀] {s : Multiset M₀},   s.prod = 0 ↔ 0 ∈ s
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `not_irreducible_zero`：not_irreducible_zero [MonoidWithZero M] : ¬Irreduc
ible (0 : M) | ⟨hn0, h⟩ => have : IsUnit (0 : M) ∨ IsUnit (0 : M)
-/
lemma factors_multiset_prod_of_irreducible {s : Multiset ℕ} (h : ∀ x : ℕ, x ∈ s → Irreducible x) :
    normalizedFactors s.prod = s := by
  rw [← Multiset.rel_eq, ← associated_eq_eq]
  apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor h
    (prod_normalizedFactors _)
  rw [Ne, Multiset.prod_eq_zero_iff]
  exact fun con ↦ not_irreducible_zero (h 0 con)

end Nat

