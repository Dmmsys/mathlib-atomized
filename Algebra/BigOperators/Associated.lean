/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Products of associated, prime, and irreducible elements.

This file contains some theorems relating definitions in `Algebra.Associated`
and products of multisets, finsets, and finsupps.

-/

public section

assert_not_exists Field

variable {ι M M₀ : Type*}

-- the same local notation used in `Algebra.Associated`
local infixl:50 " ~ᵤ " => Associated

namespace Prime

variable [CommMonoidWithZero M₀] {p : M₀}

/-
**Prime.exists_mem_multiset_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：exists_mem_multiset_dvd (hp : Prime p) {s : Multiset M₀} : p ∣ s.prod -> e
xists a in s, p ∣ a
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Prime.not_dvd_one`：not_dvd_one : ¬p ∣ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem exists_mem_multiset_dvd (hp : Prime p) {s : Multiset M₀} : p ∣ s.prod → ∃ a ∈ s, p ∣ a :=
  Multiset.induction_on s (fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.prod := by simpa using h
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩
/-
**Prime.exists_mem_multiset_map_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：exists_mem_multiset_map_dvd (hp : Prime p) {s : Multiset ι} {f : ι -> M₀} 
: p ∣ (s.map f).prod -> exists a in s, p ∣ f a
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prime.exists_mem_multiset_dvd`：exists_mem_multiset_dvd (hp : Prime p) {s
 : Multiset M₀} : p ∣ s.prod -> exists a in s, p ∣ a
-/
theorem exists_mem_multiset_map_dvd (hp : Prime p) {s : Multiset ι} {f : ι → M₀} :
    p ∣ (s.map f).prod → ∃ a ∈ s, p ∣ f a := fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    hp.exists_mem_multiset_dvd h
/-
**Prime.exists_mem_finset_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：exists_mem_finset_dvd (hp : Prime p) {s : Finset ι} {f : ι -> M₀} : p ∣ s.
prod f -> exists i in s, p ∣ f i
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.exists_mem_multiset_map_dvd`：exists_mem_multiset_map_dvd (hp : Pri
me p) {s : Multiset ι} {f : ι -> M₀} : p ∣ (s.map f).prod -> exists a in s, p ∣ 
f a
-/
theorem exists_mem_finset_dvd (hp : Prime p) {s : Finset ι} {f : ι → M₀} :
    p ∣ s.prod f → ∃ i ∈ s, p ∣ f i :=
  hp.exists_mem_multiset_map_dvd

end Prime

/-
**Prod.associated_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.associated_iff {M N : Type*} [Monoid M] [Monoid N] {x z : M × N} : x 
~ᵤ z ↔ x.1 ~ᵤ z.1 ∧ x.2 ~ᵤ z.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.eq_iff_fst_eq_snd_eq`：∀ {α : Type u_1} {β : Type u_2} {p q : α × β}
, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem Prod.associated_iff {M N : Type*} [Monoid M] [Monoid N] {x z : M × N} :
    x ~ᵤ z ↔ x.1 ~ᵤ z.1 ∧ x.2 ~ᵤ z.2 :=
  ⟨fun ⟨u, hu⟩ => ⟨⟨(MulEquiv.prodUnits.toFun u).1, (Prod.eq_iff_fst_eq_snd_eq.1 hu).1⟩,
    ⟨(MulEquiv.prodUnits.toFun u).2, (Prod.eq_iff_fst_eq_snd_eq.1 hu).2⟩⟩,
  fun ⟨⟨u₁, h₁⟩, ⟨u₂, h₂⟩⟩ =>
    ⟨MulEquiv.prodUnits.invFun (u₁, u₂), Prod.eq_iff_fst_eq_snd_eq.2 ⟨h₁, h₂⟩⟩⟩

-- TODO: this seems to trigger a bug in the mergeWithGrind linter
set_option linter.tacticAnalysis.mergeWithGrind false in
/-
**Associated.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Associated.prod {M : Type*} [CommMonoid M] {ι : Type*} (s : Finset ι) (f :
 ι -> M) (g : ι -> M) (h : forall i, i in s -> (f i) ~ᵤ (g i)) : (∏ i in s, f i)
 ~ᵤ (∏ i in s, g i)
参数：s : Finset ι；f : ι -> M；g : ι -> M；h : forall i, i in s -> (f i) ~ᵤ (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
-/
theorem Associated.prod {M : Type*} [CommMonoid M] {ι : Type*} (s : Finset ι) (f : ι → M)
    (g : ι → M) (h : ∀ i, i ∈ s → (f i) ~ᵤ (g i)) : (∏ i ∈ s, f i) ~ᵤ (∏ i ∈ s, g i) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rfl
  | insert j s hjs IH =>
    classical
    convert_to (∏ i ∈ insert j s, f i) ~ᵤ (∏ i ∈ insert j s, g i)
    grind [Associated.mul_mul]
/-
**exists_associated_mem_of_dvd_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_associated_mem_of_dvd_prod [CommMonoidWithZero M₀] [IsCancelMulZero
 M₀] {p : M₀} (hp : Prime p) {s : Multiset M₀} : (forall r in s, Prime r) -> p ∣
 s.prod -> exists q in s, p ~ᵤ q
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Prime.associated_of_dvd`：Prime.associated_of_dvd [CommMonoidWithZero M] 
[IsCancelMulZero M] {p q : M} (p_prime : Prime p) (q_prime : Prime q) (dvd : p ∣
 q) : Associa…
-/
theorem exists_associated_mem_of_dvd_prod [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
    {p : M₀} (hp : Prime p)
    {s : Multiset M₀} : (∀ r ∈ s, Prime r) → p ∣ s.prod → ∃ q ∈ s, p ~ᵤ q :=
  Multiset.induction_on s (by simp [mt isUnit_iff_dvd_one.2 hp.not_isUnit]) fun a s ih hs hps => by
    rw [Multiset.prod_cons] at hps
    rcases hp.dvd_or_dvd hps with h | h
    · have hap := hs a (Multiset.mem_cons.2 (Or.inl rfl))
      exact ⟨a, Multiset.mem_cons_self a _, hp.associated_of_dvd hap h⟩
    · rcases ih (fun r hr => hs _ (Multiset.mem_cons.2 (Or.inr hr))) h with ⟨q, hq₁, hq₂⟩
      exact ⟨q, Multiset.mem_cons.2 (Or.inr hq₁), hq₂⟩

open Submonoid in
/-- Let x, y ∈ M₀. If x * y can be written as a product of units and prime elements, then x can be
written as a product of units and prime elements. -/
/-
**divisor_closure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divisor_closure_eq_closure [CommMonoidWithZero M₀] [IsCancelMulZero M₀] (x
 y : M₀) (hxy : x * y in closure { r : M₀ | IsUnit r ∨ Prime r}) : x in closure 
{ r : M₀ | IsUnit r ∨ Prime r}
参数：x y : M₀；hxy : x * y in closure { r : M₀ | IsUnit r ∨ Prime r}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.exists_multiset_of_mem_closure`：exists_multiset_of_mem_closure
 {M : Type*} [CommMonoid M] {s : Set M} {x : M} (hx : x in closure s) : exists l
 : Multiset M, (forall y in l,…
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] (S : S
ubmonoid M) (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.forall_mem_cons`：forall_mem_cons {p : α -> Prop} {a : α} {s : M
ultiset α} : (forall x in a ::ₘ s, p x) ↔ p a ∧ forall x in s, p x
· 使用定理 `IsUnit.of_mul_eq_one_right`：IsUnit.of_mul_eq_one_right [Monoid M] [IsDed
ekindFiniteMonoid M] {b : M} (a : M) (h : a * b = 1) : IsUnit b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_eq_mul_right_iff`：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsRigh
tCancelMulZero M₀] {a b c : M₀}, a * c = b * c ↔ a = b ∨ c = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prime.dvd_mul`：dvd_mul {a b : M} : p ∣ a * b ↔ p ∣ a ∨ p ∣ b
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0

--- 原说明 ---
Let x, y ∈ M₀. If x * y can be written as a product of units and prime elements,
 then x can be
written as a product of units and prime elements.
-/
theorem divisor_closure_eq_closure [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
    (x y : M₀) (hxy : x * y ∈ closure { r : M₀ | IsUnit r ∨ Prime r}) :
    x ∈ closure { r : M₀ | IsUnit r ∨ Prime r} := by
  obtain ⟨m, hm, hprod⟩ := exists_multiset_of_mem_closure hxy
  induction m using Multiset.induction generalizing x y with
  | empty =>
    apply subset_closure
    push _ ∈ _
    simp only [Multiset.prod_zero] at hprod
    left; exact .of_mul_eq_one _ hprod.symm
  | cons c s hind =>
    simp only [Multiset.mem_cons, forall_eq_or_imp, Set.mem_ofPred] at hm
    simp only [Multiset.prod_cons] at hprod
    simp only [Set.mem_ofPred_eq] at hind
    obtain ⟨ha₁ | ha₂, hs⟩ := hm
    · rcases ha₁.exists_right_inv with ⟨k, hk⟩
      refine hind x (y * k) ?_ hs ?_
      · simp only [← mul_assoc, ← hprod, ← Multiset.prod_cons, mul_comm]
        refine multiset_prod_mem _ _ (Multiset.forall_mem_cons.2 ⟨subset_closure ?_,
          Multiset.forall_mem_cons.2 ⟨subset_closure ?_, fun t ht => subset_closure (hs t ht)⟩⟩)
        · left; exact .of_mul_eq_one_right _ hk
        · left; exact ha₁
      · rw [← mul_one s.prod, ← hk, ← mul_assoc, ← mul_assoc, mul_eq_mul_right_iff, mul_comm]
        left; exact hprod
    · rcases ha₂.dvd_mul.1 (Dvd.intro _ hprod) with ⟨c, hc⟩ | ⟨c, hc⟩
      · rw [hc]; rw [hc, mul_assoc] at hprod
        refine Submonoid.mul_mem _ (subset_closure ?_)
          (hind _ _ ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod))
        · right; exact ha₂
        rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
        exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))
      rw [hc, mul_comm x _, mul_assoc, mul_comm c _] at hprod
      refine hind x c ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod)
      rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
      exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))
/-
**Multiset.prod_primes_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.prod_primes_dvd [CommMonoidWithZero M₀] [IsCancelMulZero M₀] [for
all a : M₀, DecidablePred (Associated a)] {s : Multiset M₀} (n : M₀) (h : forall
 a in s, Prime a) (div : forall a in s, a ∣ n) (uniq : forall a, s.countP (Assoc
iated a) <= 1) : s.prod ∣ n
参数：Associated a；n : M₀；h : forall a in s, Prime a；div : forall a in s, a ∣ n；uni
q : forall a, s.countP (Associated a) <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `Prime.associated_of_dvd`：Prime.associated_of_dvd [CommMonoidWithZero M] 
[IsCancelMulZero M] {p q : M} (p_prime : Prime p) (q_prime : Prime q) (dvd : p ∣
 q) : Associa…
· 使用定理 `Multiset.countP_pos`：countP_pos {s} : 0 < countP p s ↔ exists a in s, p 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.succ_le_succ_iff`：∀ {a b : ℕ}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `Multiset.countP_cons_of_pos`：countP_cons_of_pos {a : α} (s) : p a -> cou
ntP p (a ::ₘ s) = countP p s + 1
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Multiset.countP_le_of_le`：countP_le_of_le {s t} (h : s <= t) : countP p 
s <= countP p t
· 使用定理 `Multiset.le_cons_self`：le_cons_self (s : Multiset α) (a : α) : s <= a ::
ₘ s
-/
theorem Multiset.prod_primes_dvd [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
    [∀ a : M₀, DecidablePred (Associated a)] {s : Multiset M₀} (n : M₀) (h : ∀ a ∈ s, Prime a)
    (div : ∀ a ∈ s, a ∣ n) (uniq : ∀ a, s.countP (Associated a) ≤ 1) : s.prod ∣ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty => simp only [Multiset.prod_zero, one_dvd]
  | cons a s induct =>
    rw [Multiset.prod_cons]
    obtain ⟨k, rfl⟩ : a ∣ n := div a (Multiset.mem_cons_self a s)
    gcongr
    refine induct _ (fun a ha => h a (Multiset.mem_cons_of_mem ha)) (fun b b_in_s => ?_)
      fun a => (Multiset.countP_le_of_le _ (Multiset.le_cons_self _ _)).trans (uniq a)
    have b_div_n := div b (Multiset.mem_cons_of_mem b_in_s)
    have a_prime := h a (Multiset.mem_cons_self a s)
    have b_prime := h b (Multiset.mem_cons_of_mem b_in_s)
    refine (b_prime.dvd_or_dvd b_div_n).resolve_left fun b_div_a => ?_
    have assoc := b_prime.associated_of_dvd a_prime b_div_a
    have := uniq a
    rw [Multiset.countP_cons_of_pos _ (Associated.refl _), Nat.succ_le_succ_iff, ← not_lt,
      Multiset.countP_pos] at this
    exact this ⟨b, b_in_s, assoc.symm⟩
/-
**Finset.prod_primes_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.prod_primes_dvd [CommMonoidWithZero M₀] [IsCancelMulZero M₀] [Subsi
ngleton M₀ˣ] {s : Finset M₀} (n : M₀) (h : forall a in s, Prime a) (div : forall
 a in s, a ∣ n) : ∏ p in s, p ∣ n
参数：n : M₀；h : forall a in s, Prime a；div : forall a in s, a ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_primes_dvd`：Multiset.prod_primes_dvd [CommMonoidWithZero M
₀] [IsCancelMulZero M₀] [forall a : M₀, DecidablePred (Associated a)] {s : Multi
set M₀} (n : M…
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.countP_congr`：countP_congr {s s' : Multiset α} (hs : s = s') {p
 p' : α -> Prop} [DecidablePred p] [DecidablePred p'] (hp : forall x in s, p x =
 p' x) : s.…
· 使用定理 `associated_eq_eq`：associated_eq_eq : (Associated : M -> M -> Prop) = Eq
· 使用定理 `Multiset.countP_eq_card_filter`：countP_eq_card_filter (s) : countP p s =
 card (filter p s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.count_eq_card_filter_eq`：count_eq_card_filter_eq [DecidableEq α
] (s : Multiset α) (a : α) : s.count a = card (s.filter (a = ·))
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem Finset.prod_primes_dvd [CommMonoidWithZero M₀] [IsCancelMulZero M₀] [Subsingleton M₀ˣ]
    {s : Finset M₀} (n : M₀) (h : ∀ a ∈ s, Prime a) (div : ∀ a ∈ s, a ∣ n) : ∏ p ∈ s, p ∣ n := by
  classical
    exact
      Multiset.prod_primes_dvd n (by simpa only [Multiset.map_id', Finset.mem_def] using h)
        (by simpa only [Multiset.map_id', Finset.mem_def] using div)
        (by
          simp only [Multiset.map_id', associated_eq_eq, Multiset.countP_eq_card_filter,
            ← s.val.count_eq_card_filter_eq, ← Multiset.nodup_iff_count_le_one, s.nodup])

namespace Associates

section CommMonoid

variable [CommMonoid M]

/-
**Associates.prod_mk** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prod_mk {p : Multiset M} : (p.map Associates.mk).prod = Associates.mk p.pr
od
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
-/
theorem prod_mk {p : Multiset M} : (p.map Associates.mk).prod = Associates.mk p.prod :=
  Multiset.induction_on p (by simp) fun a s ih => by simp [ih, Associates.mk_mul_mk]
/-
**Associates.finsetProd_mk** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：finsetProd_mk {p : Finset ι} {f : ι -> M} : (∏ i in p, Associates.mk (f i)
) = Associates.mk (∏ i in p, f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_multiset_prod`：prod_eq_multiset_prod [CommMonoid M] (s : 
Finset ι) (f : ι -> M) : ∏ x in s, f x = (s.1.map f).prod
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Associates.prod_mk`：prod_mk {p : Multiset M} : (p.map Associates.mk).pro
d = Associates.mk p.prod
-/
theorem finsetProd_mk {p : Finset ι} {f : ι → M} :
    (∏ i ∈ p, Associates.mk (f i)) = Associates.mk (∏ i ∈ p, f i) := by
  rw [Finset.prod_eq_multiset_prod, ← Function.comp_def, ← Multiset.map_map, prod_mk,
    ← Finset.prod_eq_multiset_prod]

@[deprecated (since := "2026-04-08")] alias finset_prod_mk := finsetProd_mk
/-
**Associates.rel_associated_iff_map_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Associates
`。
形式化陈述：rel_associated_iff_map_eq_map {p q : Multiset M} : Multiset.Rel Associated
 p q ↔ p.map Associates.mk = q.map Associates.mk
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.rel_eq`：rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t
· 使用定理 `Multiset.rel_map`：rel_map {s : Multiset α} {t : Multiset β} {f : α -> γ}
 {g : β -> δ} : Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rel_associated_iff_map_eq_map {p q : Multiset M} :
    Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map Associates.mk := by
  rw [← Multiset.rel_eq, Multiset.rel_map]
  simp only [mk_eq_mk_iff_associated]
/-
**Associates.prod_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prod_eq_one_iff {p : Multiset (Associates M)} : p.prod = 1 ↔ forall a in p
, (a : Associates M) = 1
参数：Associates M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem prod_eq_one_iff {p : Multiset (Associates M)} :
    p.prod = 1 ↔ ∀ a ∈ p, (a : Associates M) = 1 :=
  Multiset.induction_on p (by simp)
    (by simp +contextual [mul_eq_one, or_imp, forall_and])
/-
**Associates.prod_le_prod** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prod_le_prod {p q : Multiset (Associates M)} (h : p <= q) : p.prod <= q.pr
od
参数：Associates M；h : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.mul_mono`：mul_mono {a b c d : Associates M} (h₁ : a <= b) (h₂
 : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `Associates.instIsBotOneClass`：∀ {M : Type u_1} [inst : CommMonoid M], Is
BotOneClass (Associates M)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `Multiset.instExistsAddOfLE`：∀ {α : Type u_1}, ExistsAddOfLE (Multiset α)
· 使用定理 `Multiset.instOrderedSub`：∀ {α : Type u_1} [inst : DecidableEq α], Ordere
dSub (Multiset α)
-/
theorem prod_le_prod {p q : Multiset (Associates M)} (h : p ≤ q) : p.prod ≤ q.prod := by
  have := Classical.decEq (Associates M)
  suffices p.prod ≤ (p + (q - p)).prod by rwa [add_tsub_cancel_of_le h] at this
  suffices p.prod * 1 ≤ p.prod * (q - p).prod by simpa
  exact mul_mono (le_refl p.prod) one_le

end CommMonoid

section CancelCommMonoidWithZero

variable [CommMonoidWithZero M₀]

/-
**Associates.exists_mem_multiset_le_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `Associat
es`。
形式化陈述：exists_mem_multiset_le_of_prime {s : Multiset (Associates M₀)} {p : Associ
ates M₀} (hp : Prime p) : p <= s.prod -> exists a in s, p <= a
参数：Associates M₀；hp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Prime.ne_one`：ne_one : p != 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_one`：mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Associates.Prime.le_or_le`：∀ {M : Type u_1} [inst : CommMonoidWithZero M
] {p : Associates M},   Prime p → ∀ {a b : Associates M}, p ≤ a * b → p ≤ a ∨ p 
≤ b
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem exists_mem_multiset_le_of_prime {s : Multiset (Associates M₀)} {p : Associates M₀}
    (hp : Prime p) : p ≤ s.prod → ∃ a ∈ s, p ≤ a :=
  Multiset.induction_on s (fun ⟨_, eq⟩ => (hp.ne_one (mul_eq_one.1 eq.symm).1).elim)
    fun a s ih h =>
    have : p ≤ a * s.prod := by simpa using h
    match Prime.le_or_le hp this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

end CancelCommMonoidWithZero

end Associates

namespace Multiset

/-
**Multiset.prod_ne_zero_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_ne_zero_of_prime [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontriv
ial M₀] (s : Multiset M₀) (h : forall x in s, Prime x) : s.prod != 0
参数：s : Multiset M₀；h : forall x in s, Prime x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.prod_ne_zero`：prod_ne_zero (h : (0 : M₀) ∉ s) : s.prod != 0
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
-/
theorem prod_ne_zero_of_prime [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀]
    (s : Multiset M₀) (h : ∀ x ∈ s, Prime x) : s.prod ≠ 0 :=
  Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl

end Multiset

open Finset Finsupp

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M]

/-
**Prime.dvd_finsetProd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.dvd_finsetProd_iff {S : Finset M₀} {p : M} (pp : Prime p) (g : M₀ ->
 M) : p ∣ S.prod g ↔ exists a in S, p ∣ g a
参数：pp : Prime p；g : M₀ -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.exists_mem_finset_dvd`：exists_mem_finset_dvd (hp : Prime p) {s : F
inset ι} {f : ι -> M₀} : p ∣ s.prod f -> exists i in s, p ∣ f i
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
-/
theorem Prime.dvd_finsetProd_iff {S : Finset M₀} {p : M} (pp : Prime p) (g : M₀ → M) :
    p ∣ S.prod g ↔ ∃ a ∈ S, p ∣ g a :=
  ⟨pp.exists_mem_finset_dvd, fun ⟨_, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩

@[deprecated (since := "2026-04-08")] alias Prime.dvd_finset_prod_iff := Prime.dvd_finsetProd_iff
/-
**Prime.not_dvd_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.not_dvd_finsetProd {S : Finset M₀} {p : M} (pp : Prime p) {g : M₀ ->
 M} (hS : forall a in S, ¬p ∣ g a) : ¬p ∣ S.prod g
参数：pp : Prime p；hS : forall a in S, ¬p ∣ g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prime.dvd_finsetProd_iff`：Prime.dvd_finsetProd_iff {S : Finset M₀} {p : 
M} (pp : Prime p) (g : M₀ -> M) : p ∣ S.prod g ↔ exists a in S, p ∣ g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
-/
theorem Prime.not_dvd_finsetProd {S : Finset M₀} {p : M} (pp : Prime p) {g : M₀ → M}
    (hS : ∀ a ∈ S, ¬p ∣ g a) : ¬p ∣ S.prod g := by
  exact mt (Prime.dvd_finsetProd_iff pp _).1 <| not_exists.2 fun a => not_and.2 (hS a)

@[deprecated (since := "2026-04-08")] alias Prime.not_dvd_finset_prod := Prime.not_dvd_finsetProd
/-
**Prime.dvd_finsuppProd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.dvd_finsuppProd_iff {f : M₀ ->₀ M} {g : M₀ -> M -> Nat} {p : Nat} (p
p : Prime p) : p ∣ f.prod g ↔ exists a in f.support, p ∣ g a (f a)
参数：pp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.dvd_finsetProd_iff`：Prime.dvd_finsetProd_iff {S : Finset M₀} {p : 
M} (pp : Prime p) (g : M₀ -> M) : p ∣ S.prod g ↔ exists a in S, p ∣ g a
-/
theorem Prime.dvd_finsuppProd_iff {f : M₀ →₀ M} {g : M₀ → M → ℕ} {p : ℕ} (pp : Prime p) :
    p ∣ f.prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) :=
  Prime.dvd_finsetProd_iff pp _
/-
**Prime.not_dvd_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.not_dvd_finsuppProd {f : M₀ ->₀ M} {g : M₀ -> M -> Nat} {p : Nat} (p
p : Prime p) (hS : forall a in f.support, ¬p ∣ g a (f a)) : ¬p ∣ f.prod g
参数：pp : Prime p；hS : forall a in f.support, ¬p ∣ g a (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.not_dvd_finsetProd`：Prime.not_dvd_finsetProd {S : Finset M₀} {p : 
M} (pp : Prime p) {g : M₀ -> M} (hS : forall a in S, ¬p ∣ g a) : ¬p ∣ S.prod g
-/
theorem Prime.not_dvd_finsuppProd {f : M₀ →₀ M} {g : M₀ → M → ℕ} {p : ℕ} (pp : Prime p)
    (hS : ∀ a ∈ f.support, ¬p ∣ g a (f a)) : ¬p ∣ f.prod g :=
  Prime.not_dvd_finsetProd pp hS

end CommMonoidWithZero

