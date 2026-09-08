/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Vector

/-!
Results about "big operations" over a `Fintype`, and consequent
results about cardinalities of certain types.

## Implementation note
This content had previously been in `Data.Fintype.Basic`, but was moved here to avoid
requiring `Algebra.BigOperators` (and hence many other imports) as a
dependency of `Fintype`.

However many of the results here really belong in `Algebra.BigOperators.Group.Finset`
and should be moved at some point.
-/

public section

assert_not_exists MulAction

open Mathlib

universe u v

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Fintype

@[to_additive]
/-
**Fintype.prod_bool** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_bool [CommMonoid α] (f : Bool -> α) : ∏ b, f b = f true * f false
参数：f : Bool -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_bool [CommMonoid α] (f : Bool → α) : ∏ b, f b = f true * f false := by simp
/-
**Fintype.card_eq_sum_ones** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_eq_sum_ones {α} [Fintype α] : Fintype.card α = ∑ _a : α, 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
-/
theorem card_eq_sum_ones {α} [Fintype α] : Fintype.card α = ∑ _a : α, 1 :=
  Finset.card_eq_sum_ones _

section

open Finset

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

@[to_additive]
/-
**Fintype.prod_extend_by_one** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_extend_by_one [CommMonoid α] (s : Finset ι) (f : ι -> α) : ∏ i, (if i
 in s then f i else 1) = ∏ i in s, f i
参数：s : Finset ι；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_filter`：prod_filter (p : ι -> Prop) [DecidablePred p] (f : ι
 -> M) : ∏ a in s with p a, f a = ∏ a in s, if p a then f a else 1
· 使用定理 `Finset.filter_mem_eq_inter`：filter_mem_eq_inter {s t : Finset α} [forall
 i, Decidable (i in t)] : (s.filter fun i => i in t) = s inter t
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
-/
theorem prod_extend_by_one [CommMonoid α] (s : Finset ι) (f : ι → α) :
    ∏ i, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  rw [← prod_filter, filter_mem_eq_inter, univ_inter]

end

section

variable {M : Type*} [Fintype α] [CommMonoid M]

@[to_additive]
/-
**Fintype.prod_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_eq_one (f : α -> M) (h : forall a, f a = 1) : ∏ a, f a = 1
参数：f : α -> M；h : forall a, f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
-/
theorem prod_eq_one (f : α → M) (h : ∀ a, f a = 1) : ∏ a, f a = 1 :=
  Finset.prod_eq_one fun a _ha => h a

@[to_additive]
/-
**Fintype.prod_congr** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_congr (f g : α -> M) (h : forall a, f a = g a) : ∏ a, f a = ∏ a, g a
参数：f g : α -> M；h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem prod_congr (f g : α → M) (h : ∀ a, f a = g a) : ∏ a, f a = ∏ a, g a :=
  Finset.prod_congr rfl fun a _ha => h a

@[to_additive]
/-
**Fintype.prod_eq_single** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_eq_single {f : α -> M} (a : α) (h : forall x != a, f x = 1) : ∏ x, f 
x = f a
参数：a : α；h : forall x != a, f x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_eq_single`：prod_eq_single {s : Finset ι} {f : ι -> M} (a : ι
) (h₀ : forall b in s, b != a -> f b = 1) (h₁ : a ∉ s -> f a = 1) : ∏ x in s, f 
x = f a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem prod_eq_single {f : α → M} (a : α) (h : ∀ x ≠ a, f x = 1) : ∏ x, f x = f a :=
  Finset.prod_eq_single a (fun x _ hx => h x hx) fun ha => (ha (Finset.mem_univ a)).elim

@[to_additive]
/-
**Fintype.prod_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_eq_mul {f : α -> M} (a b : α) (h₁ : a != b) (h₂ : forall x, x != a ∧ 
x != b -> f x = 1) : ∏ x, f x = f a * f b
参数：a b : α；h₁ : a != b；h₂ : forall x, x != a ∧ x != b -> f x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_eq_mul`：prod_eq_mul {s : Finset ι} {f : ι -> M} (a b : ι) (h
n : a != b) (h₀ : forall c in s, c != a ∧ c != b -> f c = 1) (ha : a ∉ s -> f a 
= 1) (hb…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem prod_eq_mul {f : α → M} (a b : α) (h₁ : a ≠ b) (h₂ : ∀ x, x ≠ a ∧ x ≠ b → f x = 1) :
    ∏ x, f x = f a * f b := by
  apply Finset.prod_eq_mul a b h₁ fun x _ hx => h₂ x hx <;>
    exact fun hc => (hc (Finset.mem_univ _)).elim

/-- If a product of a `Finset` of a subsingleton type has a given
value, so do the terms in that product. -/
@[to_additive /-- If a sum of a `Finset` of a subsingleton type has a given
  value, so do the terms in that sum. -/]
/-
**Fintype.eq_of_subsingleton_of_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：eq_of_subsingleton_of_prod_eq {ι : Type*} [Subsingleton ι] {s : Finset ι} 
{f : ι -> M} {b : M} (h : ∏ i in s, f i = b) : forall i in s, f i = b
参数：h : ∏ i in s, f i = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_card_le_one_of_prod_eq`：eq_of_card_le_one_of_prod_eq {s : F
inset ι} (hc : #s <= 1) {f : ι -> M} {b : M} (h : ∏ x in s, f x = b) : forall x 
in s, f x = b
· 使用定理 `Finset.card_le_one_of_subsingleton`：card_le_one_of_subsingleton [Subsing
leton α] (s : Finset α) : #s <= 1
-/
theorem eq_of_subsingleton_of_prod_eq {ι : Type*} [Subsingleton ι] {s : Finset ι} {f : ι → M}
    {b : M} (h : ∏ i ∈ s, f i = b) : ∀ i ∈ s, f i = b :=
  Finset.eq_of_card_le_one_of_prod_eq (Finset.card_le_one_of_subsingleton s) h

end

end Fintype

open Finset

section

variable {M : Type*} [Fintype α] [CommMonoid M]

@[to_additive (attr := simp)]
/-
**Fintype.prod_option** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_option (f : Option α -> M) : ∏ i, f i = f none * ∏ i, f (some
 i)
参数：f : Option α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_insertNone`：prod_insertNone (f : Option α -> M) (s : Finset 
α) : ∏ x in insertNone s, f x = f none * ∏ x in s, f (some x)
-/
theorem Fintype.prod_option (f : Option α → M) : ∏ i, f i = f none * ∏ i, f (some i) :=
  Finset.prod_insertNone f univ

@[to_additive]
/-
**Fintype.prod_eq_mul_prod_subtype_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_eq_mul_prod_subtype_ne [DecidableEq α] (f : α -> M) (a : α) :
 ∏ i, f i = f a * ∏ i : {i // i != a}, f i.1
参数：f : α -> M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `Fintype.prod_option`：Fintype.prod_option (f : Option α -> M) : ∏ i, f i 
= f none * ∏ i, f (some i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Fintype.prod_eq_mul_prod_subtype_ne [DecidableEq α] (f : α → M) (a : α) :
    ∏ i, f i = f a * ∏ i : {i // i ≠ a}, f i.1 := by
  simp_rw [← (Equiv.optionSubtypeNe a).prod_comp, prod_option, Equiv.optionSubtypeNe_none,
    Equiv.optionSubtypeNe_some]

end

section Pi
variable {ι κ : Type*} {α : ι → Type*} [DecidableEq ι] [DecidableEq κ]

/-
**Finset.card_pi** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq ι] (s : Finset ι) 
(t : (i : ι) → Finset (α i)),   (s.pi t).card = ∏ i ∈ s, (t i).card
参数：s : Finset ι；t : (i : ι) → Finset (α i)；s.pi t；t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_pi`：card_pi (m : Multiset α) (t : forall a, Multiset (β a)
) : card (pi m t) = prod (m.map fun a => card (t a))
-/
@[simp] lemma Finset.card_pi (s : Finset ι) (t : ∀ i, Finset (α i)) :
    #(s.pi t) = ∏ i ∈ s, #(t i) := Multiset.card_pi _ _

namespace Fintype

variable [Fintype ι]

/-
**Fintype.card_piFinset** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq ι] [inst_1 : Finty
pe ι] (s : (i : ι) → Finset (α i)),   (Fintype.piFinset s).card = ∏ i, (s i).car
d
参数：s : (i : ι) → Finset (α i)；Fintype.piFinset s；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq 
ι] (s : Finset ι) (t : (i : ι) → Finset (α i)),   (s.pi t).card = ∏ i ∈ s, (t i)
.car…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma card_piFinset (s : ∀ i, Finset (α i)) :
    #(piFinset s) = ∏ i, #(s i) := by simp [piFinset, card_map]

/-- This lemma is specifically designed to be used backwards, whence the specialisation to `Fin n`
as the indexing type doesn't matter in practice. The more general forward direction lemma here is
`Fintype.card_piFinset`. -/
/-
**Fintype.card_piFinset_const** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：card_piFinset_const {α : Type*} (s : Finset α) (n : Nat) : #(piFinset fun 
_ : Fin n => s) = #s ^ n
参数：s : Finset α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_piFinset`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : Decid
ableEq ι] [inst_1 : Fintype ι] (s : (i : ι) → Finset (α i)),   (Fintype.piFinset
 s).card = …
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This lemma is specifically designed to be used backwards, whence the specialisat
ion to `Fin n`
as the indexing type doesn't matter in practice. The more general forward direct
ion lemma here is
`Fintype.card_piFinset`.
-/
lemma card_piFinset_const {α : Type*} (s : Finset α) (n : ℕ) :
    #(piFinset fun _ : Fin n ↦ s) = #s ^ n := by simp
/-
**Fintype.card_pi** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq ι] [inst_1 : Finty
pe ι] [inst_2 : (i : ι) → Fintype (α i)],   Fintype.card ((i : ι) → α i) = ∏ i, 
Fintype.card (α i)
参数：i : ι；α i；(i : ι) → α i；α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_piFinset`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : Decid
ableEq ι] [inst_1 : Fintype ι] (s : (i : ι) → Finset (α i)),   (Fintype.piFinset
 s).card = …
-/
@[simp] lemma card_pi [∀ i, Fintype (α i)] : card (∀ i, α i) = ∏ i, card (α i) :=
  card_piFinset _

/-- This lemma is specifically designed to be used backwards, whence the specialisation to `Fin n`
as the indexing type doesn't matter in practice. The more general forward direction lemma here is
`Fintype.card_pi`. -/
/-
**Fintype.card_pi_const** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：card_pi_const (α : Type*) [Fintype α] (n : Nat) : card (Fin n -> α) = card
 α ^ n
参数：α : Type*；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.card_piFinset_const`：card_piFinset_const {α : Type*} (s : Finset
 α) (n : Nat) : #(piFinset fun _ : Fin n => s) = #s ^ n

--- 原说明 ---
This lemma is specifically designed to be used backwards, whence the specialisat
ion to `Fin n`
as the indexing type doesn't matter in practice. The more general forward direct
ion lemma here is
`Fintype.card_pi`.
-/
lemma card_pi_const (α : Type*) [Fintype α] (n : ℕ) : card (Fin n → α) = card α ^ n :=
  card_piFinset_const _ _

/-- Product over a sigma type equals the repeated product.

This is a version of `Finset.prod_sigma` specialized to the case
of multiplication over `Finset.univ`. -/
@[to_additive /-- Sum over a sigma type equals the repeated sum.

This is a version of `Finset.sum_sigma` specialized to the case of summation over `Finset.univ`. -/]
/-
**Fintype.prod_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_sigma {ι} {α : ι -> Type*} {M : Type*} [Fintype ι] [forall i, Fintype
 (α i)] [CommMonoid M] (f : Sigma α -> M) : ∏ x, f x = ∏ x, ∏ y, f ⟨x, y⟩
参数：α i；f : Sigma α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_sigma`：prod_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) (f : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in
 t a, f…
-/
theorem prod_sigma {ι} {α : ι → Type*} {M : Type*} [Fintype ι] [∀ i, Fintype (α i)] [CommMonoid M]
    (f : Sigma α → M) : ∏ x, f x = ∏ x, ∏ y, f ⟨x, y⟩ :=
  Finset.prod_sigma ..

/-- Product over a sigma type equals the repeated product, curried version.
This version is useful to rewrite from right to left. -/
@[to_additive /-- Sum over a sigma type equals the repeated sum, curried version.
This version is useful to rewrite from right to left. -/]
/-
**Fintype.prod_sigma'** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_sigma' {ι} {α : ι -> Type*} {M : Type*} [Fintype ι] [forall i, Fintyp
e (α i)] [CommMonoid M] (f : (i : ι) -> α i -> M) : ∏ x : Sigma α, f x.1 x.2 = ∏
 x, ∏ y, f x y
参数：α i；f : (i : ι) -> α i -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.prod_sigma`：prod_sigma {ι} {α : ι -> Type*} {M : Type*} [Fintype
 ι] [forall i, Fintype (α i)] [CommMonoid M] (f : Sigma α -> M) : ∏ x, f x = ∏ x
, ∏ y, f…
-/
theorem prod_sigma' {ι} {α : ι → Type*} {M : Type*} [Fintype ι] [∀ i, Fintype (α i)] [CommMonoid M]
    (f : (i : ι) → α i → M) : ∏ x : Sigma α, f x.1 x.2 = ∏ x, ∏ y, f x y :=
  prod_sigma ..

@[simp] nonrec lemma card_sigma {ι} {α : ι → Type*} [Fintype ι] [∀ i, Fintype (α i)] :
    card (Sigma α) = ∑ i, card (α i) := card_sigma _ _

/-- The number of dependent maps `f : Π j, s j` for which the `i` component is `a` is the product
over all `j ≠ i` of `#(s j)`.

Note that this is just a composition of easier lemmas, but there's some glue missing to make that
smooth enough not to need this lemma. -/
/-
**Fintype.card_filter_piFinset_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：card_filter_piFinset_eq_of_mem [forall i, DecidableEq (α i)] (s : forall i
, Finset (α i)) (i : ι) {a : α i} (ha : a in s i) : #{f in piFinset s | f i = a}
 = ∏ j in univ.erase i, #(s j)
参数：α i；s : forall i, Finset (α i)；i : ι；ha : a in s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fintype.piFinset_update_singleton_eq_filter_piFinset_eq`：piFinset_update
_singleton_eq_filter_piFinset_eq (s : forall i, Finset (δ i)) (i : α) {a : δ i} 
(ha : a in s i) : piFinset (Function.update s…
· 使用定理 `Fintype.card_piFinset`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : Decid
ableEq ι] [inst_1 : Fintype ι] (s : (i : ι) → Finset (α i)),   (Fintype.piFinset
 s).card = …
· 使用定理 `Fintype.prod_congr`：prod_congr (f g : α -> M) (h : forall a, f a = g a) 
: ∏ a, f a = ∏ a, g a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.prod_update_of_mem`：prod_update_of_mem [DecidableEq ι] {s : Finse
t ι} {i : ι} (h : i in s) (f : ι -> M) (b : M) : ∏ x in s, Function.update f i b
 x = b * ∏ x in…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.erase_eq`：erase_eq (s : Finset α) (a : α) : s.erase a = s \ {a}

--- 原说明 ---
The number of dependent maps `f : Π j, s j` for which the `i` component is `a` i
s the product
over all `j ≠ i` of `#(s j)`.

Note that this is just a composition of easier lemmas, but there's some glue mis
sing to make that
smooth enough not to need this lemma.
-/
lemma card_filter_piFinset_eq_of_mem [∀ i, DecidableEq (α i)]
    (s : ∀ i, Finset (α i)) (i : ι) {a : α i} (ha : a ∈ s i) :
    #{f ∈ piFinset s | f i = a} = ∏ j ∈ univ.erase i, #(s j) := by
  calc
    _ = ∏ j, #(Function.update s i {a} j) := by
      rw [← piFinset_update_singleton_eq_filter_piFinset_eq _ _ ha, Fintype.card_piFinset]
    _ = ∏ j, Function.update (fun j ↦ #(s j)) i 1 j :=
      Fintype.prod_congr _ _ fun j ↦ by obtain rfl | hji := eq_or_ne j i <;> simp [*]
    _ = _ := by simp [prod_update_of_mem, erase_eq]
/-
**Fintype.card_filter_piFinset_const_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Fintyp
e`。
形式化陈述：card_filter_piFinset_const_eq_of_mem (s : Finset κ) (i : ι) {x : κ} (hx : 
x in s) : #{f in piFinset fun _ => s | f i = x} = #s ^ (card ι - 1)
参数：s : Finset κ；i : ι；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Fintype.card_filter_piFinset_eq_of_mem`：card_filter_piFinset_eq_of_mem [
forall i, DecidableEq (α i)] (s : forall i, Finset (α i)) (i : ι) {a : α i} (ha 
: a in s i) : #{f in piFinse…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
-/
lemma card_filter_piFinset_const_eq_of_mem (s : Finset κ) (i : ι) {x : κ} (hx : x ∈ s) :
    #{f ∈ piFinset fun _ ↦ s | f i = x} = #s ^ (card ι - 1) :=
  (card_filter_piFinset_eq_of_mem _ _ hx).trans <| by
    rw [prod_const #s, card_erase_of_mem (mem_univ _), card_univ]
/-
**Fintype.card_filter_piFinset_eq** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：card_filter_piFinset_eq [forall i, DecidableEq (α i)] (s : forall i, Finse
t (α i)) (i : ι) (a : α i) : #{f in piFinset s | f i = a} = if a in s i then ∏ b
 in univ.erase i, #(s b) else 0
参数：α i；s : forall i, Finset (α i)；i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `Fintype.card_filter_piFinset_eq_of_mem`：card_filter_piFinset_eq_of_mem [
forall i, DecidableEq (α i)] (s : forall i, Finset (α i)) (i : ι) {a : α i} (ha 
: a in s i) : #{f in piFinse…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Fintype.filter_piFinset_of_notMem`：filter_piFinset_of_notMem (t : forall
 a, Finset (δ a)) (a : α) (x : δ a) (hx : x ∉ t a) : {f in piFinset t | f a = x}
 = ∅
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
-/
lemma card_filter_piFinset_eq [∀ i, DecidableEq (α i)] (s : ∀ i, Finset (α i)) (i : ι) (a : α i) :
    #{f ∈ piFinset s | f i = a} = if a ∈ s i then ∏ b ∈ univ.erase i, #(s b) else 0 := by
  split_ifs with h
  · rw [card_filter_piFinset_eq_of_mem _ _ h]
  · rw [filter_piFinset_of_notMem _ _ _ h, Finset.card_empty]
/-
**Fintype.card_filter_piFinset_const** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：card_filter_piFinset_const (s : Finset κ) (i : ι) (j : κ) : #{f in piFinse
t fun _ => s | f i = j} = if j in s then #s ^ (card ι - 1) else 0
参数：s : Finset κ；i : ι；j : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Fintype.card_filter_piFinset_eq`：card_filter_piFinset_eq [forall i, Deci
dableEq (α i)] (s : forall i, Finset (α i)) (i : ι) (a : α i) : #{f in piFinset 
s | f i = a} = if a i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
-/
lemma card_filter_piFinset_const (s : Finset κ) (i : ι) (j : κ) :
    #{f ∈ piFinset fun _ ↦ s | f i = j} = if j ∈ s then #s ^ (card ι - 1) else 0 :=
  (card_filter_piFinset_eq _ _ _).trans <| by
    rw [prod_const #s, card_erase_of_mem (mem_univ _), card_univ]

end Fintype
end Pi

-- TODO: this is a basic theorem about `Fintype.card`,
-- and ideally could be moved to `Mathlib/Data/Fintype/Card.lean`.
/-
**Fintype.card_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype β] : Fintype.card (α
 -> β) = Fintype.card β ^ Fintype.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq
 ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Fintype (α i)],   Fintype.card ((i 
: ι) …
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype β] :
    Fintype.card (α → β) = Fintype.card β ^ Fintype.card α := by
  simp

@[simp]
/-
**card_vector** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_vector [Fintype α] (n : Nat) : Fintype.card (List.Vector α n) = Finty
pe.card α ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq
 ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Fintype (α i)],   Fintype.card ((i 
: ι) …
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_vector [Fintype α] (n : ℕ) :
    Fintype.card (List.Vector α n) = Fintype.card α ^ n := by
  rw [Fintype.ofEquiv_card]; simp

/-- The number of strings of length `s` in any finite set is at most `D^s`. -/
/-
**Finset.card_filter_length_eq_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.card_filter_length_eq_le [Fintype α] {T : Finset (List α)} {s : Nat
} : (T.filter (fun x => x.length = s)).card <= (Fintype.card α) ^ s
参数：List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `List.ofFn_injective`：ofFn_injective {n : Nat} : Function.Injective (ofFn
 : (Fin n -> α) -> List α)
· 使用定理 `Fintype.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq
 ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Fintype (α i)],   Fintype.card ((i 
: ι) …
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n

--- 原说明 ---
The number of strings of length `s` in any finite set is at most `D^s`.
-/
lemma Finset.card_filter_length_eq_le [Fintype α] {T : Finset (List α)} {s : ℕ} :
    (T.filter (fun x => x.length = s)).card ≤ (Fintype.card α) ^ s := by
  classical
  calc
    _ ≤ (Finset.univ.image List.ofFn).card := by
          apply Finset.card_le_card
          intro a ha
          let hlen := Finset.mem_filter.mp ha
          exact Finset.mem_image.mpr ⟨
              (fun j : Fin s => a.get ⟨j.val, by simp [hlen]⟩),
              by simp,
              List.ext_get (by simp [hlen]) (by simp)⟩
    _ = Fintype.card α ^ s := by
          simp [card_image_of_injective univ List.ofFn_injective]

/-- It is equivalent to compute the product of a function over `Fin n` or `Finset.range n`. -/
@[to_additive /-- It is equivalent to sum a function over `fin n` or `finset.range n`. -/]
/-
**Fin.prod_univ_eq_prod_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.prod_univ_eq_prod_range [CommMonoid α] (f : Nat -> α) (n : Nat) : ∏ i 
: Fin n, f i = ∏ i in range n, f i
参数：f : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Fin.equivSubtype_apply`：∀ {n : ℕ} (a : Fin n), Fin.equivSubtype a = ⟨↑a,
 ⋯⟩
· 使用定理 `Equiv.subtypeEquivRight_apply_coe`：∀ {α : Sort u_1} {p q : α → Prop} (e 
: ∀ (x : α), p x ↔ q x) (a : { a // p a }), ↑((Equiv.subtypeEquivRight e) a) = ↑
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.attach_eq_univ`：Finset.attach_eq_univ {s : Finset α} : s.attach =
 Finset.univ
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x

--- 原说明 ---
It is equivalent to compute the product of a function over `Fin n` or `Finset.ra
nge n`.
-/
theorem Fin.prod_univ_eq_prod_range [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∏ i : Fin n, f i = ∏ i ∈ range n, f i :=
  calc
    ∏ i : Fin n, f i = ∏ i : { x // x ∈ range n }, f i :=
      Fintype.prod_equiv (Fin.equivSubtype.trans (Equiv.subtypeEquivRight (by simp))) _ _ (by simp)
    _ = ∏ i ∈ range n, f i := by rw [← attach_eq_univ, prod_attach]

@[to_additive]
/-
**Finset.prod_fin_eq_prod_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.prod_fin_eq_prod_range [CommMonoid β] {n : Nat} (c : Fin n -> β) : 
∏ i, c i = ∏ i in Finset.range n, if h : i < n then c ⟨i, h⟩ else 1
参数：c : Fin n -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.prod_univ_eq_prod_range`：Fin.prod_univ_eq_prod_range [CommMonoid α] 
(f : Nat -> α) (n : Nat) : ∏ i : Fin n, f i = ∏ i in range n, f i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.prod_fin_eq_prod_range [CommMonoid β] {n : ℕ} (c : Fin n → β) :
    ∏ i, c i = ∏ i ∈ Finset.range n, if h : i < n then c ⟨i, h⟩ else 1 := by
  rw [← Fin.prod_univ_eq_prod_range, Finset.prod_congr rfl]
  rintro ⟨i, hi⟩ _
  simp only [hi, dif_pos]

@[to_additive]
/-
**Finset.prod_toFinset_eq_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.prod_toFinset_eq_subtype {M : Type*} [CommMonoid M] [Fintype α] (p 
: α -> Prop) [DecidablePred p] (f : α -> M) : ∏ a in { x | p x }.toFinset, f a =
 ∏ a : Subtype p, f a
参数：p : α -> Prop；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subtype`：prod_subtype {p : ι -> Prop} {F : Fintype (Subtype 
p)} (s : Finset ι) (h : forall x, x in s ↔ p x) (f : ι -> M) : ∏ a in s, f a = ∏
 a : Subt…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Finset.prod_toFinset_eq_subtype {M : Type*} [CommMonoid M] [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → M) : ∏ a ∈ { x | p x }.toFinset, f a = ∏ a : Subtype p, f a := by
  rw [← Finset.prod_subtype]
  simp_rw [Set.mem_toFinset]; intro; rfl

nonrec theorem Fintype.prod_dite [Fintype α] {p : α → Prop} [DecidablePred p] [CommMonoid β]
    (f : ∀ a, p a → β) (g : ∀ a, ¬p a → β) :
    (∏ a, dite (p a) (f a) (g a)) =
    (∏ a : { a // p a }, f a a.2) * ∏ a : { a // ¬p a }, g a a.2 := by
  simp only [prod_dite]
  congr 1
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // p x } => f x x.2
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // ¬p x } => g x x.2

section

variable {α₁ : Type*} {α₂ : Type*} {M : Type*} [Fintype α₁] [Fintype α₂] [CommMonoid M]

@[to_additive]
/-
**Fintype.prod_sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_sumElim (f : α₁ -> M) (g : α₂ -> M) : ∏ x, Sum.elim f g x = (
∏ a₁, f a₁) * ∏ a₂, g a₂
参数：f : α₁ -> M；g : α₂ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_disjSum`：prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι o
plus κ -> M) : ∏ x in s.disjSum t, f x = (∏ x in s, f (Sum.inl x)) * ∏ x in t, f
 (Sum.inr…
-/
theorem Fintype.prod_sumElim (f : α₁ → M) (g : α₂ → M) :
    ∏ x, Sum.elim f g x = (∏ a₁, f a₁) * ∏ a₂, g a₂ :=
  prod_disjSum _ _ _

@[to_additive (attr := simp)]
/-
**Fintype.prod_sum_type** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_sum_type (f : α₁ oplus α₂ -> M) : ∏ x, f x = (∏ a₁, f (Sum.in
l a₁)) * ∏ a₂, f (Sum.inr a₂)
参数：f : α₁ oplus α₂ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_disjSum`：prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι o
plus κ -> M) : ∏ x in s.disjSum t, f x = (∏ x in s, f (Sum.inl x)) * ∏ x in t, f
 (Sum.inr…
-/
theorem Fintype.prod_sum_type (f : α₁ ⊕ α₂ → M) :
    ∏ x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂) :=
  prod_disjSum _ _ _

/-- The product over a product type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Fintype.prod_prod_type'`. -/
@[to_additive Fintype.sum_prod_type /-- The sum over a product type equals the sum of fiberwise
sums. For rewriting in the reverse direction, use `Fintype.sum_prod_type'`. -/]
/-
**Fintype.prod_prod_type** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_prod_type [CommMonoid γ] (f : α₁ × α₂ -> γ) : ∏ x, f x = ∏ x,
 ∏ y, f (x, y)
参数：f : α₁ × α₂ -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_product`：prod_product (s : Finset γ) (t : Finset α) (f : γ ×
 α -> β) : ∏ x in s ×ˢ t, f x = ∏ x in s, ∏ y in t, f (x, y)
-/
theorem Fintype.prod_prod_type [CommMonoid γ] (f : α₁ × α₂ → γ) :
    ∏ x, f x = ∏ x, ∏ y, f (x, y) :=
  Finset.prod_product ..

/-- The product over a product type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Fintype.prod_prod_type`. -/
@[to_additive Fintype.sum_prod_type' /-- The sum over a product type equals the sum of fiberwise
sums. For rewriting in the reverse direction, use `Fintype.sum_prod_type`. -/]
/-
**Fintype.prod_prod_type'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_prod_type' [CommMonoid γ] (f : α₁ -> α₂ -> γ) : ∏ x : α₁ × α₂
, f x.1 x.2 = ∏ x, ∏ y, f x y
参数：f : α₁ -> α₂ -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_product'`：prod_product' (s : Finset γ) (t : Finset α) (f : γ
 -> α -> β) : ∏ x in s ×ˢ t, f x.1 x.2 = ∏ x in s, ∏ y in t, f x y
-/
theorem Fintype.prod_prod_type' [CommMonoid γ] (f : α₁ → α₂ → γ) :
    ∏ x : α₁ × α₂, f x.1 x.2 = ∏ x, ∏ y, f x y :=
  Finset.prod_product' ..

@[to_additive Fintype.sum_prod_type_right]
/-
**Fintype.prod_prod_type_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_prod_type_right [CommMonoid γ] (f : α₁ × α₂ -> γ) : ∏ x, f x 
= ∏ y, ∏ x, f (x, y)
参数：f : α₁ × α₂ -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_product_right`：prod_product_right (s : Finset γ) (t : Finset
 α) (f : γ × α -> β) : ∏ x in s ×ˢ t, f x = ∏ y in t, ∏ x in s, f (x, y)
-/
theorem Fintype.prod_prod_type_right [CommMonoid γ] (f : α₁ × α₂ → γ) :
    ∏ x, f x = ∏ y, ∏ x, f (x, y) :=
  Finset.prod_product_right ..

/-- An uncurried version of `Finset.prod_prod_type_right`. -/
@[to_additive Fintype.sum_prod_type_right'
/-- An uncurried version of `Finset.sum_prod_type_right` -/]
/-
**Fintype.prod_prod_type_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_prod_type_right' [CommMonoid γ] (f : α₁ -> α₂ -> γ) : ∏ x : α
₁ × α₂, f x.1 x.2 = ∏ y, ∏ x, f x y
参数：f : α₁ -> α₂ -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_product_right'`：prod_product_right' (s : Finset γ) (t : Fins
et α) (f : γ -> α -> β) : ∏ x in s ×ˢ t, f x.1 x.2 = ∏ y in t, ∏ x in s, f x y
-/
theorem Fintype.prod_prod_type_right' [CommMonoid γ] (f : α₁ → α₂ → γ) :
    ∏ x : α₁ × α₂, f x.1 x.2 = ∏ y, ∏ x, f x y :=
  Finset.prod_product_right' ..

end

