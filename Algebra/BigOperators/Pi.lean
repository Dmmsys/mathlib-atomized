/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.FunLike.IsApply

/-!
# Big operators for Pi Types

This file contains theorems relevant to big operators in binary and arbitrary products
of monoids and groups.
-/

@[expose] public section

open scoped Finset

variable {ι κ M N R α : Type*}

namespace Pi

@[to_additive]
/-
**Pi.list_prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：list_prod_apply {α : Type*} {M : α -> Type*} [forall a, Monoid (M a)] (a :
 α) (l : List (forall a, M a)) : l.prod a = (l.map fun f : forall a, M a => f a)
.prod
参数：M a；a : α；l : List (forall a, M a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
theorem list_prod_apply {α : Type*} {M : α → Type*} [∀ a, Monoid (M a)] (a : α)
    (l : List (∀ a, M a)) : l.prod a = (l.map fun f : ∀ a, M a ↦ f a).prod :=
  map_list_prod (evalMonoidHom M a) _

@[to_additive]
/-
**Pi.multiset_prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：multiset_prod_apply {α : Type*} {M : α -> Type*} [forall a, CommMonoid (M 
a)] (a : α) (s : Multiset (forall a, M a)) : s.prod a = (s.map fun f : forall a,
 M a => f a).prod
参数：M a；a : α；s : Multiset (forall a, M a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_multiset_prod`：∀ {M : Type u_5} {N : Type u_6} [inst : Com
mMonoid M] [inst_1 : CommMonoid N] (f : M →* N) (s : Multiset M),   f s.prod = (
Multiset.map (⇑f)…
-/
theorem multiset_prod_apply {α : Type*} {M : α → Type*} [∀ a, CommMonoid (M a)] (a : α)
    (s : Multiset (∀ a, M a)) : s.prod a = (s.map fun f : ∀ a, M a ↦ f a).prod :=
  (evalMonoidHom M a).map_multiset_prod _

end Pi

@[to_additive (attr := simp)]
/-
**Finset.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.prod_apply {α : Type*} {M : α -> Type*} [forall a, CommMonoid (M a)
] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in s, g c) a = ∏ c in s
, g c a
参数：M a；a : α；s : Finset ι；g : ι -> forall a, M a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem Finset.prod_apply {α : Type*} {M : α → Type*} [∀ a, CommMonoid (M a)] (a : α)
    (s : Finset ι) (g : ι → ∀ a, M a) : (∏ c ∈ s, g c) a = ∏ c ∈ s, g c a :=
  map_prod (Pi.evalMonoidHom M a) _ _

/-- An 'unapplied' analogue of `Finset.prod_apply`. -/
@[to_additive (attr := push ←) /-- An 'unapplied' analogue of `Finset.sum_apply`. -/]
/-
**Finset.prod_fn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.prod_fn {α : Type*} {M : α -> Type*} {ι} [forall a, CommMonoid (M a
)] (s : Finset ι) (g : ι -> forall a, M a) : ∏ c in s, g c = fun a => ∏ c in s, 
g c a
参数：M a；s : Finset ι；g : ι -> forall a, M a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…

--- 原说明 ---
An 'unapplied' analogue of `Finset.prod_apply`.
-/
theorem Finset.prod_fn {α : Type*} {M : α → Type*} {ι} [∀ a, CommMonoid (M a)] (s : Finset ι)
    (g : ι → ∀ a, M a) : ∏ c ∈ s, g c = fun a ↦ ∏ c ∈ s, g c a :=
  funext fun _ ↦ Finset.prod_apply _ _ _

@[to_additive]
/-
**Fintype.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_apply {α : Type*} {M : α -> Type*} [Fintype ι] [forall a, Com
mMonoid (M a)] (a : α) (g : ι -> forall a, M a) : (∏ c, g c) a = ∏ c, g c a
参数：M a；a : α；g : ι -> forall a, M a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
-/
theorem Fintype.prod_apply {α : Type*} {M : α → Type*} [Fintype ι] [∀ a, CommMonoid (M a)] (a : α)
    (g : ι → ∀ a, M a) : (∏ c, g c) a = ∏ c, g c a :=
  Finset.prod_apply a Finset.univ g

@[to_additive prod_mk_sum]
/-
**prod_mk_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_mk_prod [CommMonoid M] [CommMonoid N] (s : Finset ι) (f : ι -> M) (g 
: ι -> N) : (∏ x in s, f x, ∏ x in s, g x) = ∏ x in s, (f x, g x)
参数：s : Finset ι；f : ι -> M；g : ι -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_mk_prod [CommMonoid M] [CommMonoid N] (s : Finset ι) (f : ι → M) (g : ι → N) :
    (∏ x ∈ s, f x, ∏ x ∈ s, g x) = ∏ x ∈ s, (f x, g x) :=
  haveI := Classical.decEq ι
  Finset.induction_on s rfl (by simp +contextual [Prod.ext_iff])

/-- decomposing `x : ι → R` as a sum along the canonical basis -/
/-
**pi_eq_sum_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAss
ocSemiring R] (x : ι -> R) : x = ∑ i, (x i) • fun j => if i = j then (1 : R) els
e 0
参数：x : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
decomposing `x : ι → R` as a sum along the canonical basis
-/
theorem pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
    (x : ι → R) : x = ∑ i, (x i) • fun j => if i = j then (1 : R) else 0 := by
  ext
  simp

/-- Decomposing `x : ι → R` as a sum along the canonical basis `Pi.single i 1` for `i : ι`. -/
/-
**pi_eq_sum_univ'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pi_eq_sum_univ' {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAs
socSemiring R] (x : ι -> R) : x = ∑ i, (x i) • Pi.single (M
参数：x : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `pi_eq_sum_univ`：pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {
R : Type*} [NonAssocSemiring R] (x : ι -> R) : x = ∑ i, (x i) • fun j => if i = 
j th…

--- 原说明 ---
Decomposing `x : ι → R` as a sum along the canonical basis `Pi.single i 1` for `
i : ι`.
-/
theorem pi_eq_sum_univ' {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
    (x : ι → R) : x = ∑ i, (x i) • Pi.single (M := fun _ ↦ R) i 1 := by
  convert! pi_eq_sum_univ x
  aesop

section CommSemiring
variable [CommSemiring R]

/-
**prod_indicator_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prod_indicator_apply (s : Finset ι) (f : ι -> Set κ) (g : ι -> κ -> R) (j 
: κ) : ∏ i in s, (f i).indicator (g i) j = (⋂ x in s, f x).indicator (∏ i in s, 
g i) j
参数：s : Finset ι；f : ι -> Set κ；g : ι -> κ -> R；j : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator.eq_1`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s :
 Set α) (f : α → M) (x : α),   s.indicator f x = if x ∈ s then f x else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
-/
lemma prod_indicator_apply (s : Finset ι) (f : ι → Set κ) (g : ι → κ → R) (j : κ) :
    ∏ i ∈ s, (f i).indicator (g i) j = (⋂ x ∈ s, f x).indicator (∏ i ∈ s, g i) j := by
  rw [Set.indicator]
  split_ifs with hj
  · rw [Finset.prod_apply]
    congr! 1 with i hi
    simp only [Set.mem_iInter] at hj
    exact Set.indicator_of_mem (hj _ hi) _
  · obtain ⟨i, hi, hj⟩ := by simpa using hj
    exact Finset.prod_eq_zero hi <| Set.indicator_of_notMem hj _
/-
**prod_indicator** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prod_indicator (s : Finset ι) (f : ι -> Set κ) (g : ι -> κ -> R) : ∏ i in 
s, (f i).indicator (g i) = (⋂ x in s, f x).indicator (∏ i in s, g i)
参数：s : Finset ι；f : ι -> Set κ；g : ι -> κ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用引理 `prod_indicator_apply`：prod_indicator_apply (s : Finset ι) (f : ι -> Set 
κ) (g : ι -> κ -> R) (j : κ) : ∏ i in s, (f i).indicator (g i) j = (⋂ x in s, f 
x).indicat…
-/
lemma prod_indicator (s : Finset ι) (f : ι → Set κ) (g : ι → κ → R) :
    ∏ i ∈ s, (f i).indicator (g i) = (⋂ x ∈ s, f x).indicator (∏ i ∈ s, g i) := by
  ext a; simpa using prod_indicator_apply ..
/-
**prod_indicator_const_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prod_indicator_const_apply (s : Finset ι) (f : ι -> Set κ) (g : κ -> R) (j
 : κ) : ∏ i in s, (f i).indicator g j = (⋂ x in s, f x).indicator (g ^ #s) j
参数：s : Finset ι；f : ι -> Set κ；g : κ -> R；j : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `prod_indicator_apply`：prod_indicator_apply (s : Finset ι) (f : ι -> Set 
κ) (g : ι -> κ -> R) (j : κ) : ∏ i in s, (f i).indicator (g i) j = (⋂ x in s, f 
x).indicat…
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_indicator_const_apply (s : Finset ι) (f : ι → Set κ) (g : κ → R) (j : κ) :
    ∏ i ∈ s, (f i).indicator g j = (⋂ x ∈ s, f x).indicator (g ^ #s) j := by
  simp [prod_indicator_apply]
/-
**prod_indicator_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prod_indicator_const (s : Finset ι) (f : ι -> Set κ) (g : κ -> R) : ∏ i in
 s, (f i).indicator g = (⋂ x in s, f x).indicator (g ^ #s)
参数：s : Finset ι；f : ι -> Set κ；g : κ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `prod_indicator`：prod_indicator (s : Finset ι) (f : ι -> Set κ) (g : ι ->
 κ -> R) : ∏ i in s, (f i).indicator (g i) = (⋂ x in s, f x).indicator (∏ i in s
, g …
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_indicator_const (s : Finset ι) (f : ι → Set κ) (g : κ → R) :
    ∏ i ∈ s, (f i).indicator g = (⋂ x ∈ s, f x).indicator (g ^ #s) := by simp [prod_indicator]

end CommSemiring

section MulSingle

variable {I : Type*} [DecidableEq I] {M : I → Type*}
variable [∀ i, CommMonoid (M i)]

@[to_additive]
/-
**Finset.univ_prod_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.univ_prod_mulSingle [Fintype I] (f : forall i, M i) : (∏ i, Pi.mulS
ingle i (f i)) = f
参数：f : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_pi_mulSingle`：prod_pi_mulSingle {M : ι -> Type*} [DecidableE
q ι] [forall a, CommMonoid (M a)] (a : ι) (f : forall a, M a) (s : Finset ι) : (
∏ a' in s, Pi.…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.univ_prod_mulSingle [Fintype I] (f : ∀ i, M i) :
    (∏ i, Pi.mulSingle i (f i)) = f := by
  ext a
  simp

@[to_additive]
/-
**MonoidHom.functions_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.functions_ext [Finite I] (N : Type*) [CommMonoid N] (g h : (fora
ll i, M i) ->* N) (H : forall i x, g (Pi.mulSingle i x) = h (Pi.mulSingle i x)) 
: g = h
参数：N : Type*；g h : (forall i, M i) ->* N；H : forall i x, g (Pi.mulSingle i x) = 
h (Pi.mulSingle i x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_prod_mulSingle`：Finset.univ_prod_mulSingle [Fintype I] (f : 
forall i, M i) : (∏ i, Pi.mulSingle i (f i)) = f
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MonoidHom.functions_ext [Finite I] (N : Type*) [CommMonoid N] (g h : (∀ i, M i) →* N)
    (H : ∀ i x, g (Pi.mulSingle i x) = h (Pi.mulSingle i x)) : g = h := by
  cases nonempty_fintype I
  ext k
  rw [← Finset.univ_prod_mulSingle k, map_prod, map_prod]
  simp only [H]

/-- This is used as the ext lemma instead of `MonoidHom.functions_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext)
      /-- This is used as the ext lemma instead of `AddMonoidHom.functions_ext` for reasons
      explained in note [partially-applied ext lemmas]. -/]
/-
**MonoidHom.functions_ext'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.functions_ext' [Finite I] (N : Type*) [CommMonoid N] (g h : (for
all i, M i) ->* N) (H : forall i, g.comp (MonoidHom.mulSingle M i) = h.comp (Mon
oidHom.mulSingle M i)) : g = h
参数：N : Type*；g h : (forall i, M i) ->* N；H : forall i, g.comp (MonoidHom.mulSing
le M i) = h.comp (MonoidHom.mulSingle M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.functions_ext`：MonoidHom.functions_ext [Finite I] (N : Type*) 
[CommMonoid N] (g h : (forall i, M i) ->* N) (H : forall i x, g (Pi.mulSingle i 
x) = h (Pi.mu…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem MonoidHom.functions_ext' [Finite I] (N : Type*) [CommMonoid N] (g h : (∀ i, M i) →* N)
    (H : ∀ i, g.comp (MonoidHom.mulSingle M i) = h.comp (MonoidHom.mulSingle M i)) : g = h :=
  g.functions_ext N h fun i => DFunLike.congr_fun (H i)

end MulSingle

section RingHom

open Pi

variable {I : Type*} [DecidableEq I] {R : I → Type*}
variable [∀ i, NonAssocSemiring (R i)]

@[ext]
/-
**RingHom.functions_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.functions_ext [Finite I] (S : Type*) [NonAssocSemiring S] (g h : (
forall i, R i) ->+* S) (H : forall (i : I) (x : R i), g (single i x) = h (single
 i x)) : g = h
参数：S : Type*；g h : (forall i, R i) ->+* S；H : forall (i : I) (x : R i), g (singl
e i x) = h (single i x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.coe_addMonoidHom_injective`：coe_addMonoidHom_injective : Injecti
ve (fun f : α ->+* β => (f : α ->+ β))
· 使用定理 `AddMonoidHom.functions_ext`：∀ {I : Type u_7} [inst : DecidableEq I] {M :
 I → Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [Finite I]   (N : Type u
_9) [inst_3 : Ad…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem RingHom.functions_ext [Finite I] (S : Type*) [NonAssocSemiring S] (g h : (∀ i, R i) →+* S)
    (H : ∀ (i : I) (x : R i), g (single i x) = h (single i x)) : g = h :=
  RingHom.coe_addMonoidHom_injective <|
    @AddMonoidHom.functions_ext I _ R _ _ S _ (g : (∀ i, R i) →+ S) h H

end RingHom

namespace Prod

variable [CommMonoid M] [CommMonoid N] {s : Finset ι} {f : ι → M × N}

@[to_additive]
/-
**Prod.fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_prod : (∏ c in s, f c).1 = ∏ c in s, (f c).1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem fst_prod : (∏ c ∈ s, f c).1 = ∏ c ∈ s, (f c).1 :=
  map_prod (MonoidHom.fst ..) f s

@[to_additive]
/-
**Prod.snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_prod : (∏ c in s, f c).2 = ∏ c in s, (f c).2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem snd_prod : (∏ c ∈ s, f c).2 = ∏ c ∈ s, (f c).2 :=
  map_prod (MonoidHom.snd ..) f s

end Prod

section MulEquiv

/-- The canonical isomorphism between the monoid of homomorphisms from a finite product of
commutative monoids to another commutative monoid and the product of the homomorphism monoids. -/
@[to_additive /-- The canonical isomorphism between the additive monoid of homomorphisms from
a finite product of additive commutative monoids to another additive commutative monoid and
the product of the homomorphism monoids. -/]
/-
**Pi.monoidHomMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pi.monoidHomMulEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι -> Typ
e*) [(i : ι) -> CommMonoid (M i)] (M' : Type*) [CommMonoid M'] : (((i : ι) -> M 
i) ->* M') ≃* ((i : ι) -> (M i ->* M')) where toFun φ i
参数：M : ι -> Type*；i : ι；M i；M' : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Pi.monoidHomMulEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → Type*)
    [(i : ι) → CommMonoid (M i)] (M' : Type*) [CommMonoid M'] :
    (((i : ι) → M i) →* M') ≃* ((i : ι) → (M i →* M')) where
  toFun φ i := φ.comp <| MonoidHom.mulSingle M i
  invFun φ := ∏ (i : ι), (φ i).comp (Pi.evalMonoidHom M i)
  left_inv φ := by
    ext
    simp only [MonoidHom.finsetProd_apply, MonoidHom.coe_comp, Function.comp_apply,
      evalMonoidHom_apply, MonoidHom.mulSingle_apply, ← map_prod]
    refine congrArg _ <| funext fun _ ↦ ?_
    rw [Fintype.prod_apply]
    exact Fintype.prod_pi_mulSingle ..
  right_inv φ := by
    ext i m
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply,
      MonoidHom.finsetProd_apply, evalMonoidHom_apply, ]
    let φ' i : M i → M' := ⇑(φ i)
    conv =>
      enter [1, 2, j]
      rw [show φ j = φ' j from rfl, Pi.apply_mulSingle φ' (fun i ↦ map_one (φ i))]
    rw [show φ' i = φ i from rfl]
    exact Fintype.prod_pi_mulSingle' ..
  map_mul' φ ψ := by
    ext
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply,
      MonoidHom.mul_apply, mul_apply]

end MulEquiv

variable [Finite ι] [DecidableEq ι] {M : ι → Type*}

-- manually additivized to fix variable names
-- See https://github.com/leanprover-community/mathlib4/issues/11462
/-
**Pi.single_induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.single_induction [forall i, AddCommMonoid (M i)] (p : (Π i, M i) -> Pro
p) (f : Π i, M i) (zero : p 0) (add : forall f g, p f -> p g -> p (f + g)) (sing
le : forall i m, p (Pi.single i m)) : p f
参数：M i；p : (Π i, M i) -> Prop；f : Π i, M i；zero : p 0；add : forall f g, p f -> p
 g -> p (f + g)；single : forall i m, p (Pi.single i m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_sum_single`：∀ {I : Type u_7} [inst : DecidableEq I] {M : I →
 Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [inst_2 : Fintype I]   (f : 
(i : I) → M …
· 使用定理 `Finset.sum_induction`：∀ {ι : Type u_1} {s : Finset ι} {M : Type u_7} [in
st : AddCommMonoid M] (f : ι → M) (p : M → Prop),   (∀ (a b : M), p a → p b → p 
(a + b)) →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Pi.single_induction [∀ i, AddCommMonoid (M i)] (p : (Π i, M i) → Prop) (f : Π i, M i)
    (zero : p 0) (add : ∀ f g, p f → p g → p (f + g))
    (single : ∀ i m, p (Pi.single i m)) : p f := by
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single f]
  exact Finset.sum_induction _ _ add zero (by simp [single])

@[to_additive existing (attr := elab_as_elim)]
/-
**Pi.mulSingle_induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_induction [forall i, CommMonoid (M i)] (p : (Π i, M i) -> Pro
p) (f : Π i, M i) (one : p 1) (mul : forall f g, p f -> p g -> p (f * g)) (mulSi
ngle : forall i m, p (Pi.mulSingle i m)) : p f
参数：M i；p : (Π i, M i) -> Prop；f : Π i, M i；one : p 1；mul : forall f g, p f -> p 
g -> p (f * g)；mulSingle : forall i m, p (Pi.mulSingle i m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_prod_mulSingle`：Finset.univ_prod_mulSingle [Fintype I] (f : 
forall i, M i) : (∏ i, Pi.mulSingle i (f i)) = f
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Pi.mulSingle_induction [∀ i, CommMonoid (M i)] (p : (Π i, M i) → Prop) (f : Π i, M i)
    (one : p 1) (mul : ∀ f g, p f → p g → p (f * g))
    (mulSingle : ∀ i m, p (Pi.mulSingle i m)) : p f := by
  cases nonempty_fintype ι
  rw [← Finset.univ_prod_mulSingle f]
  exact Finset.prod_induction _ _ mul one (by simp [mulSingle])

section EqOn

@[to_additive]
/-
**eqOn_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eqOn_finsetProd {ι α β : Type*} [CommMonoid α] {s : Set β} {f f' : ι -> β 
-> α} (h : forall (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) : Set.EqOn (∏
 i in v, f i) (∏ i in v, f' i) s
参数：h : forall (i : ι), Set.EqOn (f i) (f' i) s；v : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eqOn_finsetProd {ι α β : Type*} [CommMonoid α]
    {s : Set β} {f f' : ι → β → α} (h : ∀ (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (∏ i ∈ v, f i) (∏ i ∈ v, f' i) s :=
  fun t ht => by simp [funext fun i ↦ h i ht]

@[to_additive]
/-
**eqOn_fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eqOn_fun_finsetProd {ι α β : Type*} [CommMonoid α] {s : Set β} {f f' : ι -
> β -> α} (h : forall (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) : Set.EqO
n (fun b => ∏ i in v, f i b) (fun b => ∏ i in v, f' i b) s
参数：h : forall (i : ι), Set.EqOn (f i) (f' i) s；v : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eqOn_finsetProd`：eqOn_finsetProd {ι α β : Type*} [CommMonoid α] {s : Set
 β} {f f' : ι -> β -> α} (h : forall (i : ι), Set.EqOn (f i) (f' i) s) (v : Fins
et ι)…
-/
theorem eqOn_fun_finsetProd {ι α β : Type*} [CommMonoid α]
    {s : Set β} {f f' : ι → β → α} (h : ∀ (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (fun b ↦ ∏ i ∈ v, f i b) (fun b ↦ ∏ i ∈ v, f' i b) s := by
  convert! eqOn_finsetProd h v <;> simp

end EqOn

section FunLike

variable {F α β ι : Type*} [FunLike F α β] [CommMonoid β] [CommMonoid F]
  [IsOneApply F α β] [IsMulApply F α β]

@[to_additive (attr := simp, grind =)]
/-
**prod_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_apply (s : Finset ι) (f : ι -> F) (x : α) : (∏ i in s, f i) x = ∏ i i
n s, f i x
参数：s : Finset ι；f : ι -> F；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : One β}   {inst_2 : One F} [self : IsOn…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Mul β}   {inst_2 : Mul F} [self : IsMu…
-/
theorem prod_apply (s : Finset ι) (f : ι → F) (x : α) : (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h => simp [his, h]

@[to_additive (attr := norm_cast)]
/-
**FunLike.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FunLike.coe_prod (s : Finset ι) (f : ι -> F) : ↑(∏ i in s, f i) = ∏ i in s
, (f i : α -> β)
参数：s : Finset ι；f : ι -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `prod_apply`：prod_apply (s : Finset ι) (f : ι -> F) (x : α) : (∏ i in s, 
f i) x = ∏ i in s, f i x
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem FunLike.coe_prod (s : Finset ι) (f : ι → F) : ↑(∏ i ∈ s, f i) = ∏ i ∈ s, (f i : α → β) := by
  ext; simp

end FunLike

