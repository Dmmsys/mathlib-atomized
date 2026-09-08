/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.ZMod.Defs

/-!
# Freiman homomorphisms

In this file, we define Freiman homomorphisms and isomorphisms.

An `n`-Freiman homomorphism from `A` to `B` is a function `f : α → β` such that `f '' A ⊆ B` and
`f x₁ * ... * f xₙ = f y₁ * ... * f yₙ` for all `x₁, ..., xₙ, y₁, ..., yₙ ∈ A` such that
`x₁ * ... * xₙ = y₁ * ... * yₙ`. In particular, any `MulHom` is a Freiman homomorphism.

Note a `0`- or `1`-Freiman homomorphism is simply a map, thus a `2`-Freiman homomorphism is the
first interesting case (and the most common). As `n` increases further, the property of being
an `n`-Freiman homomorphism between abelian groups becomes increasingly stronger.

An `n`-Freiman isomorphism from `A` to `B` is a function `f : α → β` bijective between `A` and `B`
such that `f x₁ * ... * f xₙ = f y₁ * ... * f yₙ ↔ x₁ * ... * xₙ = y₁ * ... * yₙ` for all
`x₁, ..., xₙ, y₁, ..., yₙ ∈ A`. In particular, any `MulEquiv` is a Freiman isomorphism.

They are of interest in additive combinatorics.

## Main declarations

* `IsMulFreimanHom`: Predicate for a function to be a multiplicative Freiman homomorphism.
* `IsAddFreimanHom`: Predicate for a function to be an additive Freiman homomorphism.
* `IsMulFreimanIso`: Predicate for a function to be a multiplicative Freiman isomorphism.
* `IsAddFreimanIso`: Predicate for a function to be an additive Freiman isomorphism.

## Main results

* `isMulFreimanHom_two`: Characterisation of `2`-Freiman homomorphisms.
* `IsMulFreimanHom.mono`: If `m ≤ n` and `f` is an `n`-Freiman homomorphism, then it is also an
  `m`-Freiman homomorphism.

## Implementation notes

In the context of combinatorics, we are interested in Freiman homomorphisms over sets which are not
necessarily closed under addition/multiplication. This means we must parametrize them with a set in
an `AddMonoid`/`Monoid` instead of the `AddMonoid`/`Monoid` itself.

## References

[Yufei Zhao, *18.225: Graph Theory and Additive Combinatorics*](https://yufeizhao.com/gtac/)

## TODO

* `MonoidHomClass.isMulFreimanHom` could be relaxed to `MulHom.toFreimanHom` by proving
  `(s.map f).prod = (t.map f).prod` directly by induction instead of going through `f s.prod`.
* Affine maps are Freiman homomorphisms.
-/

@[expose] public section

assert_not_exists Field Ideal TwoSidedIdeal

open Multiset Set
open scoped Pointwise

variable {F α β γ : Type*}

section CommMonoid
variable [CommMonoid α] [CommMonoid β] [CommMonoid γ] {A A₁ A₂ : Set α}
  {B B₁ B₂ : Set β} {C : Set γ} {f f₁ f₂ : α → β} {g : β → γ} {n : ℕ}

/-- An additive `n`-Freiman homomorphism from a set `A` to a set `B` is a map which preserves sums
of `n` elements. -/
/-
**IsAddFreimanHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [AddCommMonoid α] → [AddCommMonoid β] → 
ℕ → Set α → Set β → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive `n`-Freiman homomorphism from a set `A` to a set `B` is a map which 
preserves sums
of `n` elements.
-/
structure IsAddFreimanHom [AddCommMonoid α] [AddCommMonoid β] (n : ℕ) (A : Set α) (B : Set β)
    (f : α → β) : Prop where
  mapsTo : MapsTo f A B
  /-- An additive `n`-Freiman homomorphism preserves sums of `n` elements. -/
  map_sum_eq_map_sum ⦃s t : Multiset α⦄ (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.sum = t.sum) :
    (s.map f).sum = (t.map f).sum

/-- An `n`-Freiman homomorphism from a set `A` to a set `B` is a map which preserves products of `n`
elements. -/
@[to_additive]
/-
**IsMulFreimanHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [CommMonoid α] → [CommMonoid β] → ℕ → Se
t α → Set β → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `n`-Freiman homomorphism from a set `A` to a set `B` is a map which preserves
 products of `n`
elements.
-/
structure IsMulFreimanHom (n : ℕ) (A : Set α) (B : Set β) (f : α → β) : Prop where
  mapsTo : MapsTo f A B
  /-- An `n`-Freiman homomorphism preserves products of `n` elements. -/
  map_prod_eq_map_prod ⦃s t : Multiset α⦄ (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.prod = t.prod) :
    (s.map f).prod = (t.map f).prod

/-- An additive `n`-Freiman homomorphism from a set `A` to a set `B` is a bijective map which
preserves sums of `n` elements. -/
/-
**IsAddFreimanIso** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [AddCommMonoid α] → [AddCommMonoid β] → 
ℕ → Set α → Set β → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive `n`-Freiman homomorphism from a set `A` to a set `B` is a bijective 
map which
preserves sums of `n` elements.
-/
structure IsAddFreimanIso [AddCommMonoid α] [AddCommMonoid β] (n : ℕ) (A : Set α) (B : Set β)
    (f : α → β) : Prop where
  bijOn : BijOn f A B
  /-- An additive `n`-Freiman homomorphism preserves sums of `n` elements. -/
  map_sum_eq_map_sum ⦃s t : Multiset α⦄ (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) :
    (s.map f).sum = (t.map f).sum ↔ s.sum = t.sum

/-- An `n`-Freiman homomorphism from a set `A` to a set `B` is a map which preserves products of `n`
elements. -/
@[to_additive]
/-
**IsMulFreimanIso** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [CommMonoid α] → [CommMonoid β] → ℕ → Se
t α → Set β → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `n`-Freiman homomorphism from a set `A` to a set `B` is a map which preserves
 products of `n`
elements.
-/
structure IsMulFreimanIso (n : ℕ) (A : Set α) (B : Set β) (f : α → β) : Prop where
  bijOn : BijOn f A B
  /-- An `n`-Freiman homomorphism preserves products of `n` elements. -/
  map_prod_eq_map_prod ⦃s t : Multiset α⦄ (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) :
    (s.map f).prod = (t.map f).prod ↔ s.prod = t.prod

@[to_additive]
/-
**IsMulFreimanIso.isMulFreimanHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanIso.isMulFreimanHom (hf : IsMulFreimanIso n A B f) : IsMulFrei
manHom n A B f where mapsTo
参数：hf : IsMulFreimanIso n A B f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsMulFreimanIso.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanI…
-/
lemma IsMulFreimanIso.isMulFreimanHom (hf : IsMulFreimanIso n A B f) : IsMulFreimanHom n A B f where
  mapsTo := hf.bijOn.mapsTo
  map_prod_eq_map_prod _s _t hsA htA hs ht := (hf.map_prod_eq_map_prod hsA htA hs ht).2
/-
**IsMulFreimanHom.congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.congr (hf₁ : IsMulFreimanHom n A B f₁) (h : EqOn f₁ f₂ A) 
: IsMulFreimanHom n A B f₂ where mapsTo
参数：hf₁ : IsMulFreimanHom n A B f₁；h : EqOn f₁ f₂ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f₁ f₂ : α → β},   Set.MapsTo f₁ s t → Set.EqOn f₁ f₂ s → Set.MapsTo f₂ s t
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
-/
lemma IsMulFreimanHom.congr (hf₁ : IsMulFreimanHom n A B f₁) (h : EqOn f₁ f₂ A) :
    IsMulFreimanHom n A B f₂ where
  mapsTo := hf₁.mapsTo.congr h
  map_prod_eq_map_prod s t hsA htA hs ht h' := by
    rw [map_congr rfl fun x hx => (h (hsA hx)).symm, map_congr rfl fun x hx => (h (htA hx)).symm,
      hf₁.map_prod_eq_map_prod hsA htA hs ht h']
/-
**IsMulFreimanIso.congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanIso.congr (hf₁ : IsMulFreimanIso n A B f₁) (h : EqOn f₁ f₂ A) 
: IsMulFreimanIso n A B f₂ where bijOn
参数：hf₁ : IsMulFreimanIso n A B f₁；h : EqOn f₁ f₂ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f₁ f₂ : α → β},   Set.BijOn f₁ s t → Set.EqOn f₁ f₂ s → Set.BijOn f₂ s t
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用定理 `IsMulFreimanIso.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanI…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsMulFreimanIso.congr (hf₁ : IsMulFreimanIso n A B f₁) (h : EqOn f₁ f₂ A) :
    IsMulFreimanIso n A B f₂ where
  bijOn := hf₁.bijOn.congr h
  map_prod_eq_map_prod s t hsA htA hs ht := by
    rw [map_congr rfl fun x hx => h.symm (hsA hx), map_congr rfl fun x hx => h.symm (htA hx),
      hf₁.map_prod_eq_map_prod hsA htA hs ht]

/--
Given a Freiman isomorphism `f` from `A` to `B`, if `g` maps `B` into `A`, and is a right inverse
to `f` on `B`, then `g` is a Freiman isomorphism from `B` to `A`.
-/
@[to_additive
/--
Given an additive Freiman isomorphism `f` from `A` to `B`, if `g` maps `B` into `A`, and is a
right inverse to `f` on `B`, then `g` is an additive Freiman isomorphism from `B` to `A`.
-/]
/-
**IsMulFreimanIso.symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanIso.symm {g : β -> α} (hg₁ : MapsTo g B A) (hg₂ : RightInvOn g
 f B) (hf : IsMulFreimanIso n A B f) : IsMulFreimanIso n B A g where bijOn
参数：hg₁ : MapsTo g B A；hg₂ : RightInvOn g f B；hf : IsMulFreimanIso n A B f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} 
{f : α → β} {g : β → α},   Set.InvOn f g t s → Set.BijOn f s t → Set.BijOn g t s
· 使用定理 `Set.InjOn.rightInvOn_of_leftInvOn`：∀ {α : Type u_1} {β : Type u_2} {s : 
Set α} {t : Set β} {f : α → β} {f' : β → α},   Set.InjOn f s → Set.LeftInvOn f f
' t → Set.MapsTo f s t …
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMulFreimanIso.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanI…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsMulFreimanIso.symm {g : β → α} (hg₁ : MapsTo g B A) (hg₂ : RightInvOn g f B)
    (hf : IsMulFreimanIso n A B f) :
    IsMulFreimanIso n B A g where
  bijOn := hf.bijOn.symm ⟨hg₂, InjOn.rightInvOn_of_leftInvOn hf.bijOn.injOn hg₂ hf.bijOn.mapsTo hg₁⟩
  map_prod_eq_map_prod := fun s t hsB htB hs ht => by
    rw [← hf.map_prod_eq_map_prod _ _ (by simp [hs]) (by simp [ht]), map_map, map_congr rfl, map_id,
      map_map, map_congr rfl, map_id]
    all_goals aesop

/--
If the inverse of a Freiman homomorphism is itself a Freiman homomorphism, then it is a Freiman
isomorphism.
-/
@[to_additive
/--
If the inverse of a Freiman homomorphism is itself a Freiman homomorphism, then it is a Freiman
isomorphism.
-/]
/-
**IsMulFreimanHom.to_isMulFreimanIso** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.to_isMulFreimanIso {g : β -> α} (h : InvOn g f A B) (hf : 
IsMulFreimanHom n A B f) (hg : IsMulFreimanHom n B A g) : IsMulFreimanIso n A B 
f where bijOn
参数：h : InvOn g f A B；hf : IsMulFreimanHom n A B f；hg : IsMulFreimanHom n B A g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InvOn.bijOn`：bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : M
apsTo f' t s) : BijOn f s t
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
lemma IsMulFreimanHom.to_isMulFreimanIso {g : β → α} (h : InvOn g f A B)
    (hf : IsMulFreimanHom n A B f) (hg : IsMulFreimanHom n B A g) :
    IsMulFreimanIso n A B f where
  bijOn := h.bijOn hf.mapsTo hg.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht := by
    refine ⟨fun h' => ?_, hf.map_prod_eq_map_prod hsA htA hs ht⟩
    have : (map g (map f s)).prod = (map g (map f t)).prod := by
      have := hf.mapsTo
      apply hg.map_prod_eq_map_prod <;> simp_all [MapsTo]
    rwa [map_map, map_congr rfl fun x hx => ?g1, map_id, map_map,
      map_congr rfl fun x hx => ?g2, map_id] at this
    case g1 => exact h.1 (hsA hx)
    case g2 => exact h.1 (htA hx)

/-- If `f` is a multiplicative Freiman isomorphism from `A` to `B`, then `f.invFunOn A` is
a multiplicative Freiman isomorphism from `B` to `A`. -/
@[to_additive /-- If `f` is an additive Freiman isomorphism from `A` to `B`, then `f.invFunOn A` is
an additive Freiman isomorphism from `B` to `A`. -/]
/-
**IsMulFreimanIso.invFunOn** 是 Mathlib 中的一个定理，位于命名空间 `IsMulFreimanIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoid α] [inst_1 : CommMonoid
 β] {A : Set α} {B : Set β} {f : α → β}   {n : ℕ}, IsMulFreimanIso n A B f → IsM
ulFreimanIso n B A (Function.invFunOn f A)
参数：Function.invFunOn f A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsMulFreimanIso.symm`：IsMulFreimanIso.symm {g : β -> α} (hg₁ : MapsTo g 
B A) (hg₂ : RightInvOn g f B) (hf : IsMulFreimanIso n A B f) : IsMulFreimanIso n
 B A g whe…
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Set.SurjOn.mapsTo_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} 
{t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.MapsTo (Fu
nction.invFunOn …
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用定理 `Set.SurjOn.rightInvOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.RightI
nvOn (Function.invFu…
-/
protected lemma IsMulFreimanIso.invFunOn (hf : IsMulFreimanIso n A B f) :
    IsMulFreimanIso n B A (f.invFunOn A) :=
  hf.symm hf.bijOn.surjOn.mapsTo_invFunOn hf.bijOn.surjOn.rightInvOn_invFunOn

/-- A version of the Freiman homomorphism condition expressed using `Finset`s, for practicality. -/
@[to_additive /-- A version of the Freiman homomorphism condition expressed using `Finset`s,
for practicality. -/]
/-
**IsMulFreimanHom.prod_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.prod_apply (hf : IsMulFreimanHom n A B f) {s t : Finset α}
 {hsA : (s : Set α) subseteq A} {htA : (t : Set α) subseteq A} (hs : s.card = n)
 (ht : t.card = n) : ∏ i in s, i = ∏ i in t, i -> ∏ i in s, f i = ∏ i in t, f i
参数：hf : IsMulFreimanHom n A B f；s : Set α；t : Set α；hs : s.card = n；ht : t.card 
= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_val`：prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.p
rod id
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
-/
lemma IsMulFreimanHom.prod_apply (hf : IsMulFreimanHom n A B f) {s t : Finset α}
    {hsA : (s : Set α) ⊆ A} {htA : (t : Set α) ⊆ A}
    (hs : s.card = n) (ht : t.card = n) :
    ∏ i ∈ s, i = ∏ i ∈ t, i → ∏ i ∈ s, f i = ∏ i ∈ t, f i := by
  simpa using hf.map_prod_eq_map_prod hsA htA hs ht

@[to_additive]
/-
**IsMulFreimanHom.mul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.mul_eq_mul (hf : IsMulFreimanHom 2 A B f) {a b c d : α} (h
a : a in A) (hb : b in A) (hc : c in A) (hd : d in A) (h : a * b = c * d) : f a 
* f b = f c * f d
参数：hf : IsMulFreimanHom 2 A B f；ha : a in A；hb : b in A；hc : c in A；hd : d in A；
h : a * b = c * d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Multiset.card_pair`：card_pair (a b : α) : card {a, b} = 2
-/
lemma IsMulFreimanHom.mul_eq_mul (hf : IsMulFreimanHom 2 A B f) {a b c d : α}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (h : a * b = c * d) :
    f a * f b = f c * f d := by
  simp_rw [← prod_pair] at h ⊢
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) h <;> simp [ha, hb, hc, hd]

@[to_additive]
/-
**IsMulFreimanIso.mul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanIso.mul_eq_mul (hf : IsMulFreimanIso 2 A B f) {a b c d : α} (h
a : a in A) (hb : b in A) (hc : c in A) (hd : d in A) : f a * f b = f c * f d ↔ 
a * b = c * d
参数：hf : IsMulFreimanIso 2 A B f；ha : a in A；hb : b in A；hc : c in A；hd : d in A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMulFreimanIso.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanI…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Multiset.card_pair`：card_pair (a b : α) : card {a, b} = 2
-/
lemma IsMulFreimanIso.mul_eq_mul (hf : IsMulFreimanIso 2 A B f) {a b c d : α}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) :
    f a * f b = f c * f d ↔ a * b = c * d := by
  simp_rw [← prod_pair]
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) <;> simp [ha, hb, hc, hd]

/-- Characterisation of `2`-Freiman homomorphisms. -/
@[to_additive /-- Characterisation of `2`-Freiman homomorphisms. -/]
/-
**isMulFreimanHom_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulFreimanHom_two : IsMulFreimanHom 2 A B f ↔ MapsTo f A B ∧ forall a in
 A, forall b in A, forall c in A, forall d in A, a * b = c * d -> f a * f b = f 
c * f d where mp hf
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
· 使用引理 `IsMulFreimanHom.mul_eq_mul`：IsMulFreimanHom.mul_eq_mul (hf : IsMulFreima
nHom 2 A B f) {a b c d : α} (ha : a in A) (hb : b in A) (hc : c in A) (hd : d in
 A) (h : a * b =…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Characterisation of `2`-Freiman homomorphisms.
-/
lemma isMulFreimanHom_two :
    IsMulFreimanHom 2 A B f ↔ MapsTo f A B ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a * b = c * d → f a * f b = f c * f d where
  mp hf := ⟨hf.mapsTo, fun _ ha _ hb _ hc _ hd ↦ hf.mul_eq_mul ha hb hc hd⟩
  mpr hf := ⟨hf.1, by aesop (add simp card_eq_two)⟩

/-- Characterisation of `2`-Freiman homs. -/
@[to_additive /-- Characterisation of `2`-Freiman isomorphisms. -/]
/-
**isMulFreimanIso_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulFreimanIso_two : IsMulFreimanIso 2 A B f ↔ BijOn f A B ∧ forall a in 
A, forall b in A, forall c in A, forall d in A, f a * f b = f c * f d ↔ a * b = 
c * d where mp hf
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用引理 `IsMulFreimanIso.mul_eq_mul`：IsMulFreimanIso.mul_eq_mul (hf : IsMulFreima
nIso 2 A B f) {a b c d : α} (ha : a in A) (hb : b in A) (hc : c in A) (hd : d in
 A) : f a * f b …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Characterisation of `2`-Freiman homs.
-/
lemma isMulFreimanIso_two :
    IsMulFreimanIso 2 A B f ↔ BijOn f A B ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      f a * f b = f c * f d ↔ a * b = c * d where
  mp hf := ⟨hf.bijOn, fun _ ha _ hb _ hc _ hd => hf.mul_eq_mul ha hb hc hd⟩
  mpr hf := ⟨hf.1, by aesop (add simp card_eq_two)⟩
/-
**isMulFreimanHom_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : CommMonoid α] {A₁ A₂ : Set α} {n : ℕ}, A₁ ⊆ A₂ → 
IsMulFreimanHom n A₁ A₂ id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
-/
@[to_additive] lemma isMulFreimanHom_id (hA : A₁ ⊆ A₂) : IsMulFreimanHom n A₁ A₂ id where
  mapsTo := hA
  map_prod_eq_map_prod s t _ _ _ _ h := by simpa using h
/-
**isMulFreimanIso_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : CommMonoid α] {A : Set α} {n : ℕ}, IsMulFreimanIs
o n A A id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.bijOn_id`：bijOn_id (s : Set α) : BijOn id s s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] lemma isMulFreimanIso_id : IsMulFreimanIso n A A id where
  bijOn := bijOn_id _
  map_prod_eq_map_prod s t _ _ _ _ := by simp
/-
**IsMulFreimanHom.comp** 是 Mathlib 中的一个定理，位于命名空间 `IsMulFreimanHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : CommMonoid α] [inst
_1 : CommMonoid β] [inst_2 : CommMonoid γ]   {A : Set α} {B : Set β} {C : Set γ}
 {f : α → β} {g : β → γ} {n : ℕ},   IsMulFreimanHom n B C g → IsMulFreimanHom n 
A B f → IsMulFreimanHom n A C (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.MapsTo g t p → Set.Ma
psTo …
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
-/
@[to_additive] lemma IsMulFreimanHom.comp (hg : IsMulFreimanHom n B C g)
    (hf : IsMulFreimanHom n A B f) : IsMulFreimanHom n A C (g ∘ f) where
  mapsTo := hg.mapsTo.comp hf.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [← map_map, ← map_map]
    refine hg.map_prod_eq_map_prod ?_ ?_ (by rwa [card_map]) (by rwa [card_map])
      (hf.map_prod_eq_map_prod hsA htA hs ht h)
    · simpa using fun a h ↦ hf.mapsTo (hsA h)
    · simpa using fun a h ↦ hf.mapsTo (htA h)
/-
**IsMulFreimanIso.comp** 是 Mathlib 中的一个定理，位于命名空间 `IsMulFreimanIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : CommMonoid α] [inst
_1 : CommMonoid β] [inst_2 : CommMonoid γ]   {A : Set α} {B : Set β} {C : Set γ}
 {f : α → β} {g : β → γ} {n : ℕ},   IsMulFreimanIso n B C g → IsMulFreimanIso n 
A B f → IsMulFreimanIso n A C (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set 
α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.BijOn g t p → Set.BijO
n f …
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `IsMulFreimanIso.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanI…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma IsMulFreimanIso.comp (hg : IsMulFreimanIso n B C g)
    (hf : IsMulFreimanIso n A B f) : IsMulFreimanIso n A C (g ∘ f) where
  bijOn := hg.bijOn.comp hf.bijOn
  map_prod_eq_map_prod s t hsA htA hs ht := by
    rw [← map_map, ← map_map]
    rw [hg.map_prod_eq_map_prod _ _ (by rwa [card_map]) (by rwa [card_map]),
      hf.map_prod_eq_map_prod hsA htA hs ht]
    · simpa using fun a h ↦ hf.bijOn.mapsTo (hsA h)
    · simpa using fun a h ↦ hf.bijOn.mapsTo (htA h)
/-
**IsMulFreimanHom.subset** 是 Mathlib 中的一个定理，位于命名空间 `IsMulFreimanHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoid α] [inst_1 : CommMonoid
 β] {A₁ A₂ : Set α} {B₁ B₂ : Set β}   {f : α → β} {n : ℕ}, A₁ ⊆ A₂ → IsMulFreima
nHom n A₂ B₂ f → Set.MapsTo f A₁ B₁ → IsMulFreimanHom n A₁ B₁ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulFreimanHom.comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [in
st : CommMonoid α] [inst_1 : CommMonoid β] [inst_2 : CommMonoid γ]   {A : Set α}
 {B : Set …
· 使用定理 `isMulFreimanHom_id`：∀ {α : Type u_2} [inst : CommMonoid α] {A₁ A₂ : Set 
α} {n : ℕ}, A₁ ⊆ A₂ → IsMulFreimanHom n A₁ A₂ id
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
-/
@[to_additive] lemma IsMulFreimanHom.subset (hA : A₁ ⊆ A₂) (hf : IsMulFreimanHom n A₂ B₂ f)
    (hf' : MapsTo f A₁ B₁) : IsMulFreimanHom n A₁ B₁ f where
  mapsTo := hf'
  __ := hf.comp (isMulFreimanHom_id hA)
/-
**IsMulFreimanHom.superset** 是 Mathlib 中的一个定理，位于命名空间 `IsMulFreimanHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoid α] [inst_1 : CommMonoid
 β] {A : Set α} {B₁ B₂ : Set β} {f : α → β}   {n : ℕ}, B₁ ⊆ B₂ → IsMulFreimanHom
 n A B₁ f → IsMulFreimanHom n A B₂ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulFreimanHom.comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [in
st : CommMonoid α] [inst_1 : CommMonoid β] [inst_2 : CommMonoid γ]   {A : Set α}
 {B : Set …
· 使用定理 `isMulFreimanHom_id`：∀ {α : Type u_2} [inst : CommMonoid α] {A₁ A₂ : Set 
α} {n : ℕ}, A₁ ⊆ A₂ → IsMulFreimanHom n A₁ A₂ id
-/
@[to_additive] lemma IsMulFreimanHom.superset (hB : B₁ ⊆ B₂) (hf : IsMulFreimanHom n A B₁ f) :
    IsMulFreimanHom n A B₂ f := (isMulFreimanHom_id hB).comp hf
/-
**IsMulFreimanIso.subset** 是 Mathlib 中的一个定理，位于命名空间 `IsMulFreimanIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoid α] [inst_1 : CommMonoid
 β] {A₁ A₂ : Set α} {B₁ B₂ : Set β}   {f : α → β} {n : ℕ}, A₁ ⊆ A₂ → IsMulFreima
nIso n A₂ B₂ f → Set.BijOn f A₁ B₁ → IsMulFreimanIso n A₁ B₁ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulFreimanIso.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanI…
-/
@[to_additive] lemma IsMulFreimanIso.subset (hA : A₁ ⊆ A₂) (hf : IsMulFreimanIso n A₂ B₂ f)
    (hf' : BijOn f A₁ B₁) : IsMulFreimanIso n A₁ B₁ f where
  bijOn := hf'
  map_prod_eq_map_prod s t hsA htA hs ht := by
    refine hf.map_prod_eq_map_prod (fun a ha ↦ hA (hsA ha)) (fun a ha ↦ hA (htA ha)) hs ht

@[to_additive]
/-
**isMulFreimanHom_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulFreimanHom_const {b : β} (hb : b in B) : IsMulFreimanHom n A B fun _ 
=> b where mapsTo _ _
参数：hb : b in B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isMulFreimanHom_const {b : β} (hb : b ∈ B) : IsMulFreimanHom n A B fun _ ↦ b where
  mapsTo _ _ := hb
  map_prod_eq_map_prod s t _ _ hs ht _ := by simp only [map_const', hs, prod_replicate, ht]

@[to_additive (attr := simp)]
/-
**isMulFreimanHom_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulFreimanHom_zero_iff : IsMulFreimanHom 0 A B f ↔ MapsTo f A B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isMulFreimanHom_zero_iff : IsMulFreimanHom 0 A B f ↔ MapsTo f A B :=
  ⟨fun h => h.mapsTo, fun h => ⟨h, by simp_all⟩⟩

@[to_additive (attr := simp)]
/-
**isMulFreimanIso_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulFreimanIso_zero_iff : IsMulFreimanIso 0 A B f ↔ BijOn f A B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
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
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isMulFreimanIso_zero_iff : IsMulFreimanIso 0 A B f ↔ BijOn f A B :=
  ⟨fun h => h.bijOn, fun h => ⟨h, by simp_all⟩⟩

@[to_additive (attr := simp) isAddFreimanHom_one_iff]
/-
**isMulFreimanHom_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulFreimanHom_one_iff : IsMulFreimanHom 1 A B f ↔ MapsTo f A B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isMulFreimanHom_one_iff : IsMulFreimanHom 1 A B f ↔ MapsTo f A B :=
  ⟨fun h => h.mapsTo, fun h => ⟨h, by aesop (add simp card_eq_one)⟩⟩

@[to_additive (attr := simp) isAddFreimanIso_one_iff]
/-
**isMulFreimanIso_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulFreimanIso_one_iff : IsMulFreimanIso 1 A B f ↔ BijOn f A B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isMulFreimanIso_one_iff : IsMulFreimanIso 1 A B f ↔ BijOn f A B :=
  ⟨fun h => h.bijOn, fun h => ⟨h, by aesop (add simp [card_eq_one, BijOn])⟩⟩

@[to_additive (attr := simp)]
/-
**isMulFreimanHom_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulFreimanHom_empty : IsMulFreimanHom n (∅ : Set α) B f where mapsTo
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mapsTo_empty`：mapsTo_empty (f : α -> β) (t : Set β) : MapsTo f ∅ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isMulFreimanHom_empty : IsMulFreimanHom n (∅ : Set α) B f where
  mapsTo := mapsTo_empty f B
  map_prod_eq_map_prod s t := by aesop (add simp eq_zero_of_forall_notMem)

@[to_additive (attr := simp)]
/-
**isMulFreimanIso_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulFreimanIso_empty : IsMulFreimanIso n (∅ : Set α) (∅ : Set β) f where 
bijOn
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bijOn_empty`：bijOn_empty (f : α -> β) : BijOn f ∅ ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isMulFreimanIso_empty : IsMulFreimanIso n (∅ : Set α) (∅ : Set β) f where
  bijOn := bijOn_empty _
  map_prod_eq_map_prod s t hs ht := by
    simp [eq_zero_of_forall_notMem hs, eq_zero_of_forall_notMem ht]
/-
**IsMulFreimanHom.mul** 是 Mathlib 中的一个定理，位于命名空间 `IsMulFreimanHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoid α] [inst_1 : CommMonoid
 β] {A : Set α} {B₁ B₂ : Set β}   {f₁ f₂ : α → β} {n : ℕ},   IsMulFreimanHom n A
 B₁ f₁ → IsMulFreimanHom n A B₂ f₂ → IsMulFreimanHom n A (B₁ * B₂) (f₁ * f₂)
参数：B₁ * B₂；f₁ * f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.mul`：∀ {α : Type u_2} {β : Type u_3} [inst : Mul β] {A : Set 
α} {B₁ B₂ : Set β} {f₁ f₂ : α → β},   Set.MapsTo f₁ A B₁ → Set.MapsTo f₂ A B₂ → 
Set.…
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mul_def`：mul_def (f g : forall i, M i) : f * g = fun i => f i * g i
· 使用定理 `Multiset.prod_map_mul`：prod_map_mul : (m.map fun i => f i * g i).prod = 
(m.map f).prod * (m.map g).prod
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
-/
@[to_additive] lemma IsMulFreimanHom.mul (h₁ : IsMulFreimanHom n A B₁ f₁)
    (h₂ : IsMulFreimanHom n A B₂ f₂) : IsMulFreimanHom n A (B₁ * B₂) (f₁ * f₂) where
  mapsTo := h₁.mapsTo.mul h₂.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.mul_def, prod_map_mul, prod_map_mul, h₁.map_prod_eq_map_prod hsA htA hs ht h,
      h₂.map_prod_eq_map_prod hsA htA hs ht h]
/-
**MulHomClass.isMulFreimanHom** 是 Mathlib 中的一个定理，位于命名空间 `MulHomClass`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommMonoid α] [inst
_1 : CommMonoid β] {A : Set α} {B : Set β}   {n : ℕ} [inst_2 : FunLike F α β] [M
ulHomClass F α β] (f : F), Set.MapsTo (⇑f) A B → IsMulFreimanHom n A B ⇑f
参数：f : F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_multiset_ne_zero_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6
} [inst : CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MulH
omClass F M N] …
-/
@[to_additive] lemma MulHomClass.isMulFreimanHom [FunLike F α β] [MulHomClass F α β] (f : F)
    (hfAB : MapsTo f A B) : IsMulFreimanHom n A B f :=
  match n with
  | 0 => by simpa
  | n + 1 => IsMulFreimanHom.mk hfAB fun s t hsA htA hs ht h => by
    rw [← map_multiset_ne_zero_prod _ (by grind [Multiset.card_eq_zero]),
        h, map_multiset_ne_zero_prod _ (by grind [Multiset.card_eq_zero])]

@[deprecated (since := "2026-04-29")]
alias MonoidHomClass.isMulFreimanHom := MulHomClass.isMulFreimanHom

@[deprecated (since := "2026-04-29")]
alias AddMonoidHomClass.isAddFreimanHom := AddHomClass.isAddFreimanHom
/-
**MulEquivClass.isMulFreimanIso** 是 Mathlib 中的一个定理，位于命名空间 `MulEquivClass`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommMonoid α] [inst
_1 : CommMonoid β] {A : Set α} {B : Set β}   {n : ℕ} [inst_2 : EquivLike F α β] 
[MulEquivClass F α β] (f : F), Set.BijOn (⇑f) A B → IsMulFreimanIso n A B ⇑f
参数：f : F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `EquivLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : E) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma MulEquivClass.isMulFreimanIso [EquivLike F α β] [MulEquivClass F α β] (f : F)
    (hfAB : BijOn f A B) : IsMulFreimanIso n A B f where
  bijOn := hfAB
  map_prod_eq_map_prod s t _ _ _ _ := by
    rw [← map_multiset_prod, ← map_multiset_prod, EquivLike.apply_eq_iff_eq]

@[to_additive]
/-
**IsMulFreimanHom.subtypeVal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.subtypeVal {S : Type*} [SetLike S α] [SubmonoidClass S α] 
{s : S} : IsMulFreimanHom n (univ : Set s) univ Subtype.val
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHomClass.isMulFreimanHom`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : CommMonoid α] [inst_1 : CommMonoid β] {A : Set α} {B : Set β}   {n :
 ℕ} [inst_2 : Fun…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
lemma IsMulFreimanHom.subtypeVal {S : Type*} [SetLike S α] [SubmonoidClass S α] {s : S} :
    IsMulFreimanHom n (univ : Set s) univ Subtype.val :=
  MulHomClass.isMulFreimanHom (SubmonoidClass.subtype s) (mapsTo_univ ..)

end CommMonoid

section CancelCommMonoid
variable [CommMonoid α] [CancelCommMonoid β] {A : Set α} {B : Set β} {f : α → β} {m n : ℕ}

@[to_additive]
/-
**isMulFreimanHom_antitone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulFreimanHom_antitone : Antitone (IsMulFreimanHom · A B f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.card_pos_iff_exists_mem`：card_pos_iff_exists_mem {s : Multiset 
α} : 0 < card s ↔ exists a, a in s
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
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 31 条，此处仅展示前 30 条）
-/
lemma isMulFreimanHom_antitone : Antitone (IsMulFreimanHom · A B f) :=
  antitone_nat_of_succ_le fun n hf =>
  { mapsTo := hf.mapsTo,
    map_prod_eq_map_prod := fun s t hsA htA hs _ h => match n with
      | 0 => by aesop
      | n + 1 => by
        have ⟨a, ha⟩ : ∃ a, a ∈ s := card_pos_iff_exists_mem.1 (by simp [hs])
        simpa [*] using hf.map_prod_eq_map_prod (s := a ::ₘ s) (t := a ::ₘ t)
            (by simpa [hsA ha]) (by simpa [hsA ha]) }

@[to_additive]
/-
**IsMulFreimanHom.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.mono (hmn : m <= n) (hf : IsMulFreimanHom n A B f) : IsMul
FreimanHom m A B f
参数：hmn : m <= n；hf : IsMulFreimanHom n A B f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMulFreimanHom_antitone`：isMulFreimanHom_antitone : Antitone (IsMulFrei
manHom · A B f)
-/
lemma IsMulFreimanHom.mono (hmn : m ≤ n) (hf : IsMulFreimanHom n A B f) : IsMulFreimanHom m A B f :=
  isMulFreimanHom_antitone hmn hf

end CancelCommMonoid

section CancelCommMonoid
variable [CancelCommMonoid α] [CancelCommMonoid β] {A : Set α} {B : Set β} {f : α → β} {m n : ℕ}

@[to_additive]
/-
**IsMulFreimanIso.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanIso.mono {hmn : m <= n} (hf : IsMulFreimanIso n A B f) : IsMul
FreimanIso m A B f
参数：hf : IsMulFreimanIso n A B f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsMulFreimanHom.to_isMulFreimanIso`：IsMulFreimanHom.to_isMulFreimanIso {
g : β -> α} (h : InvOn g f A B) (hf : IsMulFreimanHom n A B f) (hg : IsMulFreima
nHom n B A g) : IsMulFre…
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Set.BijOn.invOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t
 : Set β} {f : α → β} [inst : Nonempty α],   Set.BijOn f s t → Set.InvOn (Functi
on.invFunOn f …
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用引理 `IsMulFreimanHom.mono`：IsMulFreimanHom.mono (hmn : m <= n) (hf : IsMulFre
imanHom n A B f) : IsMulFreimanHom m A B f
· 使用引理 `IsMulFreimanIso.isMulFreimanHom`：IsMulFreimanIso.isMulFreimanHom (hf : I
sMulFreimanIso n A B f) : IsMulFreimanHom n A B f where mapsTo
· 使用定理 `IsMulFreimanIso.invFunOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMo
noid α] [inst_1 : CommMonoid β] {A : Set α} {B : Set β} {f : α → β}   {n : ℕ}, I
sMulFreimanIso…
-/
lemma IsMulFreimanIso.mono {hmn : m ≤ n} (hf : IsMulFreimanIso n A B f) :
    IsMulFreimanIso m A B f :=
  (hf.isMulFreimanHom.mono hmn).to_isMulFreimanIso hf.bijOn.invOn_invFunOn
    (hf.invFunOn.isMulFreimanHom.mono hmn)

end CancelCommMonoid

section DivisionCommMonoid
variable [CommMonoid α] [DivisionCommMonoid β] {A : Set α} {B : Set β} {f : α → β} {n : ℕ}

@[to_additive]
/-
**IsMulFreimanHom.inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.inv (hf : IsMulFreimanHom n A B f) : IsMulFreimanHom n A B
⁻¹ f⁻¹ where mapsTo
参数：hf : IsMulFreimanHom n A B f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.inv`：∀ {α : Type u_2} {β : Type u_3} [inst : InvolutiveInv β]
 {A : Set α} {B : Set β} {f : α → β},   Set.MapsTo f A B → Set.MapsTo f⁻¹ A B⁻¹
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.inv_def`：inv_def (f : forall i, G i) : f⁻¹ = fun i => (f i)⁻¹
· 使用定理 `Multiset.prod_map_inv`：prod_map_inv : (m.map fun i => (f i)⁻¹).prod = (m
.map f).prod⁻¹
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
-/
lemma IsMulFreimanHom.inv (hf : IsMulFreimanHom n A B f) : IsMulFreimanHom n A B⁻¹ f⁻¹ where
  mapsTo := hf.mapsTo.inv
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.inv_def, prod_map_inv, prod_map_inv, hf.map_prod_eq_map_prod hsA htA hs ht h]
/-
**IsMulFreimanHom.div** 是 Mathlib 中的一个定理，位于命名空间 `IsMulFreimanHom`。
形式化陈述：∀ {α : Type u_2} [inst : CommMonoid α] {A : Set α} {n : ℕ} {β : Type u_5} 
[inst_1 : DivisionCommMonoid β]   {B₁ B₂ : Set β} {f₁ f₂ : α → β},   IsMulFreima
nHom n A B₁ f₁ → IsMulFreimanHom n A B₂ f₂ → IsMulFreimanHom n A (B₁ / B₂) (f₁ /
 f₂)
参数：B₁ / B₂；f₁ / f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.div`：∀ {α : Type u_2} {β : Type u_3} [inst : Div β] {A : Set 
α} {B₁ B₂ : Set β} {f₁ f₂ : α → β},   Set.MapsTo f₁ A B₁ → Set.MapsTo f₂ A B₂ → 
Set.…
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.div_def`：div_def (f g : forall i, G i) : f / g = fun i => f i / g i
· 使用定理 `Multiset.prod_map_div`：prod_map_div : (m.map fun i => f i / g i).prod = 
(m.map f).prod / (m.map g).prod
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
-/
@[to_additive] lemma IsMulFreimanHom.div {β : Type*} [DivisionCommMonoid β] {B₁ B₂ : Set β}
    {f₁ f₂ : α → β} (h₁ : IsMulFreimanHom n A B₁ f₁) (h₂ : IsMulFreimanHom n A B₂ f₂) :
    IsMulFreimanHom n A (B₁ / B₂) (f₁ / f₂) where
  mapsTo := h₁.mapsTo.div h₂.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.div_def, prod_map_div, prod_map_div, h₁.map_prod_eq_map_prod hsA htA hs ht h,
      h₂.map_prod_eq_map_prod hsA htA hs ht h]

end DivisionCommMonoid

section Prod

@[to_additive]
/-
**IsMulFreimanHom.fst** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.fst [CommMonoid α] [CommMonoid β] {A : Set α} {B : Set β} 
{n : Nat} : IsMulFreimanHom n (A ×ˢ B) A Prod.fst
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHomClass.isMulFreimanHom`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : CommMonoid α] [inst_1 : CommMonoid β] {A : Set α} {B : Set β}   {n :
 ℕ} [inst_2 : Fun…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `Set.mapsTo_fst_prod`：mapsTo_fst_prod {s : Set α} {t : Set β} : MapsTo Pr
od.fst (s ×ˢ t) s
-/
lemma IsMulFreimanHom.fst [CommMonoid α] [CommMonoid β] {A : Set α} {B : Set β} {n : ℕ} :
    IsMulFreimanHom n (A ×ˢ B) A Prod.fst :=
  MulHomClass.isMulFreimanHom (MonoidHom.fst _ _) mapsTo_fst_prod

@[to_additive]
/-
**IsMulFreimanHom.snd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.snd [CommMonoid α] [CommMonoid β] {A : Set α} {B : Set β} 
{n : Nat} : IsMulFreimanHom n (A ×ˢ B) B Prod.snd
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHomClass.isMulFreimanHom`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : CommMonoid α] [inst_1 : CommMonoid β] {A : Set α} {B : Set β}   {n :
 ℕ} [inst_2 : Fun…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `Set.mapsTo_snd_prod`：mapsTo_snd_prod {s : Set α} {t : Set β} : MapsTo Pr
od.snd (s ×ˢ t) t
-/
lemma IsMulFreimanHom.snd [CommMonoid α] [CommMonoid β] {A : Set α} {B : Set β} {n : ℕ} :
    IsMulFreimanHom n (A ×ˢ B) B Prod.snd :=
  MulHomClass.isMulFreimanHom (MonoidHom.snd _ _) mapsTo_snd_prod

section

variable {α β₁ β₂ : Type*} [CommMonoid α] [CommMonoid β₁] [CommMonoid β₂]
  {A : Set α} {B₁ : Set β₁} {B₂ : Set β₂} {f₁ : α → β₁} {f₂ : α → β₂} {n : ℕ}

@[to_additive prodMk]
/-
**IsMulFreimanHom.prodMk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.prodMk (h₁ : IsMulFreimanHom n A B₁ f₁) (h₂ : IsMulFreiman
Hom n A B₂ f₂) : IsMulFreimanHom n A (B₁ ×ˢ B₂) (fun x => (f₁ x, f₂ x)) where ma
psTo
参数：h₁ : IsMulFreimanHom n A B₁ f₁；h₂ : IsMulFreimanHom n A B₂ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fst_prod`：∀ {M : Type u_5} {N : Type u_6} [inst : CommMonoid M]
 [inst_1 : CommMonoid N] (s : Multiset (M × N)),   s.prod.1 = (Multiset.map Prod
.fst s)…
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `IsMulFreimanHom.map_prod_eq_map_prod`：∀ {α : Type u_2} {β : Type u_3} [i
nst : CommMonoid α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f
 : α → β},   IsMulFreimanH…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.snd_prod`：∀ {M : Type u_5} {N : Type u_6} [inst : CommMonoid M]
 [inst_1 : CommMonoid N] (s : Multiset (M × N)),   s.prod.2 = (Multiset.map Prod
.snd s)…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma IsMulFreimanHom.prodMk (h₁ : IsMulFreimanHom n A B₁ f₁) (h₂ : IsMulFreimanHom n A B₂ f₂) :
    IsMulFreimanHom n A (B₁ ×ˢ B₂) (fun x => (f₁ x, f₂ x)) where
  mapsTo := fun x hx => mk_mem_prod (h₁.mapsTo hx) (h₂.mapsTo hx)
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    simp [Prod.ext_iff, fst_prod, snd_prod,
      h₁.map_prod_eq_map_prod hsA htA hs ht h, h₂.map_prod_eq_map_prod hsA htA hs ht h]

end

section

variable {α₁ α₂ β₁ β₂ : Type*} [CommMonoid α₁] [CommMonoid α₂] [CommMonoid β₁] [CommMonoid β₂]
  {A₁ : Set α₁} {A₂ : Set α₂} {B₁ : Set β₁} {B₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} {n : ℕ}

@[to_additive prodMap]
/-
**IsMulFreimanHom.prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.prodMap (h₁ : IsMulFreimanHom n A₁ B₁ f₁) (h₂ : IsMulFreim
anHom n A₂ B₂ f₂) : IsMulFreimanHom n (A₁ ×ˢ A₂) (B₁ ×ˢ B₂) (Prod.map f₁ f₂)
参数：h₁ : IsMulFreimanHom n A₁ B₁ f₁；h₂ : IsMulFreimanHom n A₂ B₂ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsMulFreimanHom.prodMk`：IsMulFreimanHom.prodMk (h₁ : IsMulFreimanHom n A
 B₁ f₁) (h₂ : IsMulFreimanHom n A B₂ f₂) : IsMulFreimanHom n A (B₁ ×ˢ B₂) (fun x
 => (f₁ x, f…
· 使用定理 `IsMulFreimanHom.comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [in
st : CommMonoid α] [inst_1 : CommMonoid β] [inst_2 : CommMonoid γ]   {A : Set α}
 {B : Set …
· 使用引理 `IsMulFreimanHom.fst`：IsMulFreimanHom.fst [CommMonoid α] [CommMonoid β] {
A : Set α} {B : Set β} {n : Nat} : IsMulFreimanHom n (A ×ˢ B) A Prod.fst
· 使用引理 `IsMulFreimanHom.snd`：IsMulFreimanHom.snd [CommMonoid α] [CommMonoid β] {
A : Set α} {B : Set β} {n : Nat} : IsMulFreimanHom n (A ×ˢ B) B Prod.snd
-/
lemma IsMulFreimanHom.prodMap (h₁ : IsMulFreimanHom n A₁ B₁ f₁) (h₂ : IsMulFreimanHom n A₂ B₂ f₂) :
    IsMulFreimanHom n (A₁ ×ˢ A₂) (B₁ ×ˢ B₂) (Prod.map f₁ f₂) :=
  (h₁.comp .fst).prodMk (h₂.comp .snd)

@[to_additive prodMap]
/-
**IsMulFreimanIso.prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanIso.prodMap (h₁ : IsMulFreimanIso n A₁ B₁ f₁) (h₂ : IsMulFreim
anIso n A₂ B₂ f₂) : IsMulFreimanIso n (A₁ ×ˢ A₂) (B₁ ×ˢ B₂) (Prod.map f₁ f₂)
参数：h₁ : IsMulFreimanIso n A₁ B₁ f₁；h₂ : IsMulFreimanIso n A₂ B₂ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsMulFreimanHom.to_isMulFreimanIso`：IsMulFreimanHom.to_isMulFreimanIso {
g : β -> α} (h : InvOn g f A B) (hf : IsMulFreimanHom n A B f) (hg : IsMulFreima
nHom n B A g) : IsMulFre…
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Set.InvOn.prodMap`：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β₂
 : Type u_10} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁}   {t₂ : Set β₂} {f₁ : α₁
 → β₁} …
· 使用定理 `Set.BijOn.invOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t
 : Set β} {f : α → β} [inst : Nonempty α],   Set.BijOn f s t → Set.InvOn (Functi
on.invFunOn f …
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用引理 `IsMulFreimanHom.prodMap`：IsMulFreimanHom.prodMap (h₁ : IsMulFreimanHom n
 A₁ B₁ f₁) (h₂ : IsMulFreimanHom n A₂ B₂ f₂) : IsMulFreimanHom n (A₁ ×ˢ A₂) (B₁ 
×ˢ B₂) (Prod.…
· 使用引理 `IsMulFreimanIso.isMulFreimanHom`：IsMulFreimanIso.isMulFreimanHom (hf : I
sMulFreimanIso n A B f) : IsMulFreimanHom n A B f where mapsTo
· 使用定理 `IsMulFreimanIso.invFunOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMo
noid α] [inst_1 : CommMonoid β] {A : Set α} {B : Set β} {f : α → β}   {n : ℕ}, I
sMulFreimanIso…
-/
lemma IsMulFreimanIso.prodMap (h₁ : IsMulFreimanIso n A₁ B₁ f₁) (h₂ : IsMulFreimanIso n A₂ B₂ f₂) :
    IsMulFreimanIso n (A₁ ×ˢ A₂) (B₁ ×ˢ B₂) (Prod.map f₁ f₂) :=
  (h₁.isMulFreimanHom.prodMap h₂.isMulFreimanHom).to_isMulFreimanIso
    (h₁.bijOn.invOn_invFunOn.prodMap h₂.bijOn.invOn_invFunOn)
    (h₁.invFunOn.isMulFreimanHom.prodMap h₂.invFunOn.isMulFreimanHom)

end

end Prod

namespace Fin
variable {k m n : ℕ}

open Fin.CommRing

/-
**Fin.aux** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux (hm : m ≠ 0) (hkmn : m * k ≤ n) : k < (n + 1) :=
  Nat.lt_succ_iff.2 <| le_trans (Nat.le_mul_of_pos_left _ hm.bot_lt) hkmn

/-- **No wrap-around principle**.

The first `k + 1` elements of `Fin (n + 1)` are `m`-Freiman isomorphic to the first `k + 1` elements
of `ℕ` assuming there is no wrap-around. -/
/-
**Fin.isAddFreimanIso_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：isAddFreimanIso_Iic (hm : m != 0) (hkmn : m * k <= n) : IsAddFreimanIso m 
(Iic (k : Fin (n + 1))) (Iic k) val where bijOn.left
参数：hm : m != 0；hkmn : m * k <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `_private.Mathlib.Combinatorics.Additive.FreimanHom.0.Fin.aux`：∀ {k m n :
 ℕ}, m ≠ 0 → m * k ≤ n → k < n + 1
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用引理 `Nat.cast_multiset_sum`：cast_multiset_sum [AddCommMonoidWithOne R] (s : M
ultiset Nat) : (↑s.sum : R) = (s.map (↑)).sum
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Fin.cast_val_eq_self`：∀ {n : ℕ} (a : Fin n), ↑↑a = a
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.sum_le_card_nsmul`：∀ {α : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [AddLeftMono α] (s : Multiset α) (n : α),   (∀ x ∈ s, x ≤ n)
 → s.sum ≤ s.car…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
**No wrap-around principle**.

The first `k + 1` elements of `Fin (n + 1)` are `m`-Freiman isomorphic to the fi
rst `k + 1` elements
of `ℕ` assuming there is no wrap-around.
-/
lemma isAddFreimanIso_Iic (hm : m ≠ 0) (hkmn : m * k ≤ n) :
    IsAddFreimanIso m (Iic (k : Fin (n + 1))) (Iic k) val where
  bijOn.left := by simp [MapsTo, Fin.le_iff_val_le_val, Nat.mod_eq_of_lt, aux hm hkmn]
  bijOn.right.left := val_injective.injOn
  bijOn.right.right x (hx : x ≤ _) :=
    ⟨x, by simpa [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, aux hm hkmn, hx.trans_lt]⟩
  map_sum_eq_map_sum s t hsA htA hs ht := by
    have (u : Multiset (Fin (n + 1))) : Nat.castRingHom _ (u.map val).sum = u.sum := by simp
    rw [← this, ← this]
    have {u : Multiset (Fin (n + 1))} (huk : ∀ x ∈ u, x ≤ k) (hu : card u = m) :
        (u.map val).sum < (n + 1) := Nat.lt_succ_iff.2 <| hkmn.trans' <| by
      rw [← hu, ← card_map]
      refine sum_le_card_nsmul (u.map val) k ?_
      simpa [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, aux hm hkmn] using huk
    exact ⟨congr_arg _, CharP.natCast_injOn_Iio _ (n + 1) (this hsA hs) (this htA ht)⟩

/-- **No wrap-around principle**.

The first `k` elements of `Fin (n + 1)` are `m`-Freiman isomorphic to the first `k` elements of `ℕ`
assuming there is no wrap-around. -/
/-
**Fin.isAddFreimanIso_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：isAddFreimanIso_Iio (hm : m != 0) (hkmn : m * k <= n) : IsAddFreimanIso m 
(Iio (k : Fin (n + 1))) (Iio k) val
参数：hm : m != 0；hkmn : m * k <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Set.Iio_zero_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Ze
ro α] [IsBotZeroClass α], Set.Iio 0 = ∅
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `IsMin.Iio_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsMin a → Se
t.Iio a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `_private.Mathlib.Combinatorics.Additive.FreimanHom.0.Fin.aux`：∀ {k m n :
 ℕ}, m ≠ 0 → m * k ≤ n → k < n + 1
· 使用定理 `Fin.val_cast_of_lt`：val_cast_of_lt {n : Nat} [NeZero n] {a : Nat} (h : a
 < n) : (a : Fin n).val = a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Fin.isAddFreimanIso_Iic`：isAddFreimanIso_Iic (hm : m != 0) (hkmn : m * k
 <= n) : IsAddFreimanIso m (Iic (k : Fin (n + 1))) (Iic k) val where bijOn.left

--- 原说明 ---
**No wrap-around principle**.

The first `k` elements of `Fin (n + 1)` are `m`-Freiman isomorphic to the first 
`k` elements of `ℕ`
assuming there is no wrap-around.
-/
lemma isAddFreimanIso_Iio (hm : m ≠ 0) (hkmn : m * k ≤ n) :
    IsAddFreimanIso m (Iio (k : Fin (n + 1))) (Iio k) val := by
  obtain _ | k := k
  · simp
  have hkmn' : m * k ≤ n := (Nat.mul_le_mul_left _ k.le_succ).trans hkmn
  convert! isAddFreimanIso_Iic hm hkmn' using 1 <;> ext x
  · simp only [Nat.cast_add, Nat.cast_one, mem_Iio, lt_def, mem_Iic, le_iff_val_le_val,
      val_natCast, aux hm hkmn', Nat.mod_eq_of_lt]
    simp_rw [← Nat.cast_add_one]
    rw [Fin.val_cast_of_lt (aux hm hkmn), Nat.lt_succ_iff]
  · simp [Nat.lt_succ_iff]

end Fin

