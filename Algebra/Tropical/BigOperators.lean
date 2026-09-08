/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.List.MinMax
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!

# Tropicalization of finitary operations

This file provides the "big-op" or notation-based finitary operations on tropicalized types.
This allows easy conversion between sums to Infs and prods to sums. Results here are important
for expressing that evaluation of tropical polynomials are the minimum over a finite piecewise
collection of linear functions.

## Main declarations

* `untrop_sum`

## Implementation notes

No concrete (semi)ring is used here, only ones with inferable order/lattice structure, to support
`Real`, `Rat`, `EReal`, and others (`ERat` is not yet defined).

Minima over `List α` are defined as producing a value in `WithTop α` so proofs about lists do not
directly transfer to minima over multisets or finsets.

-/

public section

variable {R S : Type*}

open Tropical Finset

/-
**List.trop_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.trop_sum [AddMonoid R] (l : List R) : trop l.sum = List.prod (l.map t
rop)
参数：l : List R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem List.trop_sum [AddMonoid R] (l : List R) : trop l.sum = List.prod (l.map trop) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]
/-
**Multiset.trop_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.trop_sum [AddCommMonoid R] (s : Multiset R) : trop s.sum = Multis
et.prod (s.map trop)
参数：s : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.trop_sum`：List.trop_sum [AddMonoid R] (l : List R) : trop l.sum = L
ist.prod (l.map trop)
-/
theorem Multiset.trop_sum [AddCommMonoid R] (s : Multiset R) :
    trop s.sum = Multiset.prod (s.map trop) :=
  Quotient.inductionOn s (by simpa using List.trop_sum)
/-
**trop_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trop_sum [AddCommMonoid R] (s : Finset S) (f : S -> R) : trop (∑ i in s, f
 i) = ∏ i in s, trop (f i)
参数：s : Finset S；f : S -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.trop_sum`：Multiset.trop_sum [AddCommMonoid R] (s : Multiset R) 
: trop s.sum = Multiset.prod (s.map trop)
-/
theorem trop_sum [AddCommMonoid R] (s : Finset S) (f : S → R) :
    trop (∑ i ∈ s, f i) = ∏ i ∈ s, trop (f i) := by
  convert! Multiset.trop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl
/-
**List.untrop_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.untrop_prod [AddMonoid R] (l : List (Tropical R)) : untrop l.prod = L
ist.sum (l.map untrop)
参数：l : List (Tropical R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem List.untrop_prod [AddMonoid R] (l : List (Tropical R)) :
    untrop l.prod = List.sum (l.map untrop) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]
/-
**Multiset.untrop_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.untrop_prod [AddCommMonoid R] (s : Multiset (Tropical R)) : untro
p s.prod = Multiset.sum (s.map untrop)
参数：s : Multiset (Tropical R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.untrop_prod`：List.untrop_prod [AddMonoid R] (l : List (Tropical R))
 : untrop l.prod = List.sum (l.map untrop)
-/
theorem Multiset.untrop_prod [AddCommMonoid R] (s : Multiset (Tropical R)) :
    untrop s.prod = Multiset.sum (s.map untrop) :=
  Quotient.inductionOn s (by simpa using List.untrop_prod)
/-
**untrop_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：untrop_prod [AddCommMonoid R] (s : Finset S) (f : S -> Tropical R) : untro
p (∏ i in s, f i) = ∑ i in s, untrop (f i)
参数：s : Finset S；f : S -> Tropical R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.untrop_prod`：Multiset.untrop_prod [AddCommMonoid R] (s : Multis
et (Tropical R)) : untrop s.prod = Multiset.sum (s.map untrop)
-/
theorem untrop_prod [AddCommMonoid R] (s : Finset S) (f : S → Tropical R) :
    untrop (∏ i ∈ s, f i) = ∑ i ∈ s, untrop (f i) := by
  convert! Multiset.untrop_prod (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl
/-
**List.trop_minimum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.trop_minimum [LinearOrder R] (l : List R) : trop l.minimum = List.sum
 (l.map (trop ∘ WithTop.some))
参数：l : List R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.minimum_cons`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α) (l : 
List α), (a :: l).minimum = min (↑a) l.minimum
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem List.trop_minimum [LinearOrder R] (l : List R) :
    trop l.minimum = List.sum (l.map (trop ∘ WithTop.some)) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [List.minimum_cons, ← IH]
/-
**Multiset.trop_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.trop_inf [LinearOrder R] [OrderTop R] (s : Multiset R) : trop s.i
nf = Multiset.sum (s.map trop)
参数：s : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.inf_zero`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : 
OrderTop α], Multiset.inf 0 = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.inf_cons`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : 
OrderTop α] (a : α) (s : Multiset α), (a ::ₘ s).inf = a ⊓ s.inf
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Multiset.trop_inf [LinearOrder R] [OrderTop R] (s : Multiset R) :
    trop s.inf = Multiset.sum (s.map trop) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp [← IH]
/-
**Finset.trop_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.trop_inf [LinearOrder R] [OrderTop R] (s : Finset S) (f : S -> R) :
 trop (s.inf f) = ∑ i in s, trop (f i)
参数：s : Finset S；f : S -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.trop_inf`：Multiset.trop_inf [LinearOrder R] [OrderTop R] (s : M
ultiset R) : trop s.inf = Multiset.sum (s.map trop)
-/
theorem Finset.trop_inf [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → R) :
    trop (s.inf f) = ∑ i ∈ s, trop (f i) := by
  convert! Multiset.trop_inf (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl
/-
**trop_sInf_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trop_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S
 -> WithTop R) : trop (sInf (f '' s)) = ∑ i in s, trop (f i)
参数：s : Finset S；f : S -> WithTop R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `WithTop.sInf_empty`：sInf_empty [InfSet α] : sInf (∅ : Set (WithTop α)) =
 ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.inf'_eq_csInf_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLattice α] (s : Finset ι) (H : s.Nonempty) (f : ι → α),   s.inf
' H f = sInf (f …
· 使用定理 `Finset.inf'_eq_inf`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeI
nf α] [inst_1 : OrderTop α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.inf
' H f = …
· 使用定理 `Finset.trop_inf`：Finset.trop_inf [LinearOrder R] [OrderTop R] (s : Finse
t S) (f : S -> R) : trop (s.inf f) = ∑ i in s, trop (f i)
-/
theorem trop_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S → WithTop R) :
    trop (sInf (f '' s)) = ∑ i ∈ s, trop (f i) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, trop_top]
  rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, s.trop_inf]
/-
**trop_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trop_iInf [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S -> WithT
op R) : trop (⨅ i : S, f i) = ∑ i : S, trop (f i)
参数：f : S -> WithTop R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `trop_sInf_image`：trop_sInf_image [ConditionallyCompleteLinearOrder R] (s
 : Finset S) (f : S -> WithTop R) : trop (sInf (f '' s)) = ∑ i in s, trop (f i)
-/
theorem trop_iInf [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → WithTop R) :
    trop (⨅ i : S, f i) = ∑ i : S, trop (f i) := by
  rw [iInf, ← Set.image_univ, ← coe_univ, trop_sInf_image]
/-
**Multiset.untrop_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.untrop_sum [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R
)) : untrop s.sum = Multiset.inf (s.map untrop)
参数：s : Multiset (Tropical R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.inf_zero`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : 
OrderTop α], Multiset.inf 0 = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.inf_cons`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : 
OrderTop α] (a : α) (s : Multiset α), (a ::ₘ s).inf = a ⊓ s.inf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Multiset.untrop_sum [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R)) :
    untrop s.sum = Multiset.inf (s.map untrop) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp only [sum_cons, untrop_add, map_cons, inf_cons, ← IH]
/-
**Finset.untrop_sum'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.untrop_sum' [LinearOrder R] [OrderTop R] (s : Finset S) (f : S -> T
ropical R) : untrop (∑ i in s, f i) = s.inf (untrop ∘ f)
参数：s : Finset S；f : S -> Tropical R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.untrop_sum`：Multiset.untrop_sum [LinearOrder R] [OrderTop R] (s
 : Multiset (Tropical R)) : untrop s.sum = Multiset.inf (s.map untrop)
-/
theorem Finset.untrop_sum' [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → Tropical R) :
    untrop (∑ i ∈ s, f i) = s.inf (untrop ∘ f) := by
  convert! Multiset.untrop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply, inf_def]
/-
**untrop_sum_eq_sInf_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：untrop_sum_eq_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset 
S) (f : S -> Tropical (WithTop R)) : untrop (∑ i in s, f i) = sInf (untrop ∘ f '
' s)
参数：s : Finset S；f : S -> Tropical (WithTop R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `WithTop.sInf_empty`：sInf_empty [InfSet α] : sInf (∅ : Set (WithTop α)) =
 ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.inf'_eq_csInf_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLattice α] (s : Finset ι) (H : s.Nonempty) (f : ι → α),   s.inf
' H f = sInf (f …
· 使用定理 `Finset.inf'_eq_inf`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeI
nf α] [inst_1 : OrderTop α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.inf
' H f = …
· 使用定理 `Finset.untrop_sum'`：Finset.untrop_sum' [LinearOrder R] [OrderTop R] (s :
 Finset S) (f : S -> Tropical R) : untrop (∑ i in s, f i) = s.inf (untrop ∘ f)
-/
theorem untrop_sum_eq_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i ∈ s, f i) = sInf (untrop ∘ f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, untrop_zero]
  · rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, Finset.untrop_sum']
/-
**untrop_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：untrop_sum [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S -> Trop
ical (WithTop R)) : untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i)
参数：f : S -> Tropical (WithTop R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `untrop_sum_eq_sInf_image`：untrop_sum_eq_sInf_image [ConditionallyComplet
eLinearOrder R] (s : Finset S) (f : S -> Tropical (WithTop R)) : untrop (∑ i in 
s, f i) = sInf…
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem untrop_sum [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → Tropical (WithTop R)) :
    untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) := by
  rw [iInf, ← Set.image_univ, ← coe_univ, untrop_sum_eq_sInf_image, Function.comp_def]

/-- Note we cannot use `i ∈ s` instead of `i : s` here
as it is simply not true on conditionally complete lattices! -/
/-
**Finset.untrop_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.untrop_sum [ConditionallyCompleteLinearOrder R] (s : Finset S) (f :
 S -> Tropical (WithTop R)) : untrop (∑ i in s, f i) = ⨅ i : s, untrop (f i)
参数：s : Finset S；f : S -> Tropical (WithTop R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x

--- 原说明 ---
Note we cannot use `i ∈ s` instead of `i : s` here
as it is simply not true on conditionally complete lattices!
-/
theorem Finset.untrop_sum [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i ∈ s, f i) = ⨅ i : s, untrop (f i) := by
  simpa [← _root_.untrop_sum] using (sum_attach _ _).symm
