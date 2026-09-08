/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Data.DFinsupp.Ext
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Dependent functions with finite support

For a non-dependent version see `Mathlib/Data/Finsupp/Defs.lean`.

## Notation

This file introduces the notation `Π₀ a, β a` as notation for `DFinsupp β`, mirroring the `α →₀ β`
notation used for `Finsupp`. This works for nested binders too, with `Π₀ a b, γ a b` as notation
for `DFinsupp (fun a ↦ DFinsupp (γ a))`.

## Implementation notes

The support is internally represented (in the primed `DFinsupp.support'`) as a `Multiset` that
represents a superset of the true support of the function, quotiented by the always-true relation so
that this does not impact equality. This approach has computational benefits over storing a
`Finset`; it allows us to add together two finitely-supported functions without
having to evaluate the resulting function to recompute its support (which would required
decidability of `b = 0` for `b : β i`).

The true support of the function can still be recovered with `DFinsupp.support`; but these
decidability obligations are now postponed to when the support is actually needed. As a consequence,
there are two ways to sum a `DFinsupp`: with `DFinsupp.sum` which works over an arbitrary function
but requires recomputation of the support and therefore a `Decidable` argument; and with
`DFinsupp.sumAddHom` which requires an additive morphism, using its properties to show that
summing over a superset of the support is sufficient.

`Finsupp` takes an altogether different approach here; it uses `Classical.Decidable` and declares
the `Add` instance as noncomputable. This design difference is independent of the fact that
`DFinsupp` is dependently-typed and `Finsupp` is not; in future, we may want to align these two
definitions, or introduce two more definitions for the other combinations of decisions.
-/

@[expose] public section

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section Algebra

/-- Evaluation at a point is an `AddMonoidHom`. This is the finitely-supported version of
`Pi.evalAddMonoidHom`. -/
/-
**DFinsupp.evalAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：evalAddMonoidHom [forall i, AddZeroClass (β i)] (i : ι) : (Π₀ i, β i) ->+ 
β i
参数：β i；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation at a point is an `AddMonoidHom`. This is the finitely-supported versi
on of
`Pi.evalAddMonoidHom`.
-/
def evalAddMonoidHom [∀ i, AddZeroClass (β i)] (i : ι) : (Π₀ i, β i) →+ β i :=
  (Pi.evalAddMonoidHom β i).comp coeFnAddMonoidHom

@[simp, norm_cast]
/-
**DFinsupp.coe_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：coe_finsetSum {α} [forall i, AddCommMonoid (β i)] (s : Finset α) (g : α ->
 Π₀ i, β i) : ⇑(∑ a in s, g a) = ∑ a in s, ⇑(g a)
参数：β i；s : Finset α；g : α -> Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem coe_finsetSum {α} [∀ i, AddCommMonoid (β i)] (s : Finset α) (g : α → Π₀ i, β i) :
    ⇑(∑ a ∈ s, g a) = ∑ a ∈ s, ⇑(g a) :=
  map_sum coeFnAddMonoidHom g s

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

@[simp]
/-
**DFinsupp.finsetSum_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：finsetSum_apply {α} [forall i, AddCommMonoid (β i)] (s : Finset α) (g : α 
-> Π₀ i, β i) (i : ι) : (∑ a in s, g a) i = ∑ a in s, g a i
参数：β i；s : Finset α；g : α -> Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem finsetSum_apply {α} [∀ i, AddCommMonoid (β i)] (s : Finset α) (g : α → Π₀ i, β i) (i : ι) :
    (∑ a ∈ s, g a) i = ∑ a ∈ s, g a i :=
  map_sum (evalAddMonoidHom i) g s

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

end Algebra

section ProdAndSum

variable [DecidableEq ι]

/-- `DFinsupp.prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive /-- `sum f g` is the sum of `g i (f i)` over the support of `f`. -/]
/-
**DFinsupp.prod** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：prod [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)] [Co
mmMonoid γ] (f : Π₀ i, β i) (g : forall i, β i -> γ) : γ
参数：β i；i；x : β i；x != 0；f : Π₀ i, β i；g : forall i, β i -> γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.prod f g` is the product of `g i (f i)` over the support of `f`.
-/
def prod [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] (f : Π₀ i, β i)
    (g : ∀ i, β i → γ) : γ :=
  ∏ i ∈ f.support, g i (f i)

@[to_additive]
/-
**DFinsupp.prod_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_of_support_subset [forall i, Zero (β i)] [forall (i) (x : β i), Decid
able (x != 0)] [CommMonoid γ] {f : Π₀ i, β i} {g : (i : ι) -> β i -> γ} {s : Fin
set ι} (hs : f.support subseteq s) (map_zero : forall i in s, g i 0 = 1) : f.pro
d g = ∏ i in s, g i (f i)
参数：β i；i；x : β i；x != 0；i : ι；hs : f.support subseteq s；map_zero : forall i in s
, g i 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem prod_of_support_subset [∀ i, Zero (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {g : (i : ι) → β i → γ} {s : Finset ι}
    (hs : f.support ⊆ s) (map_zero : ∀ i ∈ s, g i 0 = 1) :
    f.prod g = ∏ i ∈ s, g i (f i) := by
  simp only [DFinsupp.prod]
  apply Finset.prod_subset hs
  intro i hi hi'
  simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hi'
  rw [hi', map_zero]
  exact hi

/-- The product over two dfinsupps agree if the functions agree and are well-behaved within the
shared support. -/
@[to_additive (attr := gcongr only)
/-- The sum over two dfinsupps agree if the functions agree and are well-behaved within the
shared support. -/]
/-
**DFinsupp.prod_congr_of_eq_on_union** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_congr_of_eq_on_union [forall i, Zero (β i)] [forall (i) (x : β i), De
cidable (x != 0)] [CommMonoid γ] {f1 f2 : Π₀ i, β i} {g1 g2 : (i : ι) -> β i -> 
γ} (h : forall x in f1.support union f2.support, g1 x (f1 x) = g2 x (f2 x)) (h1 
: forall x in f1.support union f2.support, g1 x 0 = 1) (h2 : forall x in f1.supp
ort union f2.support, g2 x 0 = 1) : f1.prod g1 = f2.prod g2
参数：β i；i；x : β i；x != 0；i : ι；h : forall x in f1.support union f2.support, g1 x 
(f1 x) = g2 x (f2 x)；h1 : forall x in f1.support union f2.support, g1 x 0 = 1；h2
 : forall x in f1.support union f2.support, g2 x 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.prod_of_support_subset`：prod_of_support_subset [forall i, Zero 
(β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ] {f : Π₀ i, β i}
 {g : (i : ι) -> β i …
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem prod_congr_of_eq_on_union
    [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f1 f2 : Π₀ i, β i} {g1 g2 : (i : ι) → β i → γ}
    (h : ∀ x ∈ f1.support ∪ f2.support, g1 x (f1 x) = g2 x (f2 x))
    (h1 : ∀ x ∈ f1.support ∪ f2.support, g1 x 0 = 1)
    (h2 : ∀ x ∈ f1.support ∪ f2.support, g2 x 0 = 1) :
    f1.prod g1 = f2.prod g2 := by
  rw [prod_of_support_subset Finset.subset_union_left h1,
    prod_of_support_subset Finset.subset_union_right h2]
  exact Finset.prod_congr rfl h

@[to_additive (attr := simp)]
/-
**DFinsupp._root_.map_dfinsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.map_dfinsuppProd
    {R S H : Type*} [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid R] [CommMonoid S] [FunLike H R S] [MonoidHomClass H R S] (h : H) (f : Π₀ i, β i)
    (g : ∀ i, β i → R) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod _ _ _

@[to_additive]
/-
**DFinsupp.prod_mapRange_index** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_mapRange_index {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂} [forall i, Zer
o (β₁ i)] [forall i, Zero (β₂ i)] [forall (i) (x : β₁ i), Decidable (x != 0)] [f
orall (i) (x : β₂ i), Decidable (x != 0)] [CommMonoid γ] {f : forall i, β₁ i -> 
β₂ i} {hf : forall i, f i 0 = 0} {g : Π₀ i, β₁ i} {h : forall i, β₂ i -> γ} (h0 
: forall i, h i 0 = 1) : (mapRange f hf g).prod h = g.prod fun i b => h i (f i b
)
参数：β₁ i；β₂ i；i；x : β₁ i；x != 0；i；x : β₂ i；x != 0；h0 : forall i, h i 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.mapRange_def`：mapRange_def [forall (i) (x : β₁ i), Decidable (x
 != 0)] {f : forall i, β₁ i -> β₂ i} {hf : forall i, f i 0 = 0} {g : Π₀ i, β₁ i}
 : mapRange…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `DFinsupp.support_mk_subset`：support_mk_subset {s : Finset ι} {x : forall
 i : (↑s : Set ι), β i.1} : (mk s x).support subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem prod_mapRange_index {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [∀ i, Zero (β₁ i)]
    [∀ i, Zero (β₂ i)] [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)]
    [CommMonoid γ] {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} {h : ∀ i, β₂ i → γ}
    (h0 : ∀ i, h i 0 = 1) : (mapRange f hf g).prod h = g.prod fun i b => h i (f i b) := by
  rw [mapRange_def]
  refine (Finset.prod_subset support_mk_subset ?_).trans ?_
  · intro i h1 h2
    simp only [mem_support_toFun, ne_eq] at h1
    simp only [Finset.coe_sort_coe, mem_support_toFun, mk_apply, ne_eq, h1, not_false_iff,
      dite_eq_ite, ite_true, not_not] at h2
    simp [h2, h0]
  · refine Finset.prod_congr rfl ?_
    intro i h1
    simp only [mem_support_toFun, ne_eq] at h1
    simp [h1]

@[to_additive]
/-
**DFinsupp.prod_zero_index** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_zero_index [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Dec
idable (x != 0)] [CommMonoid γ] {h : forall i, β i -> γ} : (0 : Π₀ i, β i).prod 
h = 1
参数：β i；i；x : β i；x != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_zero_index [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {h : ∀ i, β i → γ} : (0 : Π₀ i, β i).prod h = 1 :=
  rfl

@[to_additive]
/-
**DFinsupp.prod_single_index** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_single_index [forall i, Zero (β i)] [forall (i) (x : β i), Decidable 
(x != 0)] [CommMonoid γ] {i : ι} {b : β i} {h : forall i, β i -> γ} (h_zero : h 
i 0 = 1) : (single i b).prod h = h i b
参数：β i；i；x : β i；x != 0；h_zero : h i 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `DFinsupp.support_single`：support_single {i : ι} {b : β i} (hb : b != 0) 
: (single i b).support = {i}
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFinsupp.prod.congr_simp`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} {
inst : DecidableEq ι} [inst_1 : DecidableEq ι]   [inst_2 : (i : ι) → Zero (β i)]
 {inst_3 : (i …
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `DFinsupp.single_zero`：single_zero (i) : (single i 0 : Π₀ i, β i) = 0
-/
theorem prod_single_index [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {i : ι} {b : β i} {h : ∀ i, β i → γ} (h_zero : h i 0 = 1) : (single i b).prod h = h i b := by
  by_cases h : b ≠ 0
  · simp [DFinsupp.prod, support_single h]
  · rw [not_not] at h
    simp [h, h_zero]
    rfl

@[to_additive]
/-
**DFinsupp.prod_neg_index** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_neg_index [forall i, AddGroup (β i)] [forall (i) (x : β i), Decidable
 (x != 0)] [CommMonoid γ] {g : Π₀ i, β i} {h : forall i, β i -> γ} (h0 : forall 
i, h i 0 = 1) : (-g).prod h = g.prod fun i b => h i (-b)
参数：β i；i；x : β i；x != 0；h0 : forall i, h i 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.prod_mapRange_index`：prod_mapRange_index {β₁ : ι -> Type v₁} {β
₂ : ι -> Type v₂} [forall i, Zero (β₁ i)] [forall i, Zero (β₂ i)] [forall (i) (x
 : β₁ i), Decidabl…
-/
theorem prod_neg_index [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {g : Π₀ i, β i} {h : ∀ i, β i → γ} (h0 : ∀ i, h i 0 = 1) :
    (-g).prod h = g.prod fun i b => h i (-b) :=
  prod_mapRange_index h0

@[to_additive]
/-
**DFinsupp.prod_comm** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ -> Type*} {β₂ : ι₂ -> Type*} [Decidabl
eEq ι₁] [DecidableEq ι₂] [forall i, Zero (β₁ i)] [forall i, Zero (β₂ i)] [forall
 (i) (x : β₁ i), Decidable (x != 0)] [forall (i) (x : β₂ i), Decidable (x != 0)]
 [CommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : forall i, β₁ i -> foral
l i, β₂ i -> γ) : (f₁.prod fun i₁ x₁ => f₂.prod fun i₂ x₂ => h i₁ x₁ i₂ x₂) = f₂
.prod fun i₂ x₂ => f₁.prod fun i₁ x₁ => h i₁ x₁ i₂ x₂
参数：β₁ i；β₂ i；i；x : β₁ i；x != 0；i；x : β₂ i；x != 0；f₁ : Π₀ i, β₁ i；f₂ : Π₀ i, β₂ i
；h : forall i, β₁ i -> forall i, β₂ i -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_comm`：prod_comm {s : Finset γ} {t : Finset α} {f : γ -> α ->
 β} : (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y
-/
theorem prod_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} [DecidableEq ι₁]
    [DecidableEq ι₂] [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)] [∀ (i) (x : β₁ i), Decidable (x ≠ 0)]
    [∀ (i) (x : β₂ i), Decidable (x ≠ 0)] [CommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i)
    (h : ∀ i, β₁ i → ∀ i, β₂ i → γ) :
    (f₁.prod fun i₁ x₁ => f₂.prod fun i₂ x₂ => h i₁ x₁ i₂ x₂) =
      f₂.prod fun i₂ x₂ => f₁.prod fun i₁ x₁ => h i₁ x₁ i₂ x₂ :=
  Finset.prod_comm

@[simp]
/-
**DFinsupp.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sum_apply {ι} {β : ι -> Type v} {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ -
> Type v₁} [forall i₁, Zero (β₁ i₁)] [forall (i) (x : β₁ i), Decidable (x != 0)]
 [forall i, AddCommMonoid (β i)] {f : Π₀ i₁, β₁ i₁} {g : forall i₁, β₁ i₁ -> Π₀ 
i, β i} {i₂ : ι} : (f.sum g) i₂ = f.sum fun i₁ b => g i₁ b i₂
参数：β₁ i₁；i；x : β₁ i；x != 0；β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem sum_apply {ι} {β : ι → Type v} {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁}
    [∀ i₁, Zero (β₁ i₁)] [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)]
    {f : Π₀ i₁, β₁ i₁} {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} {i₂ : ι} :
    (f.sum g) i₂ = f.sum fun i₁ b => g i₁ b i₂ :=
  map_sum (evalAddMonoidHom i₂) _ f.support
/-
**DFinsupp.support_sum** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_sum {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ -> Type v₁} [forall i
₁, Zero (β₁ i₁)] [forall (i) (x : β₁ i), Decidable (x != 0)] [forall i, AddCommM
onoid (β i)] [forall (i) (x : β i), Decidable (x != 0)] {f : Π₀ i₁, β₁ i₁} {g : 
forall i₁, β₁ i₁ -> Π₀ i, β i} : (f.sum g).support subseteq f.support.biUnion fu
n i => (g i (f i)).support
参数：β₁ i₁；i；x : β₁ i；x != 0；β i；i；x : β i；x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.mem_support_iff`：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in
 f.support ↔ f i != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.sum_apply`：sum_apply {ι} {β : ι -> Type v} {ι₁ : Type u₁} [Deci
dableEq ι₁] {β₁ : ι₁ -> Type v₁} [forall i₁, Zero (β₁ i₁)] [forall (i) (x : β₁ i
), Decid…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem support_sum {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i₁, β₁ i₁} {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} :
    (f.sum g).support ⊆ f.support.biUnion fun i => (g i (f i)).support := by
  have :
    ∀ i₁ : ι,
      (f.sum fun (i : ι₁) (b : β₁ i) => (g i b) i₁) ≠ 0 → ∃ i : ι₁, f i ≠ 0 ∧ ¬(g i (f i)) i₁ = 0 :=
    fun i₁ h =>
    let ⟨i, hi, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨i, mem_support_iff.1 hi, Ne⟩
  simpa [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply] using this

@[to_additive (attr := simp)]
/-
**DFinsupp.prod_one** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_one [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable 
(x != 0)] [CommMonoid γ] {f : Π₀ i, β i} : (f.prod fun _ _ => (1 : γ)) = 1
参数：β i；i；x : β i；x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
-/
theorem prod_one [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} : (f.prod fun _ _ => (1 : γ)) = 1 :=
  Finset.prod_const_one

@[to_additive (attr := simp)]
/-
**DFinsupp.prod_mul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_mul [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable 
(x != 0)] [CommMonoid γ] {f : Π₀ i, β i} {h₁ h₂ : forall i, β i -> γ} : (f.prod 
fun i b => h₁ i b * h₂ i b) = f.prod h₁ * f.prod h₂
参数：β i；i；x : β i；x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
-/
theorem prod_mul [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h₁ h₂ : ∀ i, β i → γ} :
    (f.prod fun i b => h₁ i b * h₂ i b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib

@[to_additive (attr := simp)]
/-
**DFinsupp.prod_inv** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_inv [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable 
(x != 0)] [DivisionCommMonoid γ] {f : Π₀ i, β i} {h : forall i, β i -> γ} : (f.p
rod fun i b => (h i b)⁻¹) = (f.prod h)⁻¹
参数：β i；i；x : β i；x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem prod_inv [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [DivisionCommMonoid γ] {f : Π₀ i, β i} {h : ∀ i, β i → γ} :
    (f.prod fun i b => (h i b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (invMonoidHom : γ →* γ) _ f.support).symm

@[to_additive]
/-
**DFinsupp.prod_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_eq_one [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 
0)] [CommMonoid γ] {f : Π₀ i, β i} {h : forall i, β i -> γ} (hyp : forall i, h i
 (f i) = 1) : f.prod h = 1
参数：β i；i；x : β i；x != 0；hyp : forall i, h i (f i) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
-/
theorem prod_eq_one [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h : ∀ i, β i → γ} (hyp : ∀ i, h i (f i) = 1) : f.prod h = 1 :=
  Finset.prod_eq_one fun i _ => hyp i
/-
**DFinsupp.smul_sum** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：smul_sum {α : Type*} [forall i, Zero (β i)] [forall (i) (x : β i), Decidab
le (x != 0)] [AddCommMonoid γ] [DistribSMul α γ] {f : Π₀ i, β i} {h : forall i, 
β i -> γ} {c : α} : c • f.sum h = f.sum fun a b => c • h a b
参数：β i；i；x : β i；x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
-/
theorem smul_sum {α : Type*} [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [AddCommMonoid γ] [DistribSMul α γ] {f : Π₀ i, β i} {h : ∀ i, β i → γ} {c : α} :
    c • f.sum h = f.sum fun a b => c • h a b :=
  Finset.smul_sum

@[to_additive]
/-
**DFinsupp.prod_add_index** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_add_index [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Deci
dable (x != 0)] [CommMonoid γ] {f g : Π₀ i, β i} {h : forall i, β i -> γ} (h_zer
o : forall i, h i 0 = 1) (h_add : forall i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b
₂) : (f + g).prod h = f.prod h * g.prod h
参数：β i；i；x : β i；x != 0；h_zero : forall i, h i 0 = 1；h_add : forall i b₁ b₂, h i
 (b₁ + b₂) = h i b₁ * h i b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `DFinsupp.support_add`：support_add [forall i, AddZeroClass (β i)] [forall
 (i) (x : β i), Decidable (x != 0)] {g₁ g₂ : Π₀ i, β i} : (g₁ + g₂).support subs
eteq g₁.su…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
-/
theorem prod_add_index [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {f g : Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) : (f + g).prod h = f.prod h * g.prod h :=
  have f_eq : (∏ i ∈ f.support ∪ g.support, h i (f i)) = f.prod h :=
    (Finset.prod_subset Finset.subset_union_left <| by
        simp +contextual [h_zero]).symm
  have g_eq : (∏ i ∈ f.support ∪ g.support, h i (g i)) = g.prod h :=
    (Finset.prod_subset Finset.subset_union_right <| by
        simp +contextual [h_zero]).symm
  calc
    (∏ i ∈ (f + g).support, h i ((f + g) i)) = ∏ i ∈ f.support ∪ g.support, h i ((f + g) i) :=
      Finset.prod_subset support_add <| by
        simp +contextual [h_zero]
    _ = (∏ i ∈ f.support ∪ g.support, h i (f i)) * ∏ i ∈ f.support ∪ g.support, h i (g i) := by
      { simp [h_add, Finset.prod_mul_distrib] }
    _ = _ := by rw [f_eq, g_eq]

@[to_additive (attr := simp)]
/-
**DFinsupp.prod_eq_prod_fintype** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_eq_prod_fintype [Fintype ι] [forall i, Zero (β i)] [forall (i : ι) (x
 : β i), Decidable (x != 0)] [CommMonoid γ] (v : Π₀ i, β i) {f : forall i, β i -
> γ} (hf : forall i, f i 0 = 1) : v.prod f = ∏ i, f i (DFinsupp.equivFunOnFintyp
e v i)
参数：β i；i : ι；x : β i；x != 0；v : Π₀ i, β i；hf : forall i, f i 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `DFinsupp.mem_support_iff`：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in
 f.support ↔ f i != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `DFinsupp.equivFunOnFintype_apply`：∀ {ι : Type u} {β : ι → Type v} [inst 
: (i : ι) → Zero (β i)] [inst_1 : Fintype ι] (a : Π₀ (i : ι), β i) (a_1 : ι),   
DFinsupp.equivFunOnFin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_eq_prod_fintype [Fintype ι] [∀ i, Zero (β i)] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] (v : Π₀ i, β i) {f : ∀ i, β i → γ} (hf : ∀ i, f i 0 = 1) :
    v.prod f = ∏ i, f i (DFinsupp.equivFunOnFintype v i) := by
  suffices (∏ i ∈ v.support, f i (v i)) = ∏ i, f i (v i) by simp [DFinsupp.prod, this]
  apply Finset.prod_subset v.support.subset_univ
  intro i _ hi
  rw [mem_support_iff, not_not] at hi
  rw [hi, hf]

section CommMonoidWithZero
variable [Π i, Zero (β i)] [CommMonoidWithZero γ] [Nontrivial γ] [NoZeroDivisors γ]
  [Π i, DecidableEq (β i)] {f : Π₀ i, β i} {g : Π i, β i → γ}

@[simp]
/-
**DFinsupp.prod_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：prod_eq_zero_iff : f.prod g = 0 ↔ exists i in f.support, g i (f i) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_eq_zero_iff`：prod_eq_zero_iff : ∏ x in s, f x = 0 ↔ exists a
 in s, f a = 0
-/
lemma prod_eq_zero_iff : f.prod g = 0 ↔ ∃ i ∈ f.support, g i (f i) = 0 := Finset.prod_eq_zero_iff
/-
**DFinsupp.prod_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：prod_ne_zero_iff : f.prod g != 0 ↔ forall i in f.support, g i (f i) != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
-/
lemma prod_ne_zero_iff : f.prod g ≠ 0 ↔ ∀ i ∈ f.support, g i (f i) ≠ 0 := Finset.prod_ne_zero_iff

end CommMonoidWithZero

/--
When summing over an `ZeroHom`, the decidability assumption is not needed, and the result is
also an `ZeroHom`.
-/
/-
**DFinsupp.sumZeroHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：sumZeroHom [forall i, Zero (β i)] [AddCommMonoid γ] (φ : forall i, ZeroHom
 (β i) γ) : ZeroHom (Π₀ i, β i) γ where toFun f
参数：β i；φ : forall i, ZeroHom (β i) γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When summing over an `ZeroHom`, the decidability assumption is not needed, and t
he result is
also an `ZeroHom`.
-/
def sumZeroHom [∀ i, Zero (β i)] [AddCommMonoid γ] (φ : ∀ i, ZeroHom (β i) γ) :
    ZeroHom (Π₀ i, β i) γ where
  toFun f :=
    (f.support'.lift fun s => ∑ i ∈ Multiset.toFinset s.1, φ i (f i)) <| by
      rintro ⟨sx, hx⟩ ⟨sy, hy⟩
      dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
      have H1 : sx.toFinset ∩ sy.toFinset ⊆ sx.toFinset := Finset.inter_subset_left
      have H2 : sx.toFinset ∩ sy.toFinset ⊆ sy.toFinset := Finset.inter_subset_right
      refine
        (Finset.sum_subset H1 ?_).symm.trans
          ((Finset.sum_congr rfl ?_).trans (Finset.sum_subset H2 ?_))
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert! map_zero (φ i)
        exact (hy i).resolve_left (mt (And.intro H1) H2)
      · intro i _
        rfl
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert! map_zero (φ i)
        exact (hx i).resolve_left (mt (fun H3 => And.intro H3 H1) H2)
  map_zero' := by
    simp only [toFun_eq_coe, coe_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]; rfl

@[simp]
/-
**DFinsupp.sumZeroHom_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumZeroHom_single [forall i, Zero (β i)] [AddCommMonoid γ] (φ : forall i, 
ZeroHom (β i) γ) (i) (x : β i) : sumZeroHom φ (single i x) = φ i x
参数：β i；φ : forall i, ZeroHom (β i) γ；i；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.toFinset_singleton`：toFinset_singleton (a : α) : toFinset ({a} 
: Multiset α) = {a}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem sumZeroHom_single [∀ i, Zero (β i)] [AddCommMonoid γ] (φ : ∀ i, ZeroHom (β i) γ) (i)
    (x : β i) : sumZeroHom φ (single i x) = φ i x := by
  dsimp [sumZeroHom, single, Trunc.lift_mk]
  rw [Multiset.toFinset_singleton, Finset.sum_singleton, Pi.single_eq_same]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**DFinsupp.sumZeroHom_piSingle** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumZeroHom_piSingle [forall i, Zero (β i)] [AddCommMonoid γ] (i) (φ : Zero
Hom (β i) γ) : sumZeroHom (Pi.single i φ) = φ.comp { toFun
参数：β i；i；φ : ZeroHom (β i) γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 : Z
ero N] ⦃f g : ZeroHom M N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
-/
theorem sumZeroHom_piSingle [∀ i, Zero (β i)] [AddCommMonoid γ] (i) (φ : ZeroHom (β i) γ) :
    sumZeroHom (Pi.single i φ) = φ.comp { toFun := (· i), map_zero' := rfl } := by
  ext ⟨f, sf, hf⟩
  simp only [sumZeroHom, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk', ZeroHom.coe_comp,
    Function.comp_apply]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => ?_), Pi.single_eq_same]
  · simp [hji]
  · simp [(hf i).resolve_left (by simpa using hi)]

/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
/-
**DFinsupp.sumZeroHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumZeroHom_apply [forall i, AddZeroClass (β i)] [forall (i) (x : β i), Dec
idable (x != 0)] [AddCommMonoid γ] (φ : forall i, ZeroHom (β i) γ) (f : Π₀ i, β 
i) : sumZeroHom φ f = f.sum fun x => φ x
参数：β i；i；x : β i；x != 0；φ : forall i, ZeroHom (β i) γ；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N

--- 原说明 ---
While we didn't need decidable instances to define it, we do to reduce it to a s
um
-/
theorem sumZeroHom_apply [∀ i, AddZeroClass (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [AddCommMonoid γ] (φ : ∀ i, ZeroHom (β i) γ) (f : Π₀ i, β i) :
    sumZeroHom φ f = f.sum fun x => φ x := by
  rcases f with ⟨f, s, hf⟩
  change (∑ i ∈ _, _) = ∑ i ∈ _ with _, _
  rw [Finset.sum_filter, Finset.sum_congr rfl]
  intro i _
  dsimp only [coe_mk', Subtype.coe_mk] at *
  split_ifs with h
  · rfl
  · rw [not_not.mp h, map_zero]

set_option backward.isDefEq.respectTransparency false in
/--
When summing over an `AddMonoidHom`, the decidability assumption is not needed, and the result is
also an `AddMonoidHom`.
-/
@[simps toZeroHom]
/-
**DFinsupp.sumAddHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：sumAddHom [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : forall i, 
β i ->+ γ) : (Π₀ i, β i) ->+ γ where .toZeroHom __
参数：β i；φ : forall i, β i ->+ γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When summing over an `AddMonoidHom`, the decidability assumption is not needed, 
and the result is
also an `AddMonoidHom`.
-/
def sumAddHom [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) :
    (Π₀ i, β i) →+ γ where
  __ := sumZeroHom fun i => φ i |>.toZeroHom
  map_add' := by
    rintro ⟨f, sf, hf⟩ ⟨g, sg, hg⟩
    change (∑ i ∈ _, _) = (∑ i ∈ _, _) + ∑ i ∈ _, _
    simp only [AddMonoidHom.toZeroHom_coe, coe_add, coe_mk', Pi.add_apply, map_add,
      Finset.sum_add_distrib]
    congr 1
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inl
      · intro i _ H2
        simp only [Multiset.mem_toFinset] at H2
        rw [(hf i).resolve_left H2, map_zero]
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inr
      · intro i _ H2
        simp only [Multiset.mem_toFinset] at H2
        rw [(hg i).resolve_left H2, map_zero]

@[simp]
/-
**DFinsupp.sumAddHom_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumAddHom_single [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : for
all i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (single i x) = φ i x
参数：β i；φ : forall i, β i ->+ γ；i；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.sumZeroHom_single`：sumZeroHom_single [forall i, Zero (β i)] [Ad
dCommMonoid γ] (φ : forall i, ZeroHom (β i) γ) (i) (x : β i) : sumZeroHom φ (sin
gle i x) = φ i x
-/
theorem sumAddHom_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) (i)
    (x : β i) : sumAddHom φ (single i x) = φ i x := sumZeroHom_single _ _ _

@[simp]
/-
**DFinsupp.sumAddHom_piSingle** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumAddHom_piSingle [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (i) (φ
 : β i ->+ γ) : sumAddHom (Pi.single i φ) = φ.comp (evalAddMonoidHom i)
参数：β i；i；φ : β i ->+ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.toZeroHom_injective`：∀ {M : Type u_4} {N : Type u_5} [inst 
: AddZero M] [inst_1 : AddZero N], Function.Injective AddMonoidHom.toZeroHom
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.sumAddHom_toZeroHom`：∀ {ι : Type u} {γ : Type w} {β : ι → Type 
v} [inst : DecidableEq ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   [inst_2 : Ad
dCommMonoid γ] (φ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.apply_single`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} 
[inst : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decida
bleEq…
· 使用定理 `DFinsupp.sumZeroHom_piSingle`：sumZeroHom_piSingle [forall i, Zero (β i)]
 [AddCommMonoid γ] (i) (φ : ZeroHom (β i) γ) : sumZeroHom (Pi.single i φ) = φ.co
mp { toFun
-/
theorem sumAddHom_piSingle [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (i) (φ : β i →+ γ) :
    sumAddHom (Pi.single i φ) = φ.comp (evalAddMonoidHom i) :=
  AddMonoidHom.toZeroHom_injective <| by
    convert! sumZeroHom_piSingle i φ.toZeroHom using 1
    rw [DFinsupp.sumAddHom_toZeroHom]
    conv_lhs =>
      enter [1, i]
      rw [Pi.apply_single (fun i (x : β i →+ γ) => x.toZeroHom) (fun _ => rfl)]

@[simp]
/-
**DFinsupp.sumAddHom_comp_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumAddHom_comp_single [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (f 
: forall i, β i ->+ γ) (i : ι) : (sumAddHom f).comp (singleAddHom β i) = f i
参数：β i；f : forall i, β i ->+ γ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
-/
theorem sumAddHom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) : (sumAddHom f).comp (singleAddHom β i) = f i :=
  AddMonoidHom.ext fun x => sumAddHom_single f i x

/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
/-
**DFinsupp.sumAddHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumAddHom_apply [forall i, AddZeroClass (β i)] [forall (i) (x : β i), Deci
dable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (f : Π₀ i, β i) : su
mAddHom φ f = f.sum fun x => φ x
参数：β i；i；x : β i；x != 0；φ : forall i, β i ->+ γ；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.sumZeroHom_apply`：sumZeroHom_apply [forall i, AddZeroClass (β i
)] [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, Z
eroHom (β i) γ)…

--- 原说明 ---
While we didn't need decidable instances to define it, we do to reduce it to a s
um
-/
theorem sumAddHom_apply [∀ i, AddZeroClass (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) (f : Π₀ i, β i) : sumAddHom φ f = f.sum fun x => φ x :=
  sumZeroHom_apply _ _
/-
**DFinsupp.sumAddHom_comm** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumAddHom_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ -> Type*} {β₂ : ι₂ -> Type*} {γ :
 Type*} [DecidableEq ι₁] [DecidableEq ι₂] [forall i, AddZeroClass (β₁ i)] [foral
l i, AddZeroClass (β₂ i)] [AddCommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) 
(h : forall i j, β₁ i ->+ β₂ j ->+ γ) : sumAddHom (fun i₂ => sumAddHom (fun i₁ =
> h i₁ i₂) f₁) f₂ = sumAddHom (fun i₁ => sumAddHom (fun i₂ => (h i₁ i₂).flip) f₂
) f₁
参数：β₁ i；β₂ i；f₁ : Π₀ i, β₁ i；f₂ : Π₀ i, β₂ i；h : forall i j, β₁ i ->+ β₂ j ->+ γ
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quot.lift.congr_simp`：∀ {α : Sort u} {r : α → α → Prop} {β : Sort v} (f 
f_1 : α → β) (e_f : f = f_1) (a : ∀ (a b : α), r a b → f a = f b)   (a_1 a_2 : Q
uot r), a_…
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `AddMonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Ad
dZero M] [inst_1 : AddZero N] (toZeroHom toZeroHom_1 : ZeroHom M N)   (e_toZeroH
om : toZeroHom =…
· 使用定理 `AddMonoidHom.finsetSum_apply`：∀ {ι : Type u_1} {M : Type u_3} {N : Type 
u_4} [inst : AddZeroClass M] [inst_1 : AddCommMonoid N] (f : ι → M →+ N)   (s : 
Finset ι) (b : M),…
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
-/
theorem sumAddHom_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} {γ : Type*}
    [DecidableEq ι₁] [DecidableEq ι₂] [∀ i, AddZeroClass (β₁ i)] [∀ i, AddZeroClass (β₂ i)]
    [AddCommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : ∀ i j, β₁ i →+ β₂ j →+ γ) :
    sumAddHom (fun i₂ => sumAddHom (fun i₁ => h i₁ i₂) f₁) f₂ =
      sumAddHom (fun i₁ => sumAddHom (fun i₂ => (h i₁ i₂).flip) f₂) f₁ := by
  obtain ⟨⟨f₁, s₁, h₁⟩, ⟨f₂, s₂, h₂⟩⟩ := f₁, f₂
  simpa [sumAddHom, sumZeroHom, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_mk,
      AddMonoidHom.flip_apply, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk']
    using Finset.sum_comm

/-- The `DFinsupp` version of `Finsupp.liftAddHom` -/
@[simps apply symm_apply]
/-
**DFinsupp.liftAddHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：liftAddHom [forall i, AddZeroClass (β i)] [AddCommMonoid γ] : (forall i, β
 i ->+ γ) ≃+ ((Π₀ i, β i) ->+ γ) where toFun
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `DFinsupp` version of `Finsupp.liftAddHom`
-/
def liftAddHom [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] :
    (∀ i, β i →+ γ) ≃+ ((Π₀ i, β i) →+ γ) where
  toFun := sumAddHom
  invFun F i := F.comp (singleAddHom β i)
  left_inv x := by ext; simp
  right_inv ψ := by ext; simp
  map_add' F G := by ext; simp

/-- The `DFinsupp` version of `Finsupp.liftAddHom_singleAddHom` -/
/-
**DFinsupp.liftAddHom_singleAddHom** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：liftAddHom_singleAddHom [forall i, AddCommMonoid (β i)] : liftAddHom (sing
leAddHom β) = AddMonoidHom.id (Π₀ i, β i)
参数：β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x

--- 原说明 ---
The `DFinsupp` version of `Finsupp.liftAddHom_singleAddHom`
-/
theorem liftAddHom_singleAddHom [∀ i, AddCommMonoid (β i)] :
    liftAddHom (singleAddHom β) = AddMonoidHom.id (Π₀ i, β i) :=
  liftAddHom.toEquiv.eq_symm_apply.1 rfl

/-- The `DFinsupp` version of `Finsupp.liftAddHom_apply_single` -/
/-
**DFinsupp.liftAddHom_apply_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：liftAddHom_apply_single [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (
f : forall i, β i ->+ γ) (i : ι) (x : β i) : liftAddHom f (single i x) = f i x
参数：β i；f : forall i, β i ->+ γ；i : ι；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.liftAddHom_apply`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   [inst_2 : AddCo
mmMonoid γ] (φ …
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `DFinsupp` version of `Finsupp.liftAddHom_apply_single`
-/
theorem liftAddHom_apply_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) (x : β i) : liftAddHom f (single i x) = f i x := by simp

/-- The `DFinsupp` version of `Finsupp.liftAddHom_comp_single` -/
/-
**DFinsupp.liftAddHom_comp_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：liftAddHom_comp_single [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (f
 : forall i, β i ->+ γ) (i : ι) : (liftAddHom f).comp (singleAddHom β i) = f i
参数：β i；f : forall i, β i ->+ γ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.liftAddHom_apply`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   [inst_2 : AddCo
mmMonoid γ] (φ …
· 使用定理 `DFinsupp.sumAddHom_comp_single`：sumAddHom_comp_single [forall i, AddZero
Class (β i)] [AddCommMonoid γ] (f : forall i, β i ->+ γ) (i : ι) : (sumAddHom f)
.comp (singleAddHom …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `DFinsupp` version of `Finsupp.liftAddHom_comp_single`
-/
theorem liftAddHom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) : (liftAddHom f).comp (singleAddHom β i) = f i := by simp

/-- The `DFinsupp` version of `Finsupp.comp_liftAddHom` -/
/-
**DFinsupp.comp_liftAddHom** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：comp_liftAddHom {δ : Type*} [forall i, AddZeroClass (β i)] [AddCommMonoid 
γ] [AddCommMonoid δ] (g : γ ->+ δ) (f : forall i, β i ->+ γ) : g.comp (liftAddHo
m f) = liftAddHom fun a => g.comp (f a)
参数：β i；g : γ ->+ δ；f : forall i, β i ->+ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddEquiv.symm_apply_eq`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [
inst_1 : Add N] (e : M ≃+ N) {x : N} {y : M}, e.symm x = y ↔ x = e y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.liftAddHom_symm_apply`：∀ {ι : Type u} {γ : Type w} {β : ι → Typ
e v} [inst : DecidableEq ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   [inst_2 : 
AddCommMonoid γ] (F …
· 使用定理 `AddMonoidHom.comp_assoc`：∀ {M : Type u_4} {N : Type u_5} {P : Type u_6} 
{Q : Type u_10} [inst : AddZero M] [inst_1 : AddZero N]   [inst_2 : AddZero P] [
inst_3 : AddZ…
· 使用定理 `DFinsupp.liftAddHom_comp_single`：liftAddHom_comp_single [forall i, AddZe
roClass (β i)] [AddCommMonoid γ] (f : forall i, β i ->+ γ) (i : ι) : (liftAddHom
 f).comp (singleAddHo…

--- 原说明 ---
The `DFinsupp` version of `Finsupp.comp_liftAddHom`
-/
theorem comp_liftAddHom {δ : Type*} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ →+ δ) (f : ∀ i, β i →+ γ) :
    g.comp (liftAddHom f) = liftAddHom fun a => g.comp (f a) :=
  liftAddHom.symm_apply_eq.1 <|
    funext fun a => by
      rw [liftAddHom_symm_apply, AddMonoidHom.comp_assoc, liftAddHom_comp_single]

@[simp]
/-
**DFinsupp.sumAddHom_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumAddHom_zero [forall i, AddZeroClass (β i)] [AddCommMonoid γ] : (sumAddH
om fun i => (0 : β i ->+ γ)) = 0
参数：β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem sumAddHom_zero [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] :
    (sumAddHom fun i => (0 : β i →+ γ)) = 0 :=
  map_zero liftAddHom

@[simp]
/-
**DFinsupp.sumAddHom_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumAddHom_add [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (g : forall
 i, β i ->+ γ) (h : forall i, β i ->+ γ) : (sumAddHom fun i => g i + h i) = sumA
ddHom g + sumAddHom h
参数：β i；g : forall i, β i ->+ γ；h : forall i, β i ->+ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem sumAddHom_add [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (g : ∀ i, β i →+ γ)
    (h : ∀ i, β i →+ γ) : (sumAddHom fun i => g i + h i) = sumAddHom g + sumAddHom h :=
  map_add liftAddHom _ _

@[simp]
/-
**DFinsupp.sumAddHom_singleAddHom** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sumAddHom_singleAddHom [forall i, AddCommMonoid (β i)] : sumAddHom (single
AddHom β) = AddMonoidHom.id _
参数：β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.liftAddHom_singleAddHom`：liftAddHom_singleAddHom [forall i, Add
CommMonoid (β i)] : liftAddHom (singleAddHom β) = AddMonoidHom.id (Π₀ i, β i)
-/
theorem sumAddHom_singleAddHom [∀ i, AddCommMonoid (β i)] :
    sumAddHom (singleAddHom β) = AddMonoidHom.id _ :=
  liftAddHom_singleAddHom
/-
**DFinsupp.comp_sumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：comp_sumAddHom {δ : Type*} [forall i, AddZeroClass (β i)] [AddCommMonoid γ
] [AddCommMonoid δ] (g : γ ->+ δ) (f : forall i, β i ->+ γ) : g.comp (sumAddHom 
f) = sumAddHom fun a => g.comp (f a)
参数：β i；g : γ ->+ δ；f : forall i, β i ->+ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.comp_liftAddHom`：comp_liftAddHom {δ : Type*} [forall i, AddZero
Class (β i)] [AddCommMonoid γ] [AddCommMonoid δ] (g : γ ->+ δ) (f : forall i, β 
i ->+ γ) : g.c…
-/
theorem comp_sumAddHom {δ : Type*} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ →+ δ) (f : ∀ i, β i →+ γ) : g.comp (sumAddHom f) = sumAddHom fun a => g.comp (f a) :=
  comp_liftAddHom _ _
/-
**DFinsupp.sum_sub_index** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sum_sub_index [forall i, AddGroup (β i)] [forall (i) (x : β i), Decidable 
(x != 0)] [AddCommGroup γ] {f g : Π₀ i, β i} {h : forall i, β i -> γ} (h_sub : f
orall i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂) : (f - g).sum h = f.sum h - g.su
m h
参数：β i；i；x : β i；x != 0；h_sub : forall i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (g h : α),   f (g - h) = f g - f h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `DFinsupp.liftAddHom_apply`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   [inst_2 : AddCo
mmMonoid γ] (φ …
-/
theorem sum_sub_index [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [AddCommGroup γ]
    {f g : Π₀ i, β i} {h : ∀ i, β i → γ} (h_sub : ∀ i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂) :
    (f - g).sum h = f.sum h - g.sum h := by
  have := (liftAddHom fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g
  rw [liftAddHom_apply, sumAddHom_apply, sumAddHom_apply, sumAddHom_apply] at this
  exact this

@[to_additive]
/-
**DFinsupp.prod_finsetSum_index** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_finsetSum_index {γ : Type w} {α : Type x} [forall i, AddCommMonoid (β
 i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ] {s : Finset α} {g
 : α -> Π₀ i, β i} {h : forall i, β i -> γ} (h_zero : forall i, h i 0 = 1) (h_ad
d : forall i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) : (∏ i in s, (g i).prod h) 
= (∑ i in s, g i).prod h
参数：β i；i；x : β i；x != 0；h_zero : forall i, h i 0 = 1；h_add : forall i b₁ b₂, h i
 (b₁ + b₂) = h i b₁ * h i b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `DFinsupp.prod.congr_simp`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} {
inst : DecidableEq ι} [inst_1 : DecidableEq ι]   [inst_2 : (i : ι) → Zero (β i)]
 {inst_3 : (i …
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `DFinsupp.prod_add_index`：prod_add_index [forall i, AddCommMonoid (β i)] 
[forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ] {f g : Π₀ i, β i} {h :
 forall i, β …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_finsetSum_index {γ : Type w} {α : Type x} [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] {s : Finset α} {g : α → Π₀ i, β i}
    {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
    (∏ i ∈ s, (g i).prod h) = (∑ i ∈ s, g i).prod h := by
  classical
  exact Finset.induction_on s (by simp [prod_zero_index])
        (by simp +contextual [prod_add_index, h_zero, h_add])

@[deprecated (since := "2026-04-08")] alias sum_finset_sum_index := sum_finsetSum_index

@[to_additive existing, deprecated (since := "2026-04-08")]
alias prod_finset_sum_index := prod_finsetSum_index

@[to_additive]
/-
**DFinsupp.prod_sum_index** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_sum_index {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ -> Type v₁} [foral
l i₁, Zero (β₁ i₁)] [forall (i) (x : β₁ i), Decidable (x != 0)] [forall i, AddCo
mmMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ] {f : Π
₀ i₁, β₁ i₁} {g : forall i₁, β₁ i₁ -> Π₀ i, β i} {h : forall i, β i -> γ} (h_zer
o : forall i, h i 0 = 1) (h_add : forall i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b
₂) : (f.sum g).prod h = f.prod fun i b => (g i b).prod h
参数：β₁ i₁；i；x : β₁ i；x != 0；β i；i；x : β i；x != 0；h_zero : forall i, h i 0 = 1；h_a
dd : forall i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.prod_finsetSum_index`：prod_finsetSum_index {γ : Type w} {α : Ty
pe x} [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)]
 [CommMonoid γ] {s …
-/
theorem prod_sum_index {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] {f : Π₀ i₁, β₁ i₁}
    {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
    (f.sum g).prod h = f.prod fun i b => (g i b).prod h :=
  (prod_finsetSum_index h_zero h_add).symm

@[simp]
/-
**DFinsupp.sum_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sum_single [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidabl
e (x != 0)] {f : Π₀ i, β i} : f.sum single = f
参数：β i；i；x : β i；x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `DFinsupp.liftAddHom_singleAddHom`：liftAddHom_singleAddHom [forall i, Add
CommMonoid (β i)] : liftAddHom (singleAddHom β) = AddMonoidHom.id (Π₀ i, β i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `DFinsupp.liftAddHom_apply`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   [inst_2 : AddCo
mmMonoid γ] (φ …
-/
theorem sum_single [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i, β i} :
    f.sum single = f := by
  have := DFunLike.congr_fun (liftAddHom_singleAddHom (β := β)) f
  rw [liftAddHom_apply, sumAddHom_apply] at this
  exact this

@[to_additive]
/-
**DFinsupp.prod_subtypeDomain_index** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：prod_subtypeDomain_index [forall i, Zero (β i)] [forall (i) (x : β i), Dec
idable (x != 0)] [CommMonoid γ] {v : Π₀ i, β i} {p : ι -> Prop} [DecidablePred p
] {h : forall i, β i -> γ} (hp : forall x in v.support, p x) : (v.subtypeDomain 
p).prod (fun i b => h i b) = v.prod h
参数：β i；i；x : β i；x != 0；hp : forall x in v.support, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_bij`：prod_bij (i : forall a in s, κ) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.support_subtypeDomain`：support_subtypeDomain {f : Π₀ i, β i} : 
(subtypeDomain p f).support = f.support.subtype p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem prod_subtypeDomain_index [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {v : Π₀ i, β i} {p : ι → Prop} [DecidablePred p] {h : ∀ i, β i → γ}
    (hp : ∀ x ∈ v.support, p x) : (v.subtypeDomain p).prod (fun i b => h i b) = v.prod h := by
  refine Finset.prod_bij (fun p _ ↦ p) ?_ ?_ ?_ ?_ <;> aesop
/-
**DFinsupp.subtypeDomain_sum** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomain_sum {ι} {β : ι -> Type v} [forall i, AddCommMonoid (β i)] {s
 : Finset γ} {h : γ -> Π₀ i, β i} {p : ι -> Prop} [DecidablePred p] : (∑ c in s,
 h c).subtypeDomain p = ∑ c in s, (h c).subtypeDomain p
参数：β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem subtypeDomain_sum {ι} {β : ι → Type v} [∀ i, AddCommMonoid (β i)] {s : Finset γ}
    {h : γ → Π₀ i, β i} {p : ι → Prop} [DecidablePred p] :
    (∑ c ∈ s, h c).subtypeDomain p = ∑ c ∈ s, (h c).subtypeDomain p :=
  map_sum (subtypeDomainAddMonoidHom β p) _ s
/-
**DFinsupp.subtypeDomain_finsupp_sum** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomain_finsupp_sum {ι} {β : ι -> Type v} {δ : γ -> Type x} [Decidab
leEq γ] [forall c, Zero (δ c)] [forall (c) (x : δ c), Decidable (x != 0)] [foral
l i, AddCommMonoid (β i)] {p : ι -> Prop} [DecidablePred p] {s : Π₀ c, δ c} {h :
 forall c, δ c -> Π₀ i, β i} : (s.sum h).subtypeDomain p = s.sum fun c d => (h c
 d).subtypeDomain p
参数：δ c；c；x : δ c；x != 0；β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.subtypeDomain_sum`：subtypeDomain_sum {ι} {β : ι -> Type v} [for
all i, AddCommMonoid (β i)] {s : Finset γ} {h : γ -> Π₀ i, β i} {p : ι -> Prop} 
[DecidablePred p…
-/
theorem subtypeDomain_finsupp_sum {ι} {β : ι → Type v} {δ : γ → Type x} [DecidableEq γ]
    [∀ c, Zero (δ c)] [∀ (c) (x : δ c), Decidable (x ≠ 0)]
    [∀ i, AddCommMonoid (β i)] {p : ι → Prop} [DecidablePred p]
    {s : Π₀ c, δ c} {h : ∀ c, δ c → Π₀ i, β i} :
    (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p :=
  subtypeDomain_sum

end ProdAndSum

end DFinsupp

/-! ### Product and sum lemmas for bundled morphisms.

In this section, we provide analogues of `AddMonoidHom.map_sum`, `AddMonoidHom.coe_finsetSum`,
and `AddMonoidHom.finsetSum_apply` for `DFinsupp.sum` and `DFinsupp.sumAddHom` instead of
`Finset.sum`.

We provide these for `AddMonoidHom`, `MonoidHom`, `RingHom`, `AddEquiv`, and `MulEquiv`.

Lemmas for `LinearMap` and `LinearEquiv` are in another file.
-/


section

variable [DecidableEq ι]

namespace MonoidHom

variable {R S : Type*}
variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

@[to_additive (attr := simp, norm_cast)]
/-
**MonoidHom.coe_dfinsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_dfinsuppProd [MulOneClass R] [CommMonoid S] (f : Π₀ i, β i) (g : foral
l i, β i -> R ->* S) : ⇑(f.prod g) = f.prod fun a b => ⇑(g a b)
参数：f : Π₀ i, β i；g : forall i, β i -> R ->* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.coe_finsetProd`：MonoidHom.coe_finsetProd [MulOneClass M] [Comm
Monoid N] (f : ι -> M ->* N) (s : Finset ι) : ⇑(∏ x in s, f x) = ∏ x in s, ⇑(f x
)
-/
theorem coe_dfinsuppProd [MulOneClass R] [CommMonoid S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S) :
    ⇑(f.prod g) = f.prod fun a b => ⇑(g a b) :=
  coe_finsetProd _ _

@[to_additive]
/-
**MonoidHom.dfinsuppProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：dfinsuppProd_apply [MulOneClass R] [CommMonoid S] (f : Π₀ i, β i) (g : for
all i, β i -> R ->* S) (r : R) : (f.prod g) r = f.prod fun a b => (g a b) r
参数：f : Π₀ i, β i；g : forall i, β i -> R ->* S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.finsetProd_apply`：MonoidHom.finsetProd_apply [MulOneClass M] [
CommMonoid N] (f : ι -> M ->* N) (s : Finset ι) (b : M) : (∏ x in s, f x) b = ∏ 
x in s, f x b
-/
theorem dfinsuppProd_apply [MulOneClass R] [CommMonoid S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S)
    (r : R) : (f.prod g) r = f.prod fun a b => (g a b) r :=
  finsetProd_apply _ _ _

end MonoidHom

/-! The above lemmas, repeated for `DFinsupp.sumAddHom`. -/


namespace AddMonoidHom

variable {R S : Type*}

open DFinsupp

@[simp]
/-
**AddMonoidHom.map_dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：map_dfinsuppSumAddHom [AddCommMonoid R] [AddCommMonoid S] [forall i, AddZe
roClass (β i)] (h : R ->+ S) (f : Π₀ i, β i) (g : forall i, β i ->+ R) : h (sumA
ddHom g f) = sumAddHom (fun i => h.comp (g i)) f
参数：β i；h : R ->+ S；f : Π₀ i, β i；g : forall i, β i ->+ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `DFinsupp.comp_liftAddHom`：comp_liftAddHom {δ : Type*} [forall i, AddZero
Class (β i)] [AddCommMonoid γ] [AddCommMonoid δ] (g : γ ->+ δ) (f : forall i, β 
i ->+ γ) : g.c…
-/
theorem map_dfinsuppSumAddHom [AddCommMonoid R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (h : R →+ S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h g) f
/-
**AddMonoidHom.dfinsuppSumAddHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：dfinsuppSumAddHom_apply [AddZeroClass R] [AddCommMonoid S] [forall i, AddZ
eroClass (β i)] (f : Π₀ i, β i) (g : forall i, β i ->+ R ->+ S) (r : R) : (sumAd
dHom g f) r = sumAddHom (fun i => (eval r).comp (g i)) f
参数：β i；f : Π₀ i, β i；g : forall i, β i ->+ R ->+ S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_dfinsuppSumAddHom`：map_dfinsuppSumAddHom [AddCommMonoid
 R] [AddCommMonoid S] [forall i, AddZeroClass (β i)] (h : R ->+ S) (f : Π₀ i, β 
i) (g : forall i, β i ->…
-/
theorem dfinsuppSumAddHom_apply [AddZeroClass R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R →+ S) (r : R) :
    (sumAddHom g f) r = sumAddHom (fun i => (eval r).comp (g i)) f :=
  map_dfinsuppSumAddHom (eval r) f g

@[simp, norm_cast]
/-
**AddMonoidHom.coe_dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：coe_dfinsuppSumAddHom [AddZeroClass R] [AddCommMonoid S] [forall i, AddZer
oClass (β i)] (f : Π₀ i, β i) (g : forall i, β i ->+ R ->+ S) : ⇑(sumAddHom g f)
 = sumAddHom (fun i => (coeFn R S).comp (g i)) f
参数：β i；f : Π₀ i, β i；g : forall i, β i ->+ R ->+ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_dfinsuppSumAddHom`：map_dfinsuppSumAddHom [AddCommMonoid
 R] [AddCommMonoid S] [forall i, AddZeroClass (β i)] (h : R ->+ S) (f : Π₀ i, β 
i) (g : forall i, β i ->…
-/
theorem coe_dfinsuppSumAddHom [AddZeroClass R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R →+ S) :
    ⇑(sumAddHom g f) = sumAddHom (fun i => (coeFn R S).comp (g i)) f :=
  map_dfinsuppSumAddHom (coeFn R S) f g

end AddMonoidHom

namespace RingHom

variable {R S : Type*}

open DFinsupp

@[simp]
/-
**RingHom.map_dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_dfinsuppSumAddHom [NonAssocSemiring R] [NonAssocSemiring S] [forall i,
 AddZeroClass (β i)] (h : R ->+* S) (f : Π₀ i, β i) (g : forall i, β i ->+ R) : 
h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f
参数：β i；h : R ->+* S；f : Π₀ i, β i；g : forall i, β i ->+ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `DFinsupp.comp_liftAddHom`：comp_liftAddHom {δ : Type*} [forall i, AddZero
Class (β i)] [AddCommMonoid γ] [AddCommMonoid δ] (g : γ ->+ δ) (f : forall i, β 
i ->+ γ) : g.c…
-/
theorem map_dfinsuppSumAddHom [NonAssocSemiring R] [NonAssocSemiring S] [∀ i, AddZeroClass (β i)]
    (h : R →+* S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f

end RingHom

namespace AddEquiv

variable {R S : Type*}

open DFinsupp

@[simp]
/-
**AddEquiv.map_dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：map_dfinsuppSumAddHom [AddCommMonoid R] [AddCommMonoid S] [forall i, AddZe
roClass (β i)] (h : R ≃+ S) (f : Π₀ i, β i) (g : forall i, β i ->+ R) : h (sumAd
dHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f
参数：β i；h : R ≃+ S；f : Π₀ i, β i；g : forall i, β i ->+ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `DFinsupp.comp_liftAddHom`：comp_liftAddHom {δ : Type*} [forall i, AddZero
Class (β i)] [AddCommMonoid γ] [AddCommMonoid δ] (g : γ ->+ δ) (f : forall i, β 
i ->+ γ) : g.c…
-/
theorem map_dfinsuppSumAddHom [AddCommMonoid R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (h : R ≃+ S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f

end AddEquiv

end

