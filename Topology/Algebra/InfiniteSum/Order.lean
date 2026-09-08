/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Infinite sum or product in an order

This file provides lemmas about the interaction of infinite sums and products and order operations.
-/

public section

open Finset Filter Function

variable {ι κ α : Type*} {L : SummationFilter ι}

section Preorder

variable [Preorder α] [CommMonoid α] [TopologicalSpace α] {a c : α} {f : ι → α}

@[to_additive]
/-
**hasProd_le_of_prod_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProd_le_of_prod_le [ClosedIicTopology α] [L.NeBot] (hf : HasProd f a L)
 (h : forall s, ∏ i in s, f i <= c) : a <= c
参数：hf : HasProd f a L；h : forall s, ∏ i in s, f i <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
-/
lemma hasProd_le_of_prod_le [ClosedIicTopology α] [L.NeBot]
    (hf : HasProd f a L) (h : ∀ s, ∏ i ∈ s, f i ≤ c) : a ≤ c :=
  le_of_tendsto' hf h

@[to_additive]
/-
**le_hasProd_of_le_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_hasProd_of_le_prod [ClosedIciTopology α] [L.NeBot] (hf : HasProd f a L)
 (h : forall s, c <= ∏ i in s, f i) : c <= a
参数：hf : HasProd f a L；h : forall s, c <= ∏ i in s, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
-/
theorem le_hasProd_of_le_prod [ClosedIciTopology α] [L.NeBot]
    (hf : HasProd f a L) (h : ∀ s, c ≤ ∏ i ∈ s, f i) : c ≤ a :=
  ge_of_tendsto' hf h

@[to_additive]
/-
**Multipliable.tprod_le_of_prod_range_le** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable
`。
形式化陈述：∀ {α : Type u_3} [inst : Preorder α] [inst_1 : CommMonoid α] [inst_2 : Top
ologicalSpace α] {c : α} [ClosedIicTopology α]   {f : ℕ → α}, Multipliable f → (
∀ (n : ℕ), ∏ i ∈ Finset.range n, f i ≤ c) → ∏' (n : ℕ), f n ≤ c
参数：∀ (n : ℕ), ∏ i ∈ Finset.range n, f i ≤ c；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HasProd.tendsto_prod_nat`：HasProd.tendsto_prod_nat {f : Nat -> M} (h : H
asProd f m) : Tendsto (fun n => ∏ i in range n, f i) atTop (𝓝 m)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_le_of_prod_range_le [ClosedIicTopology α] {f : ℕ → α}
    (hf : Multipliable f) (h : ∀ n, ∏ i ∈ range n, f i ≤ c) : ∏' n, f n ≤ c :=
  le_of_tendsto' hf.hasProd.tendsto_prod_nat h

end Preorder

section OrderedCommMonoid

variable [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  [TopologicalSpace α] [OrderClosedTopology α] {f g : ι → α}
  {a a₁ a₂ : α}

@[to_additive]
/-
**hasProd_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_le (h : forall i, f i <= g i) (hf : HasProd f a₁ L) (hg : HasProd 
g a₂ L) [L.NeBot] : a₁ <= a₂
参数：h : forall i, f i <= g i；hf : HasProd f a₁ L；hg : HasProd g a₂ L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem hasProd_le (h : ∀ i, f i ≤ g i) (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) [L.NeBot] :
    a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto' hf hg fun _ ↦ prod_le_prod' fun i _ ↦ h i

@[to_additive]
/-
**hasProd_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_mono (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) (h : f <= g) [L.N
eBot] : a₁ <= a₂
参数：hf : HasProd f a₁ L；hg : HasProd g a₂ L；h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_le`：hasProd_le (h : forall i, f i <= g i) (hf : HasProd f a₁ L) 
(hg : HasProd g a₂ L) [L.NeBot] : a₁ <= a₂
-/
theorem hasProd_mono (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) (h : f ≤ g) [L.NeBot] : a₁ ≤ a₂ :=
  hasProd_le h hf hg

@[to_additive]
/-
**hasProd_le_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_le_inj {g : κ -> α} (e : ι -> κ) (he : Injective e) (hs : forall c
, c ∉ Set.range e -> 1 <= g c) (h : forall i, f i <= g (e i)) (hf : HasProd f a₁
) (hg : HasProd g a₂) : a₁ <= a₂
参数：e : ι -> κ；he : Injective e；hs : forall c, c ∉ Set.range e -> 1 <= g c；h : fo
rall i, f i <= g (e i)；hf : HasProd f a₁；hg : HasProd g a₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_le`：hasProd_le (h : forall i, f i <= g i) (hf : HasProd f a₁ L) 
(hg : HasProd g a₂ L) [L.NeBot] : a₁ <= a₂
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasProd_extend_one`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : CommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α} {a : α}   {g : β → γ}
, Functi…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
theorem hasProd_le_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ c, c ∉ Set.range e → 1 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : HasProd f a₁)
    (hg : HasProd g a₂) : a₁ ≤ a₂ := by
  rw [← hasProd_extend_one he] at hf
  refine hasProd_le (fun c ↦ ?_) hf hg
  obtain ⟨i, rfl⟩ | h := em (c ∈ Set.range e)
  · rw [he.extend_apply]
    exact h _
  · rw [extend_apply' _ _ _ h]
    exact hs _ h

@[to_additive]
/-
**Multipliable.tprod_le_tprod_of_inj** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {κ : Type u_2} {α : Type u_3} [inst : CommMonoid α] [inst
_1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : TopologicalSpace α] [OrderClose
dTopology α] {f : ι → α} {g : κ → α} (e : ι → κ),   Function.Injective e →     (
∀ c ∉ Set.range e, 1 ≤ g c) → (∀ (i : ι), f i ≤ g (e i)) → Multipliable f → Mult
ipliable g → tprod f ≤ tprod g
参数：e : ι → κ；∀ c ∉ Set.range e, 1 ≤ g c；∀ (i : ι), f i ≤ g (e i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_le_inj`：hasProd_le_inj {g : κ -> α} (e : ι -> κ) (he : Injective
 e) (hs : forall c, c ∉ Set.range e -> 1 <= g c) (h : forall i, f i <= g (e i)) 
(hf …
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_le_tprod_of_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ c, c ∉ Set.range e → 1 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : Multipliable f)
    (hg : Multipliable g) : tprod f ≤ tprod g :=
  hasProd_le_inj _ he hs h hf.hasProd hg.hasProd

@[to_additive]
/-
**Multipliable.tprod_subtype_le** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {κ : Type u_4} {γ : Type u_5} [inst : CommGroup γ] [inst_1 : PartialOrde
r γ] [IsOrderedMonoid γ]   [inst_3 : UniformSpace γ] [IsUniformGroup γ] [OrderCl
osedTopology γ] [CompleteSpace γ] (f : κ → γ) (β : Set κ),   (∀ (a : κ), 1 ≤ f a
) → Multipliable f → ∏' (b : ↑β), f ↑b ≤ ∏' (a : κ), f a
参数：f : κ → γ；β : Set κ；∀ (a : κ), 1 ≤ f a；b : ↑β；a : κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.tprod_le_tprod_of_inj`：∀ {ι : Type u_1} {κ : Type u_2} {α :
 Type u_3} [inst : CommMonoid α] [inst_1 : Preorder α] [IsOrderedMonoid α]   [in
st_3 : TopologicalSpace …
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multipliable.subtype`：Multipliable.subtype (hf : Multipliable f) (p : β 
-> Prop) : Multipliable (f ∘ (↑) : Subtype p -> α)
-/
protected lemma Multipliable.tprod_subtype_le {κ γ : Type*} [CommGroup γ] [PartialOrder γ]
    [IsOrderedMonoid γ] [UniformSpace γ] [IsUniformGroup γ] [OrderClosedTopology γ]
    [CompleteSpace γ] (f : κ → γ) (β : Set κ) (h : ∀ a : κ, 1 ≤ f a) (hf : Multipliable f) :
    (∏' (b : β), f b) ≤ (∏' (a : κ), f a) := by
  apply Multipliable.tprod_le_tprod_of_inj _
    (Subtype.coe_injective)
    (by simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, h, implies_true])
    (by simp only [le_refl, implies_true])
    (by apply hf.subtype)
  apply hf

@[to_additive]
/-
**prod_le_hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_le_hasProd [L.NeBot] [L.LeAtTop] (s : Finset ι) (hs : forall i, i ∉ s
 -> 1 <= f i) (hf : HasProd f a L) : ∏ i in s, f i <= a
参数：s : Finset ι；hs : forall i, i ∉ s -> 1 <= f i；hf : HasProd f a L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `SummationFilter.LeAtTop.le_atTop`：∀ {β : Type u_2} {L : SummationFilter 
β} [self : L.LeAtTop], L.filter ≤ Filter.atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le'`：prod_le_prod_of_subset_of_one_
le' [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> 1 <= f i) :
 ∏ i in s, f i <= ∏ i in t, f …
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem prod_le_hasProd [L.NeBot] [L.LeAtTop] (s : Finset ι) (hs : ∀ i, i ∉ s → 1 ≤ f i)
    (hf : HasProd f a L) : ∏ i ∈ s, f i ≤ a := by
  refine ge_of_tendsto hf <| .filter_mono L.le_atTop <| eventually_atTop.2 ?_
  exact ⟨s, fun _t hst ↦ prod_le_prod_of_subset_of_one_le' hst fun i _ hbs ↦ hs i hbs⟩

@[to_additive]
/-
**isLUB_hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_hasProd (h : forall i, 1 <= f i) (hf : HasProd f a) : IsLUB (Set.ran
ge fun s => ∏ i in s, f i) a
参数：h : forall i, 1 <= f i；hf : HasProd f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_of_tendsto_atTop`：isLUB_of_tendsto_atTop [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] [Nonempty β] {
f : β -> α} …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.prod_mono_set_of_one_le'`：prod_mono_set_of_one_le' [MulLeftMono N
] (hf : forall x, 1 <= f x) : Monotone fun s => ∏ x in s, f x
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem isLUB_hasProd (h : ∀ i, 1 ≤ f i) (hf : HasProd f a) :
    IsLUB (Set.range fun s ↦ ∏ i ∈ s, f i) a := by
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]
/-
**le_hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_hasProd [L.NeBot] [L.LeAtTop] (hf : HasProd f a L) (i : ι) (hb : forall
 j, j != i -> 1 <= f j) : f i <= a
参数：hf : HasProd f a L；i : ι；hb : forall j, j != i -> 1 <= f j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `prod_le_hasProd`：prod_le_hasProd [L.NeBot] [L.LeAtTop] (s : Finset ι) (h
s : forall i, i ∉ s -> 1 <= f i) (hf : HasProd f a L) : ∏ i in s, f i <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem le_hasProd [L.NeBot] [L.LeAtTop] (hf : HasProd f a L) (i : ι) (hb : ∀ j, j ≠ i → 1 ≤ f j) :
    f i ≤ a :=
  calc
    f i = ∏ i ∈ {i}, f i := by rw [prod_singleton]
    _ ≤ a := prod_le_hasProd _ (by simpa) hf

@[to_additive]
/-
**lt_hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_hasProd [L.NeBot] [L.LeAtTop] [MulRightStrictMono α] (hf : HasProd f a 
L) (i : ι) (hi : forall (j : ι), j != i -> 1 <= f j) (j : ι) (hij : j != i) (hj 
: 1 < f j) : f i < a
参数：hf : HasProd f a L；i : ι；hi : forall (j : ι), j != i -> 1 <= f j；j : ι；hij : 
j != i；hj : 1 < f j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_one_lt_left'`：lt_mul_of_one_lt_left' [MulRightStrictMono α] (a
 : α) {b : α} (h : 1 < b) : a < b * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_pair`：prod_pair [DecidableEq ι] {a b : ι} (h : a != b) : (∏ 
x in ({a, b} : Finset ι), f x) = f a * f b
· 使用定理 `prod_le_hasProd`：prod_le_hasProd [L.NeBot] [L.LeAtTop] (s : Finset ι) (h
s : forall i, i ∉ s -> 1 <= f i) (hf : HasProd f a L) : ∏ i in s, f i <= a
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem lt_hasProd [L.NeBot] [L.LeAtTop] [MulRightStrictMono α] (hf : HasProd f a L) (i : ι)
    (hi : ∀ (j : ι), j ≠ i → 1 ≤ f j) (j : ι) (hij : j ≠ i) (hj : 1 < f j) :
    f i < a := by
  classical
  calc
    f i < f j * f i := lt_mul_of_one_lt_left' (f i) hj
    _ = ∏ k ∈ {j, i}, f k := by rw [Finset.prod_pair hij]
    _ ≤ a := prod_le_hasProd _ (fun k hk ↦ hi k (hk ∘ mem_insert_of_mem ∘ mem_singleton.mpr)) hf

@[to_additive]
/-
**Multipliable.prod_le_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst : CommMonoid
 α] [inst_1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : TopologicalSpace α] [O
rderClosedTopology α] [L.NeBot] [L.LeAtTop] {f : ι → α} (s : Finset ι),   (∀ i ∉
 s, 1 ≤ f i) → Multipliable f L → ∏ i ∈ s, f i ≤ ∏'[L] (i : ι), f i
参数：s : Finset ι；∀ i ∉ s, 1 ≤ f i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_le_hasProd`：prod_le_hasProd [L.NeBot] [L.LeAtTop] (s : Finset ι) (h
s : forall i, i ∉ s -> 1 <= f i) (hf : HasProd f a L) : ∏ i in s, f i <= a
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.prod_le_tprod [L.NeBot] [L.LeAtTop] {f : ι → α} (s : Finset ι)
    (hs : ∀ i, i ∉ s → 1 ≤ f i) (hf : Multipliable f L) :
    ∏ i ∈ s, f i ≤ ∏'[L] i, f i :=
  prod_le_hasProd s hs hf.hasProd

@[to_additive]
/-
**Multipliable.le_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst : CommMonoid
 α] [inst_1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : TopologicalSpace α] [O
rderClosedTopology α] {f : ι → α} [L.NeBot] [L.LeAtTop],   Multipliable f L → ∀ 
(i : ι), (∀ (j : ι), j ≠ i → 1 ≤ f j) → f i ≤ ∏'[L] (i : ι), f i
参数：i : ι；∀ (j : ι), j ≠ i → 1 ≤ f j；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_hasProd`：le_hasProd [L.NeBot] [L.LeAtTop] (hf : HasProd f a L) (i : ι
) (hb : forall j, j != i -> 1 <= f j) : f i <= a
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.le_tprod [L.NeBot] [L.LeAtTop] (hf : Multipliable f L) (i : ι)
    (hb : ∀ j ≠ i, 1 ≤ f j) : f i ≤ ∏'[L] i, f i :=
  le_hasProd hf.hasProd i hb

@[to_additive (attr := gcongr)]
/-
**Multipliable.tprod_le_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst : CommMonoid
 α] [inst_1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : TopologicalSpace α] [O
rderClosedTopology α] {f g : ι → α} [L.NeBot],   (∀ (i : ι), f i ≤ g i) → Multip
liable f L → Multipliable g L → ∏'[L] (i : ι), f i ≤ ∏'[L] (i : ι), g i
参数：∀ (i : ι), f i ≤ g i；i : ι；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_le`：hasProd_le (h : forall i, f i <= g i) (hf : HasProd f a₁ L) 
(hg : HasProd g a₂ L) [L.NeBot] : a₁ <= a₂
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_le_tprod [L.NeBot] (h : ∀ i, f i ≤ g i) (hf : Multipliable f L)
    (hg : Multipliable g L) : ∏'[L] i, f i ≤ ∏'[L] i, g i :=
  hasProd_le h hf.hasProd hg.hasProd

@[to_additive (attr := mono)]
/-
**Multipliable.tprod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst : CommMonoid
 α] [inst_1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : TopologicalSpace α] [O
rderClosedTopology α] {f g : ι → α} [L.NeBot],   Multipliable f L → Multipliable
 g L → f ≤ g → ∏'[L] (n : ι), f n ≤ ∏'[L] (n : ι), g n
参数：n : ι；n : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.tprod_le_tprod`：∀ {ι : Type u_1} {α : Type u_3} {L : Summat
ionFilter ι} [inst : CommMonoid α] [inst_1 : Preorder α] [IsOrderedMonoid α]   [
inst_3 : Topologi…
-/
protected theorem Multipliable.tprod_mono [L.NeBot] (hf : Multipliable f L) (hg : Multipliable g L)
    (h : f ≤ g) : ∏'[L] n, f n ≤ ∏'[L] n, g n :=
  hf.tprod_le_tprod h hg

omit [IsOrderedMonoid α] in
@[to_additive]
/-
**Multipliable.tprod_le_of_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst : CommMonoid
 α] [inst_1 : Preorder α]   [inst_2 : TopologicalSpace α] [OrderClosedTopology α
] {f : ι → α} {a₂ : α} [L.NeBot],   Multipliable f L → (∀ (s : Finset ι), ∏ i ∈ 
s, f i ≤ a₂) → ∏'[L] (i : ι), f i ≤ a₂
参数：∀ (s : Finset ι), ∏ i ∈ s, f i ≤ a₂；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasProd_le_of_prod_le`：hasProd_le_of_prod_le [ClosedIicTopology α] [L.Ne
Bot] (hf : HasProd f a L) (h : forall s, ∏ i in s, f i <= c) : a <= c
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_le_of_prod_le [L.NeBot] (hf : Multipliable f L)
    (h : ∀ s, ∏ i ∈ s, f i ≤ a₂) : ∏'[L] i, f i ≤ a₂ :=
  hasProd_le_of_prod_le hf.hasProd h

omit [IsOrderedMonoid α] in
@[to_additive]
/-
**tprod_le_of_prod_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_le_of_prod_le' (ha₂ : 1 <= a₂) (h : forall s, ∏ i in s, f i <= a₂) :
 ∏'[L] i, f i <= a₂
参数：ha₂ : 1 <= a₂；h : forall s, ∏ i in s, f i <= a₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.tprod_le_of_prod_le`：∀ {ι : Type u_1} {α : Type u_3} {L : S
ummationFilter ι} [inst : CommMonoid α] [inst_1 : Preorder α]   [inst_2 : Topolo
gicalSpace α] [OrderCl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `tprod_bot`：tprod_bot (hL : ¬L.NeBot) (f : β -> α) : ∏'[L] b, f b = ∏ᶠ b,
 f b
· 使用定理 `finprod_eq_prod`：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport 
f) : ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
-/
theorem tprod_le_of_prod_le' (ha₂ : 1 ≤ a₂) (h : ∀ s, ∏ i ∈ s, f i ≤ a₂) :
    ∏'[L] i, f i ≤ a₂ := by
  by_cases hL : L.NeBot
  · by_cases hf : Multipliable f L
    · exact hf.tprod_le_of_prod_le h
    · rwa [tprod_eq_one_of_not_multipliable hf]
  · by_cases hf : f.mulSupport.Finite
    · simpa [tprod_bot hL, finprod_eq_prod _ hf] using h _
    · rwa [tprod_bot hL, finprod_of_infinite_mulSupport hf]

@[to_additive]
/-
**HasProd.one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.one_le [L.NeBot] (h : forall i, 1 <= g i) (ha : HasProd g a L) : 1
 <= a
参数：h : forall i, 1 <= g i；ha : HasProd g a L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_le`：hasProd_le (h : forall i, f i <= g i) (hf : HasProd f a₁ L) 
(hg : HasProd g a₂ L) [L.NeBot] : a₁ <= a₂
· 使用定理 `hasProd_one`：hasProd_one : HasProd (fun _ => 1 : β -> α) 1 L
-/
theorem HasProd.one_le [L.NeBot] (h : ∀ i, 1 ≤ g i) (ha : HasProd g a L) : 1 ≤ a :=
  hasProd_le h hasProd_one ha

@[to_additive]
/-
**HasProd.le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.le_one [L.NeBot] (h : forall i, g i <= 1) (ha : HasProd g a L) : a
 <= 1
参数：h : forall i, g i <= 1；ha : HasProd g a L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_le`：hasProd_le (h : forall i, f i <= g i) (hf : HasProd f a₁ L) 
(hg : HasProd g a₂ L) [L.NeBot] : a₁ <= a₂
· 使用定理 `hasProd_one`：hasProd_one : HasProd (fun _ => 1 : β -> α) 1 L
-/
theorem HasProd.le_one [L.NeBot] (h : ∀ i, g i ≤ 1) (ha : HasProd g a L) : a ≤ 1 :=
  hasProd_le h ha hasProd_one

@[to_additive tsum_nonneg]
/-
**one_le_tprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_tprod (h : forall i, 1 <= g i) : 1 <= ∏'[L] i, g i
参数：h : forall i, 1 <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.one_le`：HasProd.one_le [L.NeBot] (h : forall i, 1 <= g i) (ha : 
HasProd g a L) : 1 <= a
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `tprod_bot`：tprod_bot (hL : ¬L.NeBot) (f : β -> α) : ∏'[L] b, f b = ∏ᶠ b,
 f b
· 使用定理 `one_le_finprod'`：one_le_finprod' {M : Type*} [CommMonoid M] [Preorder M]
 [IsOrderedMonoid M] {f : α -> M} (hf : forall i, 1 <= f i) : 1 <= ∏ᶠ i, f i
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem one_le_tprod (h : ∀ i, 1 ≤ g i) : 1 ≤ ∏'[L] i, g i := by
  by_cases hg : Multipliable g L
  · by_cases hL : L.NeBot
    · exact hg.hasProd.one_le h
    · simpa [tprod_bot hL] using one_le_finprod' h
  · rw [tprod_eq_one_of_not_multipliable hg]

@[to_additive]
/-
**tprod_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_le_one (h : forall i, f i <= 1) : ∏'[L] i, f i <= 1
参数：h : forall i, f i <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.le_one`：HasProd.le_one [L.NeBot] (h : forall i, g i <= 1) (ha : 
HasProd g a L) : a <= 1
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `tprod_bot`：tprod_bot (hL : ¬L.NeBot) (f : β -> α) : ∏'[L] b, f b = ∏ᶠ b,
 f b
· 使用定理 `finprod_induction`：finprod_induction {f : α -> M} (p : M -> Prop) (hp₀ :
 p 1) (hp₁ : forall x y, p x -> p y -> p (x * y)) (hp₂ : forall i, p (f i)) : p 
(∏ᶠ i, …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `mul_le_one'`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Preorder 
α] [MulLeftMono α] {a b : α}, a ≤ 1 → b ≤ 1 → a * b ≤ 1
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem tprod_le_one (h : ∀ i, f i ≤ 1) : ∏'[L] i, f i ≤ 1 := by
  by_cases hf : Multipliable f L
  · by_cases hL : L.NeBot
    · exact hf.hasProd.le_one h
    · simp only [tprod_bot hL]
      exact finprod_induction (· ≤ 1) le_rfl (fun _ _ ↦ mul_le_one') h
  · rw [tprod_eq_one_of_not_multipliable hf]

@[to_additive]
/-
**hasProd_one_iff_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_one_iff_of_one_le {ι α : Type*} {L : SummationFilter ι} [CommMonoi
d α] [PartialOrder α] [IsOrderedMonoid α] [TopologicalSpace α] [OrderClosedTopol
ogy α] {f : ι -> α} [L.LeAtTop] [L.NeBot] (hf : forall i, 1 <= f i) : HasProd f 
1 L ↔ f = 1
参数：hf : forall i, 1 <= f i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `le_hasProd`：le_hasProd [L.NeBot] [L.LeAtTop] (hf : HasProd f a L) (i : ι
) (hb : forall j, j != i -> 1 <= f j) : f i <= a
· 使用定理 `hasProd_one`：hasProd_one : HasProd (fun _ => 1 : β -> α) 1 L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem hasProd_one_iff_of_one_le {ι α : Type*} {L : SummationFilter ι} [CommMonoid α]
  [PartialOrder α] [IsOrderedMonoid α] [TopologicalSpace α] [OrderClosedTopology α]
  {f : ι → α} [L.LeAtTop] [L.NeBot] (hf : ∀ i, 1 ≤ f i) :
    HasProd f 1 L ↔ f = 1 := by
  refine ⟨fun hf' ↦ ?_, ?_⟩
  · ext i
    exact (hf i).antisymm' (le_hasProd hf' _ fun j _ ↦ hf j)
  · rintro rfl
    exact hasProd_one

end OrderedCommMonoid

section OrderedCommGroup

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  [TopologicalSpace α] [IsTopologicalGroup α]
  [OrderClosedTopology α] {f g : ι → α} {a₁ a₂ : α} {i : ι}

@[to_additive]
/-
**hasProd_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_lt [L.NeBot] [L.LeAtTop] (h : f <= g) (hi : f i < g i) (hf : HasPr
od f a₁ L) (hg : HasProd g a₂ L) : a₁ < a₂
参数：h : f <= g；hi : f i < g i；hf : HasProd f a₁ L；hg : HasProd g a₂ L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `update_le_update_iff`：update_le_update_iff : Function.update x i a <= Fu
nction.update y i b ↔ a <= b ∧ forall (j) (_ : j != i), x j <= y j
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `hasProd_le`：hasProd_le (h : forall i, f i <= g i) (hf : HasProd f a₁ L) 
(hg : HasProd g a₂ L) [L.NeBot] : a₁ <= a₂
· 使用定理 `HasProd.update`：HasProd.update [L.LeAtTop] (hf : HasProd f a₁ L) (b : β)
 [DecidableEq β] (a : α) : HasProd (update f b a) (a / f b * a₁) L
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
-/
theorem hasProd_lt [L.NeBot] [L.LeAtTop] (h : f ≤ g) (hi : f i < g i) (hf : HasProd f a₁ L)
    (hg : HasProd g a₂ L) : a₁ < a₂ := by
  classical
  have : update f i 1 ≤ update g i 1 := update_le_update_iff.mpr ⟨rfl.le, fun i _ ↦ h i⟩
  have : 1 / f i * a₁ ≤ 1 / g i * a₂ := hasProd_le this (hf.update i 1) (hg.update i 1)
  simpa only [one_div, mul_inv_cancel_left] using mul_lt_mul_of_lt_of_le hi this

@[to_additive (attr := mono)]
/-
**hasProd_strict_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_strict_mono (hf : HasProd f a₁) (hg : HasProd g a₂) (h : f < g) : 
a₁ < a₂
参数：hf : HasProd f a₁；hg : HasProd g a₂；h : f < g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `hasProd_lt`：hasProd_lt [L.NeBot] [L.LeAtTop] (h : f <= g) (hi : f i < g 
i) (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) : a₁ < a₂
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
theorem hasProd_strict_mono (hf : HasProd f a₁) (hg : HasProd g a₂) (h : f < g) : a₁ < a₂ :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasProd_lt hle hi hf hg

@[to_additive]
/-
**Multipliable.tprod_lt_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst : CommGroup 
α] [inst_1 : PartialOrder α]   [IsOrderedMonoid α] [inst_3 : TopologicalSpace α]
 [IsTopologicalGroup α] [OrderClosedTopology α] {f g : ι → α} {i : ι}   [L.NeBot
] [L.LeAtTop],   f ≤ g → f i < g i → Multipliable f L → Multipliable g L → ∏'[L]
 (n : ι), f n < ∏'[L] (n : ι), g n
参数：n : ι；n : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_lt`：hasProd_lt [L.NeBot] [L.LeAtTop] (h : f <= g) (hi : f i < g 
i) (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) : a₁ < a₂
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_lt_tprod [L.NeBot] [L.LeAtTop]
    (h : f ≤ g) (hi : f i < g i) (hf : Multipliable f L) (hg : Multipliable g L) :
    ∏'[L] n, f n < ∏'[L] n, g n :=
  hasProd_lt h hi hf.hasProd hg.hasProd

@[to_additive (attr := mono)]
/-
**Multipliable.tprod_strict_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst : CommGroup 
α] [inst_1 : PartialOrder α]   [IsOrderedMonoid α] [inst_3 : TopologicalSpace α]
 [IsTopologicalGroup α] [OrderClosedTopology α] {f g : ι → α}   [L.NeBot] [L.LeA
tTop], Multipliable f L → Multipliable g L → f < g → ∏'[L] (n : ι), f n < ∏'[L] 
(n : ι), g n
参数：n : ι；n : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `Multipliable.tprod_lt_tprod`：∀ {ι : Type u_1} {α : Type u_3} {L : Summat
ionFilter ι} [inst : CommGroup α] [inst_1 : PartialOrder α]   [IsOrderedMonoid α
] [inst_3 : Topol…
-/
protected theorem Multipliable.tprod_strict_mono [L.NeBot] [L.LeAtTop]
    (hf : Multipliable f L) (hg : Multipliable g L)
    (h : f < g) : ∏'[L] n, f n < ∏'[L] n, g n :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hf.tprod_lt_tprod hle hi hg

@[to_additive Summable.tsum_pos]
/-
**Multipliable.one_lt_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst : CommGroup 
α] [inst_1 : PartialOrder α]   [IsOrderedMonoid α] [inst_3 : TopologicalSpace α]
 [IsTopologicalGroup α] [OrderClosedTopology α] {g : ι → α}   [L.LeAtTop] [L.NeB
ot], Multipliable g L → (∀ (i : ι), 1 ≤ g i) → ∀ (i : ι), 1 < g i → 1 < ∏'[L] (i
 : ι), g i
参数：∀ (i : ι), 1 ≤ g i；i : ι；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
· 使用定理 `Multipliable.tprod_lt_tprod`：∀ {ι : Type u_1} {α : Type u_3} {L : Summat
ionFilter ι} [inst : CommGroup α] [inst_1 : PartialOrder α]   [IsOrderedMonoid α
] [inst_3 : Topol…
· 使用定理 `multipliable_one`：multipliable_one : Multipliable (fun _ => 1 : β -> α) 
L
-/
protected theorem Multipliable.one_lt_tprod [L.LeAtTop] [L.NeBot] (hsum : Multipliable g L)
    (hg : ∀ i, 1 ≤ g i) (i : ι) (hi : 1 < g i) : 1 < ∏'[L] i, g i := by
  rw [← tprod_one (L := L)]
  exact multipliable_one.tprod_lt_tprod hg hi hsum

end OrderedCommGroup

section WithZero

variable [CommMonoidWithZero α] [TopologicalSpace α] [Preorder α] [ZeroLEOneClass α]
  [PosMulMono α] [ClosedIciTopology α]

/-
**HasProd.nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.nonneg [L.NeBot] {f : ι -> α} (hf : forall i, 0 <= f i) {a : α} (h
 : HasProd f a L) : 0 <= a
参数：hf : forall i, 0 <= f i；h : HasProd f a L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
-/
theorem HasProd.nonneg [L.NeBot] {f : ι → α} (hf : ∀ i, 0 ≤ f i) {a : α} (h : HasProd f a L) :
    0 ≤ a :=
  ge_of_tendsto' h fun s ↦ s.prod_nonneg fun i _ ↦ hf i
/-
**tprod_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_nonneg {f : ι -> α} (hf : forall i, 0 <= f i) : 0 <= ∏'[L] x, f x
参数：hf : forall i, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.nonneg`：HasProd.nonneg [L.NeBot] {f : ι -> α} (hf : forall i, 0 
<= f i) {a : α} (h : HasProd f a L) : 0 <= a
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `tprod_bot`：tprod_bot (hL : ¬L.NeBot) (f : β -> α) : ∏'[L] b, f b = ∏ᶠ b,
 f b
· 使用定理 `finprod_nonneg`：finprod_nonneg {R : Type*} [CommMonoidWithZero R] [Preor
der R] [ZeroLEOneClass R] [PosMulMono R] {f : α -> R} (hf : forall x, 0 <= f x) 
: 0 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
-/
theorem tprod_nonneg {f : ι → α} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ ∏'[L] x, f x := by
  by_cases h : Multipliable f L
  · by_cases hbot : L.NeBot
    · exact h.hasProd.nonneg hf
    · simpa [tprod_bot hbot] using finprod_nonneg hf
  · simp [tprod_eq_one_of_not_multipliable h]

end WithZero

section CanonicallyOrderedMul

variable [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
  [CanonicallyOrderedMul α] [TopologicalSpace α]
  [OrderClosedTopology α] {f : ι → α} {a : α}

@[to_additive]
/-
**le_hasProd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_hasProd' (hf : HasProd f a) (i : ι) : f i <= a
参数：hf : HasProd f a；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_hasProd`：le_hasProd [L.NeBot] [L.LeAtTop] (hf : HasProd f a L) (i : ι
) (hb : forall j, j != i -> 1 <= f j) : f i <= a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
-/
theorem le_hasProd' (hf : HasProd f a) (i : ι) : f i ≤ a :=
  le_hasProd hf i fun _ _ ↦ one_le

@[to_additive]
/-
**Multipliable.le_tprod'** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : CommMonoid α] [inst_1 : PartialOrd
er α] [IsOrderedMonoid α]   [CanonicallyOrderedMul α] [inst_4 : TopologicalSpace
 α] [OrderClosedTopology α] {f : ι → α},   Multipliable f → ∀ (i : ι), f i ≤ ∏' 
(i : ι), f i
参数：i : ι；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.le_tprod`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : CommMonoid α] [inst_1 : Preorder α] [IsOrderedMonoid α]   [inst_3
 : Topologi…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
-/
protected theorem Multipliable.le_tprod' (hf : Multipliable f) (i : ι) : f i ≤ ∏' i, f i :=
  hf.le_tprod i fun _ _ ↦ one_le

@[to_additive]
/-
**hasProd_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_one_iff : HasProd f 1 ↔ forall x, f x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `hasProd_one_iff_of_one_le`：hasProd_one_iff_of_one_le {ι α : Type*} {L : 
SummationFilter ι} [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α] [Topologi
calSpace α] [Or…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem hasProd_one_iff : HasProd f 1 ↔ ∀ x, f x = 1 :=
  (hasProd_one_iff_of_one_le fun _ ↦ one_le).trans funext_iff

@[to_additive]
/-
**Multipliable.tprod_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : CommMonoid α] [inst_1 : PartialOrd
er α] [IsOrderedMonoid α]   [CanonicallyOrderedMul α] [inst_4 : TopologicalSpace
 α] [OrderClosedTopology α] {f : ι → α},   Multipliable f → (∏' (i : ι), f i = 1
 ↔ ∀ (x : ι), f x = 1)
参数：∏' (i : ι), f i = 1 ↔ ∀ (x : ι), f x = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasProd_one_iff`：hasProd_one_iff : HasProd f 1 ↔ forall x, f x = 1
· 使用定理 `Multipliable.hasProd_iff`：Multipliable.hasProd_iff (h : Multipliable f L
) : HasProd f a L ↔ ∏'[L] b, f b = a
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem Multipliable.tprod_eq_one_iff (hf : Multipliable f) :
    ∏' i, f i = 1 ↔ ∀ x, f x = 1 := by
  rw [← hasProd_one_iff, hf.hasProd_iff]

@[to_additive]
/-
**Multipliable.tprod_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : CommMonoid α] [inst_1 : PartialOrd
er α] [IsOrderedMonoid α]   [CanonicallyOrderedMul α] [inst_4 : TopologicalSpace
 α] [OrderClosedTopology α] {f : ι → α},   Multipliable f → (∏' (i : ι), f i ≠ 1
 ↔ ∃ x, f x ≠ 1)
参数：∏' (i : ι), f i ≠ 1 ↔ ∃ x, f x ≠ 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Multipliable.tprod_eq_one_iff`：∀ {ι : Type u_1} {α : Type u_3} [inst : C
ommMonoid α] [inst_1 : PartialOrder α] [IsOrderedMonoid α]   [CanonicallyOrdered
Mul α] [inst_4 : To…
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem Multipliable.tprod_ne_one_iff (hf : Multipliable f) :
    ∏' i, f i ≠ 1 ↔ ∃ x, f x ≠ 1 := by
  rw [Ne, hf.tprod_eq_one_iff, not_forall]

omit [IsOrderedMonoid α] in
@[to_additive]
/-
**isLUB_hasProd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_hasProd' (hf : HasProd f a) : IsLUB (Set.range fun s => ∏ i in s, f 
i) a
参数：hf : HasProd f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_of_tendsto_atTop`：isLUB_of_tendsto_atTop [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] [Nonempty β] {
f : β -> α} …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.prod_mono_set'`：prod_mono_set' (f : ι -> M) : Monotone fun s => ∏
 x in s, f x
-/
theorem isLUB_hasProd' (hf : HasProd f a) : IsLUB (Set.range fun s ↦ ∏ i ∈ s, f i) a := by
  exact isLUB_of_tendsto_atTop (Finset.prod_mono_set' f) hf

end CanonicallyOrderedMul

section LinearOrder

/-!
For infinite sums taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/

@[to_additive]
/-
**hasProd_of_isLUB_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_of_isLUB_of_one_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid
 α] [TopologicalSpace α] [OrderTopology α] {f : ι -> α} (i : α) (h : forall i, 1
 <= f i) (hf : IsLUB (Set.range fun s => ∏ i in s, f i) i) : HasProd f i
参数：i : α；h : forall i, 1 <= f i；hf : IsLUB (Set.range fun s => ∏ i in s, f i) i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_isLUB`：tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsL
UB (Set.range f) a) : Tendsto f atTop (𝓝 a)
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `Finset.prod_mono_set_of_one_le'`：prod_mono_set_of_one_le' [MulLeftMono N
] (hf : forall x, 1 <= f x) : Monotone fun s => ∏ x in s, f x
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α

--- 原说明 ---
For infinite sums taking values in a linearly ordered monoid, the existence of a
 least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also
 a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is t
hen easy to check
the existence of a least upper bound.
-/
theorem hasProd_of_isLUB_of_one_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    [TopologicalSpace α]
    [OrderTopology α] {f : ι → α} (i : α) (h : ∀ i, 1 ≤ f i)
    (hf : IsLUB (Set.range fun s ↦ ∏ i ∈ s, f i) i) : HasProd f i :=
  tendsto_atTop_isLUB (Finset.prod_mono_set_of_one_le' h) hf

@[to_additive]
/-
**hasProd_of_isGLB_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_of_isGLB_of_le_one [CommMonoid α] [LinearOrder α] [IsOrderedMonoid
 α] [TopologicalSpace α] [OrderTopology α] {f : ι -> α} (i : α) (h₀ : forall i, 
f i <= 1) (hf : IsGLB (Set.range fun s => ∏ i in s, f i) i) : HasProd f i
参数：i : α；h₀ : forall i, f i <= 1；hf : IsGLB (Set.range fun s => ∏ i in s, f i) i
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_isGLB`：tendsto_atTop_isGLB (h_anti : Antitone f) (ha : IsG
LB (Set.range f) a) : Tendsto f atTop (𝓝 a)
· 使用定理 `LinearOrder.infConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], InfConvergenceClass α
· 使用定理 `Finset.prod_anti_set_of_le_one'`：prod_anti_set_of_le_one' {ι : Type u_1}
 {N : Type u_5} [CommMonoid N] [Preorder N] {f : ι -> N} [MulLeftMono N] (hf : f
orall (x : ι), f x <=…
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem hasProd_of_isGLB_of_le_one [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    [TopologicalSpace α]
    [OrderTopology α] {f : ι → α} (i : α) (h₀ : ∀ i, f i ≤ 1)
    (hf : IsGLB (Set.range fun s ↦ ∏ i ∈ s, f i) i) : HasProd f i :=
  tendsto_atTop_isGLB (Finset.prod_anti_set_of_le_one' h₀) hf

@[to_additive]
/-
**hasProd_of_isLUB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_of_isLUB [CommMonoid α] [LinearOrder α] [CanonicallyOrderedMul α] 
[TopologicalSpace α] [OrderTopology α] {f : ι -> α} (b : α) (hf : IsLUB (Set.ran
ge fun s => ∏ i in s, f i) b) : HasProd f b
参数：b : α；hf : IsLUB (Set.range fun s => ∏ i in s, f i) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_isLUB`：tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsL
UB (Set.range f) a) : Tendsto f atTop (𝓝 a)
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `Finset.prod_mono_set'`：prod_mono_set' (f : ι -> M) : Monotone fun s => ∏
 x in s, f x
-/
theorem hasProd_of_isLUB [CommMonoid α] [LinearOrder α]
    [CanonicallyOrderedMul α] [TopologicalSpace α]
    [OrderTopology α] {f : ι → α} (b : α) (hf : IsLUB (Set.range fun s ↦ ∏ i ∈ s, f i) b) :
    HasProd f b :=
  tendsto_atTop_isLUB (Finset.prod_mono_set' f) hf

@[to_additive]
/-
**multipliable_mabs_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_mabs_iff [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] [U
niformSpace α] [IsUniformGroup α] [CompleteSpace α] {f : ι -> α} : (Multipliable
 fun x => mabs (f x)) ↔ Multipliable f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mabs_of_lt_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], a < 1 → |a|ₘ = a⁻¹
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `multipliable_subtype_and_compl`：multipliable_subtype_and_compl {s : Set 
β} : ((Multipliable fun x : s => f x) ∧ Multipliable fun x : ↑sᶜ => f x) ↔ Multi
pliable f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
-/
theorem multipliable_mabs_iff [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]
    [UniformSpace α] [IsUniformGroup α]
    [CompleteSpace α] {f : ι → α} : (Multipliable fun x ↦ mabs (f x)) ↔ Multipliable f :=
  let s := { x | 1 ≤ f x }
  have h1 : ∀ x : s, mabs (f x) = f x := fun x ↦ mabs_of_one_le x.2
  have h2 : ∀ x : ↑sᶜ, mabs (f x) = (f x)⁻¹ := fun x ↦ mabs_of_lt_one (not_le.1 x.2)
  calc (Multipliable fun x ↦ mabs (f x)) ↔
      (Multipliable fun x : s ↦ mabs (f x)) ∧ Multipliable fun x : ↑sᶜ ↦ mabs (f x) :=
        multipliable_subtype_and_compl.symm
  _ ↔ (Multipliable fun x : s ↦ f x) ∧ Multipliable fun x : ↑sᶜ ↦ (f x)⁻¹ := by simp only [h1, h2]
  _ ↔ Multipliable f := by simp only [multipliable_inv_iff, multipliable_subtype_and_compl]

alias ⟨Summable.of_abs, Summable.abs⟩ := summable_abs_iff
/-
**Finite.of_summable_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.of_summable_const [AddCommGroup α] [LinearOrder α] [IsOrderedAddMon
oid α] [TopologicalSpace α] [Archimedean α] [OrderClosedTopology α] {b : α} (hb 
: 0 < b) (hf : Summable fun _ : ι => b) : Finite ι
参数：hb : 0 < b；hf : Summable fun _ : ι => b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `sum_le_hasSum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [
inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 :
 To…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用定理 `nsmul_le_nsmul_iff_left`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 :
 LinearOrder M] [AddLeftStrictMono M] {a : M} {m n : ℕ},   0 < a → (m • a ≤ n • 
a ↔ m ≤ n)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem Finite.of_summable_const [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [TopologicalSpace α] [Archimedean α]
    [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun _ : ι ↦ b) :
    Finite ι := by
  have H : ∀ s : Finset ι, #s • b ≤ ∑' _ : ι, b := fun s ↦ by
    simpa using sum_le_hasSum s (fun a _ ↦ hb.le) hf.hasSum
  obtain ⟨n, hn⟩ := Archimedean.arch (∑' _ : ι, b) hb
  have : ∀ s : Finset ι, #s ≤ n := fun s ↦ by
    simpa [nsmul_le_nsmul_iff_left hb] using (H s).trans hn
  have : Fintype ι := fintypeOfFinsetCardLe n this
  infer_instance
/-
**Set.Finite.of_summable_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.of_summable_const [AddCommGroup α] [LinearOrder α] [IsOrderedAd
dMonoid α] [TopologicalSpace α] [Archimedean α] [OrderClosedTopology α] {b : α} 
(hb : 0 < b) (hf : Summable fun _ : ι => b) : (Set.univ : Set ι).Finite
参数：hb : 0 < b；hf : Summable fun _ : ι => b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.finite_univ_iff`：finite_univ_iff : (@univ α).Finite ↔ Finite α
· 使用定理 `Finite.of_summable_const`：Finite.of_summable_const [AddCommGroup α] [Lin
earOrder α] [IsOrderedAddMonoid α] [TopologicalSpace α] [Archimedean α] [OrderCl
osedTopology α…
-/
theorem Set.Finite.of_summable_const [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [TopologicalSpace α]
    [Archimedean α] [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun _ : ι ↦ b) :
    (Set.univ : Set ι).Finite :=
  finite_univ_iff.2 <| .of_summable_const hb hf

end LinearOrder

section LinearOrderedCommRing

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
  [TopologicalSpace α] [OrderTopology α] {f : ι → α} {x : α}

nonrec theorem HasProd.abs (hfx : HasProd f x) : HasProd (|f ·|) |x| := by
  simpa only [HasProd, ← abs_prod] using hfx.abs

/-
**Multipliable.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.abs (hf : Multipliable f) : Multipliable (|f ·|)
参数：hf : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.abs`：∀ {ι : Type u_1} {α : Type u_3} [inst : CommRing α] [inst_1
 : LinearOrder α] [IsStrictOrderedRing α]   [inst_3 : TopologicalSpace α] [Order
T…
-/
theorem Multipliable.abs (hf : Multipliable f) : Multipliable (|f ·|) :=
  let ⟨x, hx⟩ := hf; ⟨|x|, hx.abs⟩
/-
**Multipliable.abs_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : CommRing α] [inst_1 : LinearOrder 
α] [IsStrictOrderedRing α]   [inst_3 : TopologicalSpace α] [OrderTopology α] {f 
: ι → α}, Multipliable f → |∏' (i : ι), f i| = ∏' (i : ι), |f i|
参数：i : ι；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.abs`：∀ {ι : Type u_1} {α : Type u_3} [inst : CommRing α] [inst_1
 : LinearOrder α] [IsStrictOrderedRing α]   [inst_3 : TopologicalSpace α] [Order
T…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.abs_tprod (hf : Multipliable f) : |∏' i, f i| = ∏' i, |f i| :=
  hf.hasProd.abs.tprod_eq.symm

end LinearOrderedCommRing

/-
**Summable.tendsto_atTop_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.tendsto_atTop_of_pos [Field α] [LinearOrder α] [IsStrictOrderedRi
ng α] [TopologicalSpace α] [OrderTopology α] {f : Nat -> α} (hf : Summable f⁻¹) 
(hf' : forall n, 0 < f n) : Tendsto f atTop atTop
参数：hf : Summable f⁻¹；hf' : forall n, 0 < f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inv_tendsto_nhdsGT_zero`：Filter.Tendsto.inv_tendsto_nhdsG
T_zero (h : Tendsto f l (𝓝[>] 0)) : Tendsto f⁻¹ l atTop
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `Summable.tendsto_atTop_zero`：∀ {G : Type u_2} [inst : AddCommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G},   Summable f 
→ Filter.Tendsto …
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem Summable.tendsto_atTop_of_pos [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [TopologicalSpace α] [OrderTopology α]
    {f : ℕ → α} (hf : Summable f⁻¹) (hf' : ∀ n, 0 < f n) : Tendsto f atTop atTop :=
  inv_inv f ▸ Filter.Tendsto.inv_tendsto_nhdsGT_zero <|
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf.tendsto_atTop_zero <|
      Eventually.of_forall fun _ ↦ inv_pos.2 (hf' _)

namespace Mathlib.Meta.Positivity

open Qq Lean Meta Finset

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for infinite sums.

This extension only proves non-negativity, strict positivity is more delicate for infinite sums and
requires more assumptions. -/
@[positivity tsum _]
meta def evalTsum : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match e with
  | ~q(@tsum _ $ι $instCommMonoid $instTopSpace $f $L) =>
    lambdaBoundedTelescope f 1 fun args (body : Q($α)) => do
      let #[(i : Q($ι))] := args | failure
      let rbody ← core zα pα body
      let pbody ← rbody.toNonneg
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      let mα' ← synthInstanceQ q(AddCommMonoid $α)
      let oα' ← synthInstanceQ q(Preorder $α)
      let pα' ← synthInstanceQ q(IsOrderedAddMonoid $α)
      let instOrderClosed ← synthInstanceQ q(OrderClosedTopology $α)
      assertInstancesCommute
      return .nonnegative
        q(@tsum_nonneg $ι $α $L $mα' $oα' $pα' $instTopSpace $instOrderClosed $f $pr)
  | _ => throwError "not tsum"

end Mathlib.Meta.Positivity

