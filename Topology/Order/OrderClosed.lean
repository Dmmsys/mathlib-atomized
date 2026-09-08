/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Order-closed topologies

In this file we introduce 3 typeclass mixins that relate topology and order structures:

- `ClosedIicTopology` says that all the intervals $(-∞, a]$ (formally, `Set.Iic a`)
  are closed sets;
- `ClosedIciTopology` says that all the intervals $[a, +∞)$ (formally, `Set.Ici a`)
  are closed sets;
- `OrderClosedTopology` says that the set of points `(x, y)` such that `x ≤ y`
  is closed in the product topology.

The last predicate implies the first two.

We prove many basic properties of such topologies.

## Main statements

This file contains the proofs of the following facts.
For exact requirements
(`OrderClosedTopology` vs `ClosedIciTopology` vs `ClosedIicTopology`,
`Preorder` vs `PartialOrder` vs `LinearOrder`, etc.)
see their statements.

### Open / closed sets

* `isOpen_lt` : if `f` and `g` are continuous functions, then `{x | f x < g x}` is open;
* `isOpen_Iio`, `isOpen_Ioi`, `isOpen_Ioo` : open intervals are open;
* `isClosed_le` : if `f` and `g` are continuous functions, then `{x | f x ≤ g x}` is closed;
* `isClosed_Iic`, `isClosed_Ici`, `isClosed_Icc` : closed intervals are closed;
* `frontier_le_subset_eq`, `frontier_lt_subset_eq` : frontiers of both `{x | f x ≤ g x}`
  and `{x | f x < g x}` are included by `{x | f x = g x}`;

### Convergence and inequalities

* `le_of_tendsto_of_tendsto` : if `f` converges to `a`, `g` converges to `b`, and eventually
  `f x ≤ g x`, then `a ≤ b`
* `le_of_tendsto`, `ge_of_tendsto` : if `f` converges to `a` and eventually `f x ≤ b`
  (resp., `b ≤ f x`), then `a ≤ b` (resp., `b ≤ a`); we also provide primed versions
  that assume the inequalities to hold for all `x`.
* `monotone_of_frequently_monotone_of_tendsto`, `antitone_of_frequently_antitone_of_tendsto` : the
  pointwise limit of frequently monotone or antitone functions is monotone or antitone.

### Min, max, `sSup` and `sInf`

* `Continuous.min`, `Continuous.max`: pointwise `min`/`max` of two continuous functions is
  continuous.
* `Tendsto.min`, `Tendsto.max` : if `f` tends to `a` and `g` tends to `b`, then their pointwise
  `min`/`max` tend to `min a b` and `max a b`, respectively.
-/

public section

open Set Filter TopologicalSpace
open OrderDual (toDual)
open scoped Topology

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- If `α` is a topological space and a preorder, `ClosedIicTopology α` means that `Iic a` is
closed for all `a : α`. -/
/-
**ClosedIicTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [TopologicalSpace α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a topological space and a preorder, `ClosedIicTopology α` means that `
Iic a` is
closed for all `a : α`.
-/
class ClosedIicTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `(-∞, a]` is closed. -/
  isClosed_Iic (a : α) : IsClosed (Iic a)

/-- If `α` is a topological space and a preorder, `ClosedIciTopology α` means that `Ici a` is
closed for all `a : α`. -/
@[to_dual existing]
/-
**ClosedIciTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [TopologicalSpace α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a topological space and a preorder, `ClosedIciTopology α` means that `
Ici a` is
closed for all `a : α`.
-/
class ClosedIciTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `[a, +∞)` is closed. -/
  isClosed_Ici (a : α) : IsClosed (Ici a)

/-- A topology on a set which is both a topological space and a preorder is _order-closed_ if the
set of points `(x, y)` with `x ≤ y` is closed in the product space. We introduce this as a mixin.
This property is satisfied for the order topology on a linear order, but it can be satisfied more
generally, and suffices to derive many interesting properties relating order and topology. -/
/-
**OrderClosedTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [TopologicalSpace α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topology on a set which is both a topological space and a preorder is _order-c
losed_ if the
set of points `(x, y)` with `x ≤ y` is closed in the product space. We introduce
 this as a mixin.
This property is satisfied for the order topology on a linear order, but it can 
be satisfied more
generally, and suffices to derive many interesting properties relating order and
 topology.
-/
class OrderClosedTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- The set `{ (x, y) | x ≤ y }` is a closed set. -/
  protected isClosed_le' : IsClosed { p : α × α | p.1 ≤ p.2 }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [h : FirstCountableTopology α] : FirstCountableTopology αᵒᵈ := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [h : SecondCountableTopology α] : SecondCountableTopology αᵒᵈ := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [h : SeparableSpace α] : SeparableSpace αᵒᵈ := h
/-
**Dense.orderDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.orderDual [TopologicalSpace α] {s : Set α} (hs : Dense s) : Dense (O
rderDual.ofDual ⁻¹' s)
参数：hs : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Dense.orderDual [TopologicalSpace α] {s : Set α} (hs : Dense s) :
    Dense (OrderDual.ofDual ⁻¹' s) :=
  hs

section General
variable [TopologicalSpace α] [Preorder α] {s : Set α}

@[to_dual]
/-
**BddAbove.of_closure** 是 Mathlib 中的一个定理，位于命名空间 `BddAbove`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preorder α] {s : Set 
α}, BddAbove (closure s) → BddAbove s
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
protected lemma BddAbove.of_closure : BddAbove (closure s) → BddAbove s :=
  BddAbove.mono subset_closure

end General

section ClosedIicTopology

section Preorder

variable [TopologicalSpace α] [Preorder α] [ClosedIicTopology α] {f : β → α} {a b : α} {s : Set α}

@[to_dual (attr := closedness .)]
/-
**isClosed_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_Iic : IsClosed (Iic a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedIicTopology.isClosed_Iic`：∀ {α : Type u_1} {inst : TopologicalSpac
e α} {inst_1 : Preorder α} [self : ClosedIicTopology α] (a : α),   IsClosed (Set
.Iic a)
-/
theorem isClosed_Iic : IsClosed (Iic a) :=
  ClosedIicTopology.isClosed_Iic a

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ClosedIciTopology αᵒᵈ where
  isClosed_Ici _ := isClosed_Iic (α := α)

@[to_dual (attr := simp, closedness =)]
/-
**closure_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_Iic (a : α) : closure (Iic a) = Iic a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
-/
theorem closure_Iic (a : α) : closure (Iic a) = Iic a :=
  isClosed_Iic.closure_eq

@[to_dual ge_of_tendsto_of_frequently]
/-
**le_of_tendsto_of_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_tendsto_of_frequently {x : Filter β} (lim : Tendsto f x (𝓝 a)) (h : 
existsᶠ c in x, f c <= b) : a <= b
参数：lim : Tendsto f x (𝓝 a)；h : existsᶠ c in x, f c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.mem_of_frequently_of_tendsto`：IsClosed.mem_of_frequently_of_ten
dsto {f : α -> X} {b : Filter α} (hs : IsClosed s) (h : existsᶠ x in b, f x in s
) (hf : Tendsto f b (𝓝 x)) …
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
-/
theorem le_of_tendsto_of_frequently {x : Filter β} (lim : Tendsto f x (𝓝 a))
    (h : ∃ᶠ c in x, f c ≤ b) : a ≤ b :=
  isClosed_Iic.mem_of_frequently_of_tendsto h lim

@[to_dual ge_of_tendsto]
/-
**le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a)) (h :
 forallᶠ c in x, f c <= b) : a <= b
参数：lim : Tendsto f x (𝓝 a)；h : forallᶠ c in x, f c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
-/
theorem le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ᶠ c in x, f c ≤ b) : a ≤ b :=
  isClosed_Iic.mem_of_tendsto lim h

@[to_dual ge_of_tendsto']
/-
**le_of_tendsto'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a)) (h 
: forall c, f c <= b) : a <= b
参数：lim : Tendsto f x (𝓝 a)；h : forall c, f c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ c, f c ≤ b) : a ≤ b :=
  le_of_tendsto lim (Eventually.of_forall h)

@[to_dual (attr := simp)]
/-
**upperBounds_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperBounds_closure (s : Set α) : upperBounds (closure s : Set α) = upperB
ounds s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperBounds_closure (s : Set α) : upperBounds (closure s : Set α) = upperBounds s :=
  ext fun a ↦ by simp_rw [mem_upperBounds_iff_subset_Iic, isClosed_Iic.closure_subset_iff]

@[to_dual (attr := simp)]
/-
**bddAbove_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_closure : BddAbove (closure s) ↔ BddAbove s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperBounds_closure`：upperBounds_closure (s : Set α) : upperBounds (clos
ure s : Set α) = upperBounds s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bddAbove_closure : BddAbove (closure s) ↔ BddAbove s := by
  simp_rw [BddAbove, upperBounds_closure]

@[to_dual]
protected alias ⟨_, BddAbove.closure⟩ := bddAbove_closure

@[to_dual (attr := simp) disjoint_nhds_atTop_iff]
/-
**disjoint_nhds_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhds_atBot_iff : Disjoint (𝓝 a) atBot ↔ ¬IsBot a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.disjoint_principal_right`：disjoint_principal_right {f : Filter α}
 {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ in f
· 使用定理 `IsBot.atBot_eq`：∀ {α : Type u_3} [inst : Preorder α] {a : α}, IsBot a → 
Filter.atBot = Filter.principal (Set.Iic a)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.disjoint_of_disjoint_of_mem`：disjoint_of_disjoint_of_mem {f g : F
ilter α} {s t : Set α} (h : Disjoint s t) (hs : s in f) (ht : t in g) : Disjoint
 f g
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
-/
theorem disjoint_nhds_atBot_iff : Disjoint (𝓝 a) atBot ↔ ¬IsBot a := by
  constructor
  · intro hd hbot
    rw [hbot.atBot_eq, disjoint_principal_right] at hd
    exact mem_of_mem_nhds hd le_rfl
  · simp only [IsBot, not_forall]
    rintro ⟨b, hb⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ (Iic_mem_atBot b)
    exact isClosed_Iic.isOpen_compl.mem_nhds hb

@[to_dual]
/-
**IsLUB.range_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.range_of_tendsto {F : Filter β} [F.NeBot] (hle : forall i, f i <= a)
 (hlim : Tendsto f F (𝓝 a)) : IsLUB (range f) a
参数：hle : forall i, f i <= a；hlim : Tendsto f F (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem IsLUB.range_of_tendsto {F : Filter β} [F.NeBot] (hle : ∀ i, f i ≤ a)
    (hlim : Tendsto f F (𝓝 a)) : IsLUB (range f) a :=
  ⟨forall_mem_range.mpr hle, fun _c hc ↦ le_of_tendsto' hlim fun i ↦ hc <| mem_range_self i⟩

end Preorder

section NoBotOrder

variable [Preorder α] [NoBotOrder α] [TopologicalSpace α] [ClosedIicTopology α] {a : α}
  {l : Filter β} [NeBot l] {f : β → α}

@[to_dual disjoint_nhds_atTop]
/-
**disjoint_nhds_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhds_atBot (a : α) : Disjoint (𝓝 a) atBot
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem disjoint_nhds_atBot (a : α) : Disjoint (𝓝 a) atBot := by simp

@[to_dual (attr := simp) nhds_inf_atTop]
/-
**nhds_inf_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_inf_atBot (a : α) : 𝓝 a ⊓ atBot = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `disjoint_nhds_atBot`：disjoint_nhds_atBot (a : α) : Disjoint (𝓝 a) atBot
-/
theorem nhds_inf_atBot (a : α) : 𝓝 a ⊓ atBot = ⊥ := (disjoint_nhds_atBot a).eq_bot

@[deprecated (since := "2026-04-07")] alias inf_nhds_atBot := nhds_inf_atBot
@[deprecated (since := "2026-04-07")] alias inf_nhds_atTop := nhds_inf_atTop

@[to_dual]
/-
**not_tendsto_nhds_of_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_tendsto_nhds_of_tendsto_atBot (hf : Tendsto f l atBot) (a : α) : ¬Tend
sto f l (𝓝 a)
参数：hf : Tendsto f l atBot；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.not_tendsto`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{a : Filter α} {b₁ b₂ : Filter β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoi
nt b₁ b₂ → ¬Filt…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `disjoint_nhds_atBot`：disjoint_nhds_atBot (a : α) : Disjoint (𝓝 a) atBot
-/
theorem not_tendsto_nhds_of_tendsto_atBot (hf : Tendsto f l atBot) (a : α) : ¬Tendsto f l (𝓝 a) :=
  hf.not_tendsto (disjoint_nhds_atBot a).symm

@[to_dual]
/-
**not_tendsto_atBot_of_tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_tendsto_atBot_of_tendsto_nhds (hf : Tendsto f l (𝓝 a)) : ¬Tendsto f l 
atBot
参数：hf : Tendsto f l (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.not_tendsto`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{a : Filter α} {b₁ b₂ : Filter β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoi
nt b₁ b₂ → ¬Filt…
· 使用定理 `disjoint_nhds_atBot`：disjoint_nhds_atBot (a : α) : Disjoint (𝓝 a) atBot
-/
theorem not_tendsto_atBot_of_tendsto_nhds (hf : Tendsto f l (𝓝 a)) : ¬Tendsto f l atBot :=
  hf.not_tendsto (disjoint_nhds_atBot a)

end NoBotOrder

/-
**iSup_eq_of_forall_le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_of_forall_le_of_tendsto {ι : Type*} {F : Filter ι} [Filter.NeBot F
] [ConditionallyCompleteLattice α] [TopologicalSpace α] [ClosedIicTopology α] {a
 : α} {f : ι -> α} (hle : forall i, f i <= a) (hlim : Filter.Tendsto f F (𝓝 a)) 
: ⨆ i, f i = a
参数：hle : forall i, f i <= a；hlim : Filter.Tendsto f F (𝓝 a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.nonempty_of_neBot`：nonempty_of_neBot (f : Filter α) [NeBot f] : N
onempty α
· 使用定理 `IsLUB.ciSup_eq`：IsLUB.ciSup_eq [Nonempty ι] {f : ι -> α} (H : IsLUB (ran
ge f) a) : ⨆ i, f i = a
· 使用定理 `IsLUB.range_of_tendsto`：IsLUB.range_of_tendsto {F : Filter β} [F.NeBot] 
(hle : forall i, f i <= a) (hlim : Tendsto f F (𝓝 a)) : IsLUB (range f) a
-/
theorem iSup_eq_of_forall_le_of_tendsto {ι : Type*} {F : Filter ι} [Filter.NeBot F]
    [ConditionallyCompleteLattice α] [TopologicalSpace α] [ClosedIicTopology α]
    {a : α} {f : ι → α} (hle : ∀ i, f i ≤ a) (hlim : Filter.Tendsto f F (𝓝 a)) :
    ⨆ i, f i = a :=
  have := F.nonempty_of_neBot
  (IsLUB.range_of_tendsto hle hlim).ciSup_eq
/-
**iUnion_Iic_eq_Iio_of_lt_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Iic_eq_Iio_of_lt_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot] [C
onditionallyCompleteLinearOrder α] [TopologicalSpace α] [ClosedIicTopology α] {a
 : α} {f : ι -> α} (hlt : forall i, f i < a) (hlim : Tendsto f F (𝓝 a)) : ⋃ i : 
ι, Iic (f i) = Iio a
参数：hlt : forall i, f i < a；hlim : Tendsto f F (𝓝 a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
· 使用定理 `IsLUB.biUnion_Iic_eq_Iio`：IsLUB.biUnion_Iic_eq_Iio (a_lub : IsLUB s a) (
a_notMem : a ∉ s) : ⋃ x in s, Iic x = Iio a
· 使用定理 `IsLUB.range_of_tendsto`：IsLUB.range_of_tendsto {F : Filter β} [F.NeBot] 
(hle : forall i, f i <= a) (hlim : Tendsto f F (𝓝 a)) : IsLUB (range f) a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem iUnion_Iic_eq_Iio_of_lt_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [ClosedIicTopology α]
    {a : α} {f : ι → α} (hlt : ∀ i, f i < a) (hlim : Tendsto f F (𝓝 a)) :
    ⋃ i : ι, Iic (f i) = Iio a := by
  have obs : a ∉ range f := by
    rw [mem_range]
    rintro ⟨i, rfl⟩
    exact (hlt i).false
  rw [← biUnion_range, (IsLUB.range_of_tendsto (le_of_lt <| hlt ·) hlim).biUnion_Iic_eq_Iio obs]

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α] [TopologicalSpace β]
  {a b c : α} {f : α → β}

@[to_dual]
/-
**isOpen_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_Ioi : IsOpen (Ioi a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_Iic`：compl_Iic : (Iic a)ᶜ = Ioi a
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
-/
theorem isOpen_Ioi : IsOpen (Ioi a) := by
  rw [← compl_Iic]
  exact isClosed_Iic.isOpen_compl

@[to_dual (attr := simp)]
/-
**interior_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_Ioi : interior (Ioi a) = Ioi a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
-/
theorem interior_Ioi : interior (Ioi a) = Ioi a :=
  isOpen_Ioi.interior_eq

@[to_dual]
/-
**Ioi_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
-/
theorem Ioi_mem_nhds (h : a < b) : Ioi a ∈ 𝓝 b := IsOpen.mem_nhds isOpen_Ioi h

@[to_dual eventually_lt_nhds]
/-
**eventually_gt_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_gt_nhds (hab : b < a) : forallᶠ x in 𝓝 a, b < x
参数：hab : b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
-/
theorem eventually_gt_nhds (hab : b < a) : ∀ᶠ x in 𝓝 a, b < x := Ioi_mem_nhds hab

@[to_dual]
/-
**Ici_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ici_mem_nhds (h : a < b) : Ici a in 𝓝 b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
-/
theorem Ici_mem_nhds (h : a < b) : Ici a ∈ 𝓝 b :=
  mem_of_superset (Ioi_mem_nhds h) Ioi_subset_Ici_self

@[to_dual eventually_le_nhds]
/-
**eventually_ge_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_ge_nhds (hab : b < a) : forallᶠ x in 𝓝 a, b <= x
参数：hab : b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ici_mem_nhds`：Ici_mem_nhds (h : a < b) : Ici a in 𝓝 b
-/
theorem eventually_ge_nhds (hab : b < a) : ∀ᶠ x in 𝓝 a, b ≤ x := Ici_mem_nhds hab

@[to_dual eventually_lt_const]
/-
**Filter.Tendsto.eventually_const_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.eventually_const_lt {l : Filter γ} {f : γ -> α} {u v : α} (
hv : u < v) (h : Filter.Tendsto f l (𝓝 v)) : forallᶠ a in l, u < f a
参数：hv : u < v；h : Filter.Tendsto f l (𝓝 v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `eventually_gt_nhds`：eventually_gt_nhds (hab : b < a) : forallᶠ x in 𝓝 a,
 b < x
-/
theorem Filter.Tendsto.eventually_const_lt {l : Filter γ} {f : γ → α} {u v : α} (hv : u < v)
    (h : Filter.Tendsto f l (𝓝 v)) : ∀ᶠ a in l, u < f a :=
  h.eventually <| eventually_gt_nhds hv

@[to_dual eventually_le_const]
/-
**Filter.Tendsto.eventually_const_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.eventually_const_le {l : Filter γ} {f : γ -> α} {u v : α} (
hv : u < v) (h : Tendsto f l (𝓝 v)) : forallᶠ a in l, u <= f a
参数：hv : u < v；h : Tendsto f l (𝓝 v)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `eventually_ge_nhds`：eventually_ge_nhds (hab : b < a) : forallᶠ x in 𝓝 a,
 b <= x
-/
theorem Filter.Tendsto.eventually_const_le {l : Filter γ} {f : γ → α} {u v : α} (hv : u < v)
    (h : Tendsto f l (𝓝 v)) : ∀ᶠ a in l, u ≤ f a :=
  h.eventually <| eventually_ge_nhds hv

@[to_dual exists_lt]
/-
**Dense.exists_gt** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearOrder α] [Close
dIicTopology α] [NoMaxOrder α] {s : Set α},   Dense s → ∀ (x : α), ∃ y ∈ s, x < 
y
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.exists_mem_open`：Dense.exists_mem_open (hs : Dense s) {U : Set X} 
(ho : IsOpen U) (hne : U.Nonempty) : exists x in s, x in U
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
-/
protected theorem Dense.exists_gt [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, x < y :=
  hs.exists_mem_open isOpen_Ioi (exists_gt x)

@[to_dual exists_le]
/-
**Dense.exists_ge** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearOrder α] [Close
dIicTopology α] [NoMaxOrder α] {s : Set α},   Dense s → ∀ (x : α), ∃ y ∈ s, x ≤ 
y
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Dense.exists_gt`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Li
nearOrder α] [ClosedIicTopology α] [NoMaxOrder α] {s : Set α},   Dense s → ∀ (x 
: α),…
-/
protected theorem Dense.exists_ge [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, x ≤ y :=
  (hs.exists_gt x).imp fun _ h ↦ ⟨h.1, h.2.le⟩

@[to_dual exists_le']
/-
**Dense.exists_ge'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.exists_ge' {s : Set α} (hs : Dense s) (htop : forall x, IsTop x -> x
 in s) (x : α) : exists y in s, x <= y
参数：hs : Dense s；htop : forall x, IsTop x -> x in s；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Dense.exists_mem_open`：Dense.exists_mem_open (hs : Dense s) {U : Set X} 
(ho : IsOpen U) (hne : U.Nonempty) : exists x in s, x in U
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Dense.exists_ge' {s : Set α} (hs : Dense s) (htop : ∀ x, IsTop x → x ∈ s) (x : α) :
    ∃ y ∈ s, x ≤ y := by
  by_cases hx : IsTop x
  · exact ⟨x, htop x hx, le_rfl⟩
  · simp only [IsTop, not_forall, not_le] at hx
    rcases hs.exists_mem_open isOpen_Ioi hx with ⟨y, hys, hy : x < y⟩
    exact ⟨y, hys, hy.le⟩

/-!
### Left neighborhoods on a `ClosedIicTopology`

Limits to the left of real functions are defined in terms of neighborhoods to the left, either open
or closed, i.e., members of `𝓝[<] a` and `𝓝[≤] a`. Here we prove that all left-neighborhoods of a
point are equal, and we prove other useful characterizations which require the stronger hypothesis
`OrderTopology α` in another file.
-/

/-!
#### Point excluded
-/

@[to_dual]
/-
**Ioo_mem_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
参数：H : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b

--- 原说明 ---
#### Point excluded
-/
theorem Ioo_mem_nhdsLT (H : a < b) : Ioo a b ∈ 𝓝[<] b := by
  simpa only [← Iio_inter_Ioi] using inter_mem_nhdsWithin _ (Ioi_mem_nhds H)

@[to_dual]
/-
**Ioo_mem_nhdsLT_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioo_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ioo a c in 𝓝[<] b
参数：H : b in Ioc a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Ioo_subset_Ioo_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ ≤ a₁ → Set.Ioo b a₂ ⊆ Set.Ioo b a₁
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ioo_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Ioo a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT H.1) <| Ioo_subset_Ioo_right H.2

@[to_dual]
/-
**CovBy.nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 `CovBy`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearOrder α] [Close
dIicTopology α] {a b : α},   a ⋖ b → nhdsWithin b (Set.Iio b) = ⊥
参数：Set.Iio b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CovBy.Ioo_eq`：CovBy.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅
-/
protected theorem CovBy.nhdsLT (h : a ⋖ b) : 𝓝[<] b = ⊥ :=
  empty_mem_iff_bot.mp <| h.Ioo_eq ▸ Ioo_mem_nhdsLT h.1

@[to_dual]
/-
**PredOrder.nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 `PredOrder`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearOrder α] [Close
dIicTopology α] {a : α} [PredOrder α],   nhdsWithin a (Set.Iio a) = ⊥
参数：Set.Iio a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMin.Iio_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsMin a → Se
t.Iio a = ∅
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CovBy.nhdsLT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIicTopology α] {a b : α},   a ⋖ b → nhdsWithin b (Set.Iio b) = 
⊥
· 使用定理 `Order.pred_covBy_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] [ins
t_1 : PredOrder α] {a : α}, ¬IsMin a → Order.pred a ⋖ a
-/
protected theorem PredOrder.nhdsLT [PredOrder α] : 𝓝[<] a = ⊥ := by
  if h : IsMin a then simp [h.Iio_eq]
  else exact (Order.pred_covBy_of_not_isMin h).nhdsLT

@[to_dual]
/-
**PredOrder.nhdsGT_eq_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PredOrder.nhdsGT_eq_nhdsNE [PredOrder α] (a : α) : 𝓝[>] a = 𝓝[!=] a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsLT_sup_nhdsGT`：nhdsLT_sup_nhdsGT (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[!=] a
· 使用定理 `PredOrder.nhdsLT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : L
inearOrder α] [ClosedIicTopology α] {a : α} [PredOrder α],   nhdsWithin a (Set.I
io a) …
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
theorem PredOrder.nhdsGT_eq_nhdsNE [PredOrder α] (a : α) : 𝓝[>] a = 𝓝[≠] a := by
  rw [← nhdsLT_sup_nhdsGT, PredOrder.nhdsLT, bot_sup_eq]

@[to_dual]
/-
**PredOrder.nhdsGE_eq_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PredOrder.nhdsGE_eq_nhds [PredOrder α] (a : α) : 𝓝[>=] a = 𝓝 a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsLT_sup_nhdsGE`：nhdsLT_sup_nhdsGE (a : α) : 𝓝[<] a ⊔ 𝓝[>=] a = 𝓝 a
· 使用定理 `PredOrder.nhdsLT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : L
inearOrder α] [ClosedIicTopology α] {a : α} [PredOrder α],   nhdsWithin a (Set.I
io a) …
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
theorem PredOrder.nhdsGE_eq_nhds [PredOrder α] (a : α) : 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsLT_sup_nhdsGE, PredOrder.nhdsLT, bot_sup_eq]

@[to_dual]
/-
**Ico_mem_nhdsLT_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ico_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ico a c in 𝓝[<] b
参数：H : b in Ioc a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhdsLT_of_mem`：Ioo_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ioo a 
c in 𝓝[<] b
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
theorem Ico_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Ico a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ico_self

@[to_dual]
/-
**Ico_mem_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ico_mem_nhdsLT (H : a < b) : Ico a b in 𝓝[<] b
参数：H : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ico_mem_nhdsLT_of_mem`：Ico_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ico a 
c in 𝓝[<] b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ico_mem_nhdsLT (H : a < b) : Ico a b ∈ 𝓝[<] b := Ico_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual]
/-
**Ioc_mem_nhdsLT_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioc_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ioc a c in 𝓝[<] b
参数：H : b in Ioc a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhdsLT_of_mem`：Ioo_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ioo a 
c in 𝓝[<] b
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
-/
theorem Ioc_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Ioc a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ioc_self

@[to_dual]
/-
**Ioc_mem_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioc_mem_nhdsLT (H : a < b) : Ioc a b in 𝓝[<] b
参数：H : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ioc_mem_nhdsLT_of_mem`：Ioc_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ioc a 
c in 𝓝[<] b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ioc_mem_nhdsLT (H : a < b) : Ioc a b ∈ 𝓝[<] b := Ioc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual]
/-
**Icc_mem_nhdsLT_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Icc_mem_nhdsLT_of_mem (H : b in Ioc a c) : Icc a c in 𝓝[<] b
参数：H : b in Ioc a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhdsLT_of_mem`：Ioo_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ioo a 
c in 𝓝[<] b
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
-/
theorem Icc_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Icc a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Icc_self

@[to_dual]
/-
**Icc_mem_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Icc_mem_nhdsLT (H : a < b) : Icc a b in 𝓝[<] b
参数：H : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Icc_mem_nhdsLT_of_mem`：Icc_mem_nhdsLT_of_mem (H : b in Ioc a c) : Icc a 
c in 𝓝[<] b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Icc_mem_nhdsLT (H : a < b) : Icc a b ∈ 𝓝[<] b := Icc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual (attr := simp)]
/-
**nhdsWithin_Ico_eq_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_Ico_eq_nhdsLT (h : a < b) : 𝓝[Ico a b] b = 𝓝[<] b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Ici_mem_nhds`：Ici_mem_nhds (h : a < b) : Ici a in 𝓝 b
-/
theorem nhdsWithin_Ico_eq_nhdsLT (h : a < b) : 𝓝[Ico a b] b = 𝓝[<] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ici_mem_nhds h

@[to_dual (attr := simp)]
/-
**nhdsWithin_Ioo_eq_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a b] b = 𝓝[<] b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
-/
theorem nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a b] b = 𝓝[<] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ioi_mem_nhds h

@[to_dual (attr := simp)]
/-
**continuousWithinAt_Ico_iff_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_Ico_iff_Iio (h : a < b) : ContinuousWithinAt f (Ico a b
) b ↔ ContinuousWithinAt f (Iio b) b
参数：h : a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_Ico_eq_nhdsLT`：nhdsWithin_Ico_eq_nhdsLT (h : a < b) : 𝓝[Ico a
 b] b = 𝓝[<] b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_Ico_iff_Iio (h : a < b) :
    ContinuousWithinAt f (Ico a b) b ↔ ContinuousWithinAt f (Iio b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsLT h]

@[to_dual (attr := simp)]
/-
**continuousWithinAt_Ioo_iff_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_Ioo_iff_Iio (h : a < b) : ContinuousWithinAt f (Ioo a b
) b ↔ ContinuousWithinAt f (Iio b) b
参数：h : a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_Ioo_eq_nhdsLT`：nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a
 b] b = 𝓝[<] b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_Ioo_iff_Iio (h : a < b) :
    ContinuousWithinAt f (Ioo a b) b ↔ ContinuousWithinAt f (Iio b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT h]

/-!
#### Point included
-/

@[to_dual]
/-
**CovBy.nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 `CovBy`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearOrder α] [Close
dIicTopology α] {a b : α},   a ⋖ b → nhdsWithin b (Set.Iic b) = pure b
参数：Set.Iic b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_insert`：Iio_insert : insert a (Iio a) = Iic a
· 使用定理 `nhdsWithin_insert`：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s]
 a = pure a ⊔ 𝓝[s] a
· 使用定理 `CovBy.nhdsLT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIicTopology α] {a b : α},   a ⋖ b → nhdsWithin b (Set.Iio b) = 
⊥
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a

--- 原说明 ---
#### Point included
-/
protected theorem CovBy.nhdsLE (H : a ⋖ b) : 𝓝[≤] b = pure b := by
  rw [← Iio_insert, nhdsWithin_insert, H.nhdsLT, sup_bot_eq]

@[to_dual]
/-
**PredOrder.nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 `PredOrder`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearOrder α] [Close
dIicTopology α] {b : α} [PredOrder α],   nhdsWithin b (Set.Iic b) = pure b
参数：Set.Iic b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_insert`：Iio_insert : insert a (Iio a) = Iic a
· 使用定理 `nhdsWithin_insert`：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s]
 a = pure a ⊔ 𝓝[s] a
· 使用定理 `PredOrder.nhdsLT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : L
inearOrder α] [ClosedIicTopology α] {a : α} [PredOrder α],   nhdsWithin a (Set.I
io a) …
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
protected theorem PredOrder.nhdsLE [PredOrder α] : 𝓝[≤] b = pure b := by
  rw [← Iio_insert, nhdsWithin_insert, PredOrder.nhdsLT, sup_bot_eq]

@[to_dual]
/-
**Ioc_mem_nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioc_mem_nhdsLE (H : a < b) : Ioc a b in 𝓝[<=] b
参数：H : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem Ioc_mem_nhdsLE (H : a < b) : Ioc a b ∈ 𝓝[≤] b :=
  inter_mem (nhdsWithin_le_nhds <| Ioi_mem_nhds H) self_mem_nhdsWithin

@[to_dual]
/-
**Ioo_mem_nhdsLE_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioo_mem_nhdsLE_of_mem (H : b in Ioo a c) : Ioo a c in 𝓝[<=] b
参数：H : b in Ioo a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioc_mem_nhdsLE`：Ioc_mem_nhdsLE (H : a < b) : Ioc a b in 𝓝[<=] b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Ioc_subset_Ioo_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ < a₁ → Set.Ioc b a₂ ⊆ Set.Ioo b a₁
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ioo_mem_nhdsLE_of_mem (H : b ∈ Ioo a c) : Ioo a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioc_mem_nhdsLE H.1) <| Ioc_subset_Ioo_right H.2

@[to_dual]
/-
**Ico_mem_nhdsLE_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ico_mem_nhdsLE_of_mem (H : b in Ioo a c) : Ico a c in 𝓝[<=] b
参数：H : b in Ioo a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhdsLE_of_mem`：Ioo_mem_nhdsLE_of_mem (H : b in Ioo a c) : Ioo a 
c in 𝓝[<=] b
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
theorem Ico_mem_nhdsLE_of_mem (H : b ∈ Ioo a c) : Ico a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioo_mem_nhdsLE_of_mem H) Ioo_subset_Ico_self

@[to_dual]
/-
**Ioc_mem_nhdsLE_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioc_mem_nhdsLE_of_mem (H : b in Ioc a c) : Ioc a c in 𝓝[<=] b
参数：H : b in Ioc a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioc_mem_nhdsLE`：Ioc_mem_nhdsLE (H : a < b) : Ioc a b in 𝓝[<=] b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Ioc_subset_Ioc_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ ≤ a₁ → Set.Ioc b a₂ ⊆ Set.Ioc b a₁
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ioc_mem_nhdsLE_of_mem (H : b ∈ Ioc a c) : Ioc a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioc_mem_nhdsLE H.1) <| Ioc_subset_Ioc_right H.2

@[to_dual]
/-
**Icc_mem_nhdsLE_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Icc_mem_nhdsLE_of_mem (H : b in Ioc a c) : Icc a c in 𝓝[<=] b
参数：H : b in Ioc a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioc_mem_nhdsLE_of_mem`：Ioc_mem_nhdsLE_of_mem (H : b in Ioc a c) : Ioc a 
c in 𝓝[<=] b
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem Icc_mem_nhdsLE_of_mem (H : b ∈ Ioc a c) : Icc a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioc_mem_nhdsLE_of_mem H) Ioc_subset_Icc_self

@[to_dual]
/-
**Icc_mem_nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Icc_mem_nhdsLE (H : a < b) : Icc a b in 𝓝[<=] b
参数：H : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Icc_mem_nhdsLE_of_mem`：Icc_mem_nhdsLE_of_mem (H : b in Ioc a c) : Icc a 
c in 𝓝[<=] b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Icc_mem_nhdsLE (H : a < b) : Icc a b ∈ 𝓝[≤] b := Icc_mem_nhdsLE_of_mem ⟨H, le_rfl⟩

@[to_dual (attr := simp)]
/-
**nhdsWithin_Icc_eq_nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_Icc_eq_nhdsLE (h : a < b) : 𝓝[Icc a b] b = 𝓝[<=] b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Ici_mem_nhds`：Ici_mem_nhds (h : a < b) : Ici a in 𝓝 b
-/
theorem nhdsWithin_Icc_eq_nhdsLE (h : a < b) : 𝓝[Icc a b] b = 𝓝[≤] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ici_mem_nhds h

@[to_dual (attr := simp)]
/-
**nhdsWithin_Ioc_eq_nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_Ioc_eq_nhdsLE (h : a < b) : 𝓝[Ioc a b] b = 𝓝[<=] b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
-/
theorem nhdsWithin_Ioc_eq_nhdsLE (h : a < b) : 𝓝[Ioc a b] b = 𝓝[≤] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ioi_mem_nhds h

@[to_dual (attr := simp)]
/-
**continuousWithinAt_Icc_iff_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_Icc_iff_Iic (h : a < b) : ContinuousWithinAt f (Icc a b
) b ↔ ContinuousWithinAt f (Iic b) b
参数：h : a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_Icc_eq_nhdsLE`：nhdsWithin_Icc_eq_nhdsLE (h : a < b) : 𝓝[Icc a
 b] b = 𝓝[<=] b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_Icc_iff_Iic (h : a < b) :
    ContinuousWithinAt f (Icc a b) b ↔ ContinuousWithinAt f (Iic b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE h]

@[to_dual (attr := simp)]
/-
**continuousWithinAt_Ioc_iff_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_Ioc_iff_Iic (h : a < b) : ContinuousWithinAt f (Ioc a b
) b ↔ ContinuousWithinAt f (Iic b) b
参数：h : a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_Ioc_eq_nhdsLE`：nhdsWithin_Ioc_eq_nhdsLE (h : a < b) : 𝓝[Ioc a
 b] b = 𝓝[<=] b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_Ioc_iff_Iic (h : a < b) :
    ContinuousWithinAt f (Ioc a b) b ↔ ContinuousWithinAt f (Iic b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsLE h]

end LinearOrder

end ClosedIicTopology

section ClosedIciTopology

-- TODO: we're missing some to_dual tags for conditionally complete lattices

@[to_dual existing]
/-
**iInf_eq_of_forall_le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_eq_of_forall_le_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot] [Cond
itionallyCompleteLattice α] [TopologicalSpace α] [ClosedIciTopology α] {a : α} {
f : ι -> α} (hle : forall i, a <= f i) (hlim : Tendsto f F (𝓝 a)) : ⨅ i, f i = a
参数：hle : forall i, a <= f i；hlim : Tendsto f F (𝓝 a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_of_forall_le_of_tendsto`：iSup_eq_of_forall_le_of_tendsto {ι : Ty
pe*} {F : Filter ι} [Filter.NeBot F] [ConditionallyCompleteLattice α] [Topologic
alSpace α] [ClosedIic…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem iInf_eq_of_forall_le_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLattice α] [TopologicalSpace α] [ClosedIciTopology α]
    {a : α} {f : ι → α} (hle : ∀ i, a ≤ f i) (hlim : Tendsto f F (𝓝 a)) :
    ⨅ i, f i = a :=
  iSup_eq_of_forall_le_of_tendsto (α := αᵒᵈ) hle hlim

@[to_dual existing]
/-
**iUnion_Ici_eq_Ioi_of_lt_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ici_eq_Ioi_of_lt_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot] [C
onditionallyCompleteLinearOrder α] [TopologicalSpace α] [ClosedIciTopology α] {a
 : α} {f : ι -> α} (hlt : forall i, a < f i) (hlim : Tendsto f F (𝓝 a)) : ⋃ i : 
ι, Ici (f i) = Ioi a
参数：hlt : forall i, a < f i；hlim : Tendsto f F (𝓝 a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iUnion_Iic_eq_Iio_of_lt_of_tendsto`：iUnion_Iic_eq_Iio_of_lt_of_tendsto {
ι : Type*} {F : Filter ι} [F.NeBot] [ConditionallyCompleteLinearOrder α] [Topolo
gicalSpace α] [ClosedIic…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem iUnion_Ici_eq_Ioi_of_lt_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [ClosedIciTopology α]
    {a : α} {f : ι → α} (hlt : ∀ i, a < f i) (hlim : Tendsto f F (𝓝 a)) :
    ⋃ i : ι, Ici (f i) = Ioi a :=
  iUnion_Iic_eq_Iio_of_lt_of_tendsto (α := αᵒᵈ) hlt hlim

section OrderClosedTopology

section Preorder

variable [TopologicalSpace α] [Preorder α] [t : OrderClosedTopology α]

namespace Subtype

-- todo: add `OrderEmbedding.orderClosedTopology`
/-
**Subtype.** 是 Mathlib 中的一个实例，位于命名空间 `Subtype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : α → Prop} : OrderClosedTopology (Subtype p) :=
  have : Continuous fun p : Subtype p × Subtype p => ((p.fst : α), (p.snd : α)) :=
    continuous_subtype_val.prodMap continuous_subtype_val
  OrderClosedTopology.mk (t.isClosed_le'.preimage this)

end Subtype

-- The binder info on both theorems is slightly different, see
-- https://github.com/leanprover/lean4/issues/9727
@[closedness .]
/-
**isClosed_le_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_le_prod : IsClosed { p : α × α | p.1 <= p.2 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderClosedTopology.isClosed_le'`：∀ {α : Type u_1} {inst : TopologicalSp
ace α} {inst_1 : Preorder α} [self : OrderClosedTopology α],   IsClosed {p | p.1
 ≤ p.2}
-/
theorem isClosed_le_prod : IsClosed { p : α × α | p.1 ≤ p.2 } :=
  t.isClosed_le'

@[to_dual existing isClosed_le_prod, closedness .]
/-
**isClosed_le_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_le_prod' : IsClosed { p : α × α | p.2 <= p.1 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
· 使用定理 `isClosed_le_prod`：isClosed_le_prod : IsClosed { p : α × α | p.1 <= p.2 }
-/
theorem isClosed_le_prod' : IsClosed { p : α × α | p.2 ≤ p.1 } :=
  (isClosed_le_prod (α := α)).preimage continuous_swap

@[to_dual self (reorder := f g, hf hg)]
/-
**isClosed_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : 
Continuous g) : IsClosed { b | f b <= g b }
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `isClosed_le_prod`：isClosed_le_prod : IsClosed { p : α × α | p.1 <= p.2 }
-/
theorem isClosed_le [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { b | f b ≤ g b } :=
  continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_le_prod

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ClosedIicTopology α where
  isClosed_Iic _ := isClosed_le continuous_id continuous_const
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderClosedTopology αᵒᵈ :=
  ⟨isClosed_le_prod' (α := α)⟩

@[to_dual self, closedness .]
/-
**isClosed_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_Icc {a b : α} : IsClosed (Icc a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
-/
theorem isClosed_Icc {a b : α} : IsClosed (Icc a b) :=
  IsClosed.inter isClosed_Ici isClosed_Iic

@[to_dual self, simp, closedness =]
/-
**closure_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_Icc (a b : α) : closure (Icc a b) = Icc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isClosed_Icc`：isClosed_Icc {a b : α} : IsClosed (Icc a b)
-/
theorem closure_Icc (a b : α) : closure (Icc a b) = Icc a b :=
  isClosed_Icc.closure_eq

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
/-
**le_of_tendsto_of_tendsto_of_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_tendsto_of_tendsto_of_frequently {f g : β -> α} {b : Filter β} {a₁ a
₂ : α} (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : existsᶠ x in b, 
f x <= g x) : a₁ <= a₂
参数：hf : Tendsto f b (𝓝 a₁)；hg : Tendsto g b (𝓝 a₂)；h : existsᶠ x in b, f x <= g 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.mem_of_frequently_of_tendsto`：IsClosed.mem_of_frequently_of_ten
dsto {f : α -> X} {b : Filter α} (hs : IsClosed s) (h : existsᶠ x in b, f x in s
) (hf : Tendsto f b (𝓝 x)) …
· 使用定理 `OrderClosedTopology.isClosed_le'`：∀ {α : Type u_1} {inst : TopologicalSp
ace α} {inst_1 : Preorder α} [self : OrderClosedTopology α],   IsClosed {p | p.1
 ≤ p.2}
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem le_of_tendsto_of_tendsto_of_frequently {f g : β → α} {b : Filter β} {a₁ a₂ : α}
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : ∃ᶠ x in b, f x ≤ g x) : a₁ ≤ a₂ :=
  t.isClosed_le'.mem_of_frequently_of_tendsto h (hf.prodMk_nhds hg)

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
/-
**le_of_tendsto_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_tendsto_of_tendsto {f g : β -> α} {b : Filter β} {a₁ a₂ : α} [hb : N
eBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : f <=ᶠ[b] g) : a
₁ <= a₂
参数：hf : Tendsto f b (𝓝 a₁)；hg : Tendsto g b (𝓝 a₂)；h : f <=ᶠ[b] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto_of_tendsto_of_frequently`：le_of_tendsto_of_tendsto_of_freq
uently {f g : β -> α} {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁)) (hg :
 Tendsto g b (𝓝 a₂)) (h : ex…
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
-/
theorem le_of_tendsto_of_tendsto {f g : β → α} {b : Filter β} {a₁ a₂ : α} [hb : NeBot b]
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : f ≤ᶠ[b] g) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto_of_frequently hf hg <| Eventually.frequently h

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
alias tendsto_le_of_eventuallyLE := le_of_tendsto_of_tendsto

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
/-
**le_of_tendsto_of_tendsto'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_tendsto_of_tendsto' {f g : β -> α} {b : Filter β} {a₁ a₂ : α} [hb : 
NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : forall x, f x 
<= g x) : a₁ <= a₂
参数：hf : Tendsto f b (𝓝 a₁)；hg : Tendsto g b (𝓝 a₂)；h : forall x, f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto_of_tendsto`：le_of_tendsto_of_tendsto {f g : β -> α} {b : F
ilter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b 
(𝓝 a₂)) (h : f…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem le_of_tendsto_of_tendsto' {f g : β → α} {b : Filter β} {a₁ a₂ : α} [hb : NeBot b]
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : ∀ x, f x ≤ g x) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto hf hg (Eventually.of_forall h)

@[to_dual self (reorder := f g, hf hg), simp]
/-
**closure_le_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_le_eq [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg 
: Continuous g) : closure { b | f b <= g b } = { b | f b <= g b }
参数：hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
-/
theorem closure_le_eq [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    closure { b | f b ≤ g b } = { b | f b ≤ g b } :=
  (isClosed_le hf hg).closure_eq

@[to_dual self (reorder := f g, hf hg)]
/-
**closure_lt_subset_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_lt_subset_le [TopologicalSpace β] {f g : β -> α} (hf : Continuous 
f) (hg : Continuous g) : closure { b | f b < g b } subseteq { b | f b <= g b }
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
-/
theorem closure_lt_subset_le [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : closure { b | f b < g b } ⊆ { b | f b ≤ g b } :=
  (closure_minimal fun _ => le_of_lt) <| isClosed_le hf hg

@[to_dual self (reorder := f g, hf hg)]
/-
**ContinuousWithinAt.closure_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.closure_le [TopologicalSpace β] {f g : β -> α} {s : Set
 β} {x : β} (hx : x in closure s) (hf : ContinuousWithinAt f s x) (hg : Continuo
usWithinAt g s x) (h : forall y in s, f y <= g y) : f x <= g x
参数：hx : x in closure s；hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s
 x；h : forall y in s, f y <= g y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
· 使用定理 `OrderClosedTopology.isClosed_le'`：∀ {α : Type u_1} {inst : TopologicalSp
ace α} {inst_1 : Preorder α} [self : OrderClosedTopology α],   IsClosed {p | p.1
 ≤ p.2}
· 使用定理 `ContinuousWithinAt.mem_closure`：ContinuousWithinAt.mem_closure {t : Set 
β} (h : ContinuousWithinAt f s x) (hx : x in closure s) (ht : MapsTo f s t) : f 
x in closure t
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
-/
theorem ContinuousWithinAt.closure_le [TopologicalSpace β] {f g : β → α} {s : Set β} {x : β}
    (hx : x ∈ closure s) (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
    (h : ∀ y ∈ s, f y ≤ g y) : f x ≤ g x :=
  show (f x, g x) ∈ { p : α × α | p.1 ≤ p.2 } from
    OrderClosedTopology.isClosed_le'.closure_subset ((hf.prodMk hg).mem_closure hx h)

/-- If `s` is a closed set and two functions `f` and `g` are continuous on `s`,
then the set `{x ∈ s | f x ≤ g x}` is a closed set. -/
@[to_dual self (reorder := f g, hf hg)]
/-
**IsClosed.isClosed_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.isClosed_le [TopologicalSpace β] {f g : β -> α} {s : Set β} (hs :
 IsClosed s) (hf : ContinuousOn f s) (hg : ContinuousOn g s) : IsClosed ({ x in 
s | f x <= g x })
参数：hs : IsClosed s；hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.preimage_isClosed_of_isClosed`：ContinuousOn.preimage_isClos
ed_of_isClosed {t : Set β} (hf : ContinuousOn f s) (hs : IsClosed s) (ht : IsClo
sed t) : IsClosed (s inter f ⁻¹'…
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `OrderClosedTopology.isClosed_le'`：∀ {α : Type u_1} {inst : TopologicalSp
ace α} {inst_1 : Preorder α} [self : OrderClosedTopology α],   IsClosed {p | p.1
 ≤ p.2}

--- 原说明 ---
If `s` is a closed set and two functions `f` and `g` are continuous on `s`,
then the set `{x ∈ s | f x ≤ g x}` is a closed set.
-/
theorem IsClosed.isClosed_le [TopologicalSpace β] {f g : β → α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : IsClosed ({ x ∈ s | f x ≤ g x }) :=
  (hf.prodMk hg).preimage_isClosed_of_isClosed hs OrderClosedTopology.isClosed_le'

@[to_dual self (reorder := f g, hf hg)]
/-
**le_on_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_on_closure [TopologicalSpace β] {f g : β -> α} {s : Set β} (h : forall 
x in s, f x <= g x) (hf : ContinuousOn f (closure s)) (hg : ContinuousOn g (clos
ure s)) ⦃x⦄ (hx : x in closure s) : f x <= g x
参数：h : forall x in s, f x <= g x；hf : ContinuousOn f (closure s)；hg : Continuous
On g (closure s)；hx : x in closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `IsClosed.isClosed_le`：IsClosed.isClosed_le [TopologicalSpace β] {f g : β
 -> α} {s : Set β} (hs : IsClosed s) (hf : ContinuousOn f s) (hg : ContinuousOn 
g s) : IsC…
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem le_on_closure [TopologicalSpace β] {f g : β → α} {s : Set β} (h : ∀ x ∈ s, f x ≤ g x)
    (hf : ContinuousOn f (closure s)) (hg : ContinuousOn g (closure s)) ⦃x⦄ (hx : x ∈ closure s) :
    f x ≤ g x :=
  have : s ⊆ { y ∈ closure s | f y ≤ g y } := fun y hy => ⟨subset_closure hy, h y hy⟩
  (closure_minimal this (isClosed_closure.isClosed_le hf hg) hx).2

@[to_dual]
/-
**IsClosed.epigraph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.epigraph [TopologicalSpace β] {f : β -> α} {s : Set β} (hs : IsCl
osed s) (hf : ContinuousOn f s) : IsClosed { p : β × α | p.1 in s ∧ f p.1 <= p.2
 }
参数：hs : IsClosed s；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isClosed_le`：IsClosed.isClosed_le [TopologicalSpace β] {f g : β
 -> α} {s : Set β} (hs : IsClosed s) (hf : ContinuousOn f s) (hg : ContinuousOn 
g s) : IsC…
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `continuousOn_fst`：continuousOn_fst {s : Set (α × β)} : ContinuousOn Prod
.fst s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `continuousOn_snd`：continuousOn_snd {s : Set (α × β)} : ContinuousOn Prod
.snd s
-/
theorem IsClosed.epigraph [TopologicalSpace β] {f : β → α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) : IsClosed { p : β × α | p.1 ∈ s ∧ f p.1 ≤ p.2 } :=
  (hs.preimage continuous_fst).isClosed_le (hf.comp continuousOn_fst Subset.rfl) continuousOn_snd

section Tendsto

variable {ι : Type*} {l : Filter ι} [Preorder β] {F : ι → β → α} {f : β → α} {s : Set β}

/-- The limit of a collection of functions that is frequently monotone on a set is monotone on
that set. -/
/-
**monotoneOn_of_frequently_monotoneOn_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotoneOn_of_frequently_monotoneOn_of_tendsto (hF : existsᶠ i in l, Monot
oneOn (F i) s) (hlim : forall x in s, Tendsto (fun i => F i x) l (𝓝 (f x))) : Mo
notoneOn f s
参数：hF : existsᶠ i in l, MonotoneOn (F i) s；hlim : forall x in s, Tendsto (fun i 
=> F i x) l (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto_of_tendsto_of_frequently`：le_of_tendsto_of_tendsto_of_freq
uently {f g : β -> α} {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁)) (hg :
 Tendsto g b (𝓝 a₂)) (h : ex…
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x

--- 原说明 ---
The limit of a collection of functions that is frequently monotone on a set is m
onotone on
that set.
-/
lemma monotoneOn_of_frequently_monotoneOn_of_tendsto (hF : ∃ᶠ i in l, MonotoneOn (F i) s)
    (hlim : ∀ x ∈ s, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) : MonotoneOn f s :=
  fun a ha b hb hab ↦ le_of_tendsto_of_tendsto_of_frequently (hlim a ha) (hlim b hb) <|
    hF.mono fun _ hi ↦ hi ha hb hab

/-- The limit of a collection of functions that is frequently monotone is monotone. -/
/-
**monotone_of_frequently_monotone_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_of_frequently_monotone_of_tendsto (hF : existsᶠ i in l, Monotone 
(F i)) (hlim : forall x, Tendsto (fun i => F i x) l (𝓝 (f x))) : Monotone f
参数：hF : existsᶠ i in l, Monotone (F i)；hlim : forall x, Tendsto (fun i => F i x)
 l (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `monotoneOn_univ`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β}, MonotoneOn f Set.univ ↔ Monotone f
· 使用引理 `monotoneOn_of_frequently_monotoneOn_of_tendsto`：monotoneOn_of_frequently
_monotoneOn_of_tendsto (hF : existsᶠ i in l, MonotoneOn (F i) s) (hlim : forall 
x in s, Tendsto (fun i => F i x) l (…
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s

--- 原说明 ---
The limit of a collection of functions that is frequently monotone is monotone.
-/
lemma monotone_of_frequently_monotone_of_tendsto (hF : ∃ᶠ i in l, Monotone (F i))
    (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) : Monotone f :=
  monotoneOn_univ.1 <| monotoneOn_of_frequently_monotoneOn_of_tendsto
    (hF.mono fun _ hi ↦ hi.monotoneOn _) fun x _ ↦ hlim x

/-- The limit of a collection of functions that is frequently antitone on a set is antitone on
that set. -/
/-
**antitoneOn_of_frequently_antitoneOn_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitoneOn_of_frequently_antitoneOn_of_tendsto (hF : existsᶠ i in l, Antit
oneOn (F i) s) (hlim : forall x in s, Tendsto (fun i => F i x) l (𝓝 (f x))) : An
titoneOn f s
参数：hF : existsᶠ i in l, AntitoneOn (F i) s；hlim : forall x in s, Tendsto (fun i 
=> F i x) l (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotoneOn_of_frequently_monotoneOn_of_tendsto`：monotoneOn_of_frequently
_monotoneOn_of_tendsto (hF : existsᶠ i in l, MonotoneOn (F i) s) (hlim : forall 
x in s, Tendsto (fun i => F i x) l (…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
The limit of a collection of functions that is frequently antitone on a set is a
ntitone on
that set.
-/
lemma antitoneOn_of_frequently_antitoneOn_of_tendsto (hF : ∃ᶠ i in l, AntitoneOn (F i) s)
    (hlim : ∀ x ∈ s, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) : AntitoneOn f s :=
  monotoneOn_of_frequently_monotoneOn_of_tendsto (α := αᵒᵈ) hF hlim

/-- The limit of a collection of functions that is frequently antitone is antitone. -/
/-
**antitone_of_frequently_antitone_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitone_of_frequently_antitone_of_tendsto (hF : existsᶠ i in l, Antitone 
(F i)) (hlim : forall x, Tendsto (fun i => F i x) l (𝓝 (f x))) : Antitone f
参数：hF : existsᶠ i in l, Antitone (F i)；hlim : forall x, Tendsto (fun i => F i x)
 l (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotone_of_frequently_monotone_of_tendsto`：monotone_of_frequently_monot
one_of_tendsto (hF : existsᶠ i in l, Monotone (F i)) (hlim : forall x, Tendsto (
fun i => F i x) l (𝓝 (f x))) : M…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
The limit of a collection of functions that is frequently antitone is antitone.
-/
lemma antitone_of_frequently_antitone_of_tendsto (hF : ∃ᶠ i in l, Antitone (F i))
    (hlim : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) : Antitone f :=
  monotone_of_frequently_monotone_of_tendsto (α := αᵒᵈ) hF hlim

/-- The set of monotone functions on a set is closed. -/
/-
**isClosed_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_monotoneOn : IsClosed {f : β -> α | MonotoneOn f s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `monotoneOn_of_frequently_monotoneOn_of_tendsto`：monotoneOn_of_frequently
_monotoneOn_of_tendsto (hF : existsᶠ i in l, MonotoneOn (F i) s) (hlim : forall 
x in s, Tendsto (fun i => F i x) l (…
· 使用定理 `continuousAt_apply`：continuousAt_apply (i : ι) (x : forall i, A i) : Con
tinuousAt (fun p : forall i, A i => p i) x

--- 原说明 ---
The set of monotone functions on a set is closed.
-/
theorem isClosed_monotoneOn : IsClosed {f : β → α | MonotoneOn f s} := by
  simp only [isClosed_iff_clusterPt, clusterPt_principal_iff_frequently]
  exact fun g hg => monotoneOn_of_frequently_monotoneOn_of_tendsto hg
    fun x _ ↦ continuousAt_apply x g

/-- The set of monotone functions is closed. -/
/-
**isClosed_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_monotone : IsClosed {f : β -> α | Monotone f}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isClosed_monotoneOn`：isClosed_monotoneOn : IsClosed {f : β -> α | Monoto
neOn f s}

--- 原说明 ---
The set of monotone functions is closed.
-/
theorem isClosed_monotone : IsClosed {f : β → α | Monotone f} := by
  simp_rw [← monotoneOn_univ]
  exact isClosed_monotoneOn

/-- The set of antitone functions on a set is closed. -/
/-
**isClosed_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_antitoneOn : IsClosed {f : β -> α | AntitoneOn f s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_monotoneOn`：isClosed_monotoneOn : IsClosed {f : β -> α | Monoto
neOn f s}
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
The set of antitone functions on a set is closed.
-/
theorem isClosed_antitoneOn : IsClosed {f : β → α | AntitoneOn f s} :=
  isClosed_monotoneOn (α := αᵒᵈ)

/-- The set of antitone functions is closed. -/
/-
**isClosed_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_antitone : IsClosed {f : β -> α | Antitone f}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_monotone`：isClosed_monotone : IsClosed {f : β -> α | Monotone f
}
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
The set of antitone functions is closed.
-/
theorem isClosed_antitone : IsClosed {f : β → α | Antitone f} :=
  isClosed_monotone (α := αᵒᵈ)

end Tendsto

end Preorder

section PartialOrder

variable [TopologicalSpace α] [PartialOrder α] [t : OrderClosedTopology α]

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) OrderClosedTopology.to_t2Space : T2Space α :=
  t2_iff_isClosed_diagonal.2 <| by
    simpa only [diagonal, le_antisymm_iff] using!
      t.isClosed_le'.inter (isClosed_le continuous_snd continuous_fst)

end PartialOrder

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]

@[to_dual self (reorder := f g, hf hg)]
/-
**isOpen_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : Co
ntinuous g) : IsOpen { b | f b < g b }
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
-/
theorem isOpen_lt [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    IsOpen { b | f b < g b } := by
  simpa only [lt_iff_not_ge] using! (isClosed_le hg hf).isOpen_compl

@[to_dual isOpen_lt_prod']
/-
**isOpen_lt_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_lt_prod : IsOpen { p : α × α | p.1 < p.2 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem isOpen_lt_prod : IsOpen { p : α × α | p.1 < p.2 } :=
  isOpen_lt continuous_fst continuous_snd

variable {a b : α}

@[to_dual self]
/-
**isOpen_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_Ioo : IsOpen (Ioo a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem isOpen_Ioo : IsOpen (Ioo a b) :=
  IsOpen.inter isOpen_Ioi isOpen_Iio

@[to_dual self, simp]
/-
**interior_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_Ioo : interior (Ioo a b) = Ioo a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
-/
theorem interior_Ioo : interior (Ioo a b) = Ioo a b :=
  isOpen_Ioo.interior_eq

@[to_dual self]
/-
**Ioo_subset_closure_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioo_subset_closure_interior : Ioo a b subseteq closure (interior (Ioo a b)
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ioo`：interior_Ioo : interior (Ioo a b) = Ioo a b
-/
theorem Ioo_subset_closure_interior : Ioo a b ⊆ closure (interior (Ioo a b)) := by
  simp only [interior_Ioo, subset_closure]

@[to_dual self (reorder := a b, ha hb)]
/-
**Ioo_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a b in 𝓝 x
参数：ha : a < x；hb : x < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
-/
theorem Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a b ∈ 𝓝 x :=
  IsOpen.mem_nhds isOpen_Ioo ⟨ha, hb⟩

@[to_dual (reorder := ha hb)]
/-
**Ioc_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioc a b in 𝓝 x
参数：ha : a < x；hb : x < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
-/
theorem Ioc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioc a b ∈ 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Ioc_self

@[to_dual self (reorder := a b, ha hb)]
/-
**Icc_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a b in 𝓝 x
参数：ha : a < x；hb : x < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
-/
theorem Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a b ∈ 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Icc_self

/-- The only order closed topology on a linear order which is a `PredOrder` and a `SuccOrder`
is the discrete topology.

This theorem is not an instance,
because it causes searches for `PredOrder` and `SuccOrder` with their `Preorder` arguments
and very rarely matches. -/
@[to_dual self (reorder := 5 6)]
/-
**DiscreteTopology.of_predOrder_succOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DiscreteTopology.of_predOrder_succOrder [PredOrder α] [SuccOrder α] : Disc
reteTopology α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_nhds`：discreteTopology_iff_nhds [TopologicalSpace α
] : DiscreteTopology α ↔ forall x : α, 𝓝 x = pure x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Set.Iic_union_Ioi`：Iic_union_Ioi : Iic a union Ioi a = univ
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `PredOrder.nhdsLE`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : L
inearOrder α] [ClosedIicTopology α] {b : α} [PredOrder α],   nhdsWithin b (Set.I
ic b) …
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `SuccOrder.nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : L
inearOrder α] [ClosedIciTopology α] {a : α} [SuccOrder α],   nhdsWithin a (Set.I
oi a) …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a

--- 原说明 ---
The only order closed topology on a linear order which is a `PredOrder` and a `S
uccOrder`
is the discrete topology.

This theorem is not an instance,
because it causes searches for `PredOrder` and `SuccOrder` with their `Preorder`
 arguments
and very rarely matches.
-/
theorem DiscreteTopology.of_predOrder_succOrder [PredOrder α] [SuccOrder α] :
    DiscreteTopology α := by
  refine discreteTopology_iff_nhds.mpr fun a ↦ ?_
  rw [← nhdsWithin_univ, ← Iic_union_Ioi, nhdsWithin_union, PredOrder.nhdsLE, SuccOrder.nhdsGT,
    sup_bot_eq]

end LinearOrder

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] {f g : β → α}

section

variable [TopologicalSpace β]

@[to_dual self (reorder := f g, hf hg)]
/-
**lt_subset_interior_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_subset_interior_le (hf : Continuous f) (hg : Continuous g) : { b | f b 
< g b } subseteq interior { b | f b <= g b }
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
-/
theorem lt_subset_interior_le (hf : Continuous f) (hg : Continuous g) :
    { b | f b < g b } ⊆ interior { b | f b ≤ g b } :=
  (interior_maximal fun _ => le_of_lt) <| isOpen_lt hf hg

@[to_dual (reorder := f g, hf hg) frontier_ge_subset_eq]
/-
**frontier_le_subset_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_le_subset_eq (hf : Continuous f) (hg : Continuous g) : frontier {
 b | f b <= g b } subseteq { b | f b = g b }
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_eq_closure_inter_closure`：frontier_eq_closure_inter_closure : f
rontier s = closure s inter closure sᶜ
· 使用定理 `closure_le_eq`：closure_le_eq [TopologicalSpace β] {f g : β -> α} (hf : C
ontinuous f) (hg : Continuous g) : closure { b | f b <= g b } = { b | f b <= g b
 }
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `closure_lt_subset_le`：closure_lt_subset_le [TopologicalSpace β] {f g : β
 -> α} (hf : Continuous f) (hg : Continuous g) : closure { b | f b < g b } subse
teq { b | …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem frontier_le_subset_eq (hf : Continuous f) (hg : Continuous g) :
    frontier { b | f b ≤ g b } ⊆ { b | f b = g b } := by
  rw [frontier_eq_closure_inter_closure, closure_le_eq hf hg]
  rintro b ⟨hb₁, hb₂⟩
  refine le_antisymm hb₁ (closure_lt_subset_le hg hf ?_)
  convert! hb₂ using 2; simp only [not_le.symm]; rfl

@[to_dual]
/-
**frontier_Iic_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Iic_subset (a : α) : frontier (Iic a) subseteq {a}
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frontier_le_subset_eq`：frontier_le_subset_eq (hf : Continuous f) (hg : C
ontinuous g) : frontier { b | f b <= g b } subseteq { b | f b = g b }
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem frontier_Iic_subset (a : α) : frontier (Iic a) ⊆ {a} :=
  frontier_le_subset_eq (@continuous_id α _) continuous_const

@[to_dual (reorder := f g, hf hg) frontier_gt_subset_eq]
/-
**frontier_lt_subset_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_lt_subset_eq (hf : Continuous f) (hg : Continuous g) : frontier {
 b | f b < g b } subseteq { b | f b = g b }
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `frontier_compl`：frontier_compl (s : Set X) : frontier sᶜ = frontier s
· 使用定理 `frontier_le_subset_eq`：frontier_le_subset_eq (hf : Continuous f) (hg : C
ontinuous g) : frontier { b | f b <= g b } subseteq { b | f b = g b }
-/
theorem frontier_lt_subset_eq (hf : Continuous f) (hg : Continuous g) :
    frontier { b | f b < g b } ⊆ { b | f b = g b } := by
  simpa only [← not_lt, ← compl_ofPred, frontier_compl, eq_comm] using frontier_le_subset_eq hg hf

@[to_dual none]
/-
**continuous_if_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_if_le [TopologicalSpace γ] [forall x, Decidable (f x <= g x)] {
f' g' : β -> γ} (hf : Continuous f) (hg : Continuous g) (hf' : ContinuousOn f' {
 x | f x <= g x }) (hg' : ContinuousOn g' { x | g x <= f x }) (hfg : forall x, f
 x = g x -> f' x = g' x) : Continuous fun x => if f x <= g x then f' x else g' x
参数：f x <= g x；hf : Continuous f；hg : Continuous g；hf' : ContinuousOn f' { x | f 
x <= g x }；hg' : ContinuousOn g' { x | g x <= f x }；hfg : forall x, f x = g x ->
 f' x = g' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_if`：continuous_if {p : α -> Prop} [forall a, Decidable (p a)]
 (hp : forall a in frontier { x | p x }, f a = g a) (hf : ContinuousOn f (closur
e {…
· 使用定理 `frontier_le_subset_eq`：frontier_le_subset_eq (hf : Continuous f) (hg : C
ontinuous g) : frontier { b | f b <= g b } subseteq { b | f b = g b }
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `closure_lt_subset_le`：closure_lt_subset_le [TopologicalSpace β] {f g : β
 -> α} (hf : Continuous f) (hg : Continuous g) : closure { b | f b < g b } subse
teq { b | …
-/
theorem continuous_if_le [TopologicalSpace γ] [∀ x, Decidable (f x ≤ g x)] {f' g' : β → γ}
    (hf : Continuous f) (hg : Continuous g) (hf' : ContinuousOn f' { x | f x ≤ g x })
    (hg' : ContinuousOn g' { x | g x ≤ f x }) (hfg : ∀ x, f x = g x → f' x = g' x) :
    Continuous fun x => if f x ≤ g x then f' x else g' x := by
  refine continuous_if (fun a ha => hfg _ (frontier_le_subset_eq hf hg ha)) ?_ (hg'.mono ?_)
  · rwa [(isClosed_le hf hg).closure_eq]
  · simp only [not_le]
    exact closure_lt_subset_le hg hf

@[to_dual if_ge]
/-
**Continuous.if_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.if_le [TopologicalSpace γ] [forall x, Decidable (f x <= g x)] {
f' g' : β -> γ} (hf' : Continuous f') (hg' : Continuous g') (hf : Continuous f) 
(hg : Continuous g) (hfg : forall x, f x = g x -> f' x = g' x) : Continuous fun 
x => if f x <= g x then f' x else g' x
参数：f x <= g x；hf' : Continuous f'；hg' : Continuous g'；hf : Continuous f；hg : Con
tinuous g；hfg : forall x, f x = g x -> f' x = g' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_if_le`：continuous_if_le [TopologicalSpace γ] [forall x, Decid
able (f x <= g x)] {f' g' : β -> γ} (hf : Continuous f) (hg : Continuous g) (hf'
 : Con…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem Continuous.if_le [TopologicalSpace γ] [∀ x, Decidable (f x ≤ g x)] {f' g' : β → γ}
    (hf' : Continuous f') (hg' : Continuous g') (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x = g x → f' x = g' x) : Continuous fun x => if f x ≤ g x then f' x else g' x :=
  continuous_if_le hf hg hf'.continuousOn hg'.continuousOn hfg

@[to_dual self (reorder := f g, y z, hf hg)]
/-
**Filter.Tendsto.eventually_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.eventually_lt {l : Filter γ} {f g : γ -> α} {y z : α} (hf :
 Tendsto f l (𝓝 y)) (hg : Tendsto g l (𝓝 z)) (hyz : y < z) : forallᶠ x in l, f x
 < g x
参数：hf : Tendsto f l (𝓝 y)；hg : Tendsto g l (𝓝 z)；hyz : y < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LT.lt.exists_disjoint_Iio_Ioi`：LT.lt.exists_disjoint_Iio_Ioi (h : a < b)
 : exists a' > a, exists b' < b, forall x < a', forall y > b', x < y
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem Filter.Tendsto.eventually_lt {l : Filter γ} {f g : γ → α} {y z : α} (hf : Tendsto f l (𝓝 y))
    (hg : Tendsto g l (𝓝 z)) (hyz : y < z) : ∀ᶠ x in l, f x < g x :=
  let ⟨_a, ha, _b, hb, h⟩ := hyz.exists_disjoint_Iio_Ioi
  (hg.eventually (Ioi_mem_nhds hb)).mp <| (hf.eventually (Iio_mem_nhds ha)).mono fun _ h₁ h₂ =>
    h _ h₁ _ h₂

@[to_dual self (reorder := f g, hf hg)]
nonrec theorem ContinuousAt.eventually_lt {x₀ : β} (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀)
    (hfg : f x₀ < g x₀) : ∀ᶠ x in 𝓝 x₀, f x < g x :=
  hf.eventually_lt hg hfg

@[to_dual (attr := continuity, fun_prop)]
/-
**Continuous.max** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : LinearOr
der α] [OrderClosedTopology α] {f g : β → α}   [inst_3 : TopologicalSpace β], Co
ntinuous f → Continuous g → Continuous fun b => max (f b) (g b)
参数：f b；g b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `max_def`：max_def (a b : α) : max a b = if a <= b then b else a
· 使用定理 `Continuous.if_ge`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Topol
ogicalSpace α] [inst_1 : LinearOrder α] [OrderClosedTopology α]   {f g : β → α} 
[inst_…
-/
protected theorem Continuous.max (hf : Continuous f) (hg : Continuous g) :
    Continuous fun b => max (f b) (g b) := by
  simp only [max_def]
  exact hg.if_ge hf hg hf fun x => id

end

@[to_dual]
/-
**continuous_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_max : Continuous fun p : α × α => max p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.max`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   [inst_3 : Topol
ogic…
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem continuous_max : Continuous fun p : α × α => max p.1 p.2 :=
  continuous_fst.max continuous_snd

@[to_dual]
/-
**Filter.Tendsto.max** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : LinearOr
der α] [OrderClosedTopology α] {f g : β → α}   {b : Filter β} {a₁ a₂ : α},   Fil
ter.Tendsto f b (nhds a₁) →     Filter.Tendsto g b (nhds a₂) → Filter.Tendsto (f
un b => max (f b) (g b)) b (nhds (max a₁ a₂))
参数：nhds a₁；nhds a₂；fun b => max (f b) (g b)；nhds (max a₁ a₂)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_max`：continuous_max : Continuous fun p : α × α => max p.1 p.2
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
protected theorem Filter.Tendsto.max {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁))
    (hg : Tendsto g b (𝓝 a₂)) : Tendsto (fun b => max (f b) (g b)) b (𝓝 (max a₁ a₂)) :=
  (continuous_max.tendsto (a₁, a₂)).comp (hf.prodMk_nhds hg)

@[to_dual]
/-
**Filter.Tendsto.max_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : LinearOr
der α] [OrderClosedTopology α] {f : β → α}   {l : Filter β} {a : α}, Filter.Tend
sto f l (nhds a) → Filter.Tendsto (fun i => max a (f i)) l (nhds a)
参数：nhds a；fun i => max a (f i)；nhds a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
· 使用定理 `Filter.Tendsto.max`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace
 α] [inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   {b : Filter
 β} {a₁ …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
protected theorem Filter.Tendsto.max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => max a (f i)) l (𝓝 a) := by
  simpa only [sup_idem] using (tendsto_const_nhds (x := a)).max h

@[to_dual]
/-
**Filter.Tendsto.max_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : LinearOr
der α] [OrderClosedTopology α] {f : β → α}   {l : Filter β} {a : α}, Filter.Tend
sto f l (nhds a) → Filter.Tendsto (fun i => max (f i) a) l (nhds a)
参数：nhds a；fun i => max (f i) a；nhds a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Filter.Tendsto.max_right`：∀ {α : Type u} {β : Type v} [inst : Topologica
lSpace α] [inst_1 : LinearOrder α] [OrderClosedTopology α] {f : β → α}   {l : Fi
lter β} {a : α…
-/
protected theorem Filter.Tendsto.max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => max (f i) a) l (𝓝 a) := by
  simp_rw [max_comm _ a]
  exact h.max_right

@[to_dual]
/-
**Filter.tendsto_nhds_max_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.tendsto_nhds_max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>
] a)) : Tendsto (fun i => max a (f i)) l (𝓝[>] a)
参数：h : Tendsto f l (𝓝[>] a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Tendsto.max_right`：∀ {α : Type u} {β : Type v} [inst : Topologica
lSpace α] [inst_1 : LinearOrder α] [OrderClosedTopology α] {f : β → α}   {l : Fi
lter β} {a : α…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
-/
theorem Filter.tendsto_nhds_max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a)) :
    Tendsto (fun i => max a (f i)) l (𝓝[>] a) := by
  obtain ⟨h₁, h₂⟩ := tendsto_nhdsWithin_iff.mp h
  exact tendsto_nhdsWithin_iff.mpr ⟨h₁.max_right, h₂.mono fun i hi => lt_max_of_lt_right hi⟩

@[to_dual]
/-
**Filter.tendsto_nhds_max_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.tendsto_nhds_max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>]
 a)) : Tendsto (fun i => max (f i) a) l (𝓝[>] a)
参数：h : Tendsto f l (𝓝[>] a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Filter.tendsto_nhds_max_right`：Filter.tendsto_nhds_max_right {l : Filter
 β} {a : α} (h : Tendsto f l (𝓝[>] a)) : Tendsto (fun i => max a (f i)) l (𝓝[>] 
a)
-/
theorem Filter.tendsto_nhds_max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a)) :
    Tendsto (fun i => max (f i) a) l (𝓝[>] a) := by
  simp_rw [max_comm _ a]
  exact Filter.tendsto_nhds_max_right h

@[to_dual self]
/-
**Dense.exists_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.exists_between [DenselyOrdered α] {s : Set α} (hs : Dense s) {x y : 
α} (h : x < y) : exists z in s, z in Ioo x y
参数：hs : Dense s；h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.exists_mem_open`：Dense.exists_mem_open (hs : Dense s) {U : Set X} 
(ho : IsOpen U) (hne : U.Nonempty) : exists x in s, x in U
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
-/
theorem Dense.exists_between [DenselyOrdered α] {s : Set α} (hs : Dense s) {x y : α} (h : x < y) :
    ∃ z ∈ s, z ∈ Ioo x y :=
  hs.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 h)

@[to_dual]
/-
**Dense.Ioi_eq_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.Ioi_eq_biUnion [DenselyOrdered α] {s : Set α} (hs : Dense s) (x : α)
 : Ioi x = ⋃ y in s inter Ioi x, Ioi y
参数：hs : Dense s；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Dense.exists_between`：Dense.exists_between [DenselyOrdered α] {s : Set α
} (hs : Dense s) {x y : α} (h : x < y) : exists z in s, z in Ioo x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Dense.Ioi_eq_biUnion [DenselyOrdered α] {s : Set α} (hs : Dense s) (x : α) :
    Ioi x = ⋃ y ∈ s ∩ Ioi x, Ioi y := by
  refine Subset.antisymm (fun z hz ↦ ?_) (iUnion₂_subset fun y hy ↦ Ioi_subset_Ioi (le_of_lt hy.2))
  rcases hs.exists_between hz with ⟨y, hys, hy⟩
  exact mem_iUnion₂.2 ⟨y, ⟨hys, hy.1⟩, hy.2⟩

end LinearOrder

end OrderClosedTopology

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] [TopologicalSpace α] [OrderClosedTopology α] [Preorder β] [TopologicalSpace β]
    [OrderClosedTopology β] : OrderClosedTopology (α × β) :=
  ⟨(isClosed_le continuous_fst.fst continuous_snd.fst).inter
    (isClosed_le continuous_fst.snd continuous_snd.snd)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, OrderClosedTopology (α i)] : OrderClosedTopology (∀ i, α i) := by
  constructor
  simp only [Pi.le_def, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i).fst' (continuous_apply i).snd'
/-
**Pi.orderClosedTopology'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.orderClosedTopology' [Preorder β] [TopologicalSpace β] [OrderClosedTopo
logy β] : OrderClosedTopology (α -> β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderClosedTopologyForall`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst
 : (i : ι) → Preorder (α i)] [inst_1 : (i : ι) → TopologicalSpace (α i)]   [∀ (i
 : ι), OrderClosedT…
-/
instance Pi.orderClosedTopology' [Preorder β] [TopologicalSpace β] [OrderClosedTopology β] :
    OrderClosedTopology (α → β) :=
  inferInstance
