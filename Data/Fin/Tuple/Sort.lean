/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Fintype.Fin

/-!

# Sorting tuples by their values

Given an `n`-tuple `f : Fin n → α` where `α` is ordered,
we may want to turn it into a sorted `n`-tuple.
This file provides an API for doing so, with the sorted `n`-tuple given by
`f ∘ Tuple.sort f`.

## Main declarations

* `Tuple.sort`: given `f : Fin n → α`, produces a permutation on `Fin n`
* `Tuple.monotone_sort`: `f ∘ Tuple.sort f` is `Monotone`

-/

@[expose] public section


namespace Tuple

variable {n : ℕ}
variable {α : Type*} [LinearOrder α]

/-- `graph f` produces the finset of pairs `(f i, i)`
equipped with the lexicographic order.
-/
/-
**Tuple.graph** 是 Mathlib 中的一个定义，位于命名空间 `Tuple`。
形式化陈述：graph (f : Fin n -> α) : Finset (α ×ₗ Fin n)
参数：f : Fin n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`graph f` produces the finset of pairs `(f i, i)`
equipped with the lexicographic order.
-/
def graph (f : Fin n → α) : Finset (α ×ₗ Fin n) :=
  Finset.univ.image fun i => (f i, i)

/-- Given `p : α ×ₗ (Fin n) := (f i, i)` with `p ∈ graph f`,
`graph.proj p` is defined to be `f i`.
-/
/-
**Tuple.graph.proj** 是 Mathlib 中的一个定义，位于命名空间 `Tuple.graph`。
形式化陈述：{n : ℕ} → {α : Type u_1} → [inst : LinearOrder α] → {f : Fin n → α} → ↥(Tu
ple.graph f) → α
参数：Tuple.graph f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `p : α ×ₗ (Fin n) := (f i, i)` with `p ∈ graph f`,
`graph.proj p` is defined to be `f i`.
-/
def graph.proj {f : Fin n → α} : graph f → α := fun p => p.1.1

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Tuple.graph.card** 是 Mathlib 中的一个定理，位于命名空间 `Tuple.graph`。
形式化陈述：∀ {n : ℕ} {α : Type u_1} [inst : LinearOrder α] (f : Fin n → α), (Tuple.gr
aph f).card = n
参数：f : Fin n → α；Tuple.graph f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tuple.graph.eq_1`：∀ {n : ℕ} {α : Type u_1} [inst : LinearOrder α] (f : F
in n → α),   Tuple.graph f = Finset.image (fun i => (f i, i)) Finset.univ
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
-/
theorem graph.card (f : Fin n → α) : (graph f).card = n := by
  rw [graph, Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro _ _
    -- Porting note: proof was `simp`
    rw [Prod.ext_iff]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- `graphEquiv₁ f` is the natural equivalence between `Fin n` and `graph f`,
mapping `i` to `(f i, i)`. -/
/-
**Tuple.graphEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Tuple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`graphEquiv₁ f` is the natural equivalence between `Fin n` and `graph f`,
mapping `i` to `(f i, i)`.
-/
def graphEquiv₁ (f : Fin n → α) : Fin n ≃ graph f where
  toFun i := ⟨(f i, i), by simp [graph]⟩
  invFun p := p.1.2
  left_inv i := by simp
  right_inv := fun ⟨⟨x, i⟩, h⟩ => by
    simpa [graph, eq_comm, eqComm] using h

@[simp]
/-
**Tuple.proj_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem proj_equiv₁' (f : Fin n → α) : graph.proj ∘ graphEquiv₁ f = f :=
  rfl

/-- `graphEquiv₂ f` is an equivalence between `Fin n` and `graph f` that respects the order.
-/
/-
**Tuple.graphEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Tuple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`graphEquiv₂ f` is an equivalence between `Fin n` and `graph f` that respects th
e order.
-/
def graphEquiv₂ (f : Fin n → α) : Fin n ≃o graph f :=
  Finset.orderIsoOfFin _ (by simp)

/-- `sort f` is the permutation that orders `Fin n` according to the order of the outputs of `f`. -/
/-
**Tuple.sort** 是 Mathlib 中的一个定义，位于命名空间 `Tuple`。
形式化陈述：sort (f : Fin n -> α) : Equiv.Perm (Fin n)
参数：f : Fin n -> α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`sort f` is the permutation that orders `Fin n` according to the order of the ou
tputs of `f`.
-/
def sort (f : Fin n → α) : Equiv.Perm (Fin n) :=
  (graphEquiv₂ f).toEquiv.trans (graphEquiv₁ f).symm
/-
**Tuple.graphEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem graphEquiv₂_apply (f : Fin n → α) (i : Fin n) :
    graphEquiv₂ f i = graphEquiv₁ f (sort f i) :=
  ((graphEquiv₁ f).apply_symm_apply _).symm
/-
**Tuple.self_comp_sort** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：self_comp_sort (f : Fin n -> α) : f ∘ sort f = graph.proj ∘ graphEquiv₂ f
参数：f : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem self_comp_sort (f : Fin n → α) : f ∘ sort f = graph.proj ∘ graphEquiv₂ f :=
  show graph.proj ∘ (graphEquiv₁ f ∘ (graphEquiv₁ f).symm) ∘ (graphEquiv₂ f).toEquiv = _ by simp
/-
**Tuple.monotone_proj** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：monotone_proj (f : Fin n -> α) : Monotone (graph.proj : graph f -> α)
参数：f : Fin n -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem monotone_proj (f : Fin n → α) : Monotone (graph.proj : graph f → α) := by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  · exact le_of_lt ‹_›
  · simp [graph.proj]
/-
**Tuple.monotone_sort** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：monotone_sort (f : Fin n -> α) : Monotone (f ∘ sort f)
参数：f : Fin n -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tuple.self_comp_sort`：self_comp_sort (f : Fin n -> α) : f ∘ sort f = gra
ph.proj ∘ graphEquiv₂ f
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Tuple.monotone_proj`：monotone_proj (f : Fin n -> α) : Monotone (graph.pr
oj : graph f -> α)
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
-/
theorem monotone_sort (f : Fin n → α) : Monotone (f ∘ sort f) := by
  rw [self_comp_sort]
  exact (monotone_proj f).comp (graphEquiv₂ f).monotone

end Tuple

namespace Tuple

open List

variable {n : ℕ} {α : Type*}

section

open Finset

variable {j : Fin n} {f : Fin n → α} [Preorder α] {a : α}

/-- If `f₀ ≤ f₁ ≤ f₂ ≤ ⋯` is a sorted `n`-tuple of elements of `α`, then for any `j : Fin n` and
`a : α` we have `j < #{i | fᵢ ≤ a}` iff `fⱼ ≤ a`. -/
/-
**Tuple.lt_card_le_iff_apply_le_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：lt_card_le_iff_apply_le_of_monotone [DecidableLE α] (h_sorted : Monotone f
) : j < #{i | f i <= a} ↔ f j <= a
参数：h_sorted : Monotone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_card_filter_univ_iff_apply_of_imp`：lt_card_filter_univ_iff_apply_
of_imp {j : Fin n} (p : Fin n -> Prop) [DecidablePred p] (hp : forall i j, j <= 
i -> p i -> p j) : j < #{i | p…

--- 原说明 ---
If `f₀ ≤ f₁ ≤ f₂ ≤ ⋯` is a sorted `n`-tuple of elements of `α`, then for any `j 
: Fin n` and
`a : α` we have `j < #{i | fᵢ ≤ a}` iff `fⱼ ≤ a`.
-/
theorem lt_card_le_iff_apply_le_of_monotone [DecidableLE α] (h_sorted : Monotone f) :
    j < #{i | f i ≤ a} ↔ f j ≤ a :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (f · ≤ a) (by grind [Monotone])
/-
**Tuple.lt_card_ge_iff_apply_ge_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：lt_card_ge_iff_apply_ge_of_antitone [DecidableLE α] (h_sorted : Antitone f
) : j < #{i | a <= f i} ↔ a <= f j
参数：h_sorted : Antitone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_card_filter_univ_iff_apply_of_imp`：lt_card_filter_univ_iff_apply_
of_imp {j : Fin n} (p : Fin n -> Prop) [DecidablePred p] (hp : forall i j, j <= 
i -> p i -> p j) : j < #{i | p…
-/
theorem lt_card_ge_iff_apply_ge_of_antitone [DecidableLE α] (h_sorted : Antitone f) :
    j < #{i | a ≤ f i} ↔ a ≤ f j :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (a ≤ f ·) (by grind [Antitone])
/-
**Tuple.lt_card_lt_iff_apply_lt_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：lt_card_lt_iff_apply_lt_of_monotone [DecidableLT α] (h_sorted : Monotone f
) : j < #{i | f i < a} ↔ f j < a
参数：h_sorted : Monotone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_card_filter_univ_iff_apply_of_imp`：lt_card_filter_univ_iff_apply_
of_imp {j : Fin n} (p : Fin n -> Prop) [DecidablePred p] (hp : forall i j, j <= 
i -> p i -> p j) : j < #{i | p…
-/
theorem lt_card_lt_iff_apply_lt_of_monotone [DecidableLT α] (h_sorted : Monotone f) :
    j < #{i | f i < a} ↔ f j < a :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (f · < a) (by grind [Monotone])
/-
**Tuple.lt_card_gt_iff_apply_gt_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：lt_card_gt_iff_apply_gt_of_antitone [DecidableLT α] (h_sorted : Antitone f
) : j < #{i | a < f i} ↔ a < f j
参数：h_sorted : Antitone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_card_filter_univ_iff_apply_of_imp`：lt_card_filter_univ_iff_apply_
of_imp {j : Fin n} (p : Fin n -> Prop) [DecidablePred p] (hp : forall i j, j <= 
i -> p i -> p j) : j < #{i | p…
-/
theorem lt_card_gt_iff_apply_gt_of_antitone [DecidableLT α] (h_sorted : Antitone f) :
    j < #{i | a < f i} ↔ a < f j :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (a < f ·) (by grind [Antitone])

end

/-- If two permutations of a tuple `f` are both monotone, then they are equal. -/
/-
**Tuple.unique_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：unique_monotone [PartialOrder α] {f : Fin n -> α} {σ τ : Equiv.Perm (Fin n
)} (hfσ : Monotone (f ∘ σ)) (hfτ : Monotone (f ∘ τ)) : f ∘ σ = f ∘ τ
参数：Fin n；hfσ : Monotone (f ∘ σ)；hfτ : Monotone (f ∘ τ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ofFn_injective`：ofFn_injective {n : Nat} : Function.Injective (ofFn
 : (Fin n -> α) -> List α)
· 使用定理 `List.Perm.eq_of_pairwise'`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Anti
symm r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂
 → l₁ = l₂
· 使用定理 `List.SortedLE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLE → List.Pairwise (fun x1 x2 => x1 ≤ x2) l
· 使用定理 `Monotone.sortedLE_ofFn`：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f 
: Fin n → α}, Monotone f → (List.ofFn f).SortedLE
· 使用定理 `Equiv.Perm.ofFn_comp_perm`：Equiv.Perm.ofFn_comp_perm {n : Nat} {α : Type
 u} (σ : Equiv.Perm (Fin n)) (f : Fin n -> α) : ofFn (f ∘ σ) ~ ofFn f
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁

--- 原说明 ---
If two permutations of a tuple `f` are both monotone, then they are equal.
-/
theorem unique_monotone [PartialOrder α] {f : Fin n → α} {σ τ : Equiv.Perm (Fin n)}
    (hfσ : Monotone (f ∘ σ)) (hfτ : Monotone (f ∘ τ)) : f ∘ σ = f ∘ τ :=
  ofFn_injective <|
    ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm).eq_of_pairwise'
      hfσ.sortedLE_ofFn.pairwise hfτ.sortedLE_ofFn.pairwise

/-- If two permutations of a tuple `f` are both antitone, then they are equal. -/
/-
**Tuple.unique_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：unique_antitone [PartialOrder α] {f : Fin n -> α} {σ τ : Equiv.Perm (Fin n
)} (hfσ : Antitone (f ∘ σ)) (hfτ : Antitone (f ∘ τ)) : f ∘ σ = f ∘ τ
参数：Fin n；hfσ : Antitone (f ∘ σ)；hfτ : Antitone (f ∘ τ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ofFn_injective`：ofFn_injective {n : Nat} : Function.Injective (ofFn
 : (Fin n -> α) -> List α)
· 使用定理 `List.Perm.eq_of_pairwise'`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Anti
symm r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂
 → l₁ = l₂
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `List.SortedGE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedGE → List.Pairwise (fun x1 x2 => x1 ≥ x2) l
· 使用定理 `Antitone.sortedGE_ofFn`：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f 
: Fin n → α}, Antitone f → (List.ofFn f).SortedGE
· 使用定理 `Equiv.Perm.ofFn_comp_perm`：Equiv.Perm.ofFn_comp_perm {n : Nat} {α : Type
 u} (σ : Equiv.Perm (Fin n)) (f : Fin n -> α) : ofFn (f ∘ σ) ~ ofFn f
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁

--- 原说明 ---
If two permutations of a tuple `f` are both antitone, then they are equal.
-/
theorem unique_antitone [PartialOrder α] {f : Fin n → α} {σ τ : Equiv.Perm (Fin n)}
    (hfσ : Antitone (f ∘ σ)) (hfτ : Antitone (f ∘ τ)) : f ∘ σ = f ∘ τ :=
  ofFn_injective <|
    ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm).eq_of_pairwise'
      hfσ.sortedGE_ofFn.pairwise hfτ.sortedGE_ofFn.pairwise

variable [LinearOrder α] {f : Fin n → α} {σ : Equiv.Perm (Fin n)}

/-- A permutation `σ` equals `sort f` if and only if the map `i ↦ (f (σ i), σ i)` is
strictly monotone (w.r.t. the lexicographic ordering on the target). -/
/-
**Tuple.eq_sort_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：eq_sort_iff' : σ = sort f ↔ StrictMono (σ.trans <| graphEquiv₁ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Tuple.sort.eq_1`：∀ {n : ℕ} {α : Type u_1} [inst : LinearOrder α] (f : Fi
n n → α),   Tuple.sort f = (Tuple.graphEquiv₂ f).trans (Tuple.graphEquiv₁ f).sym
m
· 使用定理 `Equiv.trans_assoc`：trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ
) : (ab.trans bc).trans cd = ab.trans (bc.trans cd)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm_trans_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.t
rans e = Equiv.refl β
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_gt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedGT α],
 IsWellOrder α fun x1 x2 => x2 < x1
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
A permutation `σ` equals `sort f` if and only if the map `i ↦ (f (σ i), σ i)` is
strictly monotone (w.r.t. the lexicographic ordering on the target).
-/
theorem eq_sort_iff' : σ = sort f ↔ StrictMono (σ.trans <| graphEquiv₁ f) := by
  constructor <;> intro h
  · rw [h, sort, Equiv.trans_assoc, Equiv.symm_trans_self]
    exact (graphEquiv₂ f).strictMono
  · have := Subsingleton.elim (graphEquiv₂ f) (h.orderIsoOfSurjective _ <| Equiv.surjective _)
    ext1 x
    exact (graphEquiv₁ f).eq_symm_apply.2 (DFunLike.congr_fun this x).symm

/-- A permutation `σ` equals `sort f` if and only if `f ∘ σ` is monotone and whenever `i < j`
and `f (σ i) = f (σ j)`, then `σ i < σ j`. This means that `sort f` is the lexicographically
smallest permutation `σ` such that `f ∘ σ` is monotone. -/
/-
**Tuple.eq_sort_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：eq_sort_iff : σ = sort f ↔ Monotone (f ∘ σ) ∧ forall i j, i < j -> f (σ i)
 = f (σ j) -> σ i < σ j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tuple.eq_sort_iff'`：eq_sort_iff' : σ = sort f ↔ StrictMono (σ.trans <| g
raphEquiv₁ f)
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Tuple.monotone_proj`：monotone_proj (f : Fin n -> α) : Monotone (graph.pr
oj : graph f -> α)
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.Lex.toLex_lt_toLex`：toLex_lt_toLex [LT α] [LT β] {x y : α × β} : to
Lex x < toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
A permutation `σ` equals `sort f` if and only if `f ∘ σ` is monotone and wheneve
r `i < j`
and `f (σ i) = f (σ j)`, then `σ i < σ j`. This means that `sort f` is the lexic
ographically
smallest permutation `σ` such that `f ∘ σ` is monotone.
-/
theorem eq_sort_iff :
    σ = sort f ↔ Monotone (f ∘ σ) ∧ ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j := by
  rw [eq_sort_iff']
  refine ⟨fun h => ⟨(monotone_proj f).comp h.monotone, fun i j hij hfij => ?_⟩, fun h i j hij => ?_⟩
  · exact ((Prod.Lex.toLex_lt_toLex.1 <| h hij).resolve_left hfij.not_lt).2
  · obtain he | hl := (h.1 hij.le).eq_or_lt <;> apply Prod.Lex.toLex_lt_toLex.2
    exacts [Or.inr ⟨he, h.2 i j hij he⟩, Or.inl hl]

/-- The permutation that sorts `f` is the identity if and only if `f` is monotone. -/
/-
**Tuple.sort_eq_refl_iff_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：sort_eq_refl_iff_monotone : sort f = Equiv.refl _ ↔ Monotone f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Tuple.eq_sort_iff`：eq_sort_iff : σ = sort f ↔ Monotone (f ∘ σ) ∧ forall 
i j, i < j -> f (σ i) = f (σ j) -> σ i < σ j
· 使用定理 `Equiv.coe_refl`：∀ {α : Sort u}, ⇑(Equiv.refl α) = id
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f

--- 原说明 ---
The permutation that sorts `f` is the identity if and only if `f` is monotone.
-/
theorem sort_eq_refl_iff_monotone : sort f = Equiv.refl _ ↔ Monotone f := by
  rw [eq_comm, eq_sort_iff, Equiv.coe_refl, Function.comp_id]
  simp only [id, and_iff_left_iff_imp]
  exact fun _ _ _ hij _ => hij

/-- A permutation of a tuple `f` is `f` sorted if and only if it is monotone. -/
/-
**Tuple.comp_sort_eq_comp_iff_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：comp_sort_eq_comp_iff_monotone : f ∘ σ = f ∘ sort f ↔ Monotone (f ∘ σ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tuple.monotone_sort`：monotone_sort (f : Fin n -> α) : Monotone (f ∘ sort
 f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tuple.unique_monotone`：unique_monotone [PartialOrder α] {f : Fin n -> α}
 {σ τ : Equiv.Perm (Fin n)} (hfσ : Monotone (f ∘ σ)) (hfτ : Monotone (f ∘ τ)) : 
f ∘ σ = f ∘…

--- 原说明 ---
A permutation of a tuple `f` is `f` sorted if and only if it is monotone.
-/
theorem comp_sort_eq_comp_iff_monotone : f ∘ σ = f ∘ sort f ↔ Monotone (f ∘ σ) :=
  ⟨fun h => h.symm ▸ monotone_sort f, fun h => unique_monotone h (monotone_sort f)⟩

/-- The sorted versions of a tuple `f` and of any permutation of `f` agree. -/
/-
**Tuple.comp_perm_comp_sort_eq_comp_sort** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：comp_perm_comp_sort_eq_comp_sort : (f ∘ σ) ∘ sort (f ∘ σ) = f ∘ sort f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.coe_mul`：∀ {α : Type u_4} (f g : Equiv.Perm α), ⇑(f * g) = ⇑f
 ∘ ⇑g
· 使用定理 `Tuple.unique_monotone`：unique_monotone [PartialOrder α] {f : Fin n -> α}
 {σ τ : Equiv.Perm (Fin n)} (hfσ : Monotone (f ∘ σ)) (hfτ : Monotone (f ∘ τ)) : 
f ∘ σ = f ∘…
· 使用定理 `Tuple.monotone_sort`：monotone_sort (f : Fin n -> α) : Monotone (f ∘ sort
 f)

--- 原说明 ---
The sorted versions of a tuple `f` and of any permutation of `f` agree.
-/
theorem comp_perm_comp_sort_eq_comp_sort : (f ∘ σ) ∘ sort (f ∘ σ) = f ∘ sort f := by
  rw [Function.comp_assoc, ← Equiv.Perm.coe_mul]
  exact unique_monotone (monotone_sort (f ∘ σ)) (monotone_sort f)

/-- If a permutation `f ∘ σ` of the tuple `f` is not the same as `f ∘ sort f`, then `f ∘ σ`
has a pair of strictly decreasing entries. -/
/-
**Tuple.antitone_pair_of_not_sorted'** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：antitone_pair_of_not_sorted' (h : f ∘ σ != f ∘ sort f) : exists i j, i < j
 ∧ (f ∘ σ) j < (f ∘ σ) i
参数：h : f ∘ σ != f ∘ sort f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Tuple.comp_sort_eq_comp_iff_monotone`：comp_sort_eq_comp_iff_monotone : f
 ∘ σ = f ∘ sort f ↔ Monotone (f ∘ σ)
· 使用定理 `monotone_iff_forall_lt`：monotone_iff_forall_lt : Monotone f ↔ forall ⦃a 
b⦄, a < b -> f a <= f b

--- 原说明 ---
If a permutation `f ∘ σ` of the tuple `f` is not the same as `f ∘ sort f`, then 
`f ∘ σ`
has a pair of strictly decreasing entries.
-/
theorem antitone_pair_of_not_sorted' (h : f ∘ σ ≠ f ∘ sort f) :
    ∃ i j, i < j ∧ (f ∘ σ) j < (f ∘ σ) i := by
  contrapose! h
  exact comp_sort_eq_comp_iff_monotone.mpr (monotone_iff_forall_lt.mpr h)

/-- If the tuple `f` is not the same as `f ∘ sort f`, then `f` has a pair of strictly decreasing
entries. -/
/-
**Tuple.antitone_pair_of_not_sorted** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：antitone_pair_of_not_sorted (h : f != f ∘ sort f) : exists i j, i < j ∧ f 
j < f i
参数：h : f != f ∘ sort f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tuple.antitone_pair_of_not_sorted'`：antitone_pair_of_not_sorted' (h : f 
∘ σ != f ∘ sort f) : exists i j, i < j ∧ (f ∘ σ) j < (f ∘ σ) i
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
If the tuple `f` is not the same as `f ∘ sort f`, then `f` has a pair of strictl
y decreasing
entries.
-/
theorem antitone_pair_of_not_sorted (h : f ≠ f ∘ sort f) : ∃ i j, i < j ∧ f j < f i :=
  antitone_pair_of_not_sorted' (id h : f ∘ Equiv.refl _ ≠ _)

/-- The sorted version of a permutation `σ` is its inverse `σ⁻¹`. -/
@[simp]
/-
**Tuple.sort_perm** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：sort_perm (σ : Equiv.Perm (Fin n)) : sort σ = σ⁻¹
参数：σ : Equiv.Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Tuple.eq_sort_iff`：eq_sort_iff : σ = sort f ↔ Monotone (f ∘ σ) ∧ forall 
i j, i < j -> f (σ i) = f (σ j) -> σ i < σ j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
The sorted version of a permutation `σ` is its inverse `σ⁻¹`.
-/
theorem sort_perm (σ : Equiv.Perm (Fin n)) :
    sort σ = σ⁻¹ := by
  apply (eq_sort_iff.2 ⟨?_ , ?_⟩).symm
  · simpa using monotone_id
  · intro _ _ hij h
    exact (hij.ne (by simpa using h)).elim

end Tuple

/-
**Equiv.Perm.monotone_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.monotone_iff {n : Nat} (σ : Perm (Fin n)) : Monotone σ ↔ σ = 1
参数：σ : Perm (Fin n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tuple.sort_eq_refl_iff_monotone`：sort_eq_refl_iff_monotone : sort f = Eq
uiv.refl _ ↔ Monotone f
· 使用定理 `Tuple.sort_perm`：sort_perm (σ : Equiv.Perm (Fin n)) : sort σ = σ⁻¹
· 使用定理 `inv_eq_one`：inv_eq_one : a⁻¹ = 1 ↔ a = 1
· 使用定理 `Equiv.Perm.one_def`：one_def : (1 : Perm α) = Equiv.refl α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Equiv.Perm.monotone_iff {n : ℕ} (σ : Perm (Fin n)) :
    Monotone σ ↔ σ = 1 := by
  rw [← Tuple.sort_eq_refl_iff_monotone, Tuple.sort_perm, ← inv_eq_one, one_def]
