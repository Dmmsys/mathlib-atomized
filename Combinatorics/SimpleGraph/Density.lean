/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Edge density

This file defines the number and density of edges of a relation/graph.

## Main declarations

Between two finsets of vertices,
* `Rel.interedges`: Finset of edges of a relation.
* `Rel.edgeDensity`: Edge density of a relation.
* `SimpleGraph.interedges`: Finset of edges of a graph.
* `SimpleGraph.edgeDensity`: Edge density of a graph.
-/

@[expose] public section

open Finset

variable {𝕜 ι κ α β : Type*}

/-! ### Density of a relation -/


namespace Rel

section Asymmetric

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  (r : α → β → Prop) [∀ a, DecidablePred (r a)] {s s₁ s₂ : Finset α}
  {t t₁ t₂ : Finset β} {a : α} {b : β} {δ : 𝕜}

/-- Finset of edges of a relation between two finsets of vertices. -/
/-
**Rel.interedges** 是 Mathlib 中的一个定义，位于命名空间 `Rel`。
形式化陈述：interedges (s : Finset α) (t : Finset β) : Finset (α × β)
参数：s : Finset α；t : Finset β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finset of edges of a relation between two finsets of vertices.
-/
def interedges (s : Finset α) (t : Finset β) : Finset (α × β) := {e ∈ s ×ˢ t | r e.1 e.2}

/-- Edge density of a relation between two finsets of vertices. -/
/-
**Rel.edgeDensity** 是 Mathlib 中的一个定义，位于命名空间 `Rel`。
形式化陈述：edgeDensity (s : Finset α) (t : Finset β) : Rat
参数：s : Finset α；t : Finset β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Edge density of a relation between two finsets of vertices.
-/
def edgeDensity (s : Finset α) (t : Finset β) : ℚ := #(interedges r s t) / (#s * #t)

variable {r}
/-
**Rel.mem_interedges_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：mem_interedges_iff {x : α × β} : x in interedges r s t ↔ x.1 in s ∧ x.2 in
 t ∧ r x.1 x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rel.interedges.eq_1`：∀ {α : Type u_4} {β : Type u_5} (r : α → β → Prop) 
[inst : (a : α) → DecidablePred (r a)] (s : Finset α) (t : Finset β),   Rel.inte
redges r …
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_interedges_iff {x : α × β} : x ∈ interedges r s t ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ r x.1 x.2 := by
  rw [interedges, mem_filter, Finset.mem_product, and_assoc]
/-
**Rel.mk_mem_interedges_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：mk_mem_interedges_iff : (a, b) in interedges r s t ↔ a in s ∧ b in t ∧ r a
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.mem_interedges_iff`：mem_interedges_iff {x : α × β} : x in interedges
 r s t ↔ x.1 in s ∧ x.2 in t ∧ r x.1 x.2
-/
theorem mk_mem_interedges_iff : (a, b) ∈ interedges r s t ↔ a ∈ s ∧ b ∈ t ∧ r a b :=
  mem_interedges_iff

@[simp]
/-
**Rel.interedges_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：interedges_empty_left (t : Finset β) : interedges r ∅ t = ∅
参数：t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rel.interedges.eq_1`：∀ {α : Type u_4} {β : Type u_5} (r : α → β → Prop) 
[inst : (a : α) → DecidablePred (r a)] (s : Finset α) (t : Finset β),   Rel.inte
redges r …
· 使用定理 `Finset.empty_product`：empty_product (t : Finset β) : (∅ : Finset α) ×ˢ t
 = ∅
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
-/
theorem interedges_empty_left (t : Finset β) : interedges r ∅ t = ∅ := by
  rw [interedges, Finset.empty_product, filter_empty]
/-
**Rel.interedges_mono** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：interedges_mono (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) : interedges r
 s₂ t₂ subseteq interedges r s₁ t₁
参数：hs : s₂ subseteq s₁；ht : t₂ subseteq t₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem interedges_mono (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) : interedges r s₂ t₂ ⊆ interedges r s₁ t₁ :=
  fun x ↦ by
    simp_rw [mem_interedges_iff]
    exact fun h ↦ ⟨hs h.1, ht h.2.1, h.2.2⟩

variable (r)
/-
**Rel.card_interedges_add_card_interedges_compl** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：card_interedges_add_card_interedges_compl (s : Finset α) (t : Finset β) : 
#(interedges r s t) + #(interedges (fun x y => ¬r x y) s t) = #s * #t
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Rel.interedges.eq_1`：∀ {α : Type u_4} {β : Type u_5} (r : α → β → Prop) 
[inst : (a : α) → DecidablePred (r a)] (s : Finset α) (t : Finset β),   Rel.inte
redges r …
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_filter`：disjoint_filter {s : Finset α} {p q : α -> Prop}
 [DecidablePred p] [DecidablePred q] : Disjoint (s.filter p) (s.filter q) ↔ fora
ll x in s, p…
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s
-/
theorem card_interedges_add_card_interedges_compl (s : Finset α) (t : Finset β) :
    #(interedges r s t) + #(interedges (fun x y ↦ ¬r x y) s t) = #s * #t := by
  classical
  rw [← card_product, interedges, interedges, ← card_union_of_disjoint, filter_union_filter_not_eq]
  exact disjoint_filter.2 fun _ _ ↦ Classical.not_not.2
/-
**Rel.interedges_disjoint_left** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：interedges_disjoint_left {s s' : Finset α} (hs : Disjoint s s') (t : Finse
t β) : Disjoint (interedges r s t) (interedges r s' t)
参数：hs : Disjoint s s'；t : Finset β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Rel.mem_interedges_iff`：mem_interedges_iff {x : α × β} : x in interedges
 r s t ↔ x.1 in s ∧ x.2 in t ∧ r x.1 x.2
-/
theorem interedges_disjoint_left {s s' : Finset α} (hs : Disjoint s s') (t : Finset β) :
    Disjoint (interedges r s t) (interedges r s' t) := by
  rw [Finset.disjoint_left] at hs ⊢
  intro _ hx hy
  rw [mem_interedges_iff] at hx hy
  exact hs hx.1 hy.1
/-
**Rel.interedges_disjoint_right** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：interedges_disjoint_right (s : Finset α) {t t' : Finset β} (ht : Disjoint 
t t') : Disjoint (interedges r s t) (interedges r s t')
参数：s : Finset α；ht : Disjoint t t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Rel.mem_interedges_iff`：mem_interedges_iff {x : α × β} : x in interedges
 r s t ↔ x.1 in s ∧ x.2 in t ∧ r x.1 x.2
-/
theorem interedges_disjoint_right (s : Finset α) {t t' : Finset β} (ht : Disjoint t t') :
    Disjoint (interedges r s t) (interedges r s t') := by
  rw [Finset.disjoint_left] at ht ⊢
  intro _ hx hy
  rw [mem_interedges_iff] at hx hy
  exact ht hx.2.1 hy.2.1

section DecidableEq

variable [DecidableEq α] [DecidableEq β]

/-
**Rel.interedges_eq_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Rel`。
形式化陈述：interedges_eq_biUnion : interedges r s t = s.biUnion fun x => {y in t | r 
x y}.map ⟨(x, ·), Prod.mk_right_injective x⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma interedges_eq_biUnion :
    interedges r s t =
      s.biUnion fun x ↦ {y ∈ t | r x y}.map ⟨(x, ·), Prod.mk_right_injective x⟩ := by
  ext ⟨x, y⟩; simp [mem_interedges_iff]
/-
**Rel.interedges_biUnion_left** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：interedges_biUnion_left (s : Finset ι) (t : Finset β) (f : ι -> Finset α) 
: interedges r (s.biUnion f) t = s.biUnion fun a => interedges r (f a) t
参数：s : Finset ι；t : Finset β；f : ι -> Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem interedges_biUnion_left (s : Finset ι) (t : Finset β) (f : ι → Finset α) :
    interedges r (s.biUnion f) t = s.biUnion fun a ↦ interedges r (f a) t := by
  ext
  simp only [mem_biUnion, mem_interedges_iff, exists_and_right, ← and_assoc]
/-
**Rel.interedges_biUnion_right** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：interedges_biUnion_right (s : Finset α) (t : Finset ι) (f : ι -> Finset β)
 : interedges r s (t.biUnion f) = t.biUnion fun b => interedges r s (f b)
参数：s : Finset α；t : Finset ι；f : ι -> Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem interedges_biUnion_right (s : Finset α) (t : Finset ι) (f : ι → Finset β) :
    interedges r s (t.biUnion f) = t.biUnion fun b ↦ interedges r s (f b) := by
  ext a
  simp only [mem_interedges_iff, mem_biUnion]
  exact ⟨fun ⟨x₁, ⟨x₂, x₃, x₄⟩, x₅⟩ ↦ ⟨x₂, x₃, x₁, x₄, x₅⟩,
    fun ⟨x₂, x₃, x₁, x₄, x₅⟩ ↦ ⟨x₁, ⟨x₂, x₃, x₄⟩, x₅⟩⟩
/-
**Rel.interedges_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：interedges_biUnion (s : Finset ι) (t : Finset κ) (f : ι -> Finset α) (g : 
κ -> Finset β) : interedges r (s.biUnion f) (t.biUnion g) = (s ×ˢ t).biUnion fun
 ab => interedges r (f ab.1) (g ab.2)
参数：s : Finset ι；t : Finset κ；f : ι -> Finset α；g : κ -> Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.product_biUnion`：product_biUnion [DecidableEq γ] (s : Finset α) (
t : Finset β) (f : α × β -> Finset γ) : (s ×ˢ t).biUnion f = s.biUnion fun a => 
t.biUnion fu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rel.interedges_biUnion_left`：interedges_biUnion_left (s : Finset ι) (t :
 Finset β) (f : ι -> Finset α) : interedges r (s.biUnion f) t = s.biUnion fun a 
=> interedges r (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Rel.interedges_biUnion_right`：interedges_biUnion_right (s : Finset α) (t
 : Finset ι) (f : ι -> Finset β) : interedges r s (t.biUnion f) = t.biUnion fun 
b => interedges r …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem interedges_biUnion (s : Finset ι) (t : Finset κ) (f : ι → Finset α) (g : κ → Finset β) :
    interedges r (s.biUnion f) (t.biUnion g) =
      (s ×ˢ t).biUnion fun ab ↦ interedges r (f ab.1) (g ab.2) := by
  simp_rw [product_biUnion, interedges_biUnion_left, interedges_biUnion_right]

end DecidableEq

/-
**Rel.card_interedges_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：card_interedges_le_mul (s : Finset α) (t : Finset β) : #(interedges r s t)
 <= #s * #t
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_filter_le`：card_filter_le (s : Finset α) (p : α -> Prop) [De
cidablePred p] : #(s.filter p) <= #s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
-/
theorem card_interedges_le_mul (s : Finset α) (t : Finset β) :
    #(interedges r s t) ≤ #s * #t :=
  (card_filter_le _ _).trans (card_product _ _).le
/-
**Rel.edgeDensity_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：edgeDensity_nonneg (s : Finset α) (t : Finset β) : 0 <= edgeDensity r s t
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem edgeDensity_nonneg (s : Finset α) (t : Finset β) : 0 ≤ edgeDensity r s t := by
  apply div_nonneg <;> exact mod_cast Nat.zero_le _
/-
**Rel.edgeDensity_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：edgeDensity_le_one (s : Finset α) (t : Finset β) : edgeDensity r s t <= 1
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Rel.card_interedges_le_mul`：card_interedges_le_mul (s : Finset α) (t : F
inset β) : #(interedges r s t) <= #s * #t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem edgeDensity_le_one (s : Finset α) (t : Finset β) : edgeDensity r s t ≤ 1 := by
  apply div_le_one_of_le₀
  · exact mod_cast card_interedges_le_mul r s t
  · exact mod_cast Nat.zero_le _
/-
**Rel.edgeDensity_add_edgeDensity_compl** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：edgeDensity_add_edgeDensity_compl (hs : s.Nonempty) (ht : t.Nonempty) : ed
geDensity r s t + edgeDensity (fun x y => ¬r x y) s t = 1
参数：hs : s.Nonempty；ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rel.edgeDensity.eq_1`：∀ {α : Type u_4} {β : Type u_5} (r : α → β → Prop)
 [inst : (a : α) → DecidablePred (r a)] (s : Finset α) (t : Finset β),   Rel.edg
eDensity r…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用引理 `div_eq_one_iff_eq`：div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rel.card_interedges_add_card_interedges_compl`：card_interedges_add_card_
interedges_compl (s : Finset α) (t : Finset β) : #(interedges r s t) + #(intered
ges (fun x y => ¬r x y) s t) = #s *…
-/
theorem edgeDensity_add_edgeDensity_compl (hs : s.Nonempty) (ht : t.Nonempty) :
    edgeDensity r s t + edgeDensity (fun x y ↦ ¬r x y) s t = 1 := by
  rw [edgeDensity, edgeDensity, ← add_div, div_eq_one_iff_eq]
  · exact mod_cast card_interedges_add_card_interedges_compl r s t
  · exact mod_cast (mul_pos hs.card_pos ht.card_pos).ne'

@[simp]
/-
**Rel.edgeDensity_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：edgeDensity_empty_left (t : Finset β) : edgeDensity r ∅ t = 0
参数：t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rel.edgeDensity.eq_1`：∀ {α : Type u_4} {β : Type u_5} (r : α → β → Prop)
 [inst : (a : α) → DecidablePred (r a)] (s : Finset α) (t : Finset β),   Rel.edg
eDensity r…
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
-/
theorem edgeDensity_empty_left (t : Finset β) : edgeDensity r ∅ t = 0 := by
  rw [edgeDensity, Finset.card_empty, Nat.cast_zero, zero_mul, div_zero]

@[simp]
/-
**Rel.edgeDensity_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：edgeDensity_empty_right (s : Finset α) : edgeDensity r s ∅ = 0
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rel.edgeDensity.eq_1`：∀ {α : Type u_4} {β : Type u_5} (r : α → β → Prop)
 [inst : (a : α) → DecidablePred (r a)] (s : Finset α) (t : Finset β),   Rel.edg
eDensity r…
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
-/
theorem edgeDensity_empty_right (s : Finset α) : edgeDensity r s ∅ = 0 := by
  rw [edgeDensity, Finset.card_empty, Nat.cast_zero, mul_zero, div_zero]
/-
**Rel.card_interedges_finpartition_left** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：card_interedges_finpartition_left [DecidableEq α] (P : Finpartition s) (t 
: Finset β) : #(interedges r s t) = ∑ a in P.parts, #(interedges r a t)
参数：P : Finpartition s；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rel.interedges.congr_simp`：∀ {α : Type u_4} {β : Type u_5} (r r_1 : α → 
β → Prop),   r = r_1 →     ∀ {inst : (a : α) → DecidablePred (r a)} [inst_1 : (a
 : α) → Decidab…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.biUnion_parts`：biUnion_parts : P.parts.biUnion id = s
· 使用定理 `Rel.interedges_biUnion_left`：interedges_biUnion_left (s : Finset ι) (t :
 Finset β) (f : ι -> Finset α) : interedges r (s.biUnion f) t = s.biUnion fun a 
=> interedges r (…
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `Rel.interedges_disjoint_left`：interedges_disjoint_left {s s' : Finset α}
 (hs : Disjoint s s') (t : Finset β) : Disjoint (interedges r s t) (interedges r
 s' t)
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
-/
theorem card_interedges_finpartition_left [DecidableEq α] (P : Finpartition s) (t : Finset β) :
    #(interedges r s t) = ∑ a ∈ P.parts, #(interedges r a t) := by
  classical
  simp_rw [← P.biUnion_parts, interedges_biUnion_left, id]
  rw [card_biUnion]
  exact fun x hx y hy h ↦ interedges_disjoint_left r (P.disjoint hx hy h) _
/-
**Rel.card_interedges_finpartition_right** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：card_interedges_finpartition_right [DecidableEq β] (s : Finset α) (P : Fin
partition t) : #(interedges r s t) = ∑ b in P.parts, #(interedges r s b)
参数：s : Finset α；P : Finpartition t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rel.interedges.congr_simp`：∀ {α : Type u_4} {β : Type u_5} (r r_1 : α → 
β → Prop),   r = r_1 →     ∀ {inst : (a : α) → DecidablePred (r a)} [inst_1 : (a
 : α) → Decidab…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.biUnion_parts`：biUnion_parts : P.parts.biUnion id = s
· 使用定理 `Rel.interedges_biUnion_right`：interedges_biUnion_right (s : Finset α) (t
 : Finset ι) (f : ι -> Finset β) : interedges r s (t.biUnion f) = t.biUnion fun 
b => interedges r …
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `Rel.interedges_disjoint_right`：interedges_disjoint_right (s : Finset α) 
{t t' : Finset β} (ht : Disjoint t t') : Disjoint (interedges r s t) (interedges
 r s t')
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
-/
theorem card_interedges_finpartition_right [DecidableEq β] (s : Finset α) (P : Finpartition t) :
    #(interedges r s t) = ∑ b ∈ P.parts, #(interedges r s b) := by
  classical
  simp_rw [← P.biUnion_parts, interedges_biUnion_right, id]
  rw [card_biUnion]
  exact fun x hx y hy h ↦ interedges_disjoint_right r _ (P.disjoint hx hy h)
/-
**Rel.card_interedges_finpartition** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：card_interedges_finpartition [DecidableEq α] [DecidableEq β] (P : Finparti
tion s) (Q : Finpartition t) : #(interedges r s t) = ∑ ab in P.parts ×ˢ Q.parts,
 #(interedges r ab.1 ab.2)
参数：P : Finpartition s；Q : Finpartition t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rel.card_interedges_finpartition_left`：card_interedges_finpartition_left
 [DecidableEq α] (P : Finpartition s) (t : Finset β) : #(interedges r s t) = ∑ a
 in P.parts, #(interedges r…
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Rel.card_interedges_finpartition_right`：card_interedges_finpartition_rig
ht [DecidableEq β] (s : Finset α) (P : Finpartition t) : #(interedges r s t) = ∑
 b in P.parts, #(interedges …
-/
theorem card_interedges_finpartition [DecidableEq α] [DecidableEq β] (P : Finpartition s)
    (Q : Finpartition t) :
    #(interedges r s t) = ∑ ab ∈ P.parts ×ˢ Q.parts, #(interedges r ab.1 ab.2) := by
  rw [card_interedges_finpartition_left _ P, sum_product]
  congr; ext
  rw [card_interedges_finpartition_right]
/-
**Rel.mul_edgeDensity_le_edgeDensity** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：mul_edgeDensity_le_edgeDensity (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁)
 (hs₂ : s₂.Nonempty) (ht₂ : t₂.Nonempty) : (#s₂ : Rat) / #s₁ * (#t₂ / #t₁) * edg
eDensity r s₂ t₂ <= edgeDensity r s₁ t₁
参数：hs : s₂ subseteq s₁；ht : t₂ subseteq t₁；hs₂ : s₂.Nonempty；ht₂ : t₂.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Rel.edgeDensity.eq_1`：∀ {α : Type u_4} {β : Type u_5} (r : α → β → Prop)
 [inst : (a : α) → DecidablePred (r a)] (s : Finset α) (t : Finset β),   Rel.edg
eDensity r…
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `div_mul_div_cancel₀`：div_mul_div_cancel₀ (hb : b != 0) : a / b * (b / c)
 = a / c
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Rel.interedges_mono`：interedges_mono (hs : s₂ subseteq s₁) (ht : t₂ subs
eteq t₁) : interedges r s₂ t₂ subseteq interedges r s₁ t₁
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
-/
theorem mul_edgeDensity_le_edgeDensity (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hs₂ : s₂.Nonempty)
    (ht₂ : t₂.Nonempty) :
    (#s₂ : ℚ) / #s₁ * (#t₂ / #t₁) * edgeDensity r s₂ t₂ ≤ edgeDensity r s₁ t₁ := by
  have hst : (#s₂ : ℚ) * #t₂ ≠ 0 := by simp [hs₂.ne_empty, ht₂.ne_empty]
  rw [edgeDensity, edgeDensity, div_mul_div_comm, mul_comm, div_mul_div_cancel₀ hst]
  gcongr
  exact interedges_mono hs ht
/-
**Rel.edgeDensity_sub_edgeDensity_le_one_sub_mul** 是 Mathlib 中的一个定理，位于命名空间 `Rel`
。
形式化陈述：edgeDensity_sub_edgeDensity_le_one_sub_mul (hs : s₂ subseteq s₁) (ht : t₂ 
subseteq t₁) (hs₂ : s₂.Nonempty) (ht₂ : t₂.Nonempty) : edgeDensity r s₂ t₂ - edg
eDensity r s₁ t₁ <= 1 - #s₂ / #s₁ * (#t₂ / #t₁)
参数：hs : s₂ subseteq s₁；ht : t₂ subseteq t₁；hs₂ : s₂.Nonempty；ht₂ : t₂.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Rel.mul_edgeDensity_le_edgeDensity`：mul_edgeDensity_le_edgeDensity (hs :
 s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hs₂ : s₂.Nonempty) (ht₂ : t₂.Nonempty) :
 (#s₂ : Rat) / #s₁ * (#t…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用引理 `mul_le_one₀`：mul_le_one₀ [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (h
b : b <= 1) : a * b <= 1
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 33 条，此处仅展示前 30 条）
-/
theorem edgeDensity_sub_edgeDensity_le_one_sub_mul (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hs₂ : s₂.Nonempty)
    (ht₂ : t₂.Nonempty) :
    edgeDensity r s₂ t₂ - edgeDensity r s₁ t₁ ≤ 1 - #s₂ / #s₁ * (#t₂ / #t₁) := by
  refine (sub_le_sub_left (mul_edgeDensity_le_edgeDensity r hs ht hs₂ ht₂) _).trans ?_
  refine le_trans ?_ (mul_le_of_le_one_right ?_ (edgeDensity_le_one r s₂ t₂))
  · rw [sub_mul, one_mul]
  refine sub_nonneg_of_le (mul_le_one₀ ?_ ?_ ?_)
  · exact div_le_one_of_le₀ ((@Nat.cast_le ℚ).2 (card_le_card hs)) (Nat.cast_nonneg _)
  · apply div_nonneg <;> exact mod_cast Nat.zero_le _
  · exact div_le_one_of_le₀ ((@Nat.cast_le ℚ).2 (card_le_card ht)) (Nat.cast_nonneg _)
/-
**Rel.abs_edgeDensity_sub_edgeDensity_le_one_sub_mul** 是 Mathlib 中的一个定理，位于命名空间 `
Rel`。
形式化陈述：abs_edgeDensity_sub_edgeDensity_le_one_sub_mul (hs : s₂ subseteq s₁) (ht :
 t₂ subseteq t₁) (hs₂ : s₂.Nonempty) (ht₂ : t₂.Nonempty) : |edgeDensity r s₂ t₂ 
- edgeDensity r s₁ t₁| <= 1 - #s₂ / #s₁ * (#t₂ / #t₁)
参数：hs : s₂ subseteq s₁；ht : t₂ subseteq t₁；hs₂ : s₂.Nonempty；ht₂ : t₂.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c
· 使用定理 `Rel.edgeDensity_sub_edgeDensity_le_one_sub_mul`：edgeDensity_sub_edgeDens
ity_le_one_sub_mul (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hs₂ : s₂.Nonempt
y) (ht₂ : t₂.Nonempty) : edgeDensity…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Rel.edgeDensity_add_edgeDensity_compl`：edgeDensity_add_edgeDensity_compl
 (hs : s.Nonempty) (ht : t.Nonempty) : edgeDensity r s t + edgeDensity (fun x y 
=> ¬r x y) s t = 1
· 使用定理 `Finset.Nonempty.mono`：∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → s.Nonem
pty → t.Nonempty
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
-/
theorem abs_edgeDensity_sub_edgeDensity_le_one_sub_mul (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁)
    (hs₂ : s₂.Nonempty) (ht₂ : t₂.Nonempty) :
    |edgeDensity r s₂ t₂ - edgeDensity r s₁ t₁| ≤ 1 - #s₂ / #s₁ * (#t₂ / #t₁) := by
  refine abs_sub_le_iff.2 ⟨edgeDensity_sub_edgeDensity_le_one_sub_mul r hs ht hs₂ ht₂, ?_⟩
  rw [← add_sub_cancel_right (edgeDensity r s₁ t₁) (edgeDensity (fun x y ↦ ¬r x y) s₁ t₁),
    ← add_sub_cancel_right (edgeDensity r s₂ t₂) (edgeDensity (fun x y ↦ ¬r x y) s₂ t₂),
    edgeDensity_add_edgeDensity_compl _ (hs₂.mono hs) (ht₂.mono ht),
    edgeDensity_add_edgeDensity_compl _ hs₂ ht₂, sub_sub_sub_cancel_left]
  exact edgeDensity_sub_edgeDensity_le_one_sub_mul _ hs ht hs₂ ht₂
/-
**Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq** 是 Mathlib 中的一个定理，位于命名空
间 `Rel`。
形式化陈述：abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq (hs : s₂ subseteq s₁) (h
t : t₂ subseteq t₁) (hδ₀ : 0 <= δ) (hδ₁ : δ < 1) (hs₂ : (1 - δ) * #s₁ <= #s₂) (h
t₂ : (1 - δ) * #t₁ <= #t₂) : |(edgeDensity r s₂ t₂ : 𝕜) - edgeDensity r s₁ t₁| <
= 2 * δ - δ ^ 2
参数：hs : s₂ subseteq s₁；ht : t₂ subseteq t₁；hδ₀ : 0 <= δ；hδ₁ : δ < 1；hs₂ : (1 - δ
) * #s₁ <= #s₂；ht₂ : (1 - δ) * #t₁ <= #t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rel.interedges_empty_left`：interedges_empty_left (t : Finset β) : intere
dges r ∅ t = ∅
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `nonpos_of_mul_nonpos_right`：nonpos_of_mul_nonpos_right [PosMulStrictMono
 R] (h : a * b <= 0) (ha : 0 < a) : b <= 0
（共 104 条，此处仅展示前 30 条）
-/
theorem abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hs₂ : (1 - δ) * #s₁ ≤ #s₂)
    (ht₂ : (1 - δ) * #t₁ ≤ #t₂) :
    |(edgeDensity r s₂ t₂ : 𝕜) - edgeDensity r s₁ t₁| ≤ 2 * δ - δ ^ 2 := by
  have hδ' : 0 ≤ 2 * δ - δ ^ 2 := by
    rw [sub_nonneg, sq]
    gcongr
    exact hδ₁.le.trans (by simp)
  rw [← sub_pos] at hδ₁
  obtain rfl | hs₂' := s₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zero] at hs₂
    simpa [edgeDensity, (nonpos_of_mul_nonpos_right hs₂ hδ₁).antisymm (Nat.cast_nonneg _)] using hδ'
  obtain rfl | ht₂' := t₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zero] at ht₂
    simpa [edgeDensity, (nonpos_of_mul_nonpos_right ht₂ hδ₁).antisymm (Nat.cast_nonneg _)] using hδ'
  have hr : 2 * δ - δ ^ 2 = 1 - (1 - δ) * (1 - δ) := by ring
  rw [hr]
  norm_cast
  refine
    (Rat.cast_le.2 <| abs_edgeDensity_sub_edgeDensity_le_one_sub_mul r hs ht hs₂' ht₂').trans ?_
  push_cast
  have h₁ := hs₂'.mono hs
  have h₂ := ht₂'.mono ht
  gcongr
  · refine (le_div_iff₀ ?_).2 hs₂
    exact mod_cast h₁.card_pos
  · refine (le_div_iff₀ ?_).2 ht₂
    exact mod_cast h₂.card_pos

/-- If `s₂ ⊆ s₁`, `t₂ ⊆ t₁` and they take up all but a `δ`-proportion, then the difference in edge
densities is at most `2 * δ`. -/
/-
**Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul** 是 Mathlib 中的一个定理，位于命名空间 `Rel`
。
形式化陈述：abs_edgeDensity_sub_edgeDensity_le_two_mul (hs : s₂ subseteq s₁) (ht : t₂ 
subseteq t₁) (hδ : 0 <= δ) (hscard : (1 - δ) * #s₁ <= #s₂) (htcard : (1 - δ) * #
t₁ <= #t₂) : |(edgeDensity r s₂ t₂ : 𝕜) - edgeDensity r s₁ t₁| <= 2 * δ
参数：hs : s₂ subseteq s₁；ht : t₂ subseteq t₁；hδ : 0 <= δ；hscard : (1 - δ) * #s₁ <=
 #s₂；htcard : (1 - δ) * #t₁ <= #t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq`：abs_edgeDensity_s
ub_edgeDensity_le_two_mul_sub_sq (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hδ
₀ : 0 <= δ) (hδ₁ : δ < 1) (hs₂ : (1 - δ) * …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_le_self_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] (a : α) {b : α}, a - b ≤ a ↔ 0 ≤ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `abs_sub`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder 
G] [IsOrderedAddMonoid G] (a b : G), |a - b| ≤ |a| + |b|
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rel.edgeDensity_nonneg`：edgeDensity_nonneg (s : Finset α) (t : Finset β)
 : 0 <= edgeDensity r s t
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rel.edgeDensity_le_one`：edgeDensity_le_one (s : Finset α) (t : Finset β)
 : edgeDensity r s t <= 1

--- 原说明 ---
If `s₂ ⊆ s₁`, `t₂ ⊆ t₁` and they take up all but a `δ`-proportion, then the diff
erence in edge
densities is at most `2 * δ`.
-/
theorem abs_edgeDensity_sub_edgeDensity_le_two_mul (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hδ : 0 ≤ δ)
    (hscard : (1 - δ) * #s₁ ≤ #s₂) (htcard : (1 - δ) * #t₁ ≤ #t₂) :
    |(edgeDensity r s₂ t₂ : 𝕜) - edgeDensity r s₁ t₁| ≤ 2 * δ := by
  rcases lt_or_ge δ 1 with h | h
  · exact (abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq r hs ht hδ h hscard htcard).trans
      ((sub_le_self_iff _).2 <| sq_nonneg δ)
  rw [two_mul]
  refine (abs_sub _ _).trans (add_le_add (le_trans ?_ h) (le_trans ?_ h)) <;>
    · rw [abs_of_nonneg]
      · exact mod_cast edgeDensity_le_one r _ _
      · exact mod_cast edgeDensity_nonneg r _ _

end Asymmetric

section Symmetric

variable {r : α → α → Prop} [DecidableRel r] {s t : Finset α} {a b : α}

@[simp]
/-
**Rel.swap_mem_interedges_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：swap_mem_interedges_iff [Std.Symm r] {x : α × α} : x.swap in interedges r 
s t ↔ x in interedges r t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rel.mem_interedges_iff`：mem_interedges_iff {x : α × β} : x in interedges
 r s t ↔ x.1 in s ∧ x.2 in t ∧ r x.1 x.2
· 使用定理 `Std.Symm.iff`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Symm r] (x y : α)
, r x y ↔ r y x
· 使用定理 `and_left_comm`：∀ {a b c : Prop}, a ∧ b ∧ c ↔ b ∧ a ∧ c
-/
theorem swap_mem_interedges_iff [Std.Symm r] {x : α × α} :
    x.swap ∈ interedges r s t ↔ x ∈ interedges r t s := by
  rw [mem_interedges_iff, mem_interedges_iff, Std.Symm.iff (r := r)]
  exact and_left_comm
/-
**Rel.mk_mem_interedges_comm** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：mk_mem_interedges_comm [Std.Symm r] : (a, b) in interedges r s t ↔ (b, a) 
in interedges r t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.swap_mem_interedges_iff`：swap_mem_interedges_iff [Std.Symm r] {x : α
 × α} : x.swap in interedges r s t ↔ x in interedges r t s
-/
theorem mk_mem_interedges_comm [Std.Symm r] :
    (a, b) ∈ interedges r s t ↔ (b, a) ∈ interedges r t s :=
  swap_mem_interedges_iff (x := (b, a))
/-
**Rel.card_interedges_comm** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：card_interedges_comm [Std.Symm r] (s t : Finset α) : #(interedges r s t) =
 #(interedges r t s)
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_bij`：card_bij (i : forall a in s, β) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rel.swap_mem_interedges_iff`：swap_mem_interedges_iff [Std.Symm r] {x : α
 × α} : x.swap in interedges r s t ↔ x in interedges r t s
· 使用定理 `Prod.swap_injective`：swap_injective : Function.Injective (@swap α β)
· 使用定理 `Prod.swap_swap`：∀ {α : Type u_1} {β : Type u_2} (x : α × β), x.swap.swap
 = x
-/
theorem card_interedges_comm [Std.Symm r] (s t : Finset α) :
    #(interedges r s t) = #(interedges r t s) :=
  Finset.card_bij (fun (x : α × α) _ ↦ x.swap) (fun _ ↦ swap_mem_interedges_iff.mpr)
    (fun _ _ _ _ h ↦ Prod.swap_injective h) fun x h ↦
    ⟨x.swap, swap_mem_interedges_iff.mpr h, x.swap_swap⟩
/-
**Rel.edgeDensity_comm** 是 Mathlib 中的一个定理，位于命名空间 `Rel`。
形式化陈述：edgeDensity_comm [Std.Symm r] (s t : Finset α) : edgeDensity r s t = edgeD
ensity r t s
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rel.edgeDensity.eq_1`：∀ {α : Type u_4} {β : Type u_5} (r : α → β → Prop)
 [inst : (a : α) → DecidablePred (r a)] (s : Finset α) (t : Finset β),   Rel.edg
eDensity r…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Rel.card_interedges_comm`：card_interedges_comm [Std.Symm r] (s t : Finse
t α) : #(interedges r s t) = #(interedges r t s)
-/
theorem edgeDensity_comm [Std.Symm r] (s t : Finset α) :
    edgeDensity r s t = edgeDensity r t s := by
  rw [edgeDensity, mul_comm, card_interedges_comm, edgeDensity]

end Symmetric

end Rel

open Rel

/-! ### Density of a graph -/


namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] {s s₁ s₂ t t₁ t₂ : Finset α} {a b : α}

/-- Finset of edges of a relation between two finsets of vertices. -/
/-
**SimpleGraph.interedges** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：interedges (s t : Finset α) : Finset (α × α)
参数：s t : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finset of edges of a relation between two finsets of vertices.
-/
def interedges (s t : Finset α) : Finset (α × α) :=
  Rel.interedges G.Adj s t

/-- Density of edges of a graph between two finsets of vertices. -/
/-
**SimpleGraph.edgeDensity** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：edgeDensity : Finset α -> Finset α -> Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Density of edges of a graph between two finsets of vertices.
-/
def edgeDensity : Finset α → Finset α → ℚ :=
  Rel.edgeDensity G.Adj
/-
**SimpleGraph.interedges_def** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：interedges_def (s t : Finset α) : G.interedges s t = {e in s ×ˢ t | G.Adj 
e.1 e.2}
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma interedges_def (s t : Finset α) : G.interedges s t = {e ∈ s ×ˢ t | G.Adj e.1 e.2} := rfl
/-
**SimpleGraph.edgeDensity_def** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeDensity_def (s t : Finset α) : G.edgeDensity s t = #(G.interedges s t)
 / (#s * #t)
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edgeDensity_def (s t : Finset α) : G.edgeDensity s t = #(G.interedges s t) / (#s * #t) := rfl
/-
**SimpleGraph.card_interedges_div_card** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_interedges_div_card (s t : Finset α) : (#(G.interedges s t) : Rat) / 
(#s * #t) = G.edgeDensity s t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_interedges_div_card (s t : Finset α) :
    (#(G.interedges s t) : ℚ) / (#s * #t) = G.edgeDensity s t :=
  rfl
/-
**SimpleGraph.mem_interedges_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_interedges_iff {x : α × α} : x in G.interedges s t ↔ x.1 in s ∧ x.2 in
 t ∧ G.Adj x.1 x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.mem_interedges_iff`：mem_interedges_iff {x : α × β} : x in interedges
 r s t ↔ x.1 in s ∧ x.2 in t ∧ r x.1 x.2
-/
theorem mem_interedges_iff {x : α × α} : x ∈ G.interedges s t ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ G.Adj x.1 x.2 :=
  Rel.mem_interedges_iff
/-
**SimpleGraph.mk_mem_interedges_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mk_mem_interedges_iff : (a, b) in G.interedges s t ↔ a in s ∧ b in t ∧ G.A
dj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.mk_mem_interedges_iff`：mk_mem_interedges_iff : (a, b) in interedges 
r s t ↔ a in s ∧ b in t ∧ r a b
-/
theorem mk_mem_interedges_iff : (a, b) ∈ G.interedges s t ↔ a ∈ s ∧ b ∈ t ∧ G.Adj a b :=
  Rel.mk_mem_interedges_iff

@[simp]
/-
**SimpleGraph.interedges_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：interedges_empty_left (t : Finset α) : G.interedges ∅ t = ∅
参数：t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.interedges_empty_left`：interedges_empty_left (t : Finset β) : intere
dges r ∅ t = ∅
-/
theorem interedges_empty_left (t : Finset α) : G.interedges ∅ t = ∅ :=
  Rel.interedges_empty_left _
/-
**SimpleGraph.interedges_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：interedges_mono : s₂ subseteq s₁ -> t₂ subseteq t₁ -> G.interedges s₂ t₂ s
ubseteq G.interedges s₁ t₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.interedges_mono`：interedges_mono (hs : s₂ subseteq s₁) (ht : t₂ subs
eteq t₁) : interedges r s₂ t₂ subseteq interedges r s₁ t₁
-/
theorem interedges_mono : s₂ ⊆ s₁ → t₂ ⊆ t₁ → G.interedges s₂ t₂ ⊆ G.interedges s₁ t₁ :=
  Rel.interedges_mono
/-
**SimpleGraph.interedges_disjoint_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：interedges_disjoint_left (hs : Disjoint s₁ s₂) (t : Finset α) : Disjoint (
G.interedges s₁ t) (G.interedges s₂ t)
参数：hs : Disjoint s₁ s₂；t : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.interedges_disjoint_left`：interedges_disjoint_left {s s' : Finset α}
 (hs : Disjoint s s') (t : Finset β) : Disjoint (interedges r s t) (interedges r
 s' t)
-/
theorem interedges_disjoint_left (hs : Disjoint s₁ s₂) (t : Finset α) :
    Disjoint (G.interedges s₁ t) (G.interedges s₂ t) :=
  Rel.interedges_disjoint_left _ hs _
/-
**SimpleGraph.interedges_disjoint_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：interedges_disjoint_right (s : Finset α) (ht : Disjoint t₁ t₂) : Disjoint 
(G.interedges s t₁) (G.interedges s t₂)
参数：s : Finset α；ht : Disjoint t₁ t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.interedges_disjoint_right`：interedges_disjoint_right (s : Finset α) 
{t t' : Finset β} (ht : Disjoint t t') : Disjoint (interedges r s t) (interedges
 r s t')
-/
theorem interedges_disjoint_right (s : Finset α) (ht : Disjoint t₁ t₂) :
    Disjoint (G.interedges s t₁) (G.interedges s t₂) :=
  Rel.interedges_disjoint_right _ _ ht

section DecidableEq

variable [DecidableEq α]

/-
**SimpleGraph.interedges_biUnion_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：interedges_biUnion_left (s : Finset ι) (t : Finset α) (f : ι -> Finset α) 
: G.interedges (s.biUnion f) t = s.biUnion fun a => G.interedges (f a) t
参数：s : Finset ι；t : Finset α；f : ι -> Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.interedges_biUnion_left`：interedges_biUnion_left (s : Finset ι) (t :
 Finset β) (f : ι -> Finset α) : interedges r (s.biUnion f) t = s.biUnion fun a 
=> interedges r (…
-/
theorem interedges_biUnion_left (s : Finset ι) (t : Finset α) (f : ι → Finset α) :
    G.interedges (s.biUnion f) t = s.biUnion fun a ↦ G.interedges (f a) t :=
  Rel.interedges_biUnion_left _ _ _ _
/-
**SimpleGraph.interedges_biUnion_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：interedges_biUnion_right (s : Finset α) (t : Finset ι) (f : ι -> Finset α)
 : G.interedges s (t.biUnion f) = t.biUnion fun b => G.interedges s (f b)
参数：s : Finset α；t : Finset ι；f : ι -> Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.interedges_biUnion_right`：interedges_biUnion_right (s : Finset α) (t
 : Finset ι) (f : ι -> Finset β) : interedges r s (t.biUnion f) = t.biUnion fun 
b => interedges r …
-/
theorem interedges_biUnion_right (s : Finset α) (t : Finset ι) (f : ι → Finset α) :
    G.interedges s (t.biUnion f) = t.biUnion fun b ↦ G.interedges s (f b) :=
  Rel.interedges_biUnion_right _ _ _ _
/-
**SimpleGraph.interedges_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：interedges_biUnion (s : Finset ι) (t : Finset κ) (f : ι -> Finset α) (g : 
κ -> Finset α) : G.interedges (s.biUnion f) (t.biUnion g) = (s ×ˢ t).biUnion fun
 ab => G.interedges (f ab.1) (g ab.2)
参数：s : Finset ι；t : Finset κ；f : ι -> Finset α；g : κ -> Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.interedges_biUnion`：interedges_biUnion (s : Finset ι) (t : Finset κ)
 (f : ι -> Finset α) (g : κ -> Finset β) : interedges r (s.biUnion f) (t.biUnion
 g) = (s ×ˢ …
-/
theorem interedges_biUnion (s : Finset ι) (t : Finset κ) (f : ι → Finset α) (g : κ → Finset α) :
    G.interedges (s.biUnion f) (t.biUnion g) =
      (s ×ˢ t).biUnion fun ab ↦ G.interedges (f ab.1) (g ab.2) :=
  Rel.interedges_biUnion _ _ _ _ _
/-
**SimpleGraph.card_interedges_add_card_interedges_compl** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph`。
形式化陈述：card_interedges_add_card_interedges_compl (h : Disjoint s t) : #(G.intered
ges s t) + #(Gᶜ.interedges s t) = #s * #t
参数：h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用引理 `SimpleGraph.interedges_def`：interedges_def (s t : Finset α) : G.interedg
es s t = {e in s ×ˢ t | G.Adj e.1 e.2}
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `SimpleGraph.compl_adj`：compl_adj (G : SimpleGraph V) (v w : V) : Gᶜ.Adj 
v w ↔ v != w ∧ ¬G.Adj v w
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Disjoint.forall_ne_finset`：∀ {α : Type u_2} {s t : Finset α} {a b : α}, 
Disjoint s t → a ∈ s → b ∈ t → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_filter`：disjoint_filter {s : Finset α} {p q : α -> Prop}
 [DecidablePred p] [DecidablePred q] : Disjoint (s.filter p) (s.filter q) ↔ fora
ll x in s, p…
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s
-/
theorem card_interedges_add_card_interedges_compl (h : Disjoint s t) :
    #(G.interedges s t) + #(Gᶜ.interedges s t) = #s * #t := by
  rw [← card_product, interedges_def, interedges_def]
  have : {e ∈ s ×ˢ t | Gᶜ.Adj e.1 e.2} = {e ∈ s ×ˢ t | ¬G.Adj e.1 e.2} := by
    refine filter_congr fun x hx ↦ ?_
    rw [mem_product] at hx
    rw [compl_adj, and_iff_right (h.forall_ne_finset hx.1 hx.2)]
  rw [this, ← card_union_of_disjoint, filter_union_filter_not_eq]
  exact disjoint_filter.2 fun _ _ ↦ Classical.not_not.2
/-
**SimpleGraph.edgeDensity_add_edgeDensity_compl** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：edgeDensity_add_edgeDensity_compl (hs : s.Nonempty) (ht : t.Nonempty) (h :
 Disjoint s t) : G.edgeDensity s t + Gᶜ.edgeDensity s t = 1
参数：hs : s.Nonempty；ht : t.Nonempty；h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.edgeDensity_def`：edgeDensity_def (s t : Finset α) : G.edgeDe
nsity s t = #(G.interedges s t) / (#s * #t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用引理 `div_eq_one_iff_eq`：div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.card_interedges_add_card_interedges_compl`：card_interedges_a
dd_card_interedges_compl (h : Disjoint s t) : #(G.interedges s t) + #(Gᶜ.intered
ges s t) = #s * #t
-/
theorem edgeDensity_add_edgeDensity_compl (hs : s.Nonempty) (ht : t.Nonempty) (h : Disjoint s t) :
    G.edgeDensity s t + Gᶜ.edgeDensity s t = 1 := by
  rw [edgeDensity_def, edgeDensity_def, ← add_div, div_eq_one_iff_eq]
  · exact mod_cast card_interedges_add_card_interedges_compl _ h
  · positivity

end DecidableEq

/-
**SimpleGraph.card_interedges_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_interedges_le_mul (s t : Finset α) : #(G.interedges s t) <= #s * #t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.card_interedges_le_mul`：card_interedges_le_mul (s : Finset α) (t : F
inset β) : #(interedges r s t) <= #s * #t
-/
theorem card_interedges_le_mul (s t : Finset α) : #(G.interedges s t) ≤ #s * #t :=
  Rel.card_interedges_le_mul _ _ _
/-
**SimpleGraph.edgeDensity_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeDensity_nonneg (s t : Finset α) : 0 <= G.edgeDensity s t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.edgeDensity_nonneg`：edgeDensity_nonneg (s : Finset α) (t : Finset β)
 : 0 <= edgeDensity r s t
-/
theorem edgeDensity_nonneg (s t : Finset α) : 0 ≤ G.edgeDensity s t :=
  Rel.edgeDensity_nonneg _ _ _
/-
**SimpleGraph.edgeDensity_le_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeDensity_le_one (s t : Finset α) : G.edgeDensity s t <= 1
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.edgeDensity_le_one`：edgeDensity_le_one (s : Finset α) (t : Finset β)
 : edgeDensity r s t <= 1
-/
theorem edgeDensity_le_one (s t : Finset α) : G.edgeDensity s t ≤ 1 :=
  Rel.edgeDensity_le_one _ _ _

@[simp]
/-
**SimpleGraph.edgeDensity_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeDensity_empty_left (t : Finset α) : G.edgeDensity ∅ t = 0
参数：t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.edgeDensity_empty_left`：edgeDensity_empty_left (t : Finset β) : edge
Density r ∅ t = 0
-/
theorem edgeDensity_empty_left (t : Finset α) : G.edgeDensity ∅ t = 0 :=
  Rel.edgeDensity_empty_left _ _

@[simp]
/-
**SimpleGraph.edgeDensity_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeDensity_empty_right (s : Finset α) : G.edgeDensity s ∅ = 0
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rel.edgeDensity_empty_right`：edgeDensity_empty_right (s : Finset α) : ed
geDensity r s ∅ = 0
-/
theorem edgeDensity_empty_right (s : Finset α) : G.edgeDensity s ∅ = 0 :=
  Rel.edgeDensity_empty_right _ _

@[simp]
/-
**SimpleGraph.swap_mem_interedges_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：swap_mem_interedges_iff {x : α × α} : x.swap in G.interedges s t ↔ x in G.
interedges t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
· 使用定理 `Rel.swap_mem_interedges_iff`：swap_mem_interedges_iff [Std.Symm r] {x : α
 × α} : x.swap in interedges r s t ↔ x in interedges r t s
-/
theorem swap_mem_interedges_iff {x : α × α} : x.swap ∈ G.interedges s t ↔ x ∈ G.interedges t s :=
  have := G.symm
  Rel.swap_mem_interedges_iff
/-
**SimpleGraph.mk_mem_interedges_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mk_mem_interedges_comm : (a, b) in G.interedges s t ↔ (b, a) in G.interedg
es t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
· 使用定理 `Rel.mk_mem_interedges_comm`：mk_mem_interedges_comm [Std.Symm r] : (a, b)
 in interedges r s t ↔ (b, a) in interedges r t s
-/
theorem mk_mem_interedges_comm : (a, b) ∈ G.interedges s t ↔ (b, a) ∈ G.interedges t s :=
  have := G.symm
  Rel.mk_mem_interedges_comm
/-
**SimpleGraph.edgeDensity_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeDensity_comm (s t : Finset α) : G.edgeDensity s t = G.edgeDensity t s
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
· 使用定理 `Rel.edgeDensity_comm`：edgeDensity_comm [Std.Symm r] (s t : Finset α) : e
dgeDensity r s t = edgeDensity r t s
-/
theorem edgeDensity_comm (s t : Finset α) : G.edgeDensity s t = G.edgeDensity t s :=
  have := G.symm
  Rel.edgeDensity_comm s t

end SimpleGraph

/- Porting note: Commented out `Tactic` namespace.
namespace Tactic

open Positivity

/-- Extension for the `positivity` tactic: `Rel.edgeDensity` and `SimpleGraph.edgeDensity` are
always nonnegative. -/
@[positivity]
unsafe def positivity_edge_density : expr → tactic strictness
  | q(Rel.edgeDensity $(r) $(s) $(t)) =>
    nonnegative <$> mk_mapp `` Rel.edgeDensity_nonneg [none, none, r, none, s, t]
  | q(SimpleGraph.edgeDensity $(G) $(s) $(t)) =>
    nonnegative <$> mk_mapp `` SimpleGraph.edgeDensity_nonneg [none, G, none, s, t]
  | e =>
    pp e >>=
      fail ∘
        format.bracket "The expression `"
          "` isn't of the form `Rel.edgeDensity r s t` nor `SimpleGraph.edgeDensity G s t`"

end Tactic
-/

