/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Tactic.TFAE

/-!
# Locally closed sets

## Main definitions

* `IsLocallyClosed`: Predicate saying that a set is locally closed

## Main results

* `isLocallyClosed_tfae`:
  A set `s` is locally closed if one of the equivalent conditions below hold
  1. It is the intersection of some open set and some closed set.
  2. The coborder `(closure s \ s)ᶜ` is open.
  3. `s` is closed in some neighborhood of `x` for all `x ∈ s`.
  4. Every `x ∈ s` has some open neighborhood `U` such that `U ∩ closure s ⊆ s`.
  5. `s` is open in the closure of `s`.

-/

public section

open Set Topology
open scoped Set.Notation

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X} {f : X → Y}

/-
**subset_coborder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subset_coborder : s subseteq coborder s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coborder.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), c
oborder s = (closure s \ s)ᶜ
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
-/
lemma subset_coborder :
    s ⊆ coborder s := by
  rw [coborder, subset_compl_iff_disjoint_right]
  exact disjoint_sdiff_self_right
/-
**coborder_inter_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coborder_inter_closure : coborder s inter closure s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coborder.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), c
oborder s = (closure s \ s)ᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用定理 `Set.sdiff_sdiff_right_self`：sdiff_sdiff_right_self (s t : Set α) : s \ (
s \ t) = s inter t
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma coborder_inter_closure :
    coborder s ∩ closure s = s := by
  rw [coborder, ← sdiff_eq_compl_inter, sdiff_sdiff_right_self, inter_eq_right]
  exact subset_closure
/-
**closure_inter_coborder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closure_inter_coborder : closure s inter coborder s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `coborder_inter_closure`：coborder_inter_closure : coborder s inter closur
e s = s
-/
lemma closure_inter_coborder :
    closure s ∩ coborder s = s := by
  rw [inter_comm, coborder_inter_closure]
/-
**coborder_eq_union_frontier_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coborder_eq_union_frontier_compl : coborder s = s union (frontier s)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coborder.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), c
oborder s = (closure s \ s)ᶜ
· 使用定理 `compl_eq_comm`：compl_eq_comm : xᶜ = y ↔ yᶜ = x
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用定理 `Set.union_sdiff_right`：union_sdiff_right {s t : Set α} : (s union t) \ t
 = s \ t
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `closure_eq_self_union_frontier`：closure_eq_self_union_frontier (s : Set 
X) : closure s = s union frontier s
-/
lemma coborder_eq_union_frontier_compl :
    coborder s = s ∪ (frontier s)ᶜ := by
  rw [coborder, compl_eq_comm, compl_union, compl_compl, ← sdiff_eq_compl_inter,
    ← union_sdiff_right, union_comm, ← closure_eq_self_union_frontier]
/-
**coborder_eq_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coborder_eq_univ_iff : coborder s = univ ↔ IsClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coborder_eq_univ_iff :
    coborder s = univ ↔ IsClosed s := by
  simp [coborder, sdiff_eq_empty, closure_subset_iff_isClosed]

alias ⟨_, IsClosed.coborder_eq⟩ := coborder_eq_univ_iff
/-
**coborder_eq_compl_frontier_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coborder_eq_compl_frontier_iff : coborder s = (frontier s)ᶜ ↔ IsOpen s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `coborder_eq_union_frontier_compl`：coborder_eq_union_frontier_compl : cob
order s = s union (frontier s)ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coborder_eq_compl_frontier_iff :
    coborder s = (frontier s)ᶜ ↔ IsOpen s := by
  simp_rw [coborder_eq_union_frontier_compl, union_eq_right, subset_compl_iff_disjoint_left,
    disjoint_frontier_iff_isOpen]
/-
**coborder_eq_union_closure_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coborder_eq_union_closure_compl {s : Set X} : coborder s = s union (closur
e s)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coborder.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), c
oborder s = (closure s \ s)ᶜ
· 使用定理 `compl_eq_comm`：compl_eq_comm : xᶜ = y ↔ yᶜ = x
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem coborder_eq_union_closure_compl {s : Set X} : coborder s = s ∪ (closure s)ᶜ := by
  rw [coborder, compl_eq_comm, compl_union, compl_compl, inter_comm]
  rfl

/-- The coborder of any set is dense -/
/-
**dense_coborder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_coborder {s : Set X} : Dense (coborder s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `coborder_eq_union_closure_compl`：coborder_eq_union_closure_compl {s : Se
t X} : coborder s = s union (closure s)ᶜ
· 使用定理 `closure_union`：closure_union : closure (s union t) = closure s union clo
sure t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
The coborder of any set is dense
-/
theorem dense_coborder {s : Set X} :
    Dense (coborder s) := by
  rw [dense_iff_closure_eq, coborder_eq_union_closure_compl, closure_union, ← univ_subset_iff]
  refine _root_.subset_trans ?_ (union_subset_union_right _ (subset_closure))
  simp

alias ⟨_, IsOpen.coborder_eq⟩ := coborder_eq_compl_frontier_iff
/-
**IsOpenMap.coborder_preimage_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpenMap.coborder_preimage_subset (hf : IsOpenMap f) (s : Set Y) : cobord
er (f ⁻¹' s) subseteq f ⁻¹' (coborder s)
参数：hf : IsOpenMap f；s : Set Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coborder.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), c
oborder s = (closure s \ s)ᶜ
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Set.preimage_sdiff`：preimage_sdiff (f : α -> β) (s t : Set β) : f ⁻¹' (s
 \ t) = f ⁻¹' s \ f ⁻¹' t
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `IsOpenMap.preimage_closure_subset_closure_preimage`：∀ {X : Type u_1} {Y 
: Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y
],   IsOpenMap f → ∀ {s : Set Y}, f ⁻¹' …
-/
lemma IsOpenMap.coborder_preimage_subset (hf : IsOpenMap f) (s : Set Y) :
    coborder (f ⁻¹' s) ⊆ f ⁻¹' (coborder s) := by
  rw [coborder, coborder, preimage_compl, preimage_sdiff, compl_subset_compl]
  apply sdiff_subset_sdiff_left
  exact hf.preimage_closure_subset_closure_preimage
/-
**Continuous.preimage_coborder_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.preimage_coborder_subset (hf : Continuous f) (s : Set Y) : f ⁻¹
' (coborder s) subseteq coborder (f ⁻¹' s)
参数：hf : Continuous f；s : Set Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coborder.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), c
oborder s = (closure s \ s)ᶜ
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Set.preimage_sdiff`：preimage_sdiff (f : α -> β) (s t : Set β) : f ⁻¹' (s
 \ t) = f ⁻¹' s \ f ⁻¹' t
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t
-/
lemma Continuous.preimage_coborder_subset (hf : Continuous f) (s : Set Y) :
    f ⁻¹' (coborder s) ⊆ coborder (f ⁻¹' s) := by
  rw [coborder, coborder, preimage_compl, preimage_sdiff, compl_subset_compl]
  apply sdiff_subset_sdiff_left
  exact hf.closure_preimage_subset s
/-
**coborder_preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coborder_preimage (hf : IsOpenMap f) (hf' : Continuous f) (s : Set Y) : co
border (f ⁻¹' s) = f ⁻¹' (coborder s)
参数：hf : IsOpenMap f；hf' : Continuous f；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `IsOpenMap.coborder_preimage_subset`：IsOpenMap.coborder_preimage_subset (
hf : IsOpenMap f) (s : Set Y) : coborder (f ⁻¹' s) subseteq f ⁻¹' (coborder s)
· 使用引理 `Continuous.preimage_coborder_subset`：Continuous.preimage_coborder_subset
 (hf : Continuous f) (s : Set Y) : f ⁻¹' (coborder s) subseteq coborder (f ⁻¹' s
)
-/
lemma coborder_preimage (hf : IsOpenMap f) (hf' : Continuous f) (s : Set Y) :
    coborder (f ⁻¹' s) = f ⁻¹' (coborder s) :=
  (hf.coborder_preimage_subset s).antisymm (hf'.preimage_coborder_subset s)

protected
/-
**Topology.IsOpenEmbedding.coborder_preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.coborder_preimage (hf : IsOpenEmbedding f) (s : S
et Y) : coborder (f ⁻¹' s) = f ⁻¹' coborder s
参数：hf : IsOpenEmbedding f；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `coborder_preimage`：coborder_preimage (hf : IsOpenMap f) (hf' : Continuou
s f) (s : Set Y) : coborder (f ⁻¹' s) = f ⁻¹' (coborder s)
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
-/
lemma Topology.IsOpenEmbedding.coborder_preimage (hf : IsOpenEmbedding f) (s : Set Y) :
    coborder (f ⁻¹' s) = f ⁻¹' coborder s :=
  coborder_preimage hf.isOpenMap hf.continuous s
/-
**isClosed_preimage_val_coborder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_preimage_val_coborder : IsClosed (coborder s ↓inter s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isClosed_preimage_val`：isClosed_preimage_val {s t : Set X} : IsClosed (s
 ↓inter t) ↔ s inter closure (s inter t) subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用引理 `subset_coborder`：subset_coborder : s subseteq coborder s
· 使用引理 `coborder_inter_closure`：coborder_inter_closure : coborder s inter closur
e s = s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma isClosed_preimage_val_coborder :
    IsClosed (coborder s ↓∩ s) := by
  rw [isClosed_preimage_val, inter_eq_right.mpr subset_coborder, coborder_inter_closure]
/-
**IsLocallyClosed.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocallyClosed.inter (hs : IsLocallyClosed s) (ht : IsLocallyClosed t) : 
IsLocallyClosed (s inter t)
参数：hs : IsLocallyClosed s；ht : IsLocallyClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `Set.inter_inter_inter_comm`：inter_inter_inter_comm (s t u v : Set α) : s
 inter t inter (u inter v) = s inter u inter (t inter v)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsLocallyClosed.inter (hs : IsLocallyClosed s) (ht : IsLocallyClosed t) :
    IsLocallyClosed (s ∩ t) := by
  obtain ⟨U₁, Z₁, hU₁, hZ₁, rfl⟩ := hs
  obtain ⟨U₂, Z₂, hU₂, hZ₂, rfl⟩ := ht
  refine ⟨_, _, hU₁.inter hU₂, hZ₁.inter hZ₂, inter_inter_inter_comm U₁ Z₁ U₂ Z₂⟩
/-
**IsLocallyClosed.preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocallyClosed.preimage {s : Set Y} (hs : IsLocallyClosed s) {f : X -> Y}
 (hf : Continuous f) : IsLocallyClosed (f ⁻¹' s)
参数：hs : IsLocallyClosed s；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Set.preimage_inter`：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f
 ⁻¹' s inter f ⁻¹' t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsLocallyClosed.preimage {s : Set Y} (hs : IsLocallyClosed s)
    {f : X → Y} (hf : Continuous f) :
    IsLocallyClosed (f ⁻¹' s) := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  exact ⟨_, _, hU.preimage hf, hZ.preimage hf, preimage_inter⟩

nonrec
/-
**Topology.IsInducing.isLocallyClosed_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isLocallyClosed_iff {s : Set X} {f : X -> Y} (hf : IsI
nducing f) : IsLocallyClosed s ↔ exists s' : Set Y, IsLocallyClosed s' ∧ f ⁻¹' s
' = s
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `Topology.IsInducing.isClosed_iff`：isClosed_iff (hf : IsInducing f) {s : 
Set X} : IsClosed s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Topology.IsInducing.isLocallyClosed_iff {s : Set X}
    {f : X → Y} (hf : IsInducing f) :
    IsLocallyClosed s ↔ ∃ s' : Set Y, IsLocallyClosed s' ∧ f ⁻¹' s' = s := by
  simp_rw [IsLocallyClosed, hf.isOpen_iff, hf.isClosed_iff]
  constructor
  · rintro ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩
    exact ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
    exact ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩
/-
**Topology.IsEmbedding.isLocallyClosed_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.isLocallyClosed_iff {s : Set X} {f : X -> Y} (hf : Is
Embedding f) : IsLocallyClosed s ↔ exists s' : Set Y, IsLocallyClosed s' ∧ s' in
ter range f = f '' s
参数：hf : IsEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.isLocallyClosed_iff`：Topology.IsInducing.isLocallyCl
osed_iff {s : Set X} {f : X -> Y} (hf : IsInducing f) : IsLocallyClosed s ↔ exis
ts s' : Set Y, IsLocallyClose…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Topology.IsEmbedding.isLocallyClosed_iff {s : Set X}
    {f : X → Y} (hf : IsEmbedding f) :
    IsLocallyClosed s ↔ ∃ s' : Set Y, IsLocallyClosed s' ∧ s' ∩ range f = f '' s := by
  simp_rw [hf.isInducing.isLocallyClosed_iff,
    ← (image_injective.mpr hf.injective).eq_iff, image_preimage_eq_inter_range]
/-
**IsLocallyClosed.image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocallyClosed.image {s : Set X} (hs : IsLocallyClosed s) {f : X -> Y} (h
f : IsInducing f) (hf' : IsLocallyClosed (range f)) : IsLocallyClosed (f '' s)
参数：hs : IsLocallyClosed s；hf : IsInducing f；hf' : IsLocallyClosed (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Topology.IsInducing.isLocallyClosed_iff`：Topology.IsInducing.isLocallyCl
osed_iff {s : Set X} {f : X -> Y} (hf : IsInducing f) : IsLocallyClosed s ↔ exis
ts s' : Set Y, IsLocallyClose…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用引理 `IsLocallyClosed.inter`：IsLocallyClosed.inter (hs : IsLocallyClosed s) (h
t : IsLocallyClosed t) : IsLocallyClosed (s inter t)
-/
lemma IsLocallyClosed.image {s : Set X} (hs : IsLocallyClosed s)
    {f : X → Y} (hf : IsInducing f) (hf' : IsLocallyClosed (range f)) :
    IsLocallyClosed (f '' s) := by
  obtain ⟨t, ht, rfl⟩ := hf.isLocallyClosed_iff.mp hs
  rw [image_preimage_eq_inter_range]
  exact ht.inter hf'

/--
A set `s` is locally closed if one of the equivalent conditions below hold
1. It is the intersection of some open set and some closed set.
2. The coborder `(closure s \ s)ᶜ` is open.
3. `s` is closed in some neighborhood of `x` for all `x ∈ s`.
4. Every `x ∈ s` has some open neighborhood `U` such that `U ∩ closure s ⊆ s`.
5. `s` is open in the closure of `s`.
-/
/-
**isLocallyClosed_tfae** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocallyClosed_tfae (s : Set X) : List.TFAE [ IsLocallyClosed s, IsOpen (
coborder s), forall x in s, exists U in 𝓝 x, IsClosed (U ↓inter s), forall x in 
s, exists U, x in U ∧ IsOpen U ∧ U inter closure s subseteq s, IsOpen (closure s
 ↓inter s)]
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Set.compl_subset_iff_union`：compl_subset_iff_union {s t : Set α} : sᶜ su
bseteq t ↔ s union t = univ
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `frontier_subset_closure`：frontier_subset_closure : frontier s subseteq c
losure s
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `coborder_eq_union_frontier_compl`：coborder_eq_union_frontier_compl : cob
order s = s union (frontier s)ᶜ
· 使用定理 `Set.inter_union_distrib_right`：inter_union_distrib_right (s t u : Set α)
 : s inter t union u = (s union u) inter (t union u)
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_frontier`：isClosed_frontier : IsClosed (frontier s)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `subset_coborder`：subset_coborder : s subseteq coborder s
· 使用引理 `isClosed_preimage_val_coborder`：isClosed_preimage_val_coborder : IsClose
d (coborder s ↓inter s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `IsOpen.inter_closure`：IsOpen.inter_closure (h : IsOpen s) : s inter clos
ure t subseteq closure (s inter t)
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用引理 `isClosed_preimage_val`：isClosed_preimage_val {s t : Set X} : IsClosed (s
 ↓inter t) ↔ s inter closure (s inter t) subseteq t
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
A set `s` is locally closed if one of the equivalent conditions below hold
1. It is the intersection of some open set and some closed set.
2. The coborder `(closure s \ s)ᶜ` is open.
3. `s` is closed in some neighborhood of `x` for all `x ∈ s`.
4. Every `x ∈ s` has some open neighborhood `U` such that `U ∩ closure s ⊆ s`.
5. `s` is open in the closure of `s`.
-/
lemma isLocallyClosed_tfae (s : Set X) :
    List.TFAE
    [ IsLocallyClosed s,
      IsOpen (coborder s),
      ∀ x ∈ s, ∃ U ∈ 𝓝 x, IsClosed (U ↓∩ s),
      ∀ x ∈ s, ∃ U, x ∈ U ∧ IsOpen U ∧ U ∩ closure s ⊆ s,
      IsOpen (closure s ↓∩ s)] := by
  tfae_have 1 → 2 := by
    rintro ⟨U, Z, hU, hZ, rfl⟩
    have : Z ∪ (frontier (U ∩ Z))ᶜ = univ := by
      nth_rw 1 [← hZ.closure_eq]
      rw [← compl_subset_iff_union, compl_subset_compl]
      refine frontier_subset_closure.trans (closure_mono inter_subset_right)
    rw [coborder_eq_union_frontier_compl, inter_union_distrib_right, this,
      inter_univ]
    exact hU.union isClosed_frontier.isOpen_compl
  tfae_have 2 → 3
  | h, x => (⟨coborder s, h.mem_nhds <| subset_coborder ·, isClosed_preimage_val_coborder⟩)
  tfae_have 3 → 4
  | h, x, hx => by
    obtain ⟨t, ht, ht'⟩ := h x hx
    obtain ⟨U, hUt, hU, hxU⟩ := mem_nhds_iff.mp ht
    rw [isClosed_preimage_val] at ht'
    exact ⟨U, hxU, hU, (subset_inter (inter_subset_left.trans hUt) (hU.inter_closure.trans
      (closure_mono <| inter_subset_inter hUt subset_rfl))).trans ht'⟩
  tfae_have 4 → 5
  | H => by
    choose U hxU hU e using H
    refine ⟨⋃ x ∈ s, U x ‹_›, isOpen_iUnion (isOpen_iUnion <| hU ·), ext fun x ↦ ⟨?_, ?_⟩⟩
    · rintro ⟨_, ⟨⟨y, rfl⟩, ⟨_, ⟨hy, rfl⟩, hxU⟩⟩⟩
      exact e y hy ⟨hxU, x.2⟩
    · exact (subset_iUnion₂ _ _ <| hxU x ·)
  tfae_have 5 → 1
  | H => by
    convert!
      H.isLocallyClosed.image IsInducing.subtypeVal
        (by simpa using isClosed_closure.isLocallyClosed)
    simpa using subset_closure
  tfae_finish
/-
**isLocallyClosed_iff_isOpen_coborder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocallyClosed_iff_isOpen_coborder : IsLocallyClosed s ↔ IsOpen (coborder
 s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `isLocallyClosed_tfae`：isLocallyClosed_tfae (s : Set X) : List.TFAE [ IsL
ocallyClosed s, IsOpen (coborder s), forall x in s, exists U in 𝓝 x, IsClosed (U
 ↓inter s)…
-/
lemma isLocallyClosed_iff_isOpen_coborder : IsLocallyClosed s ↔ IsOpen (coborder s) :=
  (isLocallyClosed_tfae s).out 0 1

alias ⟨IsLocallyClosed.isOpen_coborder, _⟩ := isLocallyClosed_iff_isOpen_coborder
/-
**IsLocallyClosed.isOpen_preimage_val_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocallyClosed.isOpen_preimage_val_closure (hs : IsLocallyClosed s) : IsO
pen (closure s ↓inter s)
参数：hs : IsLocallyClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `isLocallyClosed_tfae`：isLocallyClosed_tfae (s : Set X) : List.TFAE [ IsL
ocallyClosed s, IsOpen (coborder s), forall x in s, exists U in 𝓝 x, IsClosed (U
 ↓inter s)…
-/
lemma IsLocallyClosed.isOpen_preimage_val_closure (hs : IsLocallyClosed s) :
    IsOpen (closure s ↓∩ s) :=
  ((isLocallyClosed_tfae s).out 0 4).mp hs
