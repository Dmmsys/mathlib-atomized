/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Lift
public import Mathlib.Topology.Basic

/-!
# Interior, closure and frontier of a set

This file provides lemmas relating to the functions `interior`, `closure` and `frontier` of a set
endowed with a topology.

## Notation

* `𝓝 x`: the filter `nhds x` of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhdsWithin x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝[≠] x`: the filter `nhdsWithin x {x}ᶜ` of punctured neighborhoods of `x`.

## Tags

interior, closure, frontier
-/

public section

open Set

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Sort v} {x : X} {s s₁ s₂ t : Set X}

section Interior

/-
**mem_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_interior : x in interior s ↔ exists t subseteq s, IsOpen t ∧ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_interior : x ∈ interior s ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t := by
  simp only [interior, mem_sUnion, mem_ofPred_eq, and_assoc, and_left_comm]

@[simp]
/-
**isOpen_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_interior : IsOpen (interior s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_sUnion`：isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpe
n t) : IsOpen (⋃₀ s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isOpen_interior : IsOpen (interior s) :=
  isOpen_sUnion fun _ => And.left
/-
**interior_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_subset : interior s subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sUnion_subset`：sUnion_subset {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t' subseteq t) : ⋃₀ S subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem interior_subset : interior s ⊆ s :=
  sUnion_subset fun _ => And.right
/-
**interior_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) : t subseteq interior
 s
参数：h₁ : t subseteq s；h₂ : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
theorem interior_maximal (h₁ : t ⊆ s) (h₂ : IsOpen t) : t ⊆ interior s :=
  subset_sUnion_of_mem ⟨h₂, h₁⟩

@[grind =]
/-
**IsOpen.interior_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.interior_eq (h : IsOpen s) : interior s = s
参数：h : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem IsOpen.interior_eq (h : IsOpen s) : interior s = s :=
  interior_subset.antisymm (interior_maximal (Subset.refl s) h)
/-
**forall_isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_isOpen_iff {p : Set X -> Prop} : (forall t, IsOpen t -> p t) ↔ fora
ll t, p (interior t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
-/
theorem forall_isOpen_iff {p : Set X → Prop} :
    (∀ t, IsOpen t → p t) ↔ ∀ t, p (interior t) :=
  ⟨fun h t ↦ h (interior t) isOpen_interior, fun h t ht ↦ ht.interior_eq ▸ h t⟩
/-
**exists_isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isOpen_iff {p : Set X -> Prop} : (exists t, IsOpen t ∧ p t) ↔ exist
s t, p (interior t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem exists_isOpen_iff {p : Set X → Prop} :
    (∃ t, IsOpen t ∧ p t) ↔ ∃ t, p (interior t) :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h.1.interior_eq ▸ h.2⟩, fun ⟨_, h⟩ ↦ ⟨_, isOpen_interior, h⟩⟩
/-
**interior_eq_iff_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_eq_iff_isOpen : interior s = s ↔ IsOpen s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
-/
theorem interior_eq_iff_isOpen : interior s = s ↔ IsOpen s :=
  ⟨fun h => h ▸ isOpen_interior, IsOpen.interior_eq⟩
/-
**subset_interior_iff_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_iff_isOpen : s subseteq interior s ↔ IsOpen s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `interior_eq_iff_isOpen`：interior_eq_iff_isOpen : interior s = s ↔ IsOpen
 s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subset_interior_iff_isOpen : s ⊆ interior s ↔ IsOpen s := by
  simp only [interior_eq_iff_isOpen.symm, Subset.antisymm_iff, interior_subset, true_and]
/-
**IsOpen.subset_interior_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.subset_interior_iff (h₁ : IsOpen s) : s subseteq interior t ↔ s sub
seteq t
参数：h₁ : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
-/
theorem IsOpen.subset_interior_iff (h₁ : IsOpen s) : s ⊆ interior t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h interior_subset, fun h₂ => interior_maximal h₂ h₁⟩
/-
**subset_interior_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_iff : t subseteq interior s ↔ exists U, IsOpen U ∧ t subse
teq U ∧ U subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
-/
theorem subset_interior_iff : t ⊆ interior s ↔ ∃ U, IsOpen U ∧ t ⊆ U ∧ U ⊆ s :=
  ⟨fun h => ⟨interior s, isOpen_interior, h, interior_subset⟩, fun ⟨_U, hU, htU, hUs⟩ =>
    htU.trans (interior_maximal hUs hU)⟩
/-
**interior_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：interior_subset_iff : interior s subseteq t ↔ forall U, IsOpen U -> U subs
eteq s -> U subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma interior_subset_iff : interior s ⊆ t ↔ ∀ U, IsOpen U → U ⊆ s → U ⊆ t := by
  simp [interior]

@[mono, gcongr]
/-
**interior_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_mono (h : s subseteq t) : interior s subseteq interior t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem interior_mono (h : s ⊆ t) : interior s ⊆ interior t :=
  interior_maximal (Subset.trans interior_subset h) isOpen_interior
/-
**subset_interior_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_union : interior s union interior t subseteq interior (s u
nion t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem subset_interior_union : interior s ∪ interior t ⊆ interior (s ∪ t) :=
  union_subset (interior_mono subset_union_left) (interior_mono subset_union_right)

@[simp]
/-
**interior_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_empty : interior (∅ : Set X) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
-/
theorem interior_empty : interior (∅ : Set X) = ∅ :=
  isOpen_empty.interior_eq

@[simp]
/-
**interior_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_univ : interior (univ : Set X) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem interior_univ : interior (univ : Set X) = univ :=
  isOpen_univ.interior_eq

@[simp]
/-
**interior_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_eq_univ : interior s = univ ↔ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
-/
theorem interior_eq_univ : interior s = univ ↔ s = univ :=
  ⟨fun h => univ_subset_iff.mp <| h.symm.trans_le interior_subset, fun h => h.symm ▸ interior_univ⟩

@[simp]
/-
**interior_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_interior : interior (interior s) = interior s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem interior_interior : interior (interior s) = interior s :=
  isOpen_interior.interior_eq

@[simp]
/-
**interior_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_inter : interior (s inter t) = interior s inter interior t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem interior_inter : interior (s ∩ t) = interior s ∩ interior t :=
  (Monotone.map_inf_le (fun _ _ ↦ interior_mono) s t).antisymm <|
    interior_maximal (inter_subset_inter interior_subset interior_subset) <|
      isOpen_interior.inter isOpen_interior
/-
**Set.Finite.interior_biInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.interior_biInter {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι
 -> Set X) : interior (⋂ i in s, f i) = ⋂ i in s, interior (f i)
参数：hs : s.Finite；f : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.iInter_iInter_eq_or_left`：iInter_iInter_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋂ (x) (h), s x h = s b (Or.inl
 rfl) inter ⋂ (x) …
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
-/
theorem Set.Finite.interior_biInter {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι → Set X) :
    interior (⋂ i ∈ s, f i) = ⋂ i ∈ s, interior (f i) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ _ => simp [*]
/-
**Set.Finite.interior_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.interior_sInter {S : Set (Set X)} (hS : S.Finite) : interior (⋂
₀ S) = ⋂ s in S, interior s
参数：Set X；hS : S.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.Finite.interior_biInter`：Set.Finite.interior_biInter {ι : Type*} {s 
: Set ι} (hs : s.Finite) (f : ι -> Set X) : interior (⋂ i in s, f i) = ⋂ i in s,
 interior (f i)
-/
theorem Set.Finite.interior_sInter {S : Set (Set X)} (hS : S.Finite) :
    interior (⋂₀ S) = ⋂ s ∈ S, interior s := by
  rw [sInter_eq_biInter, hS.interior_biInter]

@[simp]
/-
**Finset.interior_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.interior_iInter {ι : Type*} (s : Finset ι) (f : ι -> Set X) : inter
ior (⋂ i in s, f i) = ⋂ i in s, interior (f i)
参数：s : Finset ι；f : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.interior_biInter`：Set.Finite.interior_biInter {ι : Type*} {s 
: Set ι} (hs : s.Finite) (f : ι -> Set X) : interior (⋂ i in s, f i) = ⋂ i in s,
 interior (f i)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem Finset.interior_iInter {ι : Type*} (s : Finset ι) (f : ι → Set X) :
    interior (⋂ i ∈ s, f i) = ⋂ i ∈ s, interior (f i) :=
  s.finite_toSet.interior_biInter f

@[simp]
/-
**interior_iInter_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_iInter_of_finite [Finite ι] (f : ι -> Set X) : interior (⋂ i, f i
) = ⋂ i, interior (f i)
参数：f : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `Set.Finite.interior_sInter`：Set.Finite.interior_sInter {S : Set (Set X)}
 (hS : S.Finite) : interior (⋂₀ S) = ⋂ s in S, interior s
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Set.biInter_range`：biInter_range {f : ι -> α} {g : α -> Set β} : ⋂ x in 
range f, g x = ⋂ y, g (f y)
-/
theorem interior_iInter_of_finite [Finite ι] (f : ι → Set X) :
    interior (⋂ i, f i) = ⋂ i, interior (f i) := by
  rw [← sInter_range, (finite_range f).interior_sInter, biInter_range]

@[simp]
/-
**interior_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] (f : ι → Set α),   interior (⋂ i, f i) = ⋂ i, interior (f i)
参数：f : ι → Set α；⋂ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.iInter_mono`：iInter_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋂ i, s i subseteq ⋂ i, t i
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `isOpen_iInter`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace 
α] [AlexandrovDiscrete α] {f : ι → Set α},   (∀ (i : ι), IsOpen (f i)) → IsOpen 
(⋂ …
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem interior_iInter₂_lt_nat {n : ℕ} (f : ℕ → Set X) :
    interior (⋂ m < n, f m) = ⋂ m < n, interior (f m) :=
  (finite_lt_nat n).interior_biInter f

@[simp]
/-
**interior_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] (f : ι → Set α),   interior (⋂ i, f i) = ⋂ i, interior (f i)
参数：f : ι → Set α；⋂ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.iInter_mono`：iInter_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋂ i, s i subseteq ⋂ i, t i
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `isOpen_iInter`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace 
α] [AlexandrovDiscrete α] {f : ι → Set α},   (∀ (i : ι), IsOpen (f i)) → IsOpen 
(⋂ …
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem interior_iInter₂_le_nat {n : ℕ} (f : ℕ → Set X) :
    interior (⋂ m ≤ n, f m) = ⋂ m ≤ n, interior (f m) :=
  (finite_le_nat n).interior_biInter f
/-
**interior_union_inter_interior_compl_left_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_union_inter_interior_compl_left_subset : interior (s union t) int
er interior sᶜ subseteq interior t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.union_inter_compl_left_subset`：union_inter_compl_left_subset (s t : 
Set α) : (s union t) inter sᶜ subseteq t
-/
theorem interior_union_inter_interior_compl_left_subset :
    interior (s ∪ t) ∩ interior sᶜ ⊆ interior t :=
  interior_inter.symm.trans_subset <| interior_mono (union_inter_compl_left_subset ..)
/-
**interior_union_inter_interior_compl_right_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_union_inter_interior_compl_right_subset : interior (s union t) in
ter interior tᶜ subseteq interior s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.union_inter_compl_right_subset`：union_inter_compl_right_subset (s t 
: Set α) : (s union t) inter tᶜ subseteq s
-/
theorem interior_union_inter_interior_compl_right_subset :
    interior (s ∪ t) ∩ interior tᶜ ⊆ interior s :=
  interior_inter.symm.trans_subset <| interior_mono (union_inter_compl_right_subset ..)
/-
**interior_union_isClosed_of_interior_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_union_isClosed_of_interior_empty (h₁ : IsClosed s) (h₂ : interior
 t = ∅) : interior (s union t) = interior s
参数：h₁ : IsClosed s；h₂ : interior t = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.subset_interior_iff`：IsOpen.subset_interior_iff (h₁ : IsOpen s) :
 s subseteq interior t ↔ s subseteq t
· 使用定理 `IsOpen.sdiff`：IsOpen.sdiff (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s
 \ t)
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
theorem interior_union_isClosed_of_interior_empty (h₁ : IsClosed s)
    (h₂ : interior t = ∅) : interior (s ∪ t) = interior s :=
  have : interior (s ∪ t) ⊆ s := fun x ⟨u, ⟨(hu₁ : IsOpen u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩ =>
    by_contradiction fun hx₂ : x ∉ s =>
      have : u \ s ⊆ t := fun _ ⟨h₁, h₂⟩ => Or.resolve_left (hu₂ h₁) h₂
      have : u \ s ⊆ interior t := by rwa [(IsOpen.sdiff hu₁ h₁).subset_interior_iff]
      have : u \ s ⊆ ∅ := by rwa [h₂] at this
      this ⟨hx₁, hx₂⟩
  Subset.antisymm (interior_maximal this isOpen_interior) (interior_mono subset_union_left)
/-
**isOpen_iff_forall_mem_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iff_forall_mem_open : IsOpen s ↔ forall x in s, exists t, t subsete
q s ∧ IsOpen t ∧ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_interior_iff_isOpen`：subset_interior_iff_isOpen : s subseteq inte
rior s ↔ IsOpen s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff_forall_mem_open : IsOpen s ↔ ∀ x ∈ s, ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t := by
  rw [← subset_interior_iff_isOpen]
  simp only [subset_def, mem_interior]
/-
**interior_iInter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_iInter_subset (s : ι -> Set X) : interior (⋂ i, s i) subseteq ⋂ i
, interior (s i)
参数：s : ι -> Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem interior_iInter_subset (s : ι → Set X) : interior (⋂ i, s i) ⊆ ⋂ i, interior (s i) :=
  subset_iInter fun _ => interior_mono <| iInter_subset _ _
/-
**interior_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] (f : ι → Set α),   interior (⋂ i, f i) = ⋂ i, interior (f i)
参数：f : ι → Set α；⋂ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.iInter_mono`：iInter_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋂ i, s i subseteq ⋂ i, t i
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `isOpen_iInter`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace 
α] [AlexandrovDiscrete α] {f : ι → Set α},   (∀ (i : ι), IsOpen (f i)) → IsOpen 
(⋂ …
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem interior_iInter₂_subset (p : ι → Sort*) (s : ∀ i, p i → Set X) :
    interior (⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), interior (s i j) :=
  (interior_iInter_subset _).trans <| iInter_mono fun _ => interior_iInter_subset _
/-
**interior_sInter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_sInter_subset (S : Set (Set X)) : interior (⋂₀ S) subseteq ⋂ s in
 S, interior s
参数：S : Set (Set X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `interior_iInter₂_subset`：interior_iInter₂_subset (p : ι -> Sort*) (s : f
orall i, p i -> Set X) : interior (⋂ (i) (j), s i j) subseteq ⋂ (i) (j), interio
r (s i j)
-/
theorem interior_sInter_subset (S : Set (Set X)) : interior (⋂₀ S) ⊆ ⋂ s ∈ S, interior s :=
  calc
    interior (⋂₀ S) = interior (⋂ s ∈ S, s) := by rw [sInter_eq_biInter]
    _ ⊆ ⋂ s ∈ S, interior s := interior_iInter₂_subset _ _
/-
**Filter.HasBasis.lift'_interior** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {ι : Sort v} {l : Filter X} {p 
: ι → Prop} {s : ι → Set X},   l.HasBasis p s → (l.lift' interior).HasBasis p fu
n i => interior (s i)
参数：l.lift' interior；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.lift'`：Filter.HasBasis.lift'_interior {l : Filter X} {p 
: ι -> Prop} {s : ι -> Set X} (h : l.HasBasis p s) : (l.lift' interior).HasBasis
 p fun i =>…
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
-/
theorem Filter.HasBasis.lift'_interior {l : Filter X} {p : ι → Prop} {s : ι → Set X}
    (h : l.HasBasis p s) : (l.lift' interior).HasBasis p fun i => interior (s i) :=
  h.lift' fun _ _ ↦ interior_mono
/-
**Filter.lift'_interior_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] (l : Filter X), l.lift' interio
r ≤ l
参数：l : Filter X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem Filter.lift'_interior_le (l : Filter X) : l.lift' interior ≤ l := fun _s hs ↦
  mem_of_superset (mem_lift' hs) interior_subset
/-
**Filter.HasBasis.lift'_interior_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBa
sis`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {ι : Sort v} {l : Filter X} {p 
: ι → Prop} {s : ι → Set X},   l.HasBasis p s → (∀ (i : ι), p i → IsOpen (s i)) 
→ l.lift' interior = l
参数：∀ (i : ι), p i → IsOpen (s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.lift'_interior_le`：∀ {X : Type u} [inst : TopologicalSpace X] (l 
: Filter X), l.lift' interior ≤ l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Filter.HasBasis.lift'_interior`：∀ {X : Type u} [inst : TopologicalSpace 
X] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBasis p s 
→ (l.lift' interior)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
-/
theorem Filter.HasBasis.lift'_interior_eq_self {l : Filter X} {p : ι → Prop} {s : ι → Set X}
    (h : l.HasBasis p s) (ho : ∀ i, p i → IsOpen (s i)) : l.lift' interior = l :=
  le_antisymm l.lift'_interior_le <| h.lift'_interior.ge_iff.2 fun i hi ↦ by
    simpa only [(ho i hi).interior_eq] using h.mem_of_mem hi

end Interior

section Closure

@[simp, closedness ., grind .]
/-
**isClosed_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_closure : IsClosed (closure s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_sInter`：isClosed_sInter {s : Set (Set X)} : (forall t in s, IsC
losed t) -> IsClosed (⋂₀ s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isClosed_closure : IsClosed (closure s) :=
  isClosed_sInter fun _ => And.left
/-
**subset_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_closure : s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_sInter`：subset_sInter {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t subseteq t') : t subseteq ⋂₀ S
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem subset_closure : s ⊆ closure s :=
  subset_sInter fun _ => And.right
/-
**notMem_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：notMem_of_notMem_closure {P : X} (hP : P ∉ closure s) : P ∉ s
参数：hP : P ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem notMem_of_notMem_closure {P : X} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
/-
**closure_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) : closure s subseteq
 t
参数：h₁ : s subseteq t；h₂ : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
-/
theorem closure_minimal (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t :=
  sInter_subset_of_mem ⟨h₂, h₁⟩
/-
**Disjoint.closure_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.closure_left (hd : Disjoint s t) (ht : IsOpen t) : Disjoint (clos
ure s) t
参数：hd : Disjoint s t；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
-/
theorem Disjoint.closure_left (hd : Disjoint s t) (ht : IsOpen t) :
    Disjoint (closure s) t :=
  disjoint_compl_left.mono_left <| closure_minimal hd.subset_compl_right ht.isClosed_compl
/-
**Disjoint.closure_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.closure_right (hd : Disjoint s t) (hs : IsOpen s) : Disjoint s (c
losure t)
参数：hd : Disjoint s t；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Disjoint.closure_left`：Disjoint.closure_left (hd : Disjoint s t) (ht : I
sOpen t) : Disjoint (closure s) t
-/
theorem Disjoint.closure_right (hd : Disjoint s t) (hs : IsOpen s) :
    Disjoint s (closure t) :=
  (hd.symm.closure_left hs).symm

@[simp, closedness =]
/-
**IsClosed.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：IsClosed.closure_eq : c.IsClosed x -> c x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem IsClosed.closure_eq (h : IsClosed s) : closure s = s :=
  Subset.antisymm (closure_minimal (Subset.refl s) h) subset_closure
/-
**forall_isClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_isClosed_iff {p : Set X -> Prop} : (forall t, IsClosed t -> p t) ↔ 
forall t, p (closure t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem forall_isClosed_iff {p : Set X → Prop} :
    (∀ t, IsClosed t → p t) ↔ ∀ t, p (closure t) :=
  ⟨fun h t ↦ h (closure t) isClosed_closure, fun h t ht ↦ ht.closure_eq ▸ h t⟩
/-
**exists_isClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isClosed_iff {p : Set X -> Prop} : (exists t, IsClosed t ∧ p t) ↔ e
xists t, p (closure t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem exists_isClosed_iff {p : Set X → Prop} :
    (∃ t, IsClosed t ∧ p t) ↔ ∃ t, p (closure t) :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h.1.closure_eq ▸ h.2⟩, fun ⟨_, h⟩ ↦ ⟨_, isClosed_closure, h⟩⟩
/-
**IsClosed.closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.closure_subset (hs : IsClosed s) : closure s subseteq s
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem IsClosed.closure_subset (hs : IsClosed s) : closure s ⊆ s :=
  closure_minimal (Subset.refl _) hs
/-
**IsClosed.closure_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.closure_subset_iff (h₁ : IsClosed t) : closure s subseteq t ↔ s s
ubseteq t
参数：h₁ : IsClosed t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem IsClosed.closure_subset_iff (h₁ : IsClosed t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans subset_closure, fun h => closure_minimal h h₁⟩
/-
**IsClosed.mem_iff_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.mem_iff_closure_subset (hs : IsClosed s) : x in s ↔ closure ({x} 
: Set X) subseteq s
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem IsClosed.mem_iff_closure_subset (hs : IsClosed s) :
    x ∈ s ↔ closure ({x} : Set X) ⊆ s :=
  (hs.closure_subset_iff.trans Set.singleton_subset_iff).symm

@[mono, gcongr]
/-
**closure_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_mono (h : s subseteq t) : closure s subseteq closure t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem closure_mono (h : s ⊆ t) : closure s ⊆ closure t :=
  closure_minimal (Subset.trans h subset_closure) isClosed_closure
/-
**monotone_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_closure (X : Type*) [TopologicalSpace X] : Monotone (@closure X _
)
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem monotone_closure (X : Type*) [TopologicalSpace X] : Monotone (@closure X _) := fun _ _ =>
  closure_mono
/-
**closure_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_inter_subset : closure (s inter t) subseteq closure s inter closur
e t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem closure_inter_subset : closure (s ∩ t) ⊆ closure s ∩ closure t :=
  subset_inter (closure_mono inter_subset_left) (closure_mono inter_subset_right)
/-
**sdiff_subset_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_subset_closure_iff : s \ t subseteq closure t ↔ s subseteq closure t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sdiff_subset_closure_iff : s \ t ⊆ closure t ↔ s ⊆ closure t := by
  rw [sdiff_subset_iff, union_eq_self_of_subset_left subset_closure]

@[deprecated (since := "2026-06-03")] alias diff_subset_closure_iff := sdiff_subset_closure_iff
/-
**closure_inter_subset_inter_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_inter_subset_inter_closure (s t : Set X) : closure (s inter t) sub
seteq closure s inter closure t
参数：s t : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `monotone_closure`：monotone_closure (X : Type*) [TopologicalSpace X] : Mo
notone (@closure X _)
-/
theorem closure_inter_subset_inter_closure (s t : Set X) :
    closure (s ∩ t) ⊆ closure s ∩ closure t :=
  (monotone_closure X).map_inf_le s t
/-
**isClosed_of_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_of_closure_subset (h : closure s subseteq s) : IsClosed s
参数：h : closure s subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem isClosed_of_closure_subset (h : closure s ⊆ s) : IsClosed s := by
  rw [subset_closure.antisymm h]; exact isClosed_closure
/-
**closure_eq_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_eq_iff_isClosed : closure s = s ↔ IsClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem closure_eq_iff_isClosed : closure s = s ↔ IsClosed s :=
  ⟨fun h => h ▸ isClosed_closure, IsClosed.closure_eq⟩
/-
**closure_subset_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_subset_iff_isClosed : closure s subseteq s ↔ IsClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
-/
theorem closure_subset_iff_isClosed : closure s ⊆ s ↔ IsClosed s :=
  ⟨isClosed_of_closure_subset, IsClosed.closure_subset⟩
/-
**closure_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_empty : closure (∅ : Set X) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
-/
theorem closure_empty : closure (∅ : Set X) = ∅ :=
  isClosed_empty.closure_eq

@[simp]
/-
**closure_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_empty_iff (s : Set X) : closure s = ∅ ↔ s = ∅
参数：s : Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_eq_empty`：subset_eq_empty {s t : Set α} (h : t subseteq s) (e
 : s = ∅) : t = ∅
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `closure_empty`：closure_empty : closure (∅ : Set X) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem closure_empty_iff (s : Set X) : closure s = ∅ ↔ s = ∅ :=
  ⟨subset_eq_empty subset_closure, fun h => h.symm ▸ closure_empty⟩

@[simp]
/-
**closure_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_nonempty_iff : (closure s).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closure_nonempty_iff : (closure s).Nonempty ↔ s.Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, closure_empty_iff]

alias ⟨Set.Nonempty.of_closure, Set.Nonempty.closure⟩ := closure_nonempty_iff
/-
**closure_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_univ : closure (univ : Set X) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
-/
theorem closure_univ : closure (univ : Set X) = univ :=
  isClosed_univ.closure_eq
/-
**closure_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_closure : closure (closure s) = closure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem closure_closure : closure (closure s) = closure s :=
  isClosed_closure.closure_eq
/-
**closure_eq_compl_interior_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_eq_compl_interior_compl : closure s = (interior sᶜ)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), i
nterior s = ⋃₀ {t | IsOpen t ∧ t ⊆ s}
· 使用定理 `closure.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), cl
osure s = ⋂₀ {t | IsClosed t ∧ s ⊆ t}
· 使用定理 `Set.compl_sUnion`：compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '
' S)
· 使用定理 `Set.compl_image_ofPred`：compl_image_ofPred {p : Set α -> Prop} : compl '
' { s | p s } = { s | p sᶜ }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_eq_compl_interior_compl : closure s = (interior sᶜ)ᶜ := by
  rw [interior, closure, compl_sUnion, compl_image_ofPred]
  simp only [compl_subset_compl, isOpen_compl_iff]

@[simp]
/-
**closure_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_union : closure (s union t) = closure s union closure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_eq_compl_interior_compl`：closure_eq_compl_interior_compl : closu
re s = (interior sᶜ)ᶜ
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_union : closure (s ∪ t) = closure s ∪ closure t := by
  simp [closure_eq_compl_interior_compl, compl_inter]
/-
**Set.Finite.closure_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.closure_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι 
-> Set X) : closure (⋃ i in s, f i) = ⋃ i in s, closure (f i)
参数：hs : s.Finite；f : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_eq_compl_interior_compl`：closure_eq_compl_interior_compl : closu
re s = (interior sᶜ)ᶜ
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.interior_biInter`：Set.Finite.interior_biInter {ι : Type*} {s 
: Set ι} (hs : s.Finite) (f : ι -> Set X) : interior (⋂ i in s, f i) = ⋂ i in s,
 interior (f i)
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Set.Finite.closure_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι → Set X) :
    closure (⋃ i ∈ s, f i) = ⋃ i ∈ s, closure (f i) := by
  simp [closure_eq_compl_interior_compl, hs.interior_biInter]
/-
**Set.Finite.closure_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.closure_sUnion {S : Set (Set X)} (hS : S.Finite) : closure (⋃₀ 
S) = ⋃ s in S, closure s
参数：Set X；hS : S.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.Finite.closure_biUnion`：Set.Finite.closure_biUnion {ι : Type*} {s : 
Set ι} (hs : s.Finite) (f : ι -> Set X) : closure (⋃ i in s, f i) = ⋃ i in s, cl
osure (f i)
-/
theorem Set.Finite.closure_sUnion {S : Set (Set X)} (hS : S.Finite) :
    closure (⋃₀ S) = ⋃ s ∈ S, closure s := by
  rw [sUnion_eq_biUnion, hS.closure_biUnion]

@[simp]
/-
**Finset.closure_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.closure_biUnion {ι : Type*} (s : Finset ι) (f : ι -> Set X) : closu
re (⋃ i in s, f i) = ⋃ i in s, closure (f i)
参数：s : Finset ι；f : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.closure_biUnion`：Set.Finite.closure_biUnion {ι : Type*} {s : 
Set ι} (hs : s.Finite) (f : ι -> Set X) : closure (⋃ i in s, f i) = ⋃ i in s, cl
osure (f i)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem Finset.closure_biUnion {ι : Type*} (s : Finset ι) (f : ι → Set X) :
    closure (⋃ i ∈ s, f i) = ⋃ i ∈ s, closure (f i) :=
  s.finite_toSet.closure_biUnion f

@[simp]
/-
**closure_iUnion_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_iUnion_of_finite [Finite ι] (f : ι -> Set X) : closure (⋃ i, f i) 
= ⋃ i, closure (f i)
参数：f : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `Set.Finite.closure_sUnion`：Set.Finite.closure_sUnion {S : Set (Set X)} (
hS : S.Finite) : closure (⋃₀ S) = ⋃ s in S, closure s
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
-/
theorem closure_iUnion_of_finite [Finite ι] (f : ι → Set X) :
    closure (⋃ i, f i) = ⋃ i, closure (f i) := by
  rw [← sUnion_range, (finite_range _).closure_sUnion, biUnion_range]

@[simp]
/-
**closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] (f : ι → Set α),   closure (⋃ i, f i) = ⋃ i, closure (f i)
参数：f : ι → Set α；⋃ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `interior_iInter`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpac
e α] [AlexandrovDiscrete α] (f : ι → Set α),   interior (⋂ i, f i) = ⋂ i, interi
or (f…
-/
theorem closure_iUnion₂_lt_nat {n : ℕ} (f : ℕ → Set X) :
    closure (⋃ m < n, f m) = ⋃ m < n, closure (f m) :=
  (finite_lt_nat n).closure_biUnion f

@[simp]
/-
**closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpace α] [AlexandrovDis
crete α] (f : ι → Set α),   closure (⋃ i, f i) = ⋃ i, closure (f i)
参数：f : ι → Set α；⋃ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `interior_iInter`：∀ {ι : Sort u_1} {α : Type u_3} [inst : TopologicalSpac
e α] [AlexandrovDiscrete α] (f : ι → Set α),   interior (⋂ i, f i) = ⋂ i, interi
or (f…
-/
theorem closure_iUnion₂_le_nat {n : ℕ} (f : ℕ → Set X) :
    closure (⋃ m ≤ n, f m) = ⋃ m ≤ n, closure (f m) :=
  (finite_le_nat n).closure_biUnion f
/-
**subset_closure_inter_union_closure_compl_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_closure_inter_union_closure_compl_left : closure t subseteq closure
 (s inter t) union closure sᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.subset_inter_union_compl_left`：subset_inter_union_compl_left (s t : 
Set α) : t subseteq s inter t union sᶜ
· 使用定理 `closure_union`：closure_union : closure (s union t) = closure s union clo
sure t
-/
theorem subset_closure_inter_union_closure_compl_left :
    closure t ⊆ closure (s ∩ t) ∪ closure sᶜ :=
  (closure_mono <| subset_inter_union_compl_left ..).trans_eq closure_union
/-
**subset_closure_inter_union_closure_compl_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_closure_inter_union_closure_compl_right : closure s subseteq closur
e (s inter t) union closure tᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.subset_inter_union_compl_right`：subset_inter_union_compl_right (s t 
: Set α) : s subseteq s inter t union tᶜ
· 使用定理 `closure_union`：closure_union : closure (s union t) = closure s union clo
sure t
-/
theorem subset_closure_inter_union_closure_compl_right :
    closure s ⊆ closure (s ∩ t) ∪ closure tᶜ :=
  (closure_mono <| subset_inter_union_compl_right ..).trans_eq closure_union
/-
**interior_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_subset_closure : interior s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem interior_subset_closure : interior s ⊆ closure s :=
  Subset.trans interior_subset subset_closure

@[simp]
/-
**interior_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_compl : interior sᶜ = (closure s)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_eq_compl_interior_compl`：closure_eq_compl_interior_compl : closu
re s = (interior sᶜ)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem interior_compl : interior sᶜ = (closure s)ᶜ := by
  simp [closure_eq_compl_interior_compl]

@[simp]
/-
**closure_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_compl : closure sᶜ = (interior s)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_eq_compl_interior_compl`：closure_eq_compl_interior_compl : closu
re s = (interior sᶜ)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_compl : closure sᶜ = (interior s)ᶜ := by
  simp [closure_eq_compl_interior_compl]
/-
**interior_eq_compl_closure_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_eq_compl_closure_compl : interior s = (closure sᶜ)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem interior_eq_compl_closure_compl : interior s = (closure sᶜ)ᶜ := by simp
/-
**interior_union_of_disjoint_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_union_of_disjoint_closure (h : Disjoint (closure s) (closure t)) 
: interior (s union t) = interior s union interior t
参数：h : Disjoint (closure s) (closure t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `interior_compl`：interior_compl : interior sᶜ = (closure s)ᶜ
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `interior_union_inter_interior_compl_left_subset`：interior_union_inter_in
terior_compl_left_subset : interior (s union t) inter interior sᶜ subseteq inter
ior t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `interior_union_inter_interior_compl_right_subset`：interior_union_inter_i
nterior_compl_right_subset : interior (s union t) inter interior tᶜ subseteq int
erior s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `subset_interior_union`：subset_interior_union : interior s union interior
 t subseteq interior (s union t)
-/
theorem interior_union_of_disjoint_closure (h : Disjoint (closure s) (closure t)) :
    interior (s ∪ t) = interior s ∪ interior t := by
  have full : interior sᶜ ∪ interior tᶜ = univ := by simpa [disjoint_iff, ← compl_inter] using h
  refine subset_antisymm ?_ subset_interior_union
  rw [← (interior _).inter_univ, ← full, inter_union_distrib_left]
  exact union_subset
    (interior_union_inter_interior_compl_left_subset.trans subset_union_right)
    (interior_union_inter_interior_compl_right_subset.trans subset_union_left)
/-
**closure_inter_of_codisjoint_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_inter_of_codisjoint_interior (h : Codisjoint (interior s) (interio
r t)) : closure (s inter t) = closure s inter closure t
参数：h : Codisjoint (interior s) (interior t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `interior_union_of_disjoint_closure`：interior_union_of_disjoint_closure (
h : Disjoint (closure s) (closure t)) : interior (s union t) = interior s union 
interior t
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
-/
theorem closure_inter_of_codisjoint_interior (h : Codisjoint (interior s) (interior t)) :
    closure (s ∩ t) = closure s ∩ closure t := by
  rw [← compl_inj_iff]
  simp only [← interior_compl, compl_inter]
  apply interior_union_of_disjoint_closure
  simpa only [closure_compl, disjoint_compl_left_iff, ← codisjoint_iff_compl_le_left]
/-
**mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -> x in o -> (o inte
r s).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
theorem mem_closure_iff :
    x ∈ closure s ↔ ∀ o, IsOpen o → x ∈ o → (o ∩ s).Nonempty :=
  ⟨fun h o oo ao =>
    by_contradiction fun os =>
      have : s ⊆ oᶜ := fun x xs xo => os ⟨x, xo, xs⟩
      closure_minimal this (isClosed_compl_iff.2 oo) h ao,
    fun H _ ⟨h₁, h₂⟩ =>
    by_contradiction fun nc =>
      let ⟨_, hc, hs⟩ := H _ h₁.isOpen_compl nc
      hc (h₂ hs)⟩
/-
**closure_inter_open_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_inter_open_nonempty_iff (h : IsOpen t) : (closure s inter t).Nonem
pty ↔ (s inter t).Nonempty
参数：h : IsOpen t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -
> x in o -> (o inter s).Nonempty
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem closure_inter_open_nonempty_iff (h : IsOpen t) :
    (closure s ∩ t).Nonempty ↔ (s ∩ t).Nonempty :=
  ⟨fun ⟨_x, hxcs, hxt⟩ => inter_comm t s ▸ mem_closure_iff.1 hxcs t h hxt, fun h =>
    h.mono <| inf_le_inf_right t subset_closure⟩
/-
**Filter.le_lift'_closure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] (l : Filter X), l ≤ l.lift' clo
sure
参数：l : Filter X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.le_lift'`：le_lift' {f : Filter α} {h : Set α -> Set β} {g : Filte
r β} : g <= f.lift' h ↔ forall s in f, h s in g
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Filter.le_lift'_closure (l : Filter X) : l ≤ l.lift' closure :=
  le_lift'.2 fun _ h => mem_of_superset h subset_closure
/-
**Filter.HasBasis.lift'_closure** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {ι : Sort v} {l : Filter X} {p 
: ι → Prop} {s : ι → Set X},   l.HasBasis p s → (l.lift' closure).HasBasis p fun
 i => closure (s i)
参数：l.lift' closure；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.lift'`：Filter.HasBasis.lift'_interior {l : Filter X} {p 
: ι -> Prop} {s : ι -> Set X} (h : l.HasBasis p s) : (l.lift' interior).HasBasis
 p fun i =>…
· 使用定理 `monotone_closure`：monotone_closure (X : Type*) [TopologicalSpace X] : Mo
notone (@closure X _)
-/
theorem Filter.HasBasis.lift'_closure {l : Filter X} {p : ι → Prop} {s : ι → Set X}
    (h : l.HasBasis p s) : (l.lift' closure).HasBasis p fun i => closure (s i) :=
  h.lift' (monotone_closure X)
/-
**Filter.HasBasis.lift'_closure_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBas
is`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {ι : Sort v} {l : Filter X} {p 
: ι → Prop} {s : ι → Set X},   l.HasBasis p s → (∀ (i : ι), p i → IsClosed (s i)
) → l.lift' closure = l
参数：∀ (i : ι), p i → IsClosed (s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Filter.le_lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X] (l :
 Filter X), l ≤ l.lift' closure
-/
theorem Filter.HasBasis.lift'_closure_eq_self {l : Filter X} {p : ι → Prop} {s : ι → Set X}
    (h : l.HasBasis p s) (hc : ∀ i, p i → IsClosed (s i)) : l.lift' closure = l :=
  le_antisymm (h.ge_iff.2 fun i hi => (hc i hi).closure_eq ▸ mem_lift' (h.mem_of_mem hi))
    l.le_lift'_closure

@[simp]
/-
**Filter.lift'_closure_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {l : Filter X}, l.lift' closure
 = ⊥ ↔ l = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Filter.le_lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X] (l :
 Filter X), l ≤ l.lift' closure
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.lift'_bot`：∀ {α : Type u_1} {β : Type u_2} {h : Set α → Set β}, M
onotone h → ⊥.lift' h = Filter.principal (h ∅)
· 使用定理 `monotone_closure`：monotone_closure (X : Type*) [TopologicalSpace X] : Mo
notone (@closure X _)
· 使用定理 `closure_empty`：closure_empty : closure (∅ : Set X) = ∅
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Filter.lift'_closure_eq_bot {l : Filter X} : l.lift' closure = ⊥ ↔ l = ⊥ :=
  ⟨fun h => bot_unique <| h ▸ l.le_lift'_closure, fun h =>
    h.symm ▸ by rw [lift'_bot (monotone_closure _), closure_empty, principal_empty]⟩
/-
**dense_iff_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_iff_closure_eq : Dense s ↔ closure s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
-/
theorem dense_iff_closure_eq : Dense s ↔ closure s = univ :=
  eq_univ_iff_forall.symm

alias ⟨Dense.closure_eq, _⟩ := dense_iff_closure_eq
/-
**interior_eq_empty_iff_dense_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_eq_empty_iff_dense_compl : interior s = ∅ ↔ Dense sᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `Set.compl_univ_iff`：compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem interior_eq_empty_iff_dense_compl : interior s = ∅ ↔ Dense sᶜ := by
  rw [dense_iff_closure_eq, closure_compl, compl_univ_iff]
/-
**Dense.interior_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.interior_compl (h : Dense s) : interior sᶜ = ∅
参数：h : Dense s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `interior_eq_empty_iff_dense_compl`：interior_eq_empty_iff_dense_compl : i
nterior s = ∅ ↔ Dense sᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem Dense.interior_compl (h : Dense s) : interior sᶜ = ∅ :=
  interior_eq_empty_iff_dense_compl.2 <| by rwa [compl_compl]

/-- The closure of a set `s` is dense if and only if `s` is dense. -/
@[simp]
/-
**dense_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_closure : Dense (closure s) ↔ Dense s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dense.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), Dens
e s = ∀ (x : X), x ∈ closure s
· 使用定理 `closure_closure`：closure_closure : closure (closure s) = closure s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The closure of a set `s` is dense if and only if `s` is dense.
-/
theorem dense_closure : Dense (closure s) ↔ Dense s := by
  rw [Dense, Dense, closure_closure]

protected alias ⟨_, Dense.closure⟩ := dense_closure
alias ⟨Dense.of_closure, _⟩ := dense_closure

@[simp]
/-
**dense_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_univ : Dense (univ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `trivial`：True
-/
theorem dense_univ : Dense (univ : Set X) := fun _ => subset_closure trivial

/-- A set is dense if and only if it has a nonempty intersection with each nonempty open set. -/
/-
**dense_iff_inter_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_iff_inter_open : Dense s ↔ forall U, IsOpen U -> U.Nonempty -> (U in
ter s).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -
> x in o -> (o inter s).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
A set is dense if and only if it has a nonempty intersection with each nonempty 
open set.
-/
theorem dense_iff_inter_open :
    Dense s ↔ ∀ U, IsOpen U → U.Nonempty → (U ∩ s).Nonempty := by
  constructor <;> intro h
  · rintro U U_op ⟨x, x_in⟩
    exact mem_closure_iff.1 (h _) U U_op x_in
  · intro x
    rw [mem_closure_iff]
    intro U U_op x_in
    exact h U U_op ⟨_, x_in⟩

alias ⟨Dense.inter_open_nonempty, _⟩ := dense_iff_inter_open
/-
**Dense.exists_mem_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.exists_mem_open (hs : Dense s) {U : Set X} (ho : IsOpen U) (hne : U.
Nonempty) : exists x in s, x in U
参数：hs : Dense s；ho : IsOpen U；hne : U.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.inter_open_nonempty`：∀ {X : Type u} [inst : TopologicalSpace X] {s
 : Set X},   Dense s → ∀ (U : Set X), IsOpen U → U.Nonempty → (U ∩ s).Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Dense.exists_mem_open (hs : Dense s) {U : Set X} (ho : IsOpen U)
    (hne : U.Nonempty) : ∃ x ∈ s, x ∈ U :=
  let ⟨x, hx⟩ := hs.inter_open_nonempty U ho hne
  ⟨x, hx.2, hx.1⟩
/-
**Dense.nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.nonempty_iff (hs : Dense s) : s.Nonempty ↔ Nonempty X
参数：hs : Dense s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.inter_open_nonempty`：∀ {X : Type u} [inst : TopologicalSpace X] {s
 : Set X},   Dense s → ∀ (U : Set X), IsOpen U → U.Nonempty → (U ∩ s).Nonempty
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `trivial`：True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Dense.nonempty_iff (hs : Dense s) : s.Nonempty ↔ Nonempty X :=
  ⟨fun ⟨x, _⟩ => ⟨x⟩, fun ⟨x⟩ =>
    let ⟨y, hy⟩ := hs.inter_open_nonempty _ isOpen_univ ⟨x, trivial⟩
    ⟨y, hy.2⟩⟩
/-
**Dense.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.nonempty [h : Nonempty X] (hs : Dense s) : s.Nonempty
参数：hs : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Dense.nonempty_iff`：Dense.nonempty_iff (hs : Dense s) : s.Nonempty ↔ Non
empty X
-/
theorem Dense.nonempty [h : Nonempty X] (hs : Dense s) : s.Nonempty :=
  hs.nonempty_iff.2 h

@[mono, gcongr]
/-
**Dense.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
参数：h : s₁ subseteq s₂；hd : Dense s₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem Dense.mono (h : s₁ ⊆ s₂) (hd : Dense s₁) : Dense s₂ := fun x =>
  closure_mono h (hd x)
/-
**DenseRange.of_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DenseRange.of_comp {α β : Type*} {f : α -> X} {g : β -> α} (h : DenseRange
 (f ∘ g)) : DenseRange f
参数：h : DenseRange (f ∘ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
lemma DenseRange.of_comp {α β : Type*} {f : α → X} {g : β → α}
    (h : DenseRange (f ∘ g)) : DenseRange f :=
  Dense.mono (range_comp_subset_range g f) h

/-- Complement to a singleton is dense if and only if the singleton is not an open set. -/
/-
**dense_compl_singleton_iff_not_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_compl_singleton_iff_not_open : Dense ({x}ᶜ : Set X) ↔ ¬IsOpen ({x} :
 Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Dense.inter_open_nonempty`：∀ {X : Type u} [inst : TopologicalSpace X] {s
 : Set X},   Dense s → ∀ (U : Set X), IsOpen U → U.Nonempty → (U ∩ s).Nonempty
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dense_iff_inter_open`：dense_iff_inter_open : Dense s ↔ forall U, IsOpen 
U -> U.Nonempty -> (U inter s).Nonempty
· 使用定理 `Set.inter_compl_nonempty_iff`：inter_compl_nonempty_iff {s t : Set α} : (
s inter tᶜ).Nonempty ↔ ¬s subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_singleton_iff_nonempty_unique_mem`：eq_singleton_iff_nonempty_uniq
ue_mem : s = {a} ↔ s.Nonempty ∧ forall x in s, x = a

--- 原说明 ---
Complement to a singleton is dense if and only if the singleton is not an open s
et.
-/
theorem dense_compl_singleton_iff_not_open :
    Dense ({x}ᶜ : Set X) ↔ ¬IsOpen ({x} : Set X) := by
  constructor
  · intro hd ho
    exact (hd.inter_open_nonempty _ ho (singleton_nonempty _)).ne_empty (inter_compl_self _)
  · refine fun ho => dense_iff_inter_open.2 fun U hU hne => inter_compl_nonempty_iff.2 fun hUx => ?_
    obtain rfl : U = {x} := eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, hUx⟩
    exact ho hU

/-- If a closed property holds for a dense subset, it holds for the whole space. -/
@[elab_as_elim]
/-
**Dense.induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Dense.induction (hs : Dense s) {P : X -> Prop} (mem : forall x in s, P x) 
(isClosed : IsClosed { x | P x }) (x : X) : P x
参数：hs : Dense s；mem : forall x in s, P x；isClosed : IsClosed { x | P x }；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
If a closed property holds for a dense subset, it holds for the whole space.
-/
lemma Dense.induction (hs : Dense s) {P : X → Prop}
    (mem : ∀ x ∈ s, P x) (isClosed : IsClosed { x | P x }) (x : X) : P x :=
  hs.closure_eq.symm.subset.trans (isClosed.closure_subset_iff.mpr mem) (Set.mem_univ _)
/-
**IsOpen.subset_interior_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.subset_interior_closure {s : Set X} (s_open : IsOpen s) : s subsete
q interior (closure s)
参数：s_open : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.subset_interior_iff`：IsOpen.subset_interior_iff (h₁ : IsOpen s) :
 s subseteq interior t ↔ s subseteq t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem IsOpen.subset_interior_closure {s : Set X} (s_open : IsOpen s) :
    s ⊆ interior (closure s) := s_open.subset_interior_iff.mpr subset_closure
/-
**IsClosed.closure_interior_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.closure_interior_subset {s : Set X} (s_closed : IsClosed s) : clo
sure (interior s) subseteq s
参数：s_closed : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem IsClosed.closure_interior_subset {s : Set X} (s_closed : IsClosed s) :
    closure (interior s) ⊆ s := s_closed.closure_subset_iff.mpr interior_subset
/-
**closure_interior_idem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, closure (interior 
(closure (interior s))) = closure (interior s)
参数：interior (closure (interior s))；interior s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IsClosed.closure_interior_subset`：IsClosed.closure_interior_subset {s : 
Set X} (s_closed : IsClosed s) : closure (interior s) subseteq s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `IsOpen.subset_interior_closure`：IsOpen.subset_interior_closure {s : Set 
X} (s_open : IsOpen s) : s subseteq interior (closure s)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
@[simp] theorem closure_interior_idem :
    closure (interior (closure (interior s))) = closure (interior s) :=
  isClosed_closure.closure_interior_subset.antisymm
    (closure_mono isOpen_interior.subset_interior_closure)
/-
**interior_closure_idem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, interior (closure 
(interior (closure s))) = interior (closure s)
参数：closure (interior (closure s))；closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `IsClosed.closure_interior_subset`：IsClosed.closure_interior_subset {s : 
Set X} (s_closed : IsClosed s) : closure (interior s) subseteq s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsOpen.subset_interior_closure`：IsOpen.subset_interior_closure {s : Set 
X} (s_open : IsOpen s) : s subseteq interior (closure s)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
@[simp] theorem interior_closure_idem :
    interior (closure (interior (closure s))) = interior (closure s) :=
  (interior_mono isClosed_closure.closure_interior_subset).antisymm
    isOpen_interior.subset_interior_closure

end Closure

section Frontier

@[simp]
/-
**closure_sdiff_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_sdiff_interior (s : Set X) : closure s \ interior s = frontier s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem closure_sdiff_interior (s : Set X) : closure s \ interior s = frontier s :=
  rfl

@[deprecated (since := "2026-06-03")] alias closure_diff_interior := closure_sdiff_interior

/-- Interior and frontier are disjoint. -/
/-
**disjoint_interior_frontier** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjoint_interior_frontier : Disjoint (interior s) (frontier s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_sdiff_interior`：closure_sdiff_interior (s : Set X) : closure s \
 interior s = frontier s
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅

--- 原说明 ---
Interior and frontier are disjoint.
-/
lemma disjoint_interior_frontier : Disjoint (interior s) (frontier s) := by
  rw [disjoint_iff_inter_eq_empty, ← closure_sdiff_interior, sdiff_eq,
    ← inter_assoc, inter_comm, ← inter_assoc, compl_inter_self, empty_inter]

@[simp]
/-
**closure_sdiff_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_sdiff_frontier (s : Set X) : closure s \ frontier s = interior s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `Set.sdiff_sdiff_right_self`：sdiff_sdiff_right_self (s t : Set α) : s \ (
s \ t) = s inter t
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `interior_subset_closure`：interior_subset_closure : interior s subseteq c
losure s
-/
theorem closure_sdiff_frontier (s : Set X) : closure s \ frontier s = interior s := by
  rw [frontier, sdiff_sdiff_right_self, inter_eq_self_of_subset_right interior_subset_closure]

@[deprecated (since := "2026-06-03")] alias closure_diff_frontier := closure_sdiff_frontier

@[simp]
/-
**self_sdiff_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_sdiff_frontier (s : Set X) : s \ frontier s = interior s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `Set.sdiff_sdiff_right`：sdiff_sdiff_right {s t u : Set α} : s \ (t \ u) =
 s \ t union s inter u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
-/
theorem self_sdiff_frontier (s : Set X) : s \ frontier s = interior s := by
  rw [frontier, sdiff_sdiff_right, sdiff_eq_empty.2 subset_closure,
    inter_eq_self_of_subset_right interior_subset, empty_union]

@[deprecated (since := "2026-06-03")] alias self_diff_frontier := self_sdiff_frontier
/-
**mem_interior_iff_notMem_frontier** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_interior_iff_notMem_frontier {s : Set X} {x : X} (hx : x in s) : x in 
interior s ↔ x ∉ frontier s
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_interior_iff_notMem_frontier {s : Set X} {x : X} (hx : x ∈ s) :
    x ∈ interior s ↔ x ∉ frontier s := by
  simp [← self_sdiff_frontier, hx]
/-
**mem_frontier_iff_notMem_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_frontier_iff_notMem_interior {s : Set X} {x : X} (hx : x in s) : x in 
frontier s ↔ x ∉ interior s
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_frontier_iff_notMem_interior {s : Set X} {x : X} (hx : x ∈ s) :
    x ∈ frontier s ↔ x ∉ interior s := by
  simp [← self_sdiff_frontier, hx]
/-
**frontier_eq_closure_inter_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_eq_closure_inter_closure : frontier s = closure s inter closure s
ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
-/
theorem frontier_eq_closure_inter_closure : frontier s = closure s ∩ closure sᶜ := by
  rw [closure_compl, frontier, sdiff_eq]
/-
**frontier_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_subset_closure : frontier s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
theorem frontier_subset_closure : frontier s ⊆ closure s :=
  sdiff_subset
/-
**frontier_subset_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_subset_iff_isClosed : frontier s subseteq s ↔ IsClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem frontier_subset_iff_isClosed : frontier s ⊆ s ↔ IsClosed s := by
  rw [frontier, sdiff_subset_iff, union_eq_right.mpr interior_subset, closure_subset_iff_isClosed]

alias ⟨_, IsClosed.frontier_subset⟩ := frontier_subset_iff_isClosed
/-
**frontier_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_closure_subset : frontier (closure s) subseteq frontier s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_subset_sdiff`：sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ su
bseteq s₂ -> t₂ subseteq t₁ -> s₁ \ t₁ subseteq s₂ \ t₂
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `closure_closure`：closure_closure : closure (closure s) = closure s
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem frontier_closure_subset : frontier (closure s) ⊆ frontier s :=
  sdiff_subset_sdiff closure_closure.subset <| interior_mono subset_closure
/-
**frontier_interior_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_interior_subset : frontier (interior s) subseteq frontier s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_subset_sdiff`：sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ su
bseteq s₂ -> t₂ subseteq t₁ -> s₁ \ t₁ subseteq s₂ \ t₂
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_interior`：interior_interior : interior (interior s) = interior 
s
-/
theorem frontier_interior_subset : frontier (interior s) ⊆ frontier s :=
  sdiff_subset_sdiff (closure_mono interior_subset) interior_interior.symm.subset

/-- The complement of a set has the same frontier as the original set. -/
@[simp]
/-
**frontier_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_compl (s : Set X) : frontier sᶜ = frontier s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_eq_closure_inter_closure`：frontier_eq_closure_inter_closure : f
rontier s = closure s inter closure sᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The complement of a set has the same frontier as the original set.
-/
theorem frontier_compl (s : Set X) : frontier sᶜ = frontier s := by
  simp only [frontier_eq_closure_inter_closure, compl_compl, inter_comm]

@[simp]
/-
**frontier_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_univ : frontier (univ : Set X) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_univ : frontier (univ : Set X) = ∅ := by simp [frontier]

@[simp]
/-
**frontier_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_empty : frontier (∅ : Set X) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `interior_empty`：interior_empty : interior (∅ : Set X) = ∅
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_empty : frontier (∅ : Set X) = ∅ := by simp [frontier]
/-
**frontier_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_inter_subset (s t : Set X) : frontier (s inter t) subseteq fronti
er s inter closure t union closure s inter frontier t
参数：s t : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `frontier_eq_closure_inter_closure`：frontier_eq_closure_inter_closure : f
rontier s = closure s inter closure sᶜ
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `closure_union`：closure_union : closure (s union t) = closure s union clo
sure t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `closure_inter_subset_inter_closure`：closure_inter_subset_inter_closure (
s t : Set X) : closure (s inter t) subseteq closure s inter closure t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_inter_subset (s t : Set X) :
    frontier (s ∩ t) ⊆ frontier s ∩ closure t ∪ closure s ∩ frontier t := by
  simp only [frontier_eq_closure_inter_closure, compl_inter, closure_union]
  refine (inter_subset_inter_left _ (closure_inter_subset_inter_closure s t)).trans_eq ?_
  simp only [inter_union_distrib_left, inter_assoc,
    inter_comm (closure t)]
/-
**frontier_union_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_union_subset (s t : Set X) : frontier (s union t) subseteq fronti
er s inter closure tᶜ union closure sᶜ inter frontier t
参数：s t : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `frontier_compl`：frontier_compl (s : Set X) : frontier sᶜ = frontier s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `frontier_inter_subset`：frontier_inter_subset (s t : Set X) : frontier (s
 inter t) subseteq frontier s inter closure t union closure s inter frontier t
-/
theorem frontier_union_subset (s t : Set X) :
    frontier (s ∪ t) ⊆ frontier s ∩ closure tᶜ ∪ closure sᶜ ∩ frontier t := by
  simpa only [frontier_compl, ← compl_union] using frontier_inter_subset sᶜ tᶜ
/-
**IsClosed.frontier_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.frontier_eq (hs : IsClosed s) : frontier s = s \ interior s
参数：hs : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem IsClosed.frontier_eq (hs : IsClosed s) : frontier s = s \ interior s := by
  rw [frontier, hs.closure_eq]
/-
**IsOpen.frontier_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.frontier_eq (hs : IsOpen s) : frontier s = closure s \ s
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
-/
theorem IsOpen.frontier_eq (hs : IsOpen s) : frontier s = closure s \ s := by
  rw [frontier, hs.interior_eq]
/-
**IsOpen.inter_frontier_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.inter_frontier_eq (hs : IsOpen s) : s inter frontier s = ∅
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.frontier_eq`：IsOpen.frontier_eq (hs : IsOpen s) : frontier s = cl
osure s \ s
· 使用定理 `Set.inter_sdiff_self`：inter_sdiff_self (a b : Set α) : a inter (b \ a) =
 ∅
-/
theorem IsOpen.inter_frontier_eq (hs : IsOpen s) : s ∩ frontier s = ∅ := by
  rw [hs.frontier_eq, inter_sdiff_self]
/-
**disjoint_frontier_iff_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_frontier_iff_isOpen : Disjoint (frontier s) s ↔ IsOpen s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `frontier_subset_iff_isClosed`：frontier_subset_iff_isClosed : frontier s 
subseteq s ↔ IsClosed s
· 使用定理 `frontier_compl`：frontier_compl (s : Set X) : frontier sᶜ = frontier s
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_frontier_iff_isOpen : Disjoint (frontier s) s ↔ IsOpen s := by
  rw [← isClosed_compl_iff, ← frontier_subset_iff_isClosed,
    frontier_compl, subset_compl_iff_disjoint_right]

/-- The frontier of a set is closed. -/
/-
**isClosed_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_frontier : IsClosed (frontier s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_eq_closure_inter_closure`：frontier_eq_closure_inter_closure : f
rontier s = closure s inter closure sᶜ
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
The frontier of a set is closed.
-/
theorem isClosed_frontier : IsClosed (frontier s) := by
  rw [frontier_eq_closure_inter_closure]; exact IsClosed.inter isClosed_closure isClosed_closure

/-- The frontier of a closed set has no interior point. -/
/-
**interior_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_frontier (h : IsClosed s) : interior (frontier s) = ∅
参数：h : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.frontier_eq`：IsClosed.frontier_eq (hs : IsClosed s) : frontier 
s = s \ interior s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `Set.inter_sdiff_self`：inter_sdiff_self (a b : Set α) : a inter (b \ a) =
 ∅

--- 原说明 ---
The frontier of a closed set has no interior point.
-/
theorem interior_frontier (h : IsClosed s) : interior (frontier s) = ∅ := by
  have A : frontier s = s \ interior s := h.frontier_eq
  have B : interior (frontier s) ⊆ interior s := by rw [A]; exact interior_mono sdiff_subset
  have C : interior (frontier s) ⊆ frontier s := interior_subset
  have : interior (frontier s) ⊆ interior s ∩ (s \ interior s) :=
    subset_inter B (by simpa [A] using C)
  rwa [inter_sdiff_self, subset_empty_iff] at this
/-
**closure_eq_interior_union_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_eq_interior_union_frontier (s : Set X) : closure s = interior s un
ion frontier s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
· 使用定理 `interior_subset_closure`：interior_subset_closure : interior s subseteq c
losure s
-/
theorem closure_eq_interior_union_frontier (s : Set X) : closure s = interior s ∪ frontier s :=
  (union_sdiff_cancel interior_subset_closure).symm
/-
**closure_eq_self_union_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_eq_self_union_frontier (s : Set X) : closure s = s union frontier 
s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_sdiff_cancel'`：union_sdiff_cancel' {s t u : Set α} (h₁ : s sub
seteq t) (h₂ : t subseteq u) : t union u \ s = u
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem closure_eq_self_union_frontier (s : Set X) : closure s = s ∪ frontier s :=
  (union_sdiff_cancel' interior_subset subset_closure).symm
/-
**Disjoint.frontier_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.frontier_left (ht : IsOpen t) (hd : Disjoint s t) : Disjoint (fro
ntier s) t
参数：ht : IsOpen t；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `frontier_subset_closure`：frontier_subset_closure : frontier s subseteq c
losure s
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
-/
theorem Disjoint.frontier_left (ht : IsOpen t) (hd : Disjoint s t) : Disjoint (frontier s) t :=
  subset_compl_iff_disjoint_right.1 <|
    frontier_subset_closure.trans <| closure_minimal (disjoint_left.1 hd) <| isClosed_compl_iff.2 ht
/-
**Disjoint.frontier_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.frontier_right (hs : IsOpen s) (hd : Disjoint s t) : Disjoint s (
frontier t)
参数：hs : IsOpen s；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Disjoint.frontier_left`：Disjoint.frontier_left (ht : IsOpen t) (hd : Dis
joint s t) : Disjoint (frontier s) t
-/
theorem Disjoint.frontier_right (hs : IsOpen s) (hd : Disjoint s t) : Disjoint s (frontier t) :=
  (hd.symm.frontier_left hs).symm
/-
**frontier_eq_inter_compl_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_eq_inter_compl_interior : frontier s = (interior s)ᶜ inter (inter
ior sᶜ)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `frontier_compl`：frontier_compl (s : Set X) : frontier sᶜ = frontier s
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `closure_sdiff_interior`：closure_sdiff_interior (s : Set X) : closure s \
 interior s = frontier s
-/
theorem frontier_eq_inter_compl_interior : frontier s = (interior s)ᶜ ∩ (interior sᶜ)ᶜ := by
  rw [← frontier_compl, ← closure_compl, ← sdiff_eq, closure_sdiff_interior]
/-
**compl_frontier_eq_union_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_frontier_eq_union_interior : (frontier s)ᶜ = interior s union interi
or sᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_eq_inter_compl_interior`：frontier_eq_inter_compl_interior : fro
ntier s = (interior s)ᶜ inter (interior sᶜ)ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_frontier_eq_union_interior : (frontier s)ᶜ = interior s ∪ interior sᶜ := by
  rw [frontier_eq_inter_compl_interior]
  simp only [compl_inter, compl_compl]

end Frontier

