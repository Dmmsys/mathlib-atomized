/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.BoolIndicator
public import Mathlib.Topology.ContinuousOn

/-!
# Clopen sets

A clopen set is a set that is both closed and open.
-/

public section

open Set Filter Topology TopologicalSpace

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Clopen

/-
**IsClopen.isOpen** 是 Mathlib 中的一个定理，位于命名空间 `IsClopen`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, IsClopen s → IsOpe
n s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem IsClopen.isOpen (hs : IsClopen s) : IsOpen s := hs.2
/-
**IsClopen.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `IsClopen`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, IsClopen s → IsClo
sed s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected theorem IsClopen.isClosed (hs : IsClopen s) : IsClosed s := hs.1
/-
**isClopen_iff_frontier_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_iff_frontier_eq_empty : IsClopen s ↔ frontier s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClopen.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), I
sClopen s = (IsClosed s ∧ IsOpen s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_eq_iff_isClosed`：closure_eq_iff_isClosed : closure s = s ↔ IsClo
sed s
· 使用定理 `interior_eq_iff_isOpen`：interior_eq_iff_isOpen : interior s = s ↔ IsOpen
 s
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem isClopen_iff_frontier_eq_empty : IsClopen s ↔ frontier s = ∅ := by
  rw [IsClopen, ← closure_eq_iff_isClosed, ← interior_eq_iff_isOpen, frontier, sdiff_eq_empty]
  refine ⟨fun h => (h.1.trans h.2.symm).subset, fun h => ?_⟩
  exact ⟨(h.trans interior_subset).antisymm subset_closure,
    interior_subset.antisymm (subset_closure.trans h)⟩

@[simp] alias ⟨IsClopen.frontier_eq, _⟩ := isClopen_iff_frontier_eq_empty
/-
**IsClopen.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClopen.union (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s union t)
参数：hs : IsClopen s；ht : IsClopen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsClopen.union (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∪ t) :=
  ⟨hs.1.union ht.1, hs.2.union ht.2⟩
/-
**IsClopen.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClopen.inter (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s inter t)
参数：hs : IsClopen s；ht : IsClopen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsClopen.inter (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
/-
**isClopen_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_empty : IsClopen (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
-/
theorem isClopen_empty : IsClopen (∅ : Set X) := ⟨isClosed_empty, isOpen_empty⟩
/-
**isClopen_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_univ : IsClopen (univ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem isClopen_univ : IsClopen (univ : Set X) := ⟨isClosed_univ, isOpen_univ⟩
/-
**IsClopen.compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
参数：hs : IsClopen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ :=
  ⟨hs.2.isClosed_compl, hs.1.isOpen_compl⟩

@[simp]
/-
**isClopen_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_compl_iff : IsClopen sᶜ ↔ IsClopen s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClopen.compl`：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem isClopen_compl_iff : IsClopen sᶜ ↔ IsClopen s :=
  ⟨fun h => compl_compl s ▸ IsClopen.compl h, IsClopen.compl⟩
/-
**IsClopen.diff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClopen.diff (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s \ t)
参数：hs : IsClopen s；ht : IsClopen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClopen.inter`：IsClopen.inter (hs : IsClopen s) (ht : IsClopen t) : IsC
lopen (s inter t)
· 使用定理 `IsClopen.compl`：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
-/
theorem IsClopen.diff (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s \ t) :=
  hs.inter ht.compl
/-
**IsClopen.himp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClopen.himp (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ⇨ t)
参数：hs : IsClopen s；ht : IsClopen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
· 使用定理 `IsClopen.union`：IsClopen.union (hs : IsClopen s) (ht : IsClopen t) : IsC
lopen (s union t)
· 使用定理 `IsClopen.compl`：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
-/
lemma IsClopen.himp (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ⇨ t) := by
  simpa [himp_eq] using ht.union hs.compl
/-
**IsClopen.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClopen.prod {t : Set Y} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (
s ×ˢ t)
参数：hs : IsClopen s；ht : IsClopen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.prod`：IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁
) (h₂ : IsClosed s₂) : IsClosed (s₁ ×ˢ s₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsClopen.prod {t : Set Y} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
/-
**isClopen_iUnion_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_iUnion_of_finite {Y} [Finite Y] {s : Y -> Set X} (h : forall i, I
sClopen (s i)) : IsClopen (⋃ i, s i)
参数：h : forall i, IsClopen (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iUnion_of_finite`：isClosed_iUnion_of_finite [Finite ι] {s : ι -
> Set X} (h : forall i, IsClosed (s i)) : IsClosed (⋃ i, s i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isClopen_iUnion_of_finite {Y} [Finite Y] {s : Y → Set X} (h : ∀ i, IsClopen (s i)) :
    IsClopen (⋃ i, s i) :=
  ⟨isClosed_iUnion_of_finite (forall_and.1 h).1, isOpen_iUnion (forall_and.1 h).2⟩
/-
**Set.Finite.isClopen_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isClopen_biUnion {Y} {s : Set Y} {f : Y -> Set X} (hs : s.Finit
e) (h : forall i in s, IsClopen <| f i) : IsClopen (⋃ i in s, f i)
参数：hs : s.Finite；h : forall i in s, IsClopen <| f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isClosed_biUnion`：Set.Finite.isClosed_biUnion {s : Set α} {f 
: α -> Set X} (hs : s.Finite) (h : forall i in s, IsClosed (f i)) : IsClosed (⋃ 
i in s, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Set.Finite.isClopen_biUnion {Y} {s : Set Y} {f : Y → Set X} (hs : s.Finite)
    (h : ∀ i ∈ s, IsClopen <| f i) : IsClopen (⋃ i ∈ s, f i) :=
  ⟨hs.isClosed_biUnion fun i hi => (h i hi).1, isOpen_biUnion fun i hi => (h i hi).2⟩
/-
**isClopen_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_biUnion_finset {Y} {s : Finset Y} {f : Y -> Set X} (h : forall i 
in s, IsClopen <| f i) : IsClopen (⋃ i in s, f i)
参数：h : forall i in s, IsClopen <| f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isClopen_biUnion`：Set.Finite.isClopen_biUnion {Y} {s : Set Y}
 {f : Y -> Set X} (hs : s.Finite) (h : forall i in s, IsClopen <| f i) : IsClope
n (⋃ i in s, f i)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem isClopen_biUnion_finset {Y} {s : Finset Y} {f : Y → Set X}
    (h : ∀ i ∈ s, IsClopen <| f i) : IsClopen (⋃ i ∈ s, f i) :=
  s.finite_toSet.isClopen_biUnion h
/-
**isClopen_iInter_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_iInter_of_finite {Y} [Finite Y] {s : Y -> Set X} (h : forall i, I
sClopen (s i)) : IsClopen (⋂ i, s i)
参数：h : forall i, IsClopen (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `isOpen_iInter_of_finite`：isOpen_iInter_of_finite [Finite ι] {s : ι -> Se
t X} (h : forall i, IsOpen (s i)) : IsOpen (⋂ i, s i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isClopen_iInter_of_finite {Y} [Finite Y] {s : Y → Set X} (h : ∀ i, IsClopen (s i)) :
    IsClopen (⋂ i, s i) :=
  ⟨isClosed_iInter (forall_and.1 h).1, isOpen_iInter_of_finite (forall_and.1 h).2⟩
/-
**Set.Finite.isClopen_biInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isClopen_biInter {Y} {s : Set Y} (hs : s.Finite) {f : Y -> Set 
X} (h : forall i in s, IsClopen (f i)) : IsClopen (⋂ i in s, f i)
参数：hs : s.Finite；h : forall i in s, IsClopen (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Finite.isOpen_biInter`：Set.Finite.isOpen_biInter {s : Set α} {f : α 
-> Set X} (hs : s.Finite) (h : forall i in s, IsOpen (f i)) : IsOpen (⋂ i in s, 
f i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Set.Finite.isClopen_biInter {Y} {s : Set Y} (hs : s.Finite) {f : Y → Set X}
    (h : ∀ i ∈ s, IsClopen (f i)) : IsClopen (⋂ i ∈ s, f i) :=
  ⟨isClosed_biInter fun i hi => (h i hi).1, hs.isOpen_biInter fun i hi => (h i hi).2⟩
/-
**isClopen_biInter_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_biInter_finset {Y} {s : Finset Y} {f : Y -> Set X} (h : forall i 
in s, IsClopen (f i)) : IsClopen (⋂ i in s, f i)
参数：h : forall i in s, IsClopen (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isClopen_biInter`：Set.Finite.isClopen_biInter {Y} {s : Set Y}
 (hs : s.Finite) {f : Y -> Set X} (h : forall i in s, IsClopen (f i)) : IsClopen
 (⋂ i in s, f i)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem isClopen_biInter_finset {Y} {s : Finset Y} {f : Y → Set X}
    (h : ∀ i ∈ s, IsClopen (f i)) : IsClopen (⋂ i ∈ s, f i) :=
  s.finite_toSet.isClopen_biInter h
/-
**IsClopen.preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X -> Y} (hf : Continuo
us f) : IsClopen (f ⁻¹' s)
参数：h : IsClopen s；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X → Y} (hf : Continuous f) :
    IsClopen (f ⁻¹' s) :=
  ⟨h.1.preimage hf, h.2.preimage hf⟩
/-
**ContinuousOn.preimage_isClopen_of_isClopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.preimage_isClopen_of_isClopen {f : X -> Y} {s : Set X} {t : S
et Y} (hf : ContinuousOn f s) (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s 
inter f ⁻¹' t)
参数：hf : ContinuousOn f s；hs : IsClopen s；ht : IsClopen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.preimage_isClosed_of_isClosed`：ContinuousOn.preimage_isClos
ed_of_isClosed {t : Set β} (hf : ContinuousOn f s) (hs : IsClosed s) (ht : IsClo
sed t) : IsClosed (s inter f ⁻¹'…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ContinuousOn.preimage_isClopen_of_isClopen {f : X → Y} {s : Set X} {t : Set Y}
    (hf : ContinuousOn f s) (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ f ⁻¹' t) :=
  ⟨ContinuousOn.preimage_isClosed_of_isClosed hf hs.1 ht.1,
    ContinuousOn.isOpen_inter_preimage hf hs.2 ht.2⟩

/-- The intersection of a disjoint covering by two open sets of a clopen set will be clopen. -/
/-
**isClopen_inter_of_disjoint_cover_clopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_inter_of_disjoint_cover_clopen {s a b : Set X} (h : IsClopen s) (
cover : s subseteq a union b) (ha : IsOpen a) (hb : IsOpen b) (hab : Disjoint a 
b) : IsClopen (s inter a)
参数：h : IsClopen s；cover : s subseteq a union b；ha : IsOpen a；hb : IsOpen b；hab :
 Disjoint a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.notMem_of_mem_compl`：notMem_of_mem_compl {s : Set α} {x : α} (h : x 
in sᶜ) : x ∉ s
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The intersection of a disjoint covering by two open sets of a clopen set will be
 clopen.
-/
theorem isClopen_inter_of_disjoint_cover_clopen {s a b : Set X} (h : IsClopen s) (cover : s ⊆ a ∪ b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : Disjoint a b) : IsClopen (s ∩ a) := by
  refine ⟨?_, IsOpen.inter h.2 ha⟩
  have : IsClosed (s ∩ bᶜ) := IsClosed.inter h.1 (isClosed_compl_iff.2 hb)
  convert! this using 1
  refine (inter_subset_inter_right s hab.subset_compl_right).antisymm ?_
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨hx₁, by simpa [notMem_of_mem_compl hx₂] using cover hx₁⟩

/-- Variant of `isClopen_inter_of_disjoint_cover_clopen` with weaker disjointness condition. -/
/-
**isClopen_inter_of_disjoint_cover_clopen'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClopen_inter_of_disjoint_cover_clopen' {s a b : Set X} (h : IsClopen s) 
(cover : s subseteq a union b) (ha : IsOpen a) (hb : IsOpen b) (hab : s inter a 
inter b = ∅) : IsClopen (s inter a)
参数：h : IsClopen s；cover : s subseteq a union b；ha : IsOpen a；hb : IsOpen b；hab :
 s inter a inter b = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isClopen_inter_of_disjoint_cover_clopen`：isClopen_inter_of_disjoint_cove
r_clopen {s a b : Set X} (h : IsClopen s) (cover : s subseteq a union b) (ha : I
sOpen a) (hb : IsOpen b) (hab…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅

--- 原说明 ---
Variant of `isClopen_inter_of_disjoint_cover_clopen` with weaker disjointness co
ndition.
-/
lemma isClopen_inter_of_disjoint_cover_clopen' {s a b : Set X} (h : IsClopen s) (cover : s ⊆ a ∪ b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : s ∩ a ∩ b = ∅) : IsClopen (s ∩ a) := by
  rw [show s ∩ a = s ∩ (s ∩ a) by simp]
  refine isClopen_inter_of_disjoint_cover_clopen h ?_ (h.2.inter ha) (h.2.inter hb) ?_
  · rw [← inter_union_distrib_left]
    exact subset_inter .rfl cover
  · rw [disjoint_iff_inter_eq_empty, inter_comm s b, ← inter_assoc, hab, empty_inter]
/-
**isClopen_of_disjoint_cover_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_of_disjoint_cover_open {a b : Set X} (cover : univ subseteq a uni
on b) (ha : IsOpen a) (hb : IsOpen b) (hab : Disjoint a b) : IsClopen a
参数：cover : univ subseteq a union b；ha : IsOpen a；hb : IsOpen b；hab : Disjoint a 
b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClopen_inter_of_disjoint_cover_clopen`：isClopen_inter_of_disjoint_cove
r_clopen {s a b : Set X} (h : IsClopen s) (cover : s subseteq a union b) (ha : I
sOpen a) (hb : IsOpen b) (hab…
· 使用定理 `isClopen_univ`：isClopen_univ : IsClopen (univ : Set X)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem isClopen_of_disjoint_cover_open {a b : Set X} (cover : univ ⊆ a ∪ b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : Disjoint a b) : IsClopen a :=
  univ_inter a ▸ isClopen_inter_of_disjoint_cover_clopen isClopen_univ cover ha hb hab

@[simp]
/-
**isClopen_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_discrete [DiscreteTopology X] (s : Set X) : IsClopen s
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_discrete`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Discret
eTopology α] (s : Set α), IsClosed s
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
-/
theorem isClopen_discrete [DiscreteTopology X] (s : Set X) : IsClopen s :=
  ⟨isClosed_discrete _, isOpen_discrete _⟩
/-
**isClopen_range_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_range_inl : IsClopen (range (Sum.inl : X -> X oplus Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_range_inl`：isClosed_range_inl : IsClosed (range (inl : X -> X o
plus Y))
· 使用引理 `isOpen_range_inl`：isOpen_range_inl : IsOpen (range (inl : X -> X oplus Y
))
-/
theorem isClopen_range_inl : IsClopen (range (Sum.inl : X → X ⊕ Y)) :=
  ⟨isClosed_range_inl, isOpen_range_inl⟩
/-
**isClopen_range_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_range_inr : IsClopen (range (Sum.inr : Y -> X oplus Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_range_inr`：isClosed_range_inr : IsClosed (range (inr : Y -> X o
plus Y))
· 使用引理 `isOpen_range_inr`：isOpen_range_inr : IsOpen (range (inr : Y -> X oplus Y
))
-/
theorem isClopen_range_inr : IsClopen (range (Sum.inr : Y → X ⊕ Y)) :=
  ⟨isClosed_range_inr, isOpen_range_inr⟩
/-
**isClopen_range_sigmaMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_range_sigmaMk {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
 {i : ι} : IsClopen (Set.range (@Sigma.mk ι X i))
参数：X i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用引理 `Topology.IsClosedEmbedding.sigmaMk`：Topology.IsClosedEmbedding.sigmaMk {
i : ι} : IsClosedEmbedding (@Sigma.mk ι σ i)
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用引理 `Topology.IsOpenEmbedding.sigmaMk`：Topology.IsOpenEmbedding.sigmaMk {i : 
ι} : IsOpenEmbedding (@Sigma.mk ι σ i)
-/
theorem isClopen_range_sigmaMk {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {i : ι} :
    IsClopen (Set.range (@Sigma.mk ι X i)) :=
  ⟨IsClosedEmbedding.sigmaMk.isClosed_range, IsOpenEmbedding.sigmaMk.isOpen_range⟩
/-
**Topology.IsQuotientMap.isClopen_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Topology.I
sQuotientMap`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {f : X → Y},   Topology.IsQuotientMap f → ∀ {s : Set Y}, IsClopen (f
 ⁻¹' s) ↔ IsClopen s
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Topology.IsCoinducing.isClosed_preimage`：∀ {X : Type u_1} {Y : Type u_2}
 {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolo
gy.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
-/
protected theorem Topology.IsQuotientMap.isClopen_preimage {f : X → Y} (hf : IsQuotientMap f)
    {s : Set Y} : IsClopen (f ⁻¹' s) ↔ IsClopen s :=
  and_congr hf.isClosed_preimage hf.isOpen_preimage
/-
**continuous_boolIndicator_iff_isClopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_boolIndicator_iff_isClopen (U : Set X) : Continuous U.boolIndic
ator ↔ IsClopen U
参数：U : Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `continuous_bool_rng`：continuous_bool_rng [TopologicalSpace X] {f : X -> 
Bool} (b : Bool) : Continuous f ↔ IsClopen (f ⁻¹' {b})
· 使用定理 `Set.preimage_boolIndicator_true`：preimage_boolIndicator_true : s.boolInd
icator ⁻¹' {true} = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuous_boolIndicator_iff_isClopen (U : Set X) :
    Continuous U.boolIndicator ↔ IsClopen U := by
  rw [continuous_bool_rng true, preimage_boolIndicator_true]
/-
**continuousOn_boolIndicator_iff_isClopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_boolIndicator_iff_isClopen (s U : Set X) : ContinuousOn U.boo
lIndicator s ↔ IsClopen (((↑) : s -> X) ⁻¹' U)
参数：s U : Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuous_boolIndicator_iff_isClopen`：continuous_boolIndicator_iff_isCl
open (U : Set X) : Continuous U.boolIndicator ↔ IsClopen U
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousOn_boolIndicator_iff_isClopen (s U : Set X) :
    ContinuousOn U.boolIndicator s ↔ IsClopen (((↑) : s → X) ⁻¹' U) := by
  rw [continuousOn_iff_continuous_domRestrict, ← continuous_boolIndicator_iff_isClopen]
  rfl

end Clopen

