/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.IsLUB

/-!
# Order topology on a densely ordered set
-/

public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

section DenselyOrdered

variable [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α] {a b : α}
  {s : Set α}

/-- The closure of the interval `(a, +∞)` is the closed interval `[a, +∞)`, unless `a` is a top
element. -/
/-
**closure_Ioi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi a) = Ici a
参数：h : (Ioi a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_subset_closure_iff`：sdiff_subset_closure_iff : s \ t subseteq clos
ure t ↔ s subseteq closure t
· 使用定理 `Set.Ici_sdiff_Ioi_same`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}
, Set.Ici a \ Set.Ioi a = {a}
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `IsGLB.mem_closure`：IsGLB.mem_closure {a : α} {s : Set α} (ha : IsGLB s a
) (hs : s.Nonempty) : a in closure s
· 使用定理 `isGLB_Ioi`：∀ {γ : Type u_3} [inst : LinearOrder γ] [DenselyOrdered γ] {a
 : γ}, IsGLB (Set.Ioi a) a

--- 原说明 ---
The closure of the interval `(a, +∞)` is the closed interval `[a, +∞)`, unless `
a` is a top
element.
-/
theorem closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi a) = Ici a := by
  apply Subset.antisymm
  · exact closure_minimal Ioi_subset_Ici_self isClosed_Ici
  · rw [← sdiff_subset_closure_iff, Ici_sdiff_Ioi_same, singleton_subset_iff]
    exact isGLB_Ioi.mem_closure h

/-- The closure of the interval `(a, +∞)` is the closed interval `[a, +∞)`. -/
@[simp]
/-
**closure_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_Ioi'`：closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi
 a) = Ici a
· 使用定理 `Set.nonempty_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [NoMaxOrd
er α], (Set.Ioi a).Nonempty

--- 原说明 ---
The closure of the interval `(a, +∞)` is the closed interval `[a, +∞)`.
-/
theorem closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici a :=
  closure_Ioi' nonempty_Ioi

/-- The closure of the interval `(-∞, a)` is the closed interval `(-∞, a]`, unless `a` is a bottom
element. -/
/-
**closure_Iio'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_Iio' (h : (Iio a).Nonempty) : closure (Iio a) = Iic a
参数：h : (Iio a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_Ioi'`：closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi
 a) = Ici a
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ

--- 原说明 ---
The closure of the interval `(-∞, a)` is the closed interval `(-∞, a]`, unless `
a` is a bottom
element.
-/
theorem closure_Iio' (h : (Iio a).Nonempty) : closure (Iio a) = Iic a :=
  closure_Ioi' (α := αᵒᵈ) h

/-- The closure of the interval `(-∞, a)` is the interval `(-∞, a]`. -/
@[simp]
/-
**closure_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_Iio (a : α) [NoMinOrder α] : closure (Iio a) = Iic a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_Iio'`：closure_Iio' (h : (Iio a).Nonempty) : closure (Iio a) = Ii
c a
· 使用定理 `Set.nonempty_Iio`：nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty

--- 原说明 ---
The closure of the interval `(-∞, a)` is the interval `(-∞, a]`.
-/
theorem closure_Iio (a : α) [NoMinOrder α] : closure (Iio a) = Iic a :=
  closure_Iio' nonempty_Iio
/-
**IsMax.of_disjoint_nhds_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMax.of_disjoint_nhds_Ioi {x : α} {u : Set α} (hu : u in nhds x) (hd : Di
sjoint u (Set.Ioi x)) : IsMax x
参数：hu : u in nhds x；hd : Disjoint u (Set.Ioi x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_Ioi'`：closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi
 a) = Ici a
· 使用定理 `not_isMax_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬IsMax a ↔ 
∃ b, a < b
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
-/
theorem IsMax.of_disjoint_nhds_Ioi {x : α} {u : Set α} (hu : u ∈ nhds x)
    (hd : Disjoint u (Set.Ioi x)) : IsMax x := by
  by_contra hx
  exact (mem_closure_iff_nhds.mp (closure_Ioi' (not_isMax_iff.mp hx) ▸ self_mem_Ici) u hu).ne_empty
    (disjoint_iff.mp hd)
/-
**IsMin.of_disjoint_nhds_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMin.of_disjoint_nhds_Iio {x : α} {u : Set α} (hu : u in nhds x) (hd : Di
sjoint u (Set.Iio x)) : IsMin x
参数：hu : u in nhds x；hd : Disjoint u (Set.Iio x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.of_disjoint_nhds_Ioi`：IsMax.of_disjoint_nhds_Ioi {x : α} {u : Set 
α} (hu : u in nhds x) (hd : Disjoint u (Set.Ioi x)) : IsMax x
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem IsMin.of_disjoint_nhds_Iio {x : α} {u : Set α} (hu : u ∈ nhds x)
    (hd : Disjoint u (Set.Iio x)) : IsMin x :=
  IsMax.of_disjoint_nhds_Ioi (α := αᵒᵈ) hu hd
/-
**nonempty_nhds_inter_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_nhds_inter_Ioi {x : α} {u : Set α} (hu : u in nhds x) (hx : ¬IsMa
x x) : (u inter Set.Ioi x).Nonempty
参数：hu : u in nhds x；hx : ¬IsMax x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsMax.of_disjoint_nhds_Ioi`：IsMax.of_disjoint_nhds_Ioi {x : α} {u : Set 
α} (hu : u in nhds x) (hd : Disjoint u (Set.Ioi x)) : IsMax x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
-/
theorem nonempty_nhds_inter_Ioi {x : α} {u : Set α} (hu : u ∈ nhds x) (hx : ¬IsMax x) :
    (u ∩ Set.Ioi x).Nonempty := by
  by_contra h
  exact hx (IsMax.of_disjoint_nhds_Ioi hu (Set.disjoint_iff_inter_eq_empty.mpr
    (Set.not_nonempty_iff_eq_empty.mp h)))
/-
**nonempty_nhds_inter_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_nhds_inter_Iio {x : α} {u : Set α} (hu : u in nhds x) (hx : ¬IsMi
n x) : (u inter Set.Iio x).Nonempty
参数：hu : u in nhds x；hx : ¬IsMin x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_nhds_inter_Ioi`：nonempty_nhds_inter_Ioi {x : α} {u : Set α} (hu
 : u in nhds x) (hx : ¬IsMax x) : (u inter Set.Ioi x).Nonempty
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem nonempty_nhds_inter_Iio {x : α} {u : Set α} (hu : u ∈ nhds x) (hx : ¬IsMin x) :
    (u ∩ Set.Iio x).Nonempty :=
  nonempty_nhds_inter_Ioi (α := αᵒᵈ) hu hx

/-- The closure of the open interval `(a, b)` is the closed interval `[a, b]`. -/
@[simp]
/-
**closure_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = Icc a b
参数：hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `isClosed_Icc`：isClosed_Icc {a b : α} : IsClosed (Icc a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_subset_closure_iff`：sdiff_subset_closure_iff : s \ t subseteq clos
ure t ↔ s subseteq closure t
· 使用定理 `Set.Icc_sdiff_Ioo_same`：Icc_sdiff_Ioo_same (h : a <= b) : Icc a b \ Ioo 
a b = {a, b}
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsGLB.mem_closure`：IsGLB.mem_closure {a : α} {s : Set α} (ha : IsGLB s a
) (hs : s.Nonempty) : a in closure s
· 使用定理 `isGLB_Ioo`：isGLB_Ioo {a b : γ} (h : a < b) : IsGLB (Ioo a b) a
· 使用定理 `IsLUB.mem_closure`：IsLUB.mem_closure {a : α} {s : Set α} (ha : IsLUB s a
) (hs : s.Nonempty) : a in closure s
· 使用定理 `isLUB_Ioo`：∀ {γ : Type u_3} [inst : SemilatticeInf γ] [DenselyOrdered γ]
 {a b : γ}, b < a → IsLUB (Set.Ioo b a) a
· 使用定理 `Set.Icc_eq_empty_of_lt`：Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s

--- 原说明 ---
The closure of the open interval `(a, b)` is the closed interval `[a, b]`.
-/
theorem closure_Ioo {a b : α} (hab : a ≠ b) : closure (Ioo a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  · rcases hab.lt_or_gt with hab | hab
    · rw [← sdiff_subset_closure_iff, Icc_sdiff_Ioo_same hab.le]
      have hab' : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨(isGLB_Ioo hab).mem_closure hab', (isLUB_Ioo hab).mem_closure hab'⟩
    · rw [Icc_eq_empty_of_lt hab]
      exact empty_subset _

@[simp]
/-
**closure_uIoo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_uIoo {a b : α} (hab : a != b) : closure (uIoo a b) = uIcc a b
参数：hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_uIoo {a b : α} (hab : a ≠ b) : closure (uIoo a b) = uIcc a b := by
  simp [uIoo, uIcc, hab]

/-- The closure of the interval `(a, b]` is the closed interval `[a, b]`. -/
@[simp]
/-
**closure_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_Ioc {a b : α} (hab : a != b) : closure (Ioc a b) = Icc a b
参数：hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `isClosed_Icc`：isClosed_Icc {a b : α} : IsClosed (Icc a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a

--- 原说明 ---
The closure of the interval `(a, b]` is the closed interval `[a, b]`.
-/
theorem closure_Ioc {a b : α} (hab : a ≠ b) : closure (Ioc a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ioc_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ioc_self)
    rw [closure_Ioo hab]

@[simp]
/-
**closure_uIoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_uIoc {a b : α} (hab : a != b) : closure (uIoc a b) = uIcc a b
参数：hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Ioc`：closure_Ioc {a b : α} (hab : a != b) : closure (Ioc a b) = 
Icc a b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_uIoc {a b : α} (hab : a ≠ b) : closure (uIoc a b) = uIcc a b := by
  simp [uIoc, uIcc, hab]

/-- The closure of the interval `[a, b)` is the closed interval `[a, b]`. -/
@[simp]
/-
**closure_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_Ico {a b : α} (hab : a != b) : closure (Ico a b) = Icc a b
参数：hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `isClosed_Icc`：isClosed_Icc {a b : α} : IsClosed (Icc a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b

--- 原说明 ---
The closure of the interval `[a, b)` is the closed interval `[a, b]`.
-/
theorem closure_Ico {a b : α} (hab : a ≠ b) : closure (Ico a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ico_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ico_self)
    rw [closure_Ioo hab]

@[simp]
/-
**interior_Ici'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior (Ici a) = Ioi a
参数：ha : (Iio a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_Iio`：compl_Iio : (Iio a)ᶜ = Ici a
· 使用定理 `interior_compl`：interior_compl : interior sᶜ = (closure s)ᶜ
· 使用定理 `closure_Iio'`：closure_Iio' (h : (Iio a).Nonempty) : closure (Iio a) = Ii
c a
· 使用定理 `Set.compl_Iic`：compl_Iic : (Iic a)ᶜ = Ioi a
-/
theorem interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior (Ici a) = Ioi a := by
  rw [← compl_Iio, interior_compl, closure_Iio' ha, compl_Iic]
/-
**interior_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = Ioi a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a
· 使用定理 `Set.nonempty_Iio`：nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty
-/
theorem interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = Ioi a :=
  interior_Ici' nonempty_Iio

@[simp]
/-
**interior_Iic'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior (Iic a) = Iio a
参数：ha : (Ioi a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior (Iic a) = Iio a :=
  interior_Ici' (α := αᵒᵈ) ha
/-
**interior_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_Iic [NoMaxOrder α] {a : α} : interior (Iic a) = Iio a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_Iic'`：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior 
(Iic a) = Iio a
· 使用定理 `Set.nonempty_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [NoMaxOrd
er α], (Set.Ioi a).Nonempty
-/
theorem interior_Iic [NoMaxOrder α] {a : α} : interior (Iic a) = Iio a :=
  interior_Iic' nonempty_Ioi

@[simp]
/-
**interior_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : interior (Icc a b) 
= Ioo a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `interior_Ici`：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = I
oi a
· 使用定理 `interior_Iic`：interior_Iic [NoMaxOrder α] {a : α} : interior (Iic a) = I
io a
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
-/
theorem interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : interior (Icc a b) = Ioo a b := by
  rw [← Ici_inter_Iic, interior_inter, interior_Ici, interior_Iic, Ioi_inter_Iio]

@[simp]
/-
**Icc_mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Icc_mem_nhds_iff [NoMinOrder α] [NoMaxOrder α] {a b x : α} : Icc a b in 𝓝 
x ↔ x in Ioo a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Icc_mem_nhds_iff [NoMinOrder α] [NoMaxOrder α] {a b x : α} :
    Icc a b ∈ 𝓝 x ↔ x ∈ Ioo a b := by
  rw [← interior_Icc, mem_interior_iff_mem_nhds]

@[simp]
/-
**interior_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b) = Ioo a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iio b = Set.Ico a b
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `interior_Ici`：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = I
oi a
· 使用定理 `interior_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a : α},   interior (Set.Iio a) = Set.Iio a
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
-/
theorem interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b) = Ioo a b := by
  rw [← Ici_inter_Iio, interior_inter, interior_Ici, interior_Iio, Ioi_inter_Iio]

@[simp]
/-
**Ico_mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ico_mem_nhds_iff [NoMinOrder α] {a b x : α} : Ico a b in 𝓝 x ↔ x in Ioo a 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_Ico`：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b)
 = Ioo a b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ico_mem_nhds_iff [NoMinOrder α] {a b x : α} : Ico a b ∈ 𝓝 x ↔ x ∈ Ioo a b := by
  rw [← interior_Ico, mem_interior_iff_mem_nhds]

@[simp]
/-
**interior_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b) = Ioo a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iic b = Set.Ioc a b
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `interior_Ioi`：interior_Ioi : interior (Ioi a) = Ioi a
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `interior_Iic`：interior_Iic [NoMaxOrder α] {a : α} : interior (Iic a) = I
io a
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
-/
theorem interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b) = Ioo a b := by
  rw [← Ioi_inter_Iic, interior_inter, interior_Ioi, interior_Iic, Ioi_inter_Iio]

@[simp]
/-
**Ioc_mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioc_mem_nhds_iff [NoMaxOrder α] {a b x : α} : Ioc a b in 𝓝 x ↔ x in Ioo a 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_Ioc`：interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b)
 = Ioo a b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ioc_mem_nhds_iff [NoMaxOrder α] {a b x : α} : Ioc a b ∈ 𝓝 x ↔ x ∈ Ioo a b := by
  rw [← interior_Ioc, mem_interior_iff_mem_nhds]
/-
**closure_interior_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_interior_Icc {a b : α} (h : a != b) : closure (interior (Icc a b))
 = Icc a b
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `isClosed_Icc`：isClosed_Icc {a b : α} : IsClosed (Icc a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
-/
theorem closure_interior_Icc {a b : α} (h : a ≠ b) : closure (interior (Icc a b)) = Icc a b :=
  (closure_minimal interior_subset isClosed_Icc).antisymm <|
    calc
      Icc a b = closure (Ioo a b) := (closure_Ioo h).symm
      _ ⊆ closure (interior (Icc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Icc_self isOpen_Ioo)
/-
**Ioc_subset_closure_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioc_subset_closure_interior (a b : α) : Ioc a b subseteq closure (interior
 (Ioc a b))
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `interior_empty`：interior_empty : interior (∅ : Set X) = ∅
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
-/
theorem Ioc_subset_closure_interior (a b : α) : Ioc a b ⊆ closure (interior (Ioc a b)) := by
  rcases eq_or_ne a b with (rfl | h)
  · simp
  · calc
      Ioc a b ⊆ Icc a b := Ioc_subset_Icc_self
      _ = closure (Ioo a b) := (closure_Ioo h).symm
      _ ⊆ closure (interior (Ioc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Ioc_self isOpen_Ioo)
/-
**Ico_subset_closure_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ico_subset_closure_interior (a b : α) : Ico a b subseteq closure (interior
 (Ico a b))
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_toDual`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},   Set.Io
c (OrderDual.toDual b) (OrderDual.toDual a) = ⇑OrderDual.ofDual ⁻¹' Set.Ico a b
· 使用定理 `Ioc_subset_closure_interior`：Ioc_subset_closure_interior (a b : α) : Ioc
 a b subseteq closure (interior (Ioc a b))
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem Ico_subset_closure_interior (a b : α) : Ico a b ⊆ closure (interior (Ico a b)) := by
  simpa only [Ioc_toDual] using!
    Ioc_subset_closure_interior (OrderDual.toDual b) (OrderDual.toDual a)

@[simp]
/-
**frontier_Ici'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Ici' {a : α} (ha : (Iio a).Nonempty) : frontier (Ici a) = {a}
参数：ha : (Iio a).Nonempty。
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
· 使用定理 `closure_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preord
er α] [ClosedIciTopology α] (a : α),   closure (Set.Ici a) = Set.Ici a
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a
· 使用定理 `Set.Ici_sdiff_Ioi_same`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}
, Set.Ici a \ Set.Ioi a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_Ici' {a : α} (ha : (Iio a).Nonempty) : frontier (Ici a) = {a} := by
  simp [frontier, ha]
/-
**frontier_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Ici [NoMinOrder α] {a : α} : frontier (Ici a) = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frontier_Ici'`：frontier_Ici' {a : α} (ha : (Iio a).Nonempty) : frontier 
(Ici a) = {a}
· 使用定理 `Set.nonempty_Iio`：nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty
-/
theorem frontier_Ici [NoMinOrder α] {a : α} : frontier (Ici a) = {a} :=
  frontier_Ici' nonempty_Iio

@[simp]
/-
**frontier_Iic'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Iic' {a : α} (ha : (Ioi a).Nonempty) : frontier (Iic a) = {a}
参数：ha : (Ioi a).Nonempty。
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
· 使用定理 `closure_Iic`：closure_Iic (a : α) : closure (Iic a) = Iic a
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `interior_Iic'`：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior 
(Iic a) = Iio a
· 使用定理 `Set.Iic_sdiff_Iio_same`：Iic_sdiff_Iio_same : Iic a \ Iio a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_Iic' {a : α} (ha : (Ioi a).Nonempty) : frontier (Iic a) = {a} := by
  simp [frontier, ha]
/-
**frontier_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Iic [NoMaxOrder α] {a : α} : frontier (Iic a) = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frontier_Iic'`：frontier_Iic' {a : α} (ha : (Ioi a).Nonempty) : frontier 
(Iic a) = {a}
· 使用定理 `Set.nonempty_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [NoMaxOrd
er α], (Set.Ioi a).Nonempty
-/
theorem frontier_Iic [NoMaxOrder α] {a : α} : frontier (Iic a) = {a} :=
  frontier_Iic' nonempty_Ioi

@[simp]
/-
**frontier_Ioi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Ioi' {a : α} (ha : (Ioi a).Nonempty) : frontier (Ioi a) = {a}
参数：ha : (Ioi a).Nonempty。
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
· 使用定理 `closure_Ioi'`：closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi
 a) = Ici a
· 使用定理 `interior_Ioi`：interior_Ioi : interior (Ioi a) = Ioi a
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Ici_sdiff_Ioi_same`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}
, Set.Ici a \ Set.Ioi a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_Ioi' {a : α} (ha : (Ioi a).Nonempty) : frontier (Ioi a) = {a} := by
  simp [frontier, closure_Ioi' ha]
/-
**frontier_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Ioi [NoMaxOrder α] {a : α} : frontier (Ioi a) = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frontier_Ioi'`：frontier_Ioi' {a : α} (ha : (Ioi a).Nonempty) : frontier 
(Ioi a) = {a}
· 使用定理 `Set.nonempty_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [NoMaxOrd
er α], (Set.Ioi a).Nonempty
-/
theorem frontier_Ioi [NoMaxOrder α] {a : α} : frontier (Ioi a) = {a} :=
  frontier_Ioi' nonempty_Ioi

@[simp]
/-
**frontier_Iio'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Iio' {a : α} (ha : (Iio a).Nonempty) : frontier (Iio a) = {a}
参数：ha : (Iio a).Nonempty。
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
· 使用定理 `closure_Iio'`：closure_Iio' (h : (Iio a).Nonempty) : closure (Iio a) = Ii
c a
· 使用定理 `interior_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a : α},   interior (Set.Iio a) = Set.Iio a
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Iic_sdiff_Iio_same`：Iic_sdiff_Iio_same : Iic a \ Iio a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_Iio' {a : α} (ha : (Iio a).Nonempty) : frontier (Iio a) = {a} := by
  simp [frontier, closure_Iio' ha]
/-
**frontier_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Iio [NoMinOrder α] {a : α} : frontier (Iio a) = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frontier_Iio'`：frontier_Iio' {a : α} (ha : (Iio a).Nonempty) : frontier 
(Iio a) = {a}
· 使用定理 `Set.nonempty_Iio`：nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty
-/
theorem frontier_Iio [NoMinOrder α] {a : α} : frontier (Iio a) = {a} :=
  frontier_Iio' nonempty_Iio

@[simp]
/-
**frontier_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} (h : a <= b) : fronti
er (Icc a b) = {a, b}
参数：h : a <= b。
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
· 使用定理 `closure_Icc`：closure_Icc (a b : α) : closure (Icc a b) = Icc a b
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `Set.Icc_sdiff_Ioo_same`：Icc_sdiff_Ioo_same (h : a <= b) : Icc a b \ Ioo 
a b = {a, b}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} (h : a ≤ b) :
    frontier (Icc a b) = {a, b} := by simp [frontier, h, Icc_sdiff_Ioo_same]

@[simp]
/-
**frontier_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Ioo {a b : α} (h : a < b) : frontier (Ioo a b) = {a, b}
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `interior_Ioo`：interior_Ioo : interior (Ioo a b) = Ioo a b
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Icc_sdiff_Ioo_same`：Icc_sdiff_Ioo_same (h : a <= b) : Icc a b \ Ioo 
a b = {a, b}
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem frontier_Ioo {a b : α} (h : a < b) : frontier (Ioo a b) = {a, b} := by
  rw [frontier, closure_Ioo h.ne, interior_Ioo, Icc_sdiff_Ioo_same h.le]

@[simp]
/-
**frontier_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Ico [NoMinOrder α] {a b : α} (h : a < b) : frontier (Ico a b) = {
a, b}
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `closure_Ico`：closure_Ico {a b : α} (hab : a != b) : closure (Ico a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `interior_Ico`：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b)
 = Ioo a b
· 使用定理 `Set.Icc_sdiff_Ioo_same`：Icc_sdiff_Ioo_same (h : a <= b) : Icc a b \ Ioo 
a b = {a, b}
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem frontier_Ico [NoMinOrder α] {a b : α} (h : a < b) : frontier (Ico a b) = {a, b} := by
  rw [frontier, closure_Ico h.ne, interior_Ico, Icc_sdiff_Ioo_same h.le]

@[simp]
/-
**frontier_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_Ioc [NoMaxOrder α] {a b : α} (h : a < b) : frontier (Ioc a b) = {
a, b}
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `closure_Ioc`：closure_Ioc {a b : α} (hab : a != b) : closure (Ioc a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `interior_Ioc`：interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b)
 = Ioo a b
· 使用定理 `Set.Icc_sdiff_Ioo_same`：Icc_sdiff_Ioo_same (h : a <= b) : Icc a b \ Ioo 
a b = {a, b}
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem frontier_Ioc [NoMaxOrder α] {a b : α} (h : a < b) : frontier (Ioc a b) = {a, b} := by
  rw [frontier, closure_Ioc h.ne, interior_Ioc, Icc_sdiff_Ioo_same h.le]
/-
**nhdsWithin_Ioi_neBot'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_Ioi_neBot' {a b : α} (H₁ : (Ioi a).Nonempty) (H₂ : a <= b) : Ne
Bot (𝓝[Ioi a] b)
参数：H₁ : (Ioi a).Nonempty；H₂ : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Ioi'`：closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi
 a) = Ici a
-/
theorem nhdsWithin_Ioi_neBot' {a b : α} (H₁ : (Ioi a).Nonempty) (H₂ : a ≤ b) :
    NeBot (𝓝[Ioi a] b) :=
  mem_closure_iff_nhdsWithin_neBot.1 <| by rwa [closure_Ioi' H₁]
/-
**nhdsWithin_Ioi_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_Ioi_neBot [NoMaxOrder α] {a b : α} (H : a <= b) : NeBot (𝓝[Ioi 
a] b)
参数：H : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_Ioi_neBot'`：nhdsWithin_Ioi_neBot' {a b : α} (H₁ : (Ioi a).Non
empty) (H₂ : a <= b) : NeBot (𝓝[Ioi a] b)
· 使用定理 `Set.nonempty_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [NoMaxOrd
er α], (Set.Ioi a).Nonempty
-/
theorem nhdsWithin_Ioi_neBot [NoMaxOrder α] {a b : α} (H : a ≤ b) : NeBot (𝓝[Ioi a] b) :=
  nhdsWithin_Ioi_neBot' nonempty_Ioi H
/-
**nhdsGT_neBot_of_exists_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsGT_neBot_of_exists_gt {a : α} (H : exists b, a < b) : NeBot (𝓝[>] a)
参数：H : exists b, a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_Ioi_neBot'`：nhdsWithin_Ioi_neBot' {a b : α} (H₁ : (Ioi a).Non
empty) (H₂ : a <= b) : NeBot (𝓝[Ioi a] b)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem nhdsGT_neBot_of_exists_gt {a : α} (H : ∃ b, a < b) : NeBot (𝓝[>] a) :=
  nhdsWithin_Ioi_neBot' H (le_refl a)
/-
**nhdsGT_neBot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nhdsGT_neBot [NoMaxOrder α] (a : α) : NeBot (𝓝[>] a)
参数：a : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_Ioi_neBot`：nhdsWithin_Ioi_neBot [NoMaxOrder α] {a b : α} (H :
 a <= b) : NeBot (𝓝[Ioi a] b)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
instance nhdsGT_neBot [NoMaxOrder α] (a : α) : NeBot (𝓝[>] a) := nhdsWithin_Ioi_neBot le_rfl
/-
**nhdsWithin_Iio_neBot'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_Iio_neBot' {b c : α} (H₁ : (Iio c).Nonempty) (H₂ : b <= c) : Ne
Bot (𝓝[Iio c] b)
参数：H₁ : (Iio c).Nonempty；H₂ : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Iio'`：closure_Iio' (h : (Iio a).Nonempty) : closure (Iio a) = Ii
c a
-/
theorem nhdsWithin_Iio_neBot' {b c : α} (H₁ : (Iio c).Nonempty) (H₂ : b ≤ c) :
    NeBot (𝓝[Iio c] b) :=
  mem_closure_iff_nhdsWithin_neBot.1 <| by rwa [closure_Iio' H₁]
/-
**nhdsWithin_Iio_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_Iio_neBot [NoMinOrder α] {a b : α} (H : a <= b) : NeBot (𝓝[Iio 
b] a)
参数：H : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_Iio_neBot'`：nhdsWithin_Iio_neBot' {b c : α} (H₁ : (Iio c).Non
empty) (H₂ : b <= c) : NeBot (𝓝[Iio c] b)
· 使用定理 `Set.nonempty_Iio`：nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty
-/
theorem nhdsWithin_Iio_neBot [NoMinOrder α] {a b : α} (H : a ≤ b) : NeBot (𝓝[Iio b] a) :=
  nhdsWithin_Iio_neBot' nonempty_Iio H
/-
**nhdsLT_neBot_of_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsLT_neBot_of_exists_lt {b : α} (H : exists a, a < b) : NeBot (𝓝[<] b)
参数：H : exists a, a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_Iio_neBot'`：nhdsWithin_Iio_neBot' {b c : α} (H₁ : (Iio c).Non
empty) (H₂ : b <= c) : NeBot (𝓝[Iio c] b)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem nhdsLT_neBot_of_exists_lt {b : α} (H : ∃ a, a < b) : NeBot (𝓝[<] b) :=
  nhdsWithin_Iio_neBot' H (le_refl b)

@[deprecated (since := "2026-01-16")] alias nhdsWithin_Iio_self_neBot' := nhdsLT_neBot_of_exists_lt
/-
**nhdsLT_neBot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nhdsLT_neBot [NoMinOrder α] (a : α) : NeBot (𝓝[<] a)
参数：a : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_Iio_neBot`：nhdsWithin_Iio_neBot [NoMinOrder α] {a b : α} (H :
 a <= b) : NeBot (𝓝[Iio b] a)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
instance nhdsLT_neBot [NoMinOrder α] (a : α) : NeBot (𝓝[<] a) := nhdsWithin_Iio_neBot (le_refl a)
/-
**right_nhdsWithin_Ico_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_nhdsWithin_Ico_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ico a b] b)
参数：H : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.nhdsWithin_neBot`：IsLUB.nhdsWithin_neBot {a : α} {s : Set α} (ha :
 IsLUB s a) (hs : s.Nonempty) : NeBot (𝓝[s] a)
· 使用定理 `isLUB_Ico`：∀ {γ : Type u_3} [inst : SemilatticeInf γ] [DenselyOrdered γ]
 {a b : γ}, b < a → IsLUB (Set.Ico b a) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ico`：nonempty_Ico : (Ico a b).Nonempty ↔ a < b
-/
theorem right_nhdsWithin_Ico_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ico a b] b) :=
  (isLUB_Ico H).nhdsWithin_neBot (nonempty_Ico.2 H)
/-
**left_nhdsWithin_Ioc_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_nhdsWithin_Ioc_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioc a b] a)
参数：H : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.nhdsWithin_neBot`：IsGLB.nhdsWithin_neBot {a : α} {s : Set α} (ha :
 IsGLB s a) (hs : s.Nonempty) : NeBot (𝓝[s] a)
· 使用定理 `isGLB_Ioc`：isGLB_Ioc {a b : γ} (hab : a < b) : IsGLB (Ioc a b) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, (Set.I
oc b a).Nonempty ↔ b < a
-/
theorem left_nhdsWithin_Ioc_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioc a b] a) :=
  (isGLB_Ioc H).nhdsWithin_neBot (nonempty_Ioc.2 H)
/-
**left_nhdsWithin_Ioo_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_nhdsWithin_Ioo_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioo a b] a)
参数：H : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.nhdsWithin_neBot`：IsGLB.nhdsWithin_neBot {a : α} {s : Set α} (ha :
 IsGLB s a) (hs : s.Nonempty) : NeBot (𝓝[s] a)
· 使用定理 `isGLB_Ioo`：isGLB_Ioo {a b : γ} (h : a < b) : IsGLB (Ioo a b) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
-/
theorem left_nhdsWithin_Ioo_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioo a b] a) :=
  (isGLB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)
/-
**right_nhdsWithin_Ioo_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_nhdsWithin_Ioo_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioo a b] b)
参数：H : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.nhdsWithin_neBot`：IsLUB.nhdsWithin_neBot {a : α} {s : Set α} (ha :
 IsLUB s a) (hs : s.Nonempty) : NeBot (𝓝[s] a)
· 使用定理 `isLUB_Ioo`：∀ {γ : Type u_3} [inst : SemilatticeInf γ] [DenselyOrdered γ]
 {a b : γ}, b < a → IsLUB (Set.Ioo b a) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
-/
theorem right_nhdsWithin_Ioo_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioo a b] b) :=
  (isLUB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : α) [Nontrivial α] : NeBot (𝓝[≠] x) := by
  refine forall_mem_nonempty_iff_neBot.1 fun s hs => ?_
  obtain ⟨u, u_open, xu, us⟩ : ∃ u : Set α, IsOpen u ∧ x ∈ u ∧ u ∩ {x}ᶜ ⊆ s := mem_nhdsWithin.1 hs
  obtain ⟨a, b, a_lt_b, hab⟩ : ∃ a b : α, a < b ∧ Ioo a b ⊆ u := u_open.exists_Ioo_subset ⟨x, xu⟩
  obtain ⟨y, hy⟩ : ∃ y, a < y ∧ y < b := exists_between a_lt_b
  rcases ne_or_eq x y with (xy | rfl)
  · exact ⟨y, us ⟨hab hy, xy.symm⟩⟩
  obtain ⟨z, hz⟩ : ∃ z, a < z ∧ z < x := exists_between hy.1
  exact ⟨z, us ⟨hab ⟨hz.1, hz.2.trans hy.2⟩, hz.2.ne⟩⟩

/-- If the order topology for a dense linear ordering is discrete, the space has at most one point.

We would prefer for this to be an instance but even at `(priority := 100)` this was problematic so
we have deferred this issue. TODO Promote this to an `instance`! -/
/-
**DenselyOrdered.subsingleton_of_discreteTopology** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DenselyOrdered.subsingleton_of_discreteTopology [DiscreteTopology α] : Sub
singleton α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_discrete`：closure_discrete (s : Set α) : closure s = s
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b

--- 原说明 ---
If the order topology for a dense linear ordering is discrete, the space has at 
most one point.

We would prefer for this to be an instance but even at `(priority := 100)` this 
was problematic so
we have deferred this issue. TODO Promote this to an `instance`!
-/
lemma DenselyOrdered.subsingleton_of_discreteTopology [DiscreteTopology α] : Subsingleton α := by
  suffices ∀ a b : α, b ≤ a from ⟨fun a b ↦ le_antisymm (this b a) (this a b)⟩
  intro a b
  by_contra! contra
  have : Ioo a b = Icc a b := by rw [← closure_discrete (Ioo a b), closure_Ioo contra.ne]
  grind => have : b ∈ Ioo a b; finish

/-- Let `s` be a dense set in a nontrivial dense linear order `α`. If `s` is a
separable space (e.g., if `α` has a second countable topology), then there exists a countable
dense subset `t ⊆ s` such that `t` does not contain bottom/top elements of `α`. -/
/-
**Dense.exists_countable_dense_subset_no_bot_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.exists_countable_dense_subset_no_bot_top [Nontrivial α] {s : Set α} 
[SeparableSpace s] (hs : Dense s) : exists t, t subseteq s ∧ t.Countable ∧ Dense
 t ∧ (forall x, IsBot x -> x ∉ t) ∧ forall x, IsTop x -> x ∉ t
参数：hs : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.exists_countable_dense_subset`：Dense.exists_countable_dense_subset
 {α : Type*} [TopologicalSpace α] {s : Set α} [SeparableSpace s] (hs : Dense s) 
: exists t subseteq s, t.…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Dense.sdiff_finite`：Dense.sdiff_finite [T1Space X] [forall x : X, NeBot 
(𝓝[!=] x)] {s : Set X} (hs : Dense s) {t : Set X} (ht : t.Finite) : Dense (s \ t
)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instNeBotNhdsWithinComplSetSingletonOfNontrivial`：∀ {α : Type u_1} [inst
 : TopologicalSpace α] [inst_1 : LinearOrder α] [OrderTopology α] [DenselyOrdere
d α] (x : α)   [Nontrivial α], (nhdsWi…
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
· 使用定理 `Set.subsingleton_isBot`：∀ (α : Type u_1) [inst : PartialOrder α], {x | I
sBot x}.Subsingleton
· 使用定理 `Set.subsingleton_isTop`：subsingleton_isTop (α : Type*) [PartialOrder α] 
: { x : α | IsTop x }.Subsingleton
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
Let `s` be a dense set in a nontrivial dense linear order `α`. If `s` is a
separable space (e.g., if `α` has a second countable topology), then there exist
s a countable
dense subset `t ⊆ s` such that `t` does not contain bottom/top elements of `α`.
-/
theorem Dense.exists_countable_dense_subset_no_bot_top [Nontrivial α] {s : Set α} [SeparableSpace s]
    (hs : Dense s) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ Dense t ∧ (∀ x, IsBot x → x ∉ t) ∧ ∀ x, IsTop x → x ∉ t := by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, htd⟩
  refine ⟨t \ ({ x | IsBot x } ∪ { x | IsTop x }), ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact sdiff_subset.trans hts
  · exact htc.mono sdiff_subset
  · exact htd.sdiff_finite ((subsingleton_isBot α).finite.union (subsingleton_isTop α).finite)
  · simp [hx]
  · simp [hx]

variable (α) in
/-- If `α` is a nontrivial separable dense linear order, then there exists a
countable dense set `s : Set α` that contains neither top nor bottom elements of `α`.
For a dense set containing both bot and top elements, see
`exists_countable_dense_bot_top`. -/
/-
**exists_countable_dense_no_bot_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_countable_dense_no_bot_top [SeparableSpace α] [Nontrivial α] : exis
ts s : Set α, s.Countable ∧ Dense s ∧ (forall x, IsBot x -> x ∉ s) ∧ forall x, I
sTop x -> x ∉ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Dense.exists_countable_dense_subset_no_bot_top`：Dense.exists_countable_d
ense_subset_no_bot_top [Nontrivial α] {s : Set α} [SeparableSpace s] (hs : Dense
 s) : exists t, t subseteq s ∧ t.Cou…
· 使用定理 `dense_univ`：dense_univ : Dense (univ : Set X)

--- 原说明 ---
If `α` is a nontrivial separable dense linear order, then there exists a
countable dense set `s : Set α` that contains neither top nor bottom elements of
 `α`.
For a dense set containing both bot and top elements, see
`exists_countable_dense_bot_top`.
-/
theorem exists_countable_dense_no_bot_top [SeparableSpace α] [Nontrivial α] :
    ∃ s : Set α, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∉ s) ∧ ∀ x, IsTop x → x ∉ s := by
  simpa using dense_univ.exists_countable_dense_subset_no_bot_top

/-- `Set.Ico a b` is only closed if it is empty. -/
@[simp]
/-
**isClosed_Ico_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_Ico_iff {a b : α} : IsClosed (Set.Ico a b) ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_eq_Ico_same_iff`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a = Set.Ico b a ↔ ¬b ≤ a
· 使用定理 `closure_Ico`：closure_Ico {a b : α} (hab : a != b) : closure (Ico a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
`Set.Ico a b` is only closed if it is empty.
-/
theorem isClosed_Ico_iff {a b : α} : IsClosed (Set.Ico a b) ↔ b ≤ a := by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ico hab.ne, Icc_eq_Ico_same_iff] at this
  exact this hab.le

/-- `Set.Ioc a b` is only closed if it is empty. -/
@[simp]
/-
**isClosed_Ioc_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_Ioc_iff {a b : α} : IsClosed (Set.Ioc a b) ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_eq_Ioc_same_iff`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b = Set.Ioc a b ↔ ¬a ≤ b
· 使用定理 `closure_Ioc`：closure_Ioc {a b : α} (hab : a != b) : closure (Ioc a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
`Set.Ioc a b` is only closed if it is empty.
-/
theorem isClosed_Ioc_iff {a b : α} : IsClosed (Set.Ioc a b) ↔ b ≤ a := by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ioc hab.ne, Icc_eq_Ioc_same_iff] at this
  exact this hab.le

/-- `Set.Ioo a b` is only closed if it is empty. -/
@[simp]
/-
**isClosed_Ioo_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_Ioo_iff {a b : α} : IsClosed (Set.Ioo a b) ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_eq_Ioo_same_iff`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b = Set.Ioo a b ↔ ¬a ≤ b
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
`Set.Ioo a b` is only closed if it is empty.
-/
theorem isClosed_Ioo_iff {a b : α} : IsClosed (Set.Ioo a b) ↔ b ≤ a := by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ioo hab.ne, Icc_eq_Ioo_same_iff] at this
  exact this hab.le

end DenselyOrdered

