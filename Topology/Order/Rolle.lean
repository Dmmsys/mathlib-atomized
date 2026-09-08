/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.ExtendFrom
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.Order.T5

/-!
# Rolle's Theorem (topological part)

In this file we prove the purely topological part of Rolle's Theorem:
a function that is continuous on an interval $[a, b]$, $a < b$,
has a local extremum at a point $x ∈ (a, b)$ provided that $f(a)=f(b)$.
We also prove several variations of this statement.

In `Mathlib/Analysis/Calculus/LocalExtr/Rolle` we use these lemmas
to prove several versions of Rolle's Theorem from calculus.

## Keywords
local minimum, local maximum, extremum, Rolle's Theorem
-/

public section

open Filter Set Topology

variable {X Y : Type*}
  [ConditionallyCompleteLinearOrder X] [DenselyOrdered X] [TopologicalSpace X] [OrderTopology X]
  [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y]
  {f : X → Y} {a b : X} {l : Y}

/-- A continuous function on a closed interval with `f a = f b`
takes either its maximum or its minimum value at a point in the interior of the interval. -/
/-
**exists_Ioo_extr_on_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_Ioo_extr_on_Icc (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI
 : f a = f b) : exists c in Ioo a b, IsExtrOn f (Icc a b) c
参数：hab : a < b；hfc : ContinuousOn f (Icc a b)；hfI : f a = f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsCompact.exists_isMinOn`：IsCompact.exists_isMinOn [ClosedIicTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A continuous function on a closed interval with `f a = f b`
takes either its maximum or its minimum value at a point in the interior of the 
interval.
-/
theorem exists_Ioo_extr_on_Icc (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsExtrOn f (Icc a b) c := by
  have ne : (Icc a b).Nonempty := nonempty_Icc.2 (le_of_lt hab)
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≤ f x :=
    isCompact_Icc.exists_isMinOn ne hfc
  obtain ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f C :=
    isCompact_Icc.exists_isMaxOn ne hfc
  by_cases hc : f c = f a
  · by_cases hC : f C = f a
    · have : ∀ x ∈ Icc a b, f x = f a := fun x hx => le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases nonempty_Ioo.2 hab with ⟨c', hc'⟩
      refine ⟨c', hc', Or.inl fun x hx ↦ ?_⟩
      simp only [mem_ofPred_eq, this x hx, this c' (Ioo_subset_Icc_self hc'), le_rfl]
    · refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 <| mt ?_ hC, lt_of_le_of_ne Cmem.2 <| mt ?_ hC⟩, Or.inr Cge⟩
      exacts [fun h => by rw [h], fun h => by rw [h, hfI]]
  · refine ⟨c, ⟨lt_of_le_of_ne cmem.1 <| mt ?_ hc, lt_of_le_of_ne cmem.2 <| mt ?_ hc⟩, Or.inl cle⟩
    exacts [fun h => by rw [h], fun h => by rw [h, hfI]]

/-- A continuous function on a closed interval with `f a = f b`
has a local extremum at some point of the corresponding open interval. -/
/-
**exists_isLocalExtr_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isLocalExtr_Ioo (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI
 : f a = f b) : exists c in Ioo a b, IsLocalExtr f c
参数：hab : a < b；hfc : ContinuousOn f (Icc a b)；hfI : f a = f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_Ioo_extr_on_Icc`：exists_Ioo_extr_on_Icc (hab : a < b) (hfc : Cont
inuousOn f (Icc a b)) (hfI : f a = f b) : exists c in Ioo a b, IsExtrOn f (Icc a
 b) c
· 使用定理 `IsExtrOn.isLocalExtr`：IsExtrOn.isLocalExtr (hf : IsExtrOn f s a) (hs : s
 in 𝓝 a) : IsLocalExtr f a
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A continuous function on a closed interval with `f a = f b`
has a local extremum at some point of the corresponding open interval.
-/
theorem exists_isLocalExtr_Ioo (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc hab hfc hfI
  ⟨c, cmem, hc.isLocalExtr <| Icc_mem_nhds cmem.1 cmem.2⟩

/-- If a function `f` is continuous on an open interval
and tends to the same value at its endpoints, then it has an extremum on this open interval. -/
/-
**exists_isExtrOn_Ioo_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_isExtrOn_Ioo_of_tendsto (hab : a < b) (hfc : ContinuousOn f (Ioo a 
b)) (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tendsto f (𝓝[<] b) (𝓝 l)) : exists c i
n Ioo a b, IsExtrOn f (Ioo a b) c
参数：hab : a < b；hfc : ContinuousOn f (Ioo a b)；ha : Tendsto f (𝓝[>] a) (𝓝 l)；hb :
 Tendsto f (𝓝[<] b) (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extendFrom_extends`：extendFrom_extends [T2Space Y] {f : X -> Y} {A : Set
 X} (hf : ContinuousOn f A) : forall x in A, extendFrom A f x = f x
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `exists_Ioo_extr_on_Icc`：exists_Ioo_extr_on_Icc (hab : a < b) (hfc : Cont
inuousOn f (Icc a b)) (hfI : f a = f b) : exists c in Ioo a b, IsExtrOn f (Icc a
 b) c
· 使用定理 `continuousOn_Icc_extendFrom_Ioo`：continuousOn_Icc_extendFrom_Ioo (hf : C
ontinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) (hb : Tendsto f (𝓝[<] 
b) (𝓝 lb)) : Continuo…
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_lim_at_left_extendFrom_Ioo`：eq_lim_at_left_extendFrom_Ioo (hab : a < 
b) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) : extendFrom (Ioo a b) f a = la
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_lim_at_right_extendFrom_Ioo`：eq_lim_at_right_extendFrom_Ioo (hab : a 
< b) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : extendFrom (Ioo a b) f b = lb
· 使用定理 `IsExtrFilter.congr`：IsExtrFilter.congr {α β : Type*} [Preorder β] {f g :
 α -> β} {a : α} {l : Filter α} (h : IsExtrFilter f l a) (heq : f =ᶠ[l] g) (hfga
 : f a =…
· 使用定理 `IsExtrOn.on_subset`：IsExtrOn.on_subset (hf : IsExtrOn f t a) (h : s subs
eteq t) : IsExtrOn f s a
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b

--- 原说明 ---
If a function `f` is continuous on an open interval
and tends to the same value at its endpoints, then it has an extremum on this op
en interval.
-/
lemma exists_isExtrOn_Ioo_of_tendsto (hab : a < b) (hfc : ContinuousOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    ∃ c ∈ Ioo a b, IsExtrOn f (Ioo a b) c := by
  have h : EqOn (extendFrom (Ioo a b) f) f (Ioo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : ∃ c ∈ Ioo a b, IsExtrOn (extendFrom (Ioo a b) f) (Icc a b) c :=
    exists_Ioo_extr_on_Icc hab (continuousOn_Icc_extendFrom_Ioo hfc ha hb)
      ((eq_lim_at_left_extendFrom_Ioo hab ha).trans (eq_lim_at_right_extendFrom_Ioo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset Ioo_subset_Icc_self).congr h (h hc)⟩

/-- If a function `f` is continuous on an open interval
and tends to the same value at its endpoints,
then it has a local extremum on this open interval. -/
/-
**exists_isLocalExtr_Ioo_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_isLocalExtr_Ioo_of_tendsto (hab : a < b) (hfc : ContinuousOn f (Ioo
 a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tendsto f (𝓝[<] b) (𝓝 l)) : exists 
c in Ioo a b, IsLocalExtr f c
参数：hab : a < b；hfc : ContinuousOn f (Ioo a b)；ha : Tendsto f (𝓝[>] a) (𝓝 l)；hb :
 Tendsto f (𝓝[<] b) (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_isExtrOn_Ioo_of_tendsto`：exists_isExtrOn_Ioo_of_tendsto (hab : a 
< b) (hfc : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tend
sto f (𝓝[<] b) (𝓝 l)…
· 使用定理 `IsExtrOn.isLocalExtr`：IsExtrOn.isLocalExtr (hf : IsExtrOn f s a) (hs : s
 in 𝓝 a) : IsLocalExtr f a
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a function `f` is continuous on an open interval
and tends to the same value at its endpoints,
then it has a local extremum on this open interval.
-/
lemma exists_isLocalExtr_Ioo_of_tendsto (hab : a < b) (hfc : ContinuousOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_isExtrOn_Ioo_of_tendsto hab hfc ha hb
  ⟨c, cmem, hc.isLocalExtr <| Ioo_mem_nhds cmem.1 cmem.2⟩

/-- A continuous function on an unordered closed interval with `f a = f b`
takes either its maximum or its minimum value at a point in the interior of the interval. -/
/-
**exists_uIoo_isExtrOn_uIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_uIoo_isExtrOn_uIcc (hab : a != b) (hfc : ContinuousOn f (uIcc a b))
 (hfI : f a = f b) : exists c in uIoo a b, IsExtrOn f (uIcc a b) c
参数：hab : a != b；hfc : ContinuousOn f (uIcc a b)；hfI : f a = f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_Ioo_extr_on_Icc`：exists_Ioo_extr_on_Icc (hab : a < b) (hfc : Cont
inuousOn f (Icc a b)) (hfI : f a = f b) : exists c in Ioo a b, IsExtrOn f (Icc a
 b) c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
A continuous function on an unordered closed interval with `f a = f b`
takes either its maximum or its minimum value at a point in the interior of the 
interval.
-/
theorem exists_uIoo_isExtrOn_uIcc (hab : a ≠ b) (hfc : ContinuousOn f (uIcc a b))
    (hfI : f a = f b) :
    ∃ c ∈ uIoo a b, IsExtrOn f (uIcc a b) c :=
  exists_Ioo_extr_on_Icc (by simp [hab.symm]) hfc (by grind)

/-- A continuous function on a unordered closed interval with `f a = f b`
has a local extremum at some point of the corresponding unordered open interval. -/
/-
**exists_isLocalExtr_uIoo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isLocalExtr_uIoo (hab : a != b) (hfc : ContinuousOn f (uIcc a b)) (
hfI : f a = f b) : exists c in uIoo a b, IsLocalExtr f c
参数：hab : a != b；hfc : ContinuousOn f (uIcc a b)；hfI : f a = f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isLocalExtr_Ioo`：exists_isLocalExtr_Ioo (hab : a < b) (hfc : Cont
inuousOn f (Icc a b)) (hfI : f a = f b) : exists c in Ioo a b, IsLocalExtr f c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
A continuous function on a unordered closed interval with `f a = f b`
has a local extremum at some point of the corresponding unordered open interval.
-/
theorem exists_isLocalExtr_uIoo (hab : a ≠ b) (hfc : ContinuousOn f (uIcc a b)) (hfI : f a = f b) :
    ∃ c ∈ uIoo a b, IsLocalExtr f c :=
  exists_isLocalExtr_Ioo (by simp [hab.symm]) hfc (by grind)

/-- If a function `f` is continuous on an unordered open interval
and tends to the same value at its endpoints,
then it has an extremum on this unordered open interval. -/
/-
**exists_isExtrOn_uIoo_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_isExtrOn_uIoo_of_tendsto (hab : a != b) (hfc : ContinuousOn f (uIoo
 a b)) (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 l)) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝
 l)) : exists c in uIoo a b, IsExtrOn f (uIoo a b) c
参数：hab : a != b；hfc : ContinuousOn f (uIoo a b)；ha : Tendsto f (𝓝[uIoo a b] a) (
𝓝 l)；hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extendFrom_extends`：extendFrom_extends [T2Space Y] {f : X -> Y} {A : Set
 X} (hf : ContinuousOn f A) : forall x in A, extendFrom A f x = f x
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `exists_uIoo_isExtrOn_uIcc`：exists_uIoo_isExtrOn_uIcc (hab : a != b) (hfc
 : ContinuousOn f (uIcc a b)) (hfI : f a = f b) : exists c in uIoo a b, IsExtrOn
 f (uIcc a b) c
· 使用定理 `continuousOn_uIcc_extendFrom_uIoo`：continuousOn_uIcc_extendFrom_uIoo (hf
 : ContinuousOn f (uIoo a b)) (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 la)) (hb : Tend
sto f (𝓝[uIoo a b] b) (…
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_lim_at_left_extendFrom_uIoo`：eq_lim_at_left_extendFrom_uIoo (hab : a 
!= b) (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 la)) : extendFrom (uIoo a b) f a = la
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_lim_at_right_extendFrom_uIoo`：eq_lim_at_right_extendFrom_uIoo (hab : 
a != b) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 lb)) : extendFrom (uIoo a b) f b = lb
· 使用定理 `IsExtrFilter.congr`：IsExtrFilter.congr {α β : Type*} [Preorder β] {f g :
 α -> β} {a : α} {l : Filter α} (h : IsExtrFilter f l a) (heq : f =ᶠ[l] g) (hfga
 : f a =…
· 使用定理 `IsExtrOn.on_subset`：IsExtrOn.on_subset (hf : IsExtrOn f t a) (h : s subs
eteq t) : IsExtrOn f s a
· 使用引理 `Set.uIoo_subset_uIcc_self`：uIoo_subset_uIcc_self : uIoo a b subseteq uIc
c a b

--- 原说明 ---
If a function `f` is continuous on an unordered open interval
and tends to the same value at its endpoints,
then it has an extremum on this unordered open interval.
-/
lemma exists_isExtrOn_uIoo_of_tendsto (hab : a ≠ b) (hfc : ContinuousOn f (uIoo a b))
    (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 l)) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 l)) :
    ∃ c ∈ uIoo a b, IsExtrOn f (uIoo a b) c := by
  have h : EqOn (extendFrom (uIoo a b) f) f (uIoo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : ∃ c ∈ uIoo a b, IsExtrOn (extendFrom (uIoo a b) f) (uIcc a b) c :=
    exists_uIoo_isExtrOn_uIcc hab (continuousOn_uIcc_extendFrom_uIoo hfc ha hb)
      ((eq_lim_at_left_extendFrom_uIoo hab ha).trans (eq_lim_at_right_extendFrom_uIoo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset uIoo_subset_uIcc_self).congr h (h hc)⟩

/-- If a function `f` is continuous on an unordered open interval
and tends to the same value at its endpoints,
then it has a local extremum on this unordered open interval. -/
/-
**exists_isLocalExtr_uIoo_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_isLocalExtr_uIoo_of_tendsto (hab : a != b) (hfc : ContinuousOn f (u
Ioo a b)) (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 l)) (hb : Tendsto f (𝓝[uIoo a b] b)
 (𝓝 l)) : exists c in uIoo a b, IsLocalExtr f c
参数：hab : a != b；hfc : ContinuousOn f (uIoo a b)；ha : Tendsto f (𝓝[uIoo a b] a) (
𝓝 l)；hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_isExtrOn_uIoo_of_tendsto`：exists_isExtrOn_uIoo_of_tendsto (hab : 
a != b) (hfc : ContinuousOn f (uIoo a b)) (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 l))
 (hb : Tendsto f (𝓝[u…
· 使用定理 `IsExtrOn.isLocalExtr`：IsExtrOn.isLocalExtr (hf : IsExtrOn f s a) (hs : s
 in 𝓝 a) : IsLocalExtr f a
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a function `f` is continuous on an unordered open interval
and tends to the same value at its endpoints,
then it has a local extremum on this unordered open interval.
-/
lemma exists_isLocalExtr_uIoo_of_tendsto (hab : a ≠ b) (hfc : ContinuousOn f (uIoo a b))
    (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 l)) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 l)) :
    ∃ c ∈ uIoo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_isExtrOn_uIoo_of_tendsto hab hfc ha hb
  ⟨c, cmem, hc.isLocalExtr <| Ioo_mem_nhds cmem.1 cmem.2⟩
