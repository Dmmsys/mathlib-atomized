/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.ExtendFrom
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Lemmas about `extendFrom` in an order topology.
-/

public section

open Filter Set Topology

variable {α β : Type*} [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α] [OrderTopology α]
  [TopologicalSpace β] {f : α → β} {a b : α} {la lb : β}

section RegularSpace

variable [RegularSpace β]

/-
**continuousOn_Icc_extendFrom_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_Icc_extendFrom_Ioo (hf : ContinuousOn f (Ioo a b)) (ha : Tend
sto f (𝓝[>] a) (𝓝 la)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFr
om (Ioo a b) f) (Icc a b)
参数：hf : ContinuousOn f (Ioo a b)；ha : Tendsto f (𝓝[>] a) (𝓝 la)；hb : Tendsto f (
𝓝[<] b) (𝓝 lb)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `continuousOn_extendFrom`：continuousOn_extendFrom [RegularSpace Y] {f : X
 -> Y} {A B : Set X} (hB : B subseteq closure A) (hf : forall x in B, exists y, 
Tendsto f (𝓝[…
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.eq_endpoints_or_mem_Ioo_of_mem_Icc`：eq_endpoints_or_mem_Ioo_of_mem_I
cc {x : α} (hmem : x in Icc a b) : x = a ∨ x = b ∨ x in Ioo a b
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
-/
theorem continuousOn_Icc_extendFrom_Ioo
    (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la))
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) := by
  by_cases! hab : a = b
  · simp [hab]
  apply continuousOn_extendFrom
  · rw [closure_Ioo hab]
  · intro x x_in
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc x_in with (rfl | rfl | h)
    · exact ⟨la, ha.mono_left <| nhdsWithin_mono _ Ioo_subset_Ioi_self⟩
    · exact ⟨lb, hb.mono_left <| nhdsWithin_mono _ Ioo_subset_Iio_self⟩
    · exact ⟨f x, hf x h⟩
/-
**continuousOn_uIcc_extendFrom_uIoo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_uIcc_extendFrom_uIoo (hf : ContinuousOn f (uIoo a b)) (ha : T
endsto f (𝓝[uIoo a b] a) (𝓝 la)) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 lb)) : Conti
nuousOn (extendFrom (uIoo a b) f) (uIcc a b)
参数：hf : ContinuousOn f (uIoo a b)；ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 la)；hb : Ten
dsto f (𝓝[uIoo a b] b) (𝓝 lb)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.uIoo_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoo a b = Set.Ioo a b
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用引理 `Set.uIoo_of_lt`：uIoo_of_lt (h : a < b) : uIoo a b = Ioo a b
· 使用引理 `Set.uIcc_of_lt`：uIcc_of_lt (h : a < b) : [[a, b]] = Icc a b
· 使用定理 `continuousOn_Icc_extendFrom_Ioo`：continuousOn_Icc_extendFrom_Ioo (hf : C
ontinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) (hb : Tendsto f (𝓝[<] 
b) (𝓝 lb)) : Continuo…
· 使用定理 `nhdsWithin_Ioo_eq_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Ioo b a) = …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `nhdsWithin_Ioo_eq_nhdsLT`：nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a
 b] b = 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用引理 `Set.uIoo_of_gt`：uIoo_of_gt (h : b < a) : uIoo a b = Ioo b a
· 使用引理 `Set.uIcc_of_gt`：uIcc_of_gt (h : b < a) : [[a, b]] = Icc b a
-/
theorem continuousOn_uIcc_extendFrom_uIoo
    (hf : ContinuousOn f (uIoo a b))
    (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 la)) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (uIoo a b) f) (uIcc a b) := by
  by_cases! hab : a = b
  · simp [hab]
  obtain hab' | hba' := hab.lt_or_gt
  · simp only [hab', uIoo_of_lt, nhdsWithin_Ioo_eq_nhdsGT, nhdsWithin_Ioo_eq_nhdsLT,
      uIcc_of_lt] at ha hb hf ⊢
    exact continuousOn_Icc_extendFrom_Ioo hf ha hb
  · simp only [hba', uIoo_of_gt, nhdsWithin_Ioo_eq_nhdsGT, nhdsWithin_Ioo_eq_nhdsLT,
      uIcc_of_gt] at ha hb hf ⊢
    exact continuousOn_Icc_extendFrom_Ioo hf hb ha
/-
**continuousOn_Ico_extendFrom_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_Ico_extendFrom_Ioo (hf : ContinuousOn f (Ioo a b)) (ha : Tend
sto f (𝓝[>] a) (𝓝 la)) : ContinuousOn (extendFrom (Ioo a b) f) (Ico a b)
参数：hf : ContinuousOn f (Ioo a b)；ha : Tendsto f (𝓝[>] a) (𝓝 la)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `continuousOn_extendFrom`：continuousOn_extendFrom [RegularSpace Y] {f : X
 -> Y} {A B : Set X} (hB : B subseteq closure A) (hf : forall x in B, exists y, 
Tendsto f (𝓝[…
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Set.eq_left_or_mem_Ioo_of_mem_Ico`：eq_left_or_mem_Ioo_of_mem_Ico {x : α}
 (hmem : x in Ico a b) : x = a ∨ x in Ioo a b
· 使用定理 `nhdsWithin_Ioo_eq_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Ioo b a) = …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem continuousOn_Ico_extendFrom_Ioo
    (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ico a b) := by
  by_cases! hab : a ≥ b
  · simp [hab]
  apply continuousOn_extendFrom
  · rw [closure_Ioo hab.ne]
    exact Ico_subset_Icc_self
  · intro x x_in
    rcases eq_left_or_mem_Ioo_of_mem_Ico x_in with (rfl | h)
    · use la
      simpa [hab]
    · exact ⟨f x, hf x h⟩
/-
**continuousOn_Ioc_extendFrom_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_Ioc_extendFrom_Ioo (hf : ContinuousOn f (Ioo a b)) (hb : Tend
sto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b)
参数：hf : ContinuousOn f (Ioo a b)；hb : Tendsto f (𝓝[<] b) (𝓝 lb)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_Ico_extendFrom_Ioo`：continuousOn_Ico_extendFrom_Ioo (hf : C
ontinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) : ContinuousOn (extend
From (Ioo a b) f) (Ic…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioo_toDual`：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo 
b a
· 使用定理 `Set.Ioi_toDual`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, Set.Ioi (O
rderDual.toDual a) = ⇑OrderDual.ofDual ⁻¹' Set.Iio a
· 使用定理 `Set.Ico_toDual`：Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc 
b a
-/
theorem continuousOn_Ioc_extendFrom_Ioo
    (hf : ContinuousOn f (Ioo a b)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b) := by
  have := continuousOn_Ico_extendFrom_Ioo (f := f ∘ OrderDual.ofDual) (a := OrderDual.toDual b)
    (b := OrderDual.toDual a) (la := lb)
  rw [Ico_toDual, Ioi_toDual, Ioo_toDual] at this
  exact this hf hb

end RegularSpace

section T2Space

variable [T2Space β]

/-
**eq_lim_at_left_extendFrom_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_lim_at_left_extendFrom_Ioo (hab : a < b) (ha : Tendsto f (𝓝[>] a) (𝓝 la
)) : extendFrom (Ioo a b) f a = la
参数：hab : a < b；ha : Tendsto f (𝓝[>] a) (𝓝 la)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extendFrom_eq`：extendFrom_eq [T2Space Y] {A : Set X} {f : X -> Y} {x : X
} {y : Y} (hx : x in closure A) (hf : Tendsto f (𝓝[A] x) (𝓝 y)) : extendFrom A f
 x …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_Ioo_eq_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Ioo b a) = …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem eq_lim_at_left_extendFrom_Ioo (hab : a < b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 la)) : extendFrom (Ioo a b) f a = la := by
  apply extendFrom_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_lt hab, left_mem_Icc]
  · simpa [hab]
/-
**eq_lim_at_right_extendFrom_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_lim_at_right_extendFrom_Ioo (hab : a < b) (hb : Tendsto f (𝓝[<] b) (𝓝 l
b)) : extendFrom (Ioo a b) f b = lb
参数：hab : a < b；hb : Tendsto f (𝓝[<] b) (𝓝 lb)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extendFrom_eq`：extendFrom_eq [T2Space Y] {A : Set X} {f : X -> Y} {x : X
} {y : Y} (hx : x in closure A) (hf : Tendsto f (𝓝[A] x) (𝓝 y)) : extendFrom A f
 x …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_Ioo_eq_nhdsLT`：nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a
 b] b = 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem eq_lim_at_right_extendFrom_Ioo (hab : a < b)
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : extendFrom (Ioo a b) f b = lb := by
  apply extendFrom_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_lt hab, right_mem_Icc]
  · simpa [hab]
/-
**eq_lim_at_left_extendFrom_uIoo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_lim_at_left_extendFrom_uIoo (hab : a != b) (ha : Tendsto f (𝓝[uIoo a b]
 a) (𝓝 la)) : extendFrom (uIoo a b) f a = la
参数：hab : a != b；ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 la)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extendFrom_eq`：extendFrom_eq [T2Space Y] {A : Set X} {f : X -> Y} {x : X
} {y : Y} (hx : x in closure A) (hf : Tendsto f (𝓝[A] x) (𝓝 y)) : extendFrom A f
 x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_uIoo`：closure_uIoo {a b : α} (hab : a != b) : closure (uIoo a b)
 = uIcc a b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem eq_lim_at_left_extendFrom_uIoo (hab : a ≠ b)
    (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 la)) : extendFrom (uIoo a b) f a = la :=
  extendFrom_eq (by simp [hab]) ha
/-
**eq_lim_at_right_extendFrom_uIoo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_lim_at_right_extendFrom_uIoo (hab : a != b) (hb : Tendsto f (𝓝[uIoo a b
] b) (𝓝 lb)) : extendFrom (uIoo a b) f b = lb
参数：hab : a != b；hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 lb)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extendFrom_eq`：extendFrom_eq [T2Space Y] {A : Set X} {f : X -> Y} {x : X
} {y : Y} (hx : x in closure A) (hf : Tendsto f (𝓝[A] x) (𝓝 y)) : extendFrom A f
 x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_uIoo`：closure_uIoo {a b : α} (hab : a != b) : closure (uIoo a b)
 = uIcc a b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem eq_lim_at_right_extendFrom_uIoo (hab : a ≠ b)
    (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 lb)) : extendFrom (uIoo a b) f b = lb :=
  extendFrom_eq (by simp [hab]) hb

end T2Space

