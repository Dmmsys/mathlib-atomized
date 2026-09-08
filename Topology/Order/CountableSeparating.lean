/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Filter.CountableSeparatingOn

/-!
# Countably many infinite intervals separate points

In this file we prove that in a linear order with second countable order topology,
the points can be separated by countably many infinite intervals.
We prove 4 versions of this statement (one for each of the infinite intervals),
as well as provide convenience corollaries about `Filter.EventuallyEq`.
-/

public section

open Set

variable {X : Type*} [TopologicalSpace X] [LinearOrder X]
  [OrderTopology X] [SecondCountableTopology X]

namespace HasCountableSeparatingOn

variable {s : Set X}

/-
**HasCountableSeparatingOn.range_Iio** 是 Mathlib 中的一个实例，位于命名空间 `HasCountableSepa
ratingOn`。
形式化陈述：range_Iio : HasCountableSeparatingOn X (· in range Iio) s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.exists_countable_dense`：exists_countable_dense [Separab
leSpace α] : exists s : Set α, s.Countable ∧ Dense s
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
· 使用定理 `countable_setOfPred_covBy_left`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : LinearOrder α] [OrderTopology α] [SecondCountableTopology α],   {x 
| ∃ y, y ⋖ x}.Counta…
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Dense.inter_open_nonempty`：∀ {X : Type u} [inst : TopologicalSpace X] {s
 : Set X},   Dense s → ∀ (U : Set X), IsOpen U → U.Nonempty → (U ∩ s).Nonempty
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
-/
instance range_Iio : HasCountableSeparatingOn X (· ∈ range Iio) s := by
  constructor
  rcases TopologicalSpace.exists_countable_dense X with ⟨s, hsc, hsd⟩
  set t := s ∪ {x | ∃ y, y ⋖ x}
  refine ⟨Iio '' t, .image ?_ _, ?_, ?_⟩
  · exact hsc.union countable_setOfPred_covBy_left
  · exact image_subset_range _ _
  · rintro x - y - h
    by_contra! hne
    wlog hlt : x < y generalizing x y
    · refine this y x ?_ hne.symm (hne.lt_or_gt.resolve_left hlt)
      simpa only [iff_comm] using h
    cases (Ioo x y).eq_empty_or_nonempty with
    | inl he =>
      specialize h (Iio y) (mem_image_of_mem _ (.inr ⟨x, hlt, by simpa using Set.ext_iff.mp he⟩))
      simp [hlt.not_ge] at h
    | inr hne =>
      rcases hsd.inter_open_nonempty _ isOpen_Ioo hne with ⟨z, ⟨hxz, hzy⟩, hzs⟩
      simpa [hxz, hzy.not_gt] using h (Iio z) (mem_image_of_mem _ (.inl hzs))
/-
**HasCountableSeparatingOn.range_Ioi** 是 Mathlib 中的一个实例，位于命名空间 `HasCountableSepa
ratingOn`。
形式化陈述：range_Ioi : HasCountableSeparatingOn X (· in range Ioi) s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
-/
instance range_Ioi : HasCountableSeparatingOn X (· ∈ range Ioi) s :=
  .range_Iio (X := Xᵒᵈ)
/-
**HasCountableSeparatingOn.range_Iic** 是 Mathlib 中的一个实例，位于命名空间 `HasCountableSepa
ratingOn`。
形式化陈述：range_Iic : HasCountableSeparatingOn X (· in range Iic) s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCountableSeparatingOn.exists_countable_separating`：∀ {α : Type u_1} {
p : Set α → Prop} {t : Set α} [self : HasCountableSeparatingOn α p t],   ∃ S, S.
Countable ∧ (∀ s ∈ S, p s) ∧ ∀ x ∈ t, ∀ y …
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_Ioi`：∀ {α : Type u_1} [inst : LinearOrder α] {a : α}, (Set.Ioi
 a)ᶜ = Set.Iic a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
instance range_Iic : HasCountableSeparatingOn X (· ∈ range Iic) s :=
  let ⟨t, htc, ht_sub, ht⟩ := (range_Ioi (X := X) (s := s)).1
  ⟨compl '' t, htc.image _, by simpa [← compl_inj_iff (x := Ioi _)] using ht_sub,
    by simpa [not_iff_not]⟩
/-
**HasCountableSeparatingOn.range_Ici** 是 Mathlib 中的一个实例，位于命名空间 `HasCountableSepa
ratingOn`。
形式化陈述：range_Ici : HasCountableSeparatingOn X (· in range Ici) s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
-/
instance range_Ici : HasCountableSeparatingOn X (· ∈ range Ici) s :=
  range_Iic (X := Xᵒᵈ)

end HasCountableSeparatingOn

namespace Filter.EventuallyEq

variable {α : Type*} {l : Filter α} [CountableInterFilter l] {f g : α → X}

/-
**Filter.EventuallyEq.of_forall_eventually_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fil
ter.EventuallyEq`。
形式化陈述：of_forall_eventually_lt_iff (h : forall x, forallᶠ a in l, f a < x ↔ g a <
 x) : f =ᶠ[l] g
参数：h : forall x, forallᶠ a in l, f a < x ↔ g a < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.of_forall_separating_preimage`：of_forall_separating_
preimage (p : Set β -> Prop) [HasCountableSeparatingOn β p univ] (h : forall U :
 Set β, p U -> f ⁻¹' U =ᶠ[l] g ⁻¹' U) :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Filter.Eventually.set_eq`：∀ {α : Type u} {s t : Set α} {l : Filter α}, (
∀ᶠ (x : α) in l, x ∈ s ↔ x ∈ t) → s =ᶠ[l] t
-/
lemma of_forall_eventually_lt_iff (h : ∀ x, ∀ᶠ a in l, f a < x ↔ g a < x) : f =ᶠ[l] g :=
  of_forall_separating_preimage (· ∈ range Iio) <| forall_mem_range.2 <| fun x ↦ .set_eq (h x)
/-
**Filter.EventuallyEq.of_forall_eventually_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fil
ter.EventuallyEq`。
形式化陈述：of_forall_eventually_le_iff (h : forall x, forallᶠ a in l, f a <= x ↔ g a 
<= x) : f =ᶠ[l] g
参数：h : forall x, forallᶠ a in l, f a <= x ↔ g a <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.of_forall_separating_preimage`：of_forall_separating_
preimage (p : Set β -> Prop) [HasCountableSeparatingOn β p univ] (h : forall U :
 Set β, p U -> f ⁻¹' U =ᶠ[l] g ⁻¹' U) :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Filter.Eventually.set_eq`：∀ {α : Type u} {s t : Set α} {l : Filter α}, (
∀ᶠ (x : α) in l, x ∈ s ↔ x ∈ t) → s =ᶠ[l] t
-/
lemma of_forall_eventually_le_iff (h : ∀ x, ∀ᶠ a in l, f a ≤ x ↔ g a ≤ x) : f =ᶠ[l] g :=
  of_forall_separating_preimage (· ∈ range Iic) <| forall_mem_range.2 <| fun x ↦ .set_eq (h x)
/-
**Filter.EventuallyEq.of_forall_eventually_gt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fil
ter.EventuallyEq`。
形式化陈述：of_forall_eventually_gt_iff (h : forall x, forallᶠ a in l, x < f a ↔ x < g
 a) : f =ᶠ[l] g
参数：h : forall x, forallᶠ a in l, x < f a ↔ x < g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyEq.of_forall_eventually_lt_iff`：of_forall_eventually_lt
_iff (h : forall x, forallᶠ a in l, f a < x ↔ g a < x) : f =ᶠ[l] g
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
-/
lemma of_forall_eventually_gt_iff (h : ∀ x, ∀ᶠ a in l, x < f a ↔ x < g a) : f =ᶠ[l] g :=
  of_forall_eventually_lt_iff (X := Xᵒᵈ) h
/-
**Filter.EventuallyEq.of_forall_eventually_ge_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fil
ter.EventuallyEq`。
形式化陈述：of_forall_eventually_ge_iff (h : forall x, forallᶠ a in l, x <= f a ↔ x <=
 g a) : f =ᶠ[l] g
参数：h : forall x, forallᶠ a in l, x <= f a ↔ x <= g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyEq.of_forall_eventually_le_iff`：of_forall_eventually_le
_iff (h : forall x, forallᶠ a in l, f a <= x ↔ g a <= x) : f =ᶠ[l] g
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
-/
lemma of_forall_eventually_ge_iff (h : ∀ x, ∀ᶠ a in l, x ≤ f a ↔ x ≤ g a) : f =ᶠ[l] g :=
  of_forall_eventually_le_iff (X := Xᵒᵈ) h

end Filter.EventuallyEq

