/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Bhavik Mehta, Daniel Weber, Stefan Kebekus
-/
module

public import Mathlib.Tactic.TautoSet
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Set.Subset
public import Mathlib.Topology.Separation.Basic

/-!
# Discrete subsets of topological spaces

This file contains various additional properties of discrete subsets of topological spaces.

## Discreteness and compact sets

Given a topological space `X` together with a subset `s ⊆ X`, there are two distinct concepts of
"discreteness" which may hold. These are:
  (i) Every point of `s` is isolated (i.e., the subset topology induced on `s` is the discrete
      topology).
 (ii) Every compact subset of `X` meets `s` only finitely often (i.e., the inclusion map `s → X`
      tends to the cocompact filter along the cofinite filter on `s`).

When `s` is closed, the two conditions are equivalent provided `X` is locally compact and T1,
see `IsClosed.tendsto_coe_cofinite_iff`.

### Main statements

* `tendsto_cofinite_cocompact_iff`:
* `IsClosed.tendsto_coe_cofinite_iff`:

## Co-discrete open sets

We define the filter `Filter.codiscreteWithin S`, which is the supremum of all `𝓝[S \ {x}] x`.
This is the filter of all open codiscrete sets within S. We also define `Filter.codiscrete` as
`Filter.codiscreteWithin univ`, which is the filter of all open codiscrete sets in the space.

-/

@[expose] public section

open Set Filter Function Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {s : Set X}

/-
**discreteTopology_subtype_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_subtype_iff {S : Set Y} : DiscreteTopology S ↔ forall x i
n S, 𝓝[!=] x ⊓ 𝓟 S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem discreteTopology_subtype_iff {S : Set Y} :
    DiscreteTopology S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ := by
  simp_rw [discreteTopology_iff_nhds_ne, SetCoe.forall', nhds_ne_subtype_eq_bot_iff]
/-
**isDiscrete_iff_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDiscrete_iff_nhdsNE {S : Set Y} : IsDiscrete S ↔ forall x in S, 𝓝[!=] x 
⊓ 𝓟 S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isDiscrete_iff_discreteTopology`：isDiscrete_iff_discreteTopology : IsDis
crete s ↔ DiscreteTopology s
· 使用定理 `discreteTopology_subtype_iff`：discreteTopology_subtype_iff {S : Set Y} :
 DiscreteTopology S ↔ forall x in S, 𝓝[!=] x ⊓ 𝓟 S = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isDiscrete_iff_nhdsNE {S : Set Y} :
    IsDiscrete S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ := by
  rw [isDiscrete_iff_discreteTopology, discreteTopology_subtype_iff]

/-- If a subset of a topological space has no accumulation points,
then it carries the discrete topology. -/
/-
**discreteTopology_of_noAccPts** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：discreteTopology_of_noAccPts {X : Type*} [TopologicalSpace X] {E : Set X} 
(h : forall x in E, ¬ AccPt x (𝓟 E)) : DiscreteTopology E
参数：h : forall x in E, ¬ AccPt x (𝓟 E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If a subset of a topological space has no accumulation points,
then it carries the discrete topology.
-/
lemma discreteTopology_of_noAccPts {X : Type*} [TopologicalSpace X] {E : Set X}
    (h : ∀ x ∈ E, ¬ AccPt x (𝓟 E)) : DiscreteTopology E := by
  simpa [discreteTopology_subtype_iff, AccPt] using h
/-
**discreteTopology_subtype_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：discreteTopology_subtype_iff' {S : Set Y} : DiscreteTopology S ↔ forall y 
in S, exists U : Set Y, IsOpen U ∧ U inter S = {y}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma discreteTopology_subtype_iff' {S : Set Y} :
    DiscreteTopology S ↔ ∀ y ∈ S, ∃ U : Set Y, IsOpen U ∧ U ∩ S = {y} := by
  simp [discreteTopology_iff_isOpen_singleton, isOpen_induced_iff, Set.ext_iff]
  grind

/-- A set `s` is discrete iff for every `y ∈ s` there is an open `u` with `u ∩ s = {y}`.
See `isDiscrete_iff_forall_subset_exists_isOpen'` for a related version of this with subsets. -/
/-
**isDiscrete_iff_forall_mem_exists_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDiscrete_iff_forall_mem_exists_isOpen {s : Set Y} : IsDiscrete s ↔ foral
l y in s, exists u, IsOpen u ∧ u inter s = {y}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isDiscrete_iff_discreteTopology`：isDiscrete_iff_discreteTopology : IsDis
crete s ↔ DiscreteTopology s
· 使用引理 `discreteTopology_subtype_iff'`：discreteTopology_subtype_iff' {S : Set Y}
 : DiscreteTopology S ↔ forall y in S, exists U : Set Y, IsOpen U ∧ U inter S = 
{y}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A set `s` is discrete iff for every `y ∈ s` there is an open `u` with `u ∩ s = {
y}`.
See `isDiscrete_iff_forall_subset_exists_isOpen'` for a related version of this 
with subsets.
-/
theorem isDiscrete_iff_forall_mem_exists_isOpen {s : Set Y} :
    IsDiscrete s ↔ ∀ y ∈ s, ∃ u, IsOpen u ∧ u ∩ s = {y} := by
  rw [isDiscrete_iff_discreteTopology, discreteTopology_subtype_iff']

@[deprecated (since := "2026-06-24")]
alias isDiscrete_iff_forall_exists_isOpen := isDiscrete_iff_forall_mem_exists_isOpen

/-- A set `s` is discrete iff for every `t ⊆ s` there is an open `u` with `u ∩ s = t`.
See `isDiscrete_iff_forall_mem_exists_isOpen` for a similar version of this with singletons. -/
/-
**isDiscrete_iff_forall_subset_exists_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDiscrete_iff_forall_subset_exists_isOpen {s : Set X} : IsDiscrete s ↔ fo
rall t subseteq s, exists u, IsOpen u ∧ u inter s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_image`：image_eq_image {f : α -> β} (hf : Injective f) : f '
' s = f '' t ↔ s = t
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Subtype.forall_set_subtype`：forall_set_subtype {t : Set α} (p : Set α ->
 Prop) : (forall s : Set t, p (((↑) : t -> α) '' s)) ↔ forall s : Set α, s subse
teq t -> p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A set `s` is discrete iff for every `t ⊆ s` there is an open `u` with `u ∩ s = t
`.
See `isDiscrete_iff_forall_mem_exists_isOpen` for a similar version of this with
 singletons.
-/
theorem isDiscrete_iff_forall_subset_exists_isOpen {s : Set X} :
    IsDiscrete s ↔ ∀ t ⊆ s, ∃ u, IsOpen u ∧ u ∩ s = t := by
  simp_rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_forall_isOpen,
    isOpen_induced_iff, ← image_eq_image (Subtype.val_injective), Subtype.image_preimage_coe,
    Subtype.forall_set_subtype (p := fun t ↦ ∃ u, IsOpen u ∧ s ∩ u = t), inter_comm]

/-- A set `s` is discrete iff for every `t ⊆ s` there is a closed `u` with `u ∩ s = t`. -/
/-
**isDiscrete_iff_forall_mem_exists_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDiscrete_iff_forall_mem_exists_isClosed {S : Set X} : IsDiscrete S ↔ for
all s subseteq S, exists U, IsClosed U ∧ U inter S = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isDiscrete_iff_forall_subset_exists_isOpen`：isDiscrete_iff_forall_subset
_exists_isOpen {s : Set X} : IsDiscrete s ↔ forall t subseteq s, exists u, IsOpe
n u ∧ u inter s = t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `Set.left_eq_inter`：∀ {α : Type u} {s t : Set α}, s = s ∩ t ↔ s ⊆ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s

--- 原说明 ---
A set `s` is discrete iff for every `t ⊆ s` there is a closed `u` with `u ∩ s = 
t`.
-/
theorem isDiscrete_iff_forall_mem_exists_isClosed {S : Set X} :
    IsDiscrete S ↔ ∀ s ⊆ S, ∃ U, IsClosed U ∧ U ∩ S = s := by
  rw [isDiscrete_iff_forall_subset_exists_isOpen]
  constructor <;> intro h s sS
  · obtain ⟨U, Uo, Us⟩ := h (sᶜ ∩ S) inter_subset_right
    exact ⟨Uᶜ, isClosed_compl_iff.mpr Uo, by rw [left_eq_inter.mpr sS]; simp_all [Set.ext_iff]⟩
  · obtain ⟨U, Uo, Us⟩ := h (sᶜ ∩ S) inter_subset_right
    exact ⟨Uᶜ, isOpen_compl_iff.mpr Uo, by rw [left_eq_inter.mpr sS]; simp_all [Set.ext_iff]⟩
/-
**isClosed_of_subset_discrete_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_of_subset_discrete_closed {s t : Set X} (sd : s subseteq t) (ht :
 IsDiscrete t) (tc : IsClosed t) : IsClosed s
参数：sd : s subseteq t；ht : IsDiscrete t；tc : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isDiscrete_iff_forall_mem_exists_isClosed`：isDiscrete_iff_forall_mem_exi
sts_isClosed {S : Set X} : IsDiscrete S ↔ forall s subseteq S, exists U, IsClose
d U ∧ U inter S = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
-/
theorem isClosed_of_subset_discrete_closed {s t : Set X} (sd : s ⊆ t)
    (ht : IsDiscrete t) (tc : IsClosed t) : IsClosed s := by
  obtain ⟨_, rp, rt⟩ := isDiscrete_iff_forall_mem_exists_isClosed.mp ht s sd
  rw [← rt]
  exact rp.inter tc
/-
**Set.Subsingleton.isDiscrete** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.isDiscrete (hs : s.Subsingleton) : IsDiscrete s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
-/
lemma Set.Subsingleton.isDiscrete (hs : s.Subsingleton) : IsDiscrete s :=
  have : Subsingleton s := (Set.subsingleton_coe s).mpr hs
  ⟨inferInstance⟩
/-
**isDiscrete_iff_nhdsWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isDiscrete_iff_nhdsWithin : IsDiscrete s ↔ forall x in s, 𝓝[s] x = pure x
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
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Filter.map_injective`：map_injective {m : α -> β} (hm : Injective m) : In
jective (map m)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Filter.map_comap`：map_comap (f : Filter β) (m : α -> β) : (f.comap m).ma
p m = f ⊓ 𝓟 (range m)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isDiscrete_iff_nhdsWithin : IsDiscrete s ↔ ∀ x ∈ s, 𝓝[s] x = pure x := by
  simp [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure, nhds_induced,
    ← (Filter.map_injective Subtype.val_injective).eq_iff,
    Filter.map_comap, nhdsWithin]

protected alias ⟨IsDiscrete.nhdsWithin, _⟩ := isDiscrete_iff_nhdsWithin
/-
**IsDiscrete.of_nhdsWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscrete.of_nhdsWithin (H : forall x in s, 𝓝[s] x <= pure x) : IsDiscret
e s
参数：H : forall x in s, 𝓝[s] x <= pure x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isDiscrete_iff_nhdsWithin`：isDiscrete_iff_nhdsWithin : IsDiscrete s ↔ fo
rall x in s, 𝓝[s] x = pure x
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
-/
lemma IsDiscrete.of_nhdsWithin (H : ∀ x ∈ s, 𝓝[s] x ≤ pure x) : IsDiscrete s :=
  isDiscrete_iff_nhdsWithin.mpr fun x hx ↦ (H x hx).antisymm (pure_le_nhdsWithin hx)
/-
**isDiscrete_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isDiscrete_univ_iff : IsDiscrete (Set.univ : Set X) ↔ DiscreteTopology X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isDiscrete_univ_iff : IsDiscrete (Set.univ : Set X) ↔ DiscreteTopology X := by
  simp [isDiscrete_iff_nhdsWithin, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure]
/-
**IsDiscrete.univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscrete.univ [DiscreteTopology X] : IsDiscrete (Set.univ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isDiscrete_univ_iff`：isDiscrete_univ_iff : IsDiscrete (Set.univ : Set X)
 ↔ DiscreteTopology X
-/
lemma IsDiscrete.univ [DiscreteTopology X] : IsDiscrete (Set.univ : Set X) := by
  rwa [isDiscrete_univ_iff]
/-
**IsDiscrete.image_of_isOpenMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscrete.image_of_isOpenMap (hs : IsDiscrete s) (hf : IsOpenMap f) (hf' 
: Function.Injective f) : IsDiscrete (f '' s)
参数：hs : IsDiscrete s；hf : IsOpenMap f；hf' : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDiscrete.of_nhdsWithin`：IsDiscrete.of_nhdsWithin (H : forall x in s, 𝓝
[s] x <= pure x) : IsDiscrete s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_pure`：map_pure (f : α -> β) (a : α) : map f (pure a) = pure (
f a)
· 使用定理 `IsDiscrete.nhdsWithin`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → ∀ x ∈ s, nhdsWithin x s = pure x
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.map_inf`：map_inf {f g : Filter α} {m : α -> β} (h : Injective m) 
: map m (f ⊓ g) = map m f ⊓ map m g
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `IsOpenMap.nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhd
s (f x)…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma IsDiscrete.image_of_isOpenMap (hs : IsDiscrete s) (hf : IsOpenMap f)
    (hf' : Function.Injective f) : IsDiscrete (f '' s) := by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pure, ← hs.nhdsWithin x hx, nhdsWithin, nhdsWithin, map_inf hf', map_principal]
  grw [hf.nhds_le x]
/-
**IsDiscrete.image_of_isOpenMap_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscrete.image_of_isOpenMap_of_isOpen (hs : IsDiscrete s) (hf : IsOpenMa
p f) (hs' : IsOpen s) : IsDiscrete (f '' s)
参数：hs : IsDiscrete s；hf : IsOpenMap f；hs' : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDiscrete.of_nhdsWithin`：IsDiscrete.of_nhdsWithin (H : forall x in s, 𝓝
[s] x <= pure x) : IsDiscrete s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_pure`：map_pure (f : α -> β) (a : α) : map f (pure a) = pure (
f a)
· 使用定理 `IsDiscrete.nhdsWithin`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → ∀ x ∈ s, nhdsWithin x s = pure x
· 使用定理 `IsOpenMap.nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhd
s (f x)…
-/
lemma IsDiscrete.image_of_isOpenMap_of_isOpen (hs : IsDiscrete s) (hf : IsOpenMap f)
    (hs' : IsOpen s) : IsDiscrete (f '' s) := by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [(hf _ hs').nhdsWithin_eq ⟨x, hx, rfl⟩, ← map_pure, ← hs.nhdsWithin x hx, hs'.nhdsWithin_eq hx]
  exact hf.nhds_le x
/-
**IsOpenMap.isDiscrete_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpenMap.isDiscrete_range [DiscreteTopology X] (hf : IsOpenMap f) : IsDis
crete (Set.range f)
参数：hf : IsOpenMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用引理 `IsDiscrete.image_of_isOpenMap_of_isOpen`：IsDiscrete.image_of_isOpenMap_o
f_isOpen (hs : IsDiscrete s) (hf : IsOpenMap f) (hs' : IsOpen s) : IsDiscrete (f
 '' s)
· 使用引理 `IsDiscrete.univ`：IsDiscrete.univ [DiscreteTopology X] : IsDiscrete (Set.
univ : Set X)
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
lemma IsOpenMap.isDiscrete_range [DiscreteTopology X] (hf : IsOpenMap f) :
    IsDiscrete (Set.range f) := by
  simpa using IsDiscrete.univ.image_of_isOpenMap_of_isOpen hf isOpen_univ
/-
**IsDiscrete.image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscrete.image (hs : IsDiscrete s) (hf : IsInducing f) : IsDiscrete (f '
' s)
参数：hs : IsDiscrete s；hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.map_nhdsWithin_eq`：Topology.IsInducing.map_nhdsWithi
n_eq {f : α -> β} (hf : IsInducing f) (s : Set α) (x : α) : map f (𝓝[s] x) = 𝓝[f
 '' s] f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsDiscrete.image (hs : IsDiscrete s) (hf : IsInducing f) : IsDiscrete (f '' s) := by
  simp_all [isDiscrete_iff_nhdsWithin, ← hf.map_nhdsWithin_eq s]
/-
**Topology.IsInducing.isDiscrete_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isDiscrete_range [DiscreteTopology X] (hf : IsInducing
 f) : IsDiscrete (Set.range f)
参数：hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用引理 `IsDiscrete.image`：IsDiscrete.image (hs : IsDiscrete s) (hf : IsInducing 
f) : IsDiscrete (f '' s)
· 使用引理 `IsDiscrete.univ`：IsDiscrete.univ [DiscreteTopology X] : IsDiscrete (Set.
univ : Set X)
-/
lemma Topology.IsInducing.isDiscrete_range [DiscreteTopology X] (hf : IsInducing f) :
    IsDiscrete (Set.range f) := by
  simpa using IsDiscrete.univ.image hf

@[deprecated (since := "2026-03-30")] alias
IsEmbedding.isDiscrete_range := IsInducing.isDiscrete_range
/-
**IsDiscrete.preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscrete.preimage {s : Set Y} (hs : IsDiscrete s) (hf : ContinuousOn f (
f ⁻¹' s)) (hf' : Function.Injective f) : IsDiscrete (f ⁻¹' s)
参数：hs : IsDiscrete s；hf : ContinuousOn f (f ⁻¹' s)；hf' : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDiscrete.of_nhdsWithin`：IsDiscrete.of_nhdsWithin (H : forall x in s, 𝓝
[s] x <= pure x) : IsDiscrete s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_le_map_iff`：map_le_map_iff {f g : Filter α} {m : α -> β} (hm 
: Injective m) : map m f <= map m g ↔ f <= g
· 使用定理 `Filter.map_pure`：map_pure (f : α -> β) (a : α) : map f (pure a) = pure (
f a)
· 使用定理 `IsDiscrete.nhdsWithin`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → ∀ x ∈ s, nhdsWithin x s = pure x
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
lemma IsDiscrete.preimage {s : Set Y} (hs : IsDiscrete s)
    (hf : ContinuousOn f (f ⁻¹' s)) (hf' : Function.Injective f) :
    IsDiscrete (f ⁻¹' s) := by
  refine .of_nhdsWithin fun x hx ↦ ?_
  rw [← map_le_map_iff hf', map_pure, ← hs.nhdsWithin _ hx, ← Tendsto]
  exact (hf.continuousWithinAt hx).tendsto_nhdsWithin (Set.mapsTo_preimage _ _)

/-- If `f` is continuous with discrete fibers, then the preimage of discrete sets are discrete. -/
/-
**IsDiscrete.preimage'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscrete.preimage' {s : Set Y} (hs : IsDiscrete s) (hf : ContinuousOn f 
(f ⁻¹' s)) (H : forall x, IsDiscrete (f ⁻¹' {x})) : IsDiscrete (f ⁻¹' s)
参数：hs : IsDiscrete s；hf : ContinuousOn f (f ⁻¹' s)；H : forall x, IsDiscrete (f ⁻
¹' {x})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDiscrete.of_nhdsWithin`：IsDiscrete.of_nhdsWithin (H : forall x in s, 𝓝
[s] x <= pure x) : IsDiscrete s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsDiscrete.nhdsWithin`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → ∀ x ∈ s, nhdsWithin x s = pure x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_pure`：comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b})
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s

--- 原说明 ---
If `f` is continuous with discrete fibers, then the preimage of discrete sets ar
e discrete.
-/
lemma IsDiscrete.preimage' {s : Set Y} (hs : IsDiscrete s)
    (hf : ContinuousOn f (f ⁻¹' s))
    (H : ∀ x, IsDiscrete (f ⁻¹' {x})) : IsDiscrete (f ⁻¹' s) := by
  refine .of_nhdsWithin fun x hx ↦ ?_
  have h := ((H (f x)).nhdsWithin _ rfl).le
  grw [nhdsWithin, ← comap_pure, ← hs.nhdsWithin _ hx, ← (hf.continuousWithinAt hx
    |>.tendsto_nhdsWithin fun _ ↦ by exact id).le_comap, inf_eq_right.mpr nhdsWithin_le_nhds] at h
  exact h
/-
**IsDiscrete.eq_of_specializes** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscrete.eq_of_specializes (hs : IsDiscrete s) {a b : X} (hab : a ⤳ b) (
ha : a in s) (hb : b in s) : a = b
参数：hs : IsDiscrete s；hab : a ⤳ b；ha : a in s；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscrete.to_subtype`：∀ {X : Type u_5} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → DiscreteTopology ↑s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.specializes_iff`：Topology.IsInducing.specializes_iff
 (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `specializes_iff_eq`：specializes_iff_eq [T1Space X] {x y : X} : x ⤳ y ↔ x
 = y
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
-/
lemma IsDiscrete.eq_of_specializes (hs : IsDiscrete s)
    {a b : X} (hab : a ⤳ b) (ha : a ∈ s) (hb : b ∈ s) : a = b := by
  let := hs.1
  simpa only [← Topology.IsInducing.subtypeVal.specializes_iff, hab, Subtype.mk.injEq,
    true_iff] using specializes_iff_eq (X := s) (x := ⟨a, ha⟩) (y := ⟨b, hb⟩)

section cofinite_cocompact

omit [TopologicalSpace X] in
/-
**tendsto_cofinite_cocompact_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_cofinite_cocompact_iff : Tendsto f cofinite (cocompact _) ↔ forall
 K, IsCompact K -> Set.Finite (f ⁻¹' K)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma tendsto_cofinite_cocompact_iff :
    Tendsto f cofinite (cocompact _) ↔ ∀ K, IsCompact K → Set.Finite (f ⁻¹' K) := by
  rw [hasBasis_cocompact.tendsto_right_iff]
  refine forall₂_congr (fun K _ ↦ ?_)
  simp only [mem_compl_iff, eventually_cofinite, not_not, preimage]
/-
**Continuous.discrete_of_tendsto_cofinite_cocompact** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：Continuous.discrete_of_tendsto_cofinite_cocompact [T1Space X] [WeaklyLocal
lyCompactSpace Y] (hf' : Continuous f) (hf : Tendsto f cofinite (cocompact _)) :
 DiscreteTopology X
参数：hf' : Continuous f；hf : Tendsto f cofinite (cocompact _)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_isOpen_singleton`：discreteTopology_iff_isOpen_singl
eton [TopologicalSpace α] : DiscreteTopology α ↔ (forall a : α, IsOpen ({a} : Se
t α))
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `tendsto_cofinite_cocompact_iff`：tendsto_cofinite_cocompact_iff : Tendsto
 f cofinite (cocompact _) ↔ forall K, IsCompact K -> Set.Finite (f ⁻¹' K)
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `isOpen_singleton_of_finite_mem_nhds`：isOpen_singleton_of_finite_mem_nhds
 [T1Space X] (x : X) {s : Set X} (hs : s in 𝓝 x) (hsf : s.Finite) : IsOpen ({x} 
: Set X)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
-/
lemma Continuous.discrete_of_tendsto_cofinite_cocompact [T1Space X] [WeaklyLocallyCompactSpace Y]
    (hf' : Continuous f) (hf : Tendsto f cofinite (cocompact _)) :
    DiscreteTopology X := by
  refine discreteTopology_iff_isOpen_singleton.mpr (fun x ↦ ?_)
  obtain ⟨K : Set Y, hK : IsCompact K, hK' : K ∈ 𝓝 (f x)⟩ := exists_compact_mem_nhds (f x)
  obtain ⟨U : Set Y, hU₁ : U ⊆ K, hU₂ : IsOpen U, hU₃ : f x ∈ U⟩ := mem_nhds_iff.mp hK'
  have hU₄ : Set.Finite (f ⁻¹' U) :=
    Finite.subset (tendsto_cofinite_cocompact_iff.mp hf K hK) (preimage_mono hU₁)
  exact isOpen_singleton_of_finite_mem_nhds _ ((hU₂.preimage hf').mem_nhds hU₃) hU₄
/-
**tendsto_cofinite_cocompact_of_discrete** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_cofinite_cocompact_of_discrete [DiscreteTopology X] (hf : Tendsto 
f (cocompact _) (cocompact _)) : Tendsto f cofinite (cocompact _)
参数：hf : Tendsto f (cocompact _) (cocompact _)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.cocompact_eq_cofinite`：cocompact_eq_cofinite (X : Type*) [Topolog
icalSpace X] [DiscreteTopology X] : cocompact X = cofinite
-/
lemma tendsto_cofinite_cocompact_of_discrete [DiscreteTopology X]
    (hf : Tendsto f (cocompact _) (cocompact _)) :
    Tendsto f cofinite (cocompact _) := by
  convert! hf
  rw [cocompact_eq_cofinite X]
/-
**IsClosed.tendsto_coe_cofinite_of_isDiscrete** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.tendsto_coe_cofinite_of_isDiscrete {s : Set X} (hs : IsClosed s) 
(hs' : IsDiscrete s) : Tendsto ((↑) : s -> X) cofinite (cocompact _)
参数：hs : IsClosed s；hs' : IsDiscrete s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendsto_cofinite_cocompact_of_discrete`：tendsto_cofinite_cocompact_of_di
screte [DiscreteTopology X] (hf : Tendsto f (cocompact _) (cocompact _)) : Tends
to f cofinite (cocompact _)
· 使用定理 `IsDiscrete.to_subtype`：∀ {X : Type u_5} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → DiscreteTopology ↑s
· 使用定理 `Topology.IsClosedEmbedding.tendsto_cocompact`：Topology.IsClosedEmbedding
.tendsto_cocompact (hf : IsClosedEmbedding f) : Tendsto f (Filter.cocompact X) (
Filter.cocompact Y)
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
-/
lemma IsClosed.tendsto_coe_cofinite_of_isDiscrete
    {s : Set X} (hs : IsClosed s) (hs' : IsDiscrete s) :
    Tendsto ((↑) : s → X) cofinite (cocompact _) :=
  haveI := hs'.to_subtype
  tendsto_cofinite_cocompact_of_discrete hs.isClosedEmbedding_subtypeVal.tendsto_cocompact
/-
**IsClosed.tendsto_coe_cofinite_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.tendsto_coe_cofinite_iff [T1Space X] [WeaklyLocallyCompactSpace X
] {s : Set X} (hs : IsClosed s) : Tendsto ((↑) : s -> X) cofinite (cocompact _) 
↔ IsDiscrete s
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Continuous.discrete_of_tendsto_cofinite_cocompact`：Continuous.discrete_o
f_tendsto_cofinite_cocompact [T1Space X] [WeaklyLocallyCompactSpace Y] (hf' : Co
ntinuous f) (hf : Tendsto f cofinite (c…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用引理 `IsClosed.tendsto_coe_cofinite_of_isDiscrete`：IsClosed.tendsto_coe_cofini
te_of_isDiscrete {s : Set X} (hs : IsClosed s) (hs' : IsDiscrete s) : Tendsto ((
↑) : s -> X) cofinite (cocompact …
-/
lemma IsClosed.tendsto_coe_cofinite_iff [T1Space X] [WeaklyLocallyCompactSpace X]
    {s : Set X} (hs : IsClosed s) :
    Tendsto ((↑) : s → X) cofinite (cocompact _) ↔ IsDiscrete s :=
  ⟨fun h ↦ ⟨continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact h⟩,
   fun hs' ↦ hs.tendsto_coe_cofinite_of_isDiscrete hs'⟩

end cofinite_cocompact

section codiscrete_filter

/-- Criterion for a subset `S ⊆ X` to be closed and discrete in terms of the punctured
neighbourhood filter at an arbitrary point of `X`. (Compare `isDiscrete_iff_nhds_ne`.) -/
/-
**isClosed_and_discrete_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_and_discrete_iff {S : Set X} : IsClosed S ∧ IsDiscrete S ↔ forall
 x, Disjoint (𝓝[!=] x) (𝓟 S)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isDiscrete_iff_nhdsNE`：isDiscrete_iff_nhdsNE {S : Set Y} : IsDiscrete S 
↔ forall x in S, 𝓝[!=] x ⊓ 𝓟 S = ⊥
· 使用定理 `isClosed_iff_clusterPt`：isClosed_iff_clusterPt : IsClosed s ↔ forall a, 
ClusterPt a (𝓟 s) -> a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `clusterPt_iff_not_disjoint`：clusterPt_iff_not_disjoint {F : Filter X} : 
ClusterPt x F ↔ ¬Disjoint (𝓝 x) F
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Criterion for a subset `S ⊆ X` to be closed and discrete in terms of the punctur
ed
neighbourhood filter at an arbitrary point of `X`. (Compare `isDiscrete_iff_nhds
_ne`.)
-/
theorem isClosed_and_discrete_iff {S : Set X} :
    IsClosed S ∧ IsDiscrete S ↔ ∀ x, Disjoint (𝓝[≠] x) (𝓟 S) := by
  rw [isDiscrete_iff_nhdsNE, isClosed_iff_clusterPt, ← forall_and]
  congrm (∀ x, ?_)
  rw [← not_imp_not, clusterPt_iff_not_disjoint, not_not, ← disjoint_iff]
  constructor <;> intro H
  · by_cases hx : x ∈ S
    exacts [H.2 hx, (H.1 hx).mono_left nhdsWithin_le_nhds]
  · refine ⟨fun hx ↦ ?_, fun _ ↦ H⟩
    simpa [disjoint_iff, nhdsWithin, inf_assoc, hx] using H

/-- The filter of sets with no accumulation points inside a set `S : Set X`, implemented
as the supremum over all punctured neighborhoods within `S`. -/
/-
**Filter.codiscreteWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Filter.codiscreteWithin (S : Set X) : Filter X
参数：S : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The filter of sets with no accumulation points inside a set `S : Set X`, impleme
nted
as the supremum over all punctured neighborhoods within `S`.
-/
def Filter.codiscreteWithin (S : Set X) : Filter X := ⨆ x ∈ S, 𝓝[S \ {x}] x
/-
**mem_codiscreteWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_codiscreteWithin {S T : Set X} : S in codiscreteWithin T ↔ forall x in
 T, Disjoint (𝓝[!=] x) (𝓟 (T \ S))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
lemma mem_codiscreteWithin {S T : Set X} :
    S ∈ codiscreteWithin T ↔ ∀ x ∈ T, Disjoint (𝓝[≠] x) (𝓟 (T \ S)) := by
  simp only [codiscreteWithin, mem_iSup, mem_nhdsWithin, disjoint_principal_right, subset_def,
    Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
  congr! 7 with x - u y
  tauto

/--
A set `s` is codiscrete within `U` iff `s ∪ Uᶜ` is a punctured neighborhood of every point in `U`.
-/
/-
**mem_codiscreteWithin_iff_forall_mem_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_codiscreteWithin_iff_forall_mem_nhdsNE {S T : Set X} : S in codiscrete
Within T ↔ forall x in T, S union Tᶜ in 𝓝[!=] x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_sdiff`：compl_sdiff : (t \ s)ᶜ = s union tᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A set `s` is codiscrete within `U` iff `s ∪ Uᶜ` is a punctured neighborhood of e
very point in `U`.
-/
theorem mem_codiscreteWithin_iff_forall_mem_nhdsNE {S T : Set X} :
    S ∈ codiscreteWithin T ↔ ∀ x ∈ T, S ∪ Tᶜ ∈ 𝓝[≠] x := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_sdiff]
/-
**mem_codiscreteWithin_accPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_codiscreteWithin_accPt {S T : Set X} : S in codiscreteWithin T ↔ foral
l x in T, ¬AccPt x (𝓟 (T \ S))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_codiscreteWithin_accPt {S T : Set X} :
    S ∈ codiscreteWithin T ↔ ∀ x ∈ T, ¬AccPt x (𝓟 (T \ S)) := by
  simp only [mem_codiscreteWithin, disjoint_iff, AccPt, not_neBot]

/-- Any set is codiscrete within itself. -/
@[simp]
/-
**Filter.self_mem_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.self_mem_codiscreteWithin (U : Set X) : U in Filter.codiscreteWithi
n U
参数：U : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Any set is codiscrete within itself.
-/
theorem Filter.self_mem_codiscreteWithin (U : Set X) :
    U ∈ Filter.codiscreteWithin U := by simp [mem_codiscreteWithin]

/-- If a set is codiscrete within `U`, then it is codiscrete within any subset of `U`. -/
@[gcongr]
/-
**Filter.codiscreteWithin_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.codiscreteWithin_mono {U₁ U : Set X} (hU : U₁ subseteq U) : codiscr
eteWithin U₁ <= codiscreteWithin U
参数：hU : U₁ subseteq U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If a set is codiscrete within `U`, then it is codiscrete within any subset of `U
`.
-/
lemma Filter.codiscreteWithin_mono {U₁ U : Set X} (hU : U₁ ⊆ U) :
    codiscreteWithin U₁ ≤ codiscreteWithin U := by
  refine (biSup_mono hU).trans <| iSup₂_mono fun _ _ ↦ ?_
  gcongr

@[deprecated (since := "2026-05-13")]
alias Filter.codiscreteWithin.mono := Filter.codiscreteWithin_mono

/-- If `s` is codiscrete within `U`, then `sᶜ ∩ U` has discrete topology. -/
/-
**isDiscrete_of_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDiscrete_of_codiscreteWithin {U s : Set X} (h : sᶜ in Filter.codiscreteW
ithin U) : IsDiscrete (s inter U)
参数：h : sᶜ in Filter.codiscreteWithin U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isDiscrete_iff_nhdsNE`：isDiscrete_iff_nhdsNE {S : Set Y} : IsDiscrete S 
↔ forall x in S, 𝓝[!=] x ⊓ 𝓟 S = ⊥
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sdiff_compl`：sdiff_compl : x \ yᶜ = x ⊓ y
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `s` is codiscrete within `U`, then `sᶜ ∩ U` has discrete topology.
-/
theorem isDiscrete_of_codiscreteWithin {U s : Set X} (h : sᶜ ∈ Filter.codiscreteWithin U) :
    IsDiscrete (s ∩ U) := by
  rw [(by simp : ((s ∩ U) : Set X) = ((sᶜ ∪ Uᶜ)ᶜ : Set X)), isDiscrete_iff_nhdsNE]
  simp_rw [← Filter.mem_iff_inf_principal_compl]
  simp_all [← Set.compl_sdiff, mem_codiscreteWithin]

/-- Helper lemma for `codiscreteWithin_iff_locallyFiniteComplementWithin`: A set `s` is
`codiscreteWithin U` iff every point `z ∈ U` has a punctured neighborhood that does not intersect
`U \ s`. -/
/-
**codiscreteWithin_iff_locallyEmptyComplementWithin** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：codiscreteWithin_iff_locallyEmptyComplementWithin {s U : Set X} : s in cod
iscreteWithin U ↔ forall z in U, exists t in 𝓝[!=] z, t inter (U \ s) = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.exists_mem_subset_iff`：exists_mem_subset_iff : (exists t in f, t 
subseteq s) ↔ s in f
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅

--- 原说明 ---
Helper lemma for `codiscreteWithin_iff_locallyFiniteComplementWithin`: A set `s`
 is
`codiscreteWithin U` iff every point `z ∈ U` has a punctured neighborhood that d
oes not intersect
`U \ s`.
-/
lemma codiscreteWithin_iff_locallyEmptyComplementWithin {s U : Set X} :
    s ∈ codiscreteWithin U ↔ ∀ z ∈ U, ∃ t ∈ 𝓝[≠] z, t ∩ (U \ s) = ∅ := by
  simp only [mem_codiscreteWithin, disjoint_principal_right]
  refine ⟨fun h z hz ↦ ⟨(U \ s)ᶜ, h z hz, by simp⟩, fun h z hz ↦ ?_⟩
  rw [← exists_mem_subset_iff]
  obtain ⟨t, h₁t, h₂t⟩ := h z hz
  use t, h₁t, (disjoint_iff_inter_eq_empty.mpr h₂t).subset_compl_right

/-- If `U` is closed and `s` is codiscrete within `U`, then `U \ s` is closed. -/
/-
**isClosed_sdiff_of_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_sdiff_of_codiscreteWithin {s U : Set X} (hs : s in codiscreteWith
in U) (hU : IsClosed U) : IsClosed (U \ s)
参数：hs : s in codiscreteWithin U；hU : IsClosed U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isOpen_iff_eventually`：isOpen_iff_eventually : IsOpen s ↔ forall x, x in
 s -> forallᶠ y in 𝓝 x, y in s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.disjoint_principal_right`：disjoint_principal_right {f : Filter α}
 {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ in f
· 使用引理 `mem_codiscreteWithin`：mem_codiscreteWithin {S T : Set X} : S in codiscre
teWithin T ↔ forall x in T, Disjoint (𝓝[!=] x) (𝓟 (T \ S))
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `IsClosed.compl_mem_nhds`：IsClosed.compl_mem_nhds (hs : IsClosed s) (hx :
 x ∉ s) : sᶜ in 𝓝 x
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b

--- 原说明 ---
If `U` is closed and `s` is codiscrete within `U`, then `U \ s` is closed.
-/
theorem isClosed_sdiff_of_codiscreteWithin {s U : Set X} (hs : s ∈ codiscreteWithin U)
    (hU : IsClosed U) :
    IsClosed (U \ s) := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro x hx
  by_cases h₁x : x ∈ U
  · rw [mem_codiscreteWithin] at hs
    filter_upwards [eventually_nhdsWithin_iff.1 (disjoint_principal_right.1 (hs x h₁x))]
    intro a ha
    by_cases h₂a : a = x
    · tauto_set
    · specialize ha h₂a
      tauto_set
  · rw [eventually_iff_exists_mem]
    use Uᶜ, hU.compl_mem_nhds h₁x
    intro y hy
    tauto_set

/-- In a T1Space, punctured neighborhoods are stable under removing finite sets of points. -/
/-
**nhdsNE_of_nhdsNE_sdiff_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsNE_of_nhdsNE_sdiff_finite {X : Type*} [TopologicalSpace X] [T1Space X]
 {x : X} {U s : Set X} (hU : U in 𝓝[!=] x) (hs : Finite s) : U \ s in 𝓝[!=] x
参数：hU : U in 𝓝[!=] x；hs : Finite s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `Set.compl_sdiff`：compl_sdiff : (t \ s)ᶜ = s union tᶜ
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `Set.Finite.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Spa
ce X] {s : Set X}, s.Finite → IsClosed s
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
In a T1Space, punctured neighborhoods are stable under removing finite sets of p
oints.
-/
theorem nhdsNE_of_nhdsNE_sdiff_finite {X : Type*} [TopologicalSpace X] [T1Space X] {x : X}
    {U s : Set X} (hU : U ∈ 𝓝[≠] x) (hs : Finite s) :
    U \ s ∈ 𝓝[≠] x := by
  rw [mem_nhdsWithin] at hU ⊢
  obtain ⟨t, ht, h₁ts, h₂ts⟩ := hU
  use t \ (s \ {x})
  constructor
  · rw [← isClosed_compl_iff, compl_sdiff]
    exact s.toFinite.sdiff.isClosed.union (isClosed_compl_iff.2 ht)
  · tauto_set

/-- In a T1Space, a set `s` is codiscreteWithin `U` iff it has locally finite complement within `U`.
More precisely: `s` is codiscreteWithin `U` iff every point `z ∈ U` has a punctured neighborhood
intersect `U \ s` in only finitely many points. -/
/-
**codiscreteWithin_iff_locallyFiniteComplementWithin** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：codiscreteWithin_iff_locallyFiniteComplementWithin [T1Space X] {s U : Set 
X} : s in codiscreteWithin U ↔ forall z in U, exists t in 𝓝 z, Set.Finite (t int
er (U \ s))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `codiscreteWithin_iff_locallyEmptyComplementWithin`：codiscreteWithin_iff_
locallyEmptyComplementWithin {s U : Set X} : s in codiscreteWithin U ↔ forall z 
in U, exists t in 𝓝[!=] z, t inter (U \…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `insert_mem_nhds_iff`：insert_mem_nhds_iff {a : α} {s : Set α} : insert a 
s in 𝓝 a ↔ s in 𝓝[!=] a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_insert_of_mem`：inter_insert_of_mem (h : a in s) : s inter inse
rt a t = insert a (s inter t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Set.instLawfulSingleton`：∀ {α : Type u_1}, LawfulSingleton α (Set α)
· 使用定理 `Set.inter_insert_of_notMem`：inter_insert_of_notMem (h : a ∉ s) : s inter
 insert a t = s inter t
· 使用定理 `nhdsNE_of_nhdsNE_sdiff_finite`：nhdsNE_of_nhdsNE_sdiff_finite {X : Type*}
 [TopologicalSpace X] [T1Space X] {x : X} {U s : Set X} (hU : U in 𝓝[!=] x) (hs 
: Finite s) : U \ s…
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用定理 `Set.sdiff_inter_self`：sdiff_inter_self {a b : Set α} : b \ a inter a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In a T1Space, a set `s` is codiscreteWithin `U` iff it has locally finite comple
ment within `U`.
More precisely: `s` is codiscreteWithin `U` iff every point `z ∈ U` has a punctu
red neighborhood
intersect `U \ s` in only finitely many points.
-/
theorem codiscreteWithin_iff_locallyFiniteComplementWithin [T1Space X] {s U : Set X} :
    s ∈ codiscreteWithin U ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ (U \ s)) := by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  constructor
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use insert z t, insert_mem_nhds_iff.mpr h₁t
    by_cases hz : z ∈ U \ s
    · rw [inter_comm, inter_insert_of_mem hz, inter_comm, h₂t]
      simp
    · rw [inter_comm, inter_insert_of_notMem hz, inter_comm, h₂t]
      simp
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use t \ (t ∩ (U \ s)), nhdsNE_of_nhdsNE_sdiff_finite (mem_nhdsWithin_of_mem_nhds h₁t) h₂t
    simp

/--
In a `T1Space`, every set is codiscrete within a subsingleton set.
-/
/-
**Set.Subsingleton.mem_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingle
ton`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X] {s t : Set X}, t.
Subsingleton → s ∈ Filter.codiscreteWithin t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `codiscreteWithin_iff_locallyEmptyComplementWithin`：codiscreteWithin_iff_
locallyEmptyComplementWithin {s U : Set X} : s in codiscreteWithin U ↔ forall z 
in U, exists t in 𝓝[!=] z, t inter (U \…
· 使用定理 `nhdsNE_of_nhdsNE_sdiff_finite`：nhdsNE_of_nhdsNE_sdiff_finite {X : Type*}
 [TopologicalSpace X] [T1Space X] {x : X} {U s : Set X} (hU : U in 𝓝[!=] x) (hs 
: Finite s) : U \ s…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
In a `T1Space`, every set is codiscrete within a subsingleton set.
-/
@[simp] theorem Set.Subsingleton.mem_codiscreteWithin [T1Space X] {s t : Set X}
    (h : Set.Subsingleton t) :
    s ∈ codiscreteWithin t := by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  intro z hz
  use univ \ t, nhdsNE_of_nhdsNE_sdiff_finite univ_mem h.finite, by aesop

/--
In a `T1Space`, complements of singleton sets are codiscrete within any set.
-/
@[simp]
/-
**compl_singleton_mem_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_singleton_mem_codiscreteWithin {X : Type*} [TopologicalSpace X] [T1S
pace X] {s : Set X} (x : X) : {x}ᶜ in codiscreteWithin s
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `codiscreteWithin_iff_locallyEmptyComplementWithin`：codiscreteWithin_iff_
locallyEmptyComplementWithin {s U : Set X} : s in codiscreteWithin U ↔ forall z 
in U, exists t in 𝓝[!=] z, t inter (U \…
· 使用定理 `nhdsNE_of_nhdsNE_sdiff_finite`：nhdsNE_of_nhdsNE_sdiff_finite {X : Type*}
 [TopologicalSpace X] [T1Space X] {x : X} {U s : Set X} (hU : U in 𝓝[!=] x) (hs 
: Finite s) : U \ s…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sdiff_compl`：sdiff_compl : x \ yᶜ = x ⊓ y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
In a `T1Space`, complements of singleton sets are codiscrete within any set.
-/
theorem compl_singleton_mem_codiscreteWithin {X : Type*} [TopologicalSpace X] [T1Space X]
    {s : Set X} (x : X) :
    {x}ᶜ ∈ codiscreteWithin s := by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  intro z hz
  use univ \ {x}
  exact ⟨nhdsNE_of_nhdsNE_sdiff_finite univ_mem Finite.of_subsingleton, by aesop⟩

/--
In a `T1Space`, complements of finite sets are codiscrete within any set.
-/
/-
**compl_finite_mem_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_finite_mem_codiscreteWithin {X : Type*} [TopologicalSpace X] [T1Spac
e X] {s t : Set X} (h : t.Finite) : tᶜ in codiscreteWithin s
参数：h : t.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
In a `T1Space`, complements of finite sets are codiscrete within any set.
-/
theorem compl_finite_mem_codiscreteWithin {X : Type*} [TopologicalSpace X] [T1Space X]
    {s t : Set X} (h : t.Finite) :
    tᶜ ∈ codiscreteWithin s := by
  apply h.induction_on (motive := fun t _ ↦ tᶜ ∈ codiscreteWithin s)
  · simp
  · intro τ t hτ h₁t h₂t
    have : (insert τ t)ᶜ = {τ}ᶜ ∩ tᶜ := by aesop
    simp_all

/-- In any topological space, the open sets with discrete complement form a filter,
defined as the supremum of all punctured neighborhoods.

See `Filter.mem_codiscrete'` for the equivalence. -/
/-
**Filter.codiscrete** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Filter.codiscrete (X : Type*) [TopologicalSpace X] : Filter X
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In any topological space, the open sets with discrete complement form a filter,
defined as the supremum of all punctured neighborhoods.

See `Filter.mem_codiscrete'` for the equivalence.
-/
def Filter.codiscrete (X : Type*) [TopologicalSpace X] : Filter X := codiscreteWithin Set.univ
/-
**mem_codiscrete** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_codiscrete {S : Set X} : S in codiscrete X ↔ forall x, Disjoint (𝓝[!=]
 x) (𝓟 Sᶜ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_codiscrete {S : Set X} :
    S ∈ codiscrete X ↔ ∀ x, Disjoint (𝓝[≠] x) (𝓟 Sᶜ) := by
  simp [codiscrete, mem_codiscreteWithin, compl_eq_univ_sdiff]
/-
**Disjoint.eventually_nhdsWithin_specializes** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Disjoint.eventually_nhdsWithin_specializes {p : X} {s : Set X} (hs : Disjo
int (𝓝[s] p) cofinite) : forallᶠ x in 𝓝[s] p, x ⤳ p
参数：hs : Disjoint (𝓝[s] p) cofinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.disjoint_cofinite_right`：disjoint_cofinite_right : Disjoint l cof
inite ↔ exists s in l, Set.Finite s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
lemma Disjoint.eventually_nhdsWithin_specializes
    {p : X} {s : Set X} (hs : Disjoint (𝓝[s] p) cofinite) :
    ∀ᶠ x in 𝓝[s] p, x ⤳ p := by
  obtain ⟨t, h₁t, h₂t⟩ := disjoint_cofinite_right.mp hs
  set S := {y ∈ t ∩ s | ¬(y ⤳ p)}
  have hS_nhds (y) (hy : y ∈ S) : (closure ({y} : Set X))ᶜ ∈ 𝓝 p :=
    isClosed_closure.isOpen_compl.mem_nhds <| by
      simpa [specializes_iff_mem_closure] using hy.2
  filter_upwards [h₁t, nhdsWithin_le_nhds ((biInter_mem <| h₂t.subset (by grind)).mpr hS_nhds),
    self_mem_nhdsWithin] with x hxt hxS
  contrapose
  refine fun hxp hxf ↦ mem_iInter₂.mp hxS x ⟨⟨hxt, hxf⟩, hxp⟩ ?_
  grind [subset_closure]
/-
**Disjoint.nhdsWithin_eq_of_cofinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Disjoint.nhdsWithin_eq_of_cofinite {p : X} {s : Set X} (hs : Disjoint (𝓝[s
] p) cofinite) : 𝓝[s] p = 𝓟 ({x | x ⤳ p} inter s)
参数：hs : Disjoint (𝓝[s] p) cofinite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Disjoint.eventually_nhdsWithin_specializes`：Disjoint.eventually_nhdsWith
in_specializes {p : X} {s : Set X} (hs : Disjoint (𝓝[s] p) cofinite) : forallᶠ x
 in 𝓝[s] p, x ⤳ p
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `Filter.principal_le_iff`：principal_le_iff {s : Set α} {f : Filter α} : 𝓟
 s <= f ↔ forall V in f, s subseteq V
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma Disjoint.nhdsWithin_eq_of_cofinite
    {p : X} {s : Set X} (hs : Disjoint (𝓝[s] p) cofinite) :
    𝓝[s] p = 𝓟 ({x | x ⤳ p} ∩ s) := by
  apply le_antisymm
  · simpa using ⟨hs.eventually_nhdsWithin_specializes, self_mem_nhdsWithin⟩
  · rw [← inf_principal, nhdsWithin]
    gcongr
    rw [Filter.principal_le_iff]
    exact fun s hs x hx ↦ mem_of_mem_nhds (hx hs)
/-
**mem_codiscrete_accPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_codiscrete_accPt {S : Set X} : S in codiscrete X ↔ forall x, ¬AccPt x 
(𝓟 Sᶜ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_codiscrete_accPt {S : Set X} :
    S ∈ codiscrete X ↔ ∀ x, ¬AccPt x (𝓟 Sᶜ) := by
  simp only [mem_codiscrete, disjoint_iff, AccPt, not_neBot]
/-
**mem_codiscrete'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_codiscrete' {S : Set X} : S in codiscrete X ↔ IsOpen S ∧ IsDiscrete Sᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_codiscrete`：mem_codiscrete {S : Set X} : S in codiscrete X ↔ forall 
x, Disjoint (𝓝[!=] x) (𝓟 Sᶜ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `isClosed_and_discrete_iff`：isClosed_and_discrete_iff {S : Set X} : IsClo
sed S ∧ IsDiscrete S ↔ forall x, Disjoint (𝓝[!=] x) (𝓟 S)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_codiscrete' {S : Set X} :
    S ∈ codiscrete X ↔ IsOpen S ∧ IsDiscrete Sᶜ := by
  rw [mem_codiscrete, ← isClosed_compl_iff, isClosed_and_discrete_iff]
/-
**compl_mem_codiscrete_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compl_mem_codiscrete_iff {S : Set X} : Sᶜ in codiscrete X ↔ IsClosed S ∧ I
sDiscrete S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_codiscrete`：mem_codiscrete {S : Set X} : S in codiscrete X ↔ forall 
x, Disjoint (𝓝[!=] x) (𝓟 Sᶜ)
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `isClosed_and_discrete_iff`：isClosed_and_discrete_iff {S : Set X} : IsClo
sed S ∧ IsDiscrete S ↔ forall x, Disjoint (𝓝[!=] x) (𝓟 S)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma compl_mem_codiscrete_iff {S : Set X} :
    Sᶜ ∈ codiscrete X ↔ IsClosed S ∧ IsDiscrete S := by
  rw [mem_codiscrete, compl_compl, isClosed_and_discrete_iff]
/-
**codiscreteWithin_le_codiscrete_inf_principal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：codiscreteWithin_le_codiscrete_inf_principal (s : Set X) : codiscreteWithi
n s <= codiscrete X ⊓ 𝓟 s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma codiscreteWithin_le_codiscrete_inf_principal (s : Set X) :
    codiscreteWithin s ≤ codiscrete X ⊓ 𝓟 s := by
  simp [codiscrete, codiscreteWithin_mono]
/-
**Topology.IsEmbedding.image_mem_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.image_mem_codiscreteWithin {f : X -> Y} (hf : IsEmbed
ding f) {s t : Set X} : f '' s in codiscreteWithin (f '' t) ↔ s in codiscreteWit
hin t
参数：hf : IsEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.mapClusterPt_iff`：mapClusterPt_iff (hf : IsInducing 
f) {x : X} {l : Filter X} : MapClusterPt (f x) l f ↔ ClusterPt x l
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Topology.IsEmbedding.image_mem_codiscreteWithin {f : X → Y} (hf : IsEmbedding f)
    {s t : Set X} : f '' s ∈ codiscreteWithin (f '' t) ↔ s ∈ codiscreteWithin t := by
  simp only [mem_codiscreteWithin_accPt, forall_mem_image, accPt_principal_iff_clusterPt,
    ← hf.mapClusterPt_iff, MapClusterPt, map_principal, image_sdiff hf.injective, image_singleton]
/-
**Topology.IsEmbedding.image_mem_codiscreteWithin_range** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Topology.IsEmbedding.image_mem_codiscreteWithin_range {f : X -> Y} (hf : I
sEmbedding f) {s : Set X} : f '' s in codiscreteWithin (range f) ↔ s in codiscre
te X
参数：hf : IsEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Topology.IsEmbedding.image_mem_codiscreteWithin`：Topology.IsEmbedding.im
age_mem_codiscreteWithin {f : X -> Y} (hf : IsEmbedding f) {s t : Set X} : f '' 
s in codiscreteWithin (f '' t) ↔ s in…
· 使用定理 `Filter.codiscrete.eq_1`：∀ (X : Type u_3) [inst : TopologicalSpace X], Fi
lter.codiscrete X = Filter.codiscreteWithin Set.univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Topology.IsEmbedding.image_mem_codiscreteWithin_range {f : X → Y} (hf : IsEmbedding f)
    {s : Set X} : f '' s ∈ codiscreteWithin (range f) ↔ s ∈ codiscrete X := by
  rw [← image_univ, hf.image_mem_codiscreteWithin, codiscrete]
/-
**mem_codiscrete_subtype_iff_mem_codiscreteWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_codiscrete_subtype_iff_mem_codiscreteWithin {S : Set X} {U : Set S} : 
U in codiscrete S ↔ (↑) '' U in codiscreteWithin S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsEmbedding.image_mem_codiscreteWithin_range`：Topology.IsEmbedd
ing.image_mem_codiscreteWithin_range {f : X -> Y} (hf : IsEmbedding f) {s : Set 
X} : f '' s in codiscreteWithin (range f) ↔…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_codiscrete_subtype_iff_mem_codiscreteWithin {S : Set X} {U : Set S} :
    U ∈ codiscrete S ↔ (↑) '' U ∈ codiscreteWithin S := by
  simp [← Topology.IsEmbedding.subtypeVal.image_mem_codiscreteWithin_range]

@[simp]
/-
**codiscreteWithin_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：codiscreteWithin_eq_bot_iff {S : Set X} : codiscreteWithin S = ⊥ ↔ IsDiscr
ete S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem codiscreteWithin_eq_bot_iff {S : Set X} : codiscreteWithin S = ⊥ ↔ IsDiscrete S := by
  simp [isDiscrete_iff_nhdsNE, codiscreteWithin, ← nhdsWithin_inter', Set.sdiff_eq, inter_comm]

section T1Space

variable [T1Space X]

/-
**codiscrete_le_cofinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：codiscrete_le_cofinite : codiscrete X <= cofinite
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用引理 `compl_mem_codiscrete_iff`：compl_mem_codiscrete_iff {S : Set X} : Sᶜ in c
odiscrete X ↔ IsClosed S ∧ IsDiscrete S
· 使用定理 `Set.Finite.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Spa
ce X] {s : Set X}, s.Finite → IsClosed s
· 使用引理 `Set.Finite.isDiscrete`：Set.Finite.isDiscrete [T1Space X] {s : Set X} (hs
 : s.Finite) : IsDiscrete s
-/
lemma codiscrete_le_cofinite : codiscrete X ≤ cofinite := by
  intro s hs
  rw [← compl_compl s, compl_mem_codiscrete_iff]
  exact ⟨hs.isClosed, hs.isDiscrete⟩
/-
**Set.Finite.compl_mem_codiscrete** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Finite.compl_mem_codiscrete {S : Set X} (hs : S.Finite) : Sᶜ in codisc
rete X
参数：hs : S.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `codiscrete_le_cofinite`：codiscrete_le_cofinite : codiscrete X <= cofinit
e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
lemma Set.Finite.compl_mem_codiscrete {S : Set X} (hs : S.Finite) : Sᶜ ∈ codiscrete X :=
  codiscrete_le_cofinite (by simpa)
/-
**Set.Infinite.of_accPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Infinite.of_accPt {S : Set X} {x : X} (h : AccPt x (𝓟 S)) : S.Infinite
参数：h : AccPt x (𝓟 S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Finite.compl_mem_codiscrete`：Set.Finite.compl_mem_codiscrete {S : Se
t X} (hs : S.Finite) : Sᶜ in codiscrete X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用引理 `mem_codiscrete_accPt`：mem_codiscrete_accPt {S : Set X} : S in codiscrete
 X ↔ forall x, ¬AccPt x (𝓟 Sᶜ)
-/
lemma Set.Infinite.of_accPt {S : Set X} {x : X} (h : AccPt x (𝓟 S)) : S.Infinite := by
  intro hs
  have := hs.compl_mem_codiscrete
  rw [mem_codiscrete_accPt, compl_compl] at this
  exact this _ h

end T1Space

namespace IsCompact

variable {K : Set X}

/-
**IsCompact.finite_sdiff_of_mem_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 `IsCo
mpact`。
形式化陈述：finite_sdiff_of_mem_codiscreteWithin (hK : IsCompact K) (hs : s in codiscr
eteWithin K) : (K \ s).Finite
参数：hK : IsCompact K；hs : s in codiscreteWithin K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.Infinite.exists_accPt_of_subset_isCompact`：Set.Infinite.exists_accPt
_of_subset_isCompact {K : Set X} (hs : s.Infinite) (hK : IsCompact K) (hsub : s 
subseteq K) : exists x in K, AccPt …
· 使用定理 `Set.sep_subset`：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x 
} subseteq s
· 使用引理 `mem_codiscreteWithin_accPt`：mem_codiscreteWithin_accPt {S T : Set X} : S
 in codiscreteWithin T ↔ forall x in T, ¬AccPt x (𝓟 (T \ S))
-/
theorem finite_sdiff_of_mem_codiscreteWithin (hK : IsCompact K) (hs : s ∈ codiscreteWithin K) :
    (K \ s).Finite := by
  rw [mem_codiscreteWithin_accPt] at hs
  contrapose! hs
  exact Set.Infinite.exists_accPt_of_subset_isCompact hs hK (sep_subset _ _)

@[deprecated (since := "2026-06-03")]
alias finite_diff_of_mem_codiscreteWithin := finite_sdiff_of_mem_codiscreteWithin
/-
**IsCompact.cofinite_inf_le_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 `IsCompac
t`。
形式化陈述：cofinite_inf_le_codiscreteWithin (hK : IsCompact K) : cofinite ⊓ 𝓟 K <= co
discreteWithin K
参数：hK : IsCompact K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCompact.finite_sdiff_of_mem_codiscreteWithin`：finite_sdiff_of_mem_codi
screteWithin (hK : IsCompact K) (hs : s in codiscreteWithin K) : (K \ s).Finite
-/
theorem cofinite_inf_le_codiscreteWithin (hK : IsCompact K) :
    cofinite ⊓ 𝓟 K ≤ codiscreteWithin K := by
  intro s hs
  simpa [mem_inf_principal, compl_ofPred] using! hK.finite_sdiff_of_mem_codiscreteWithin hs
/-
**IsCompact.codiscreteWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：codiscreteWithin_eq [T1Space X] (hK : IsCompact K) : codiscreteWithin K = 
cofinite ⊓ 𝓟 K
参数：hK : IsCompact K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用引理 `codiscrete_le_cofinite`：codiscrete_le_cofinite : codiscrete X <= cofinit
e
· 使用引理 `codiscreteWithin_le_codiscrete_inf_principal`：codiscreteWithin_le_codisc
rete_inf_principal (s : Set X) : codiscreteWithin s <= codiscrete X ⊓ 𝓟 s
· 使用定理 `IsCompact.cofinite_inf_le_codiscreteWithin`：cofinite_inf_le_codiscreteWi
thin (hK : IsCompact K) : cofinite ⊓ 𝓟 K <= codiscreteWithin K
-/
theorem codiscreteWithin_eq [T1Space X] (hK : IsCompact K) :
    codiscreteWithin K = cofinite ⊓ 𝓟 K := by
  refine le_antisymm ?_ hK.cofinite_inf_le_codiscreteWithin
  grw [← codiscrete_le_cofinite]
  exact codiscreteWithin_le_codiscrete_inf_principal K

end IsCompact

/-
**cofinite_le_codiscrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cofinite_le_codiscrete [CompactSpace X] : cofinite <= codiscrete X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsCompact.cofinite_inf_le_codiscreteWithin`：cofinite_inf_le_codiscreteWi
thin (hK : IsCompact K) : cofinite ⊓ 𝓟 K <= codiscreteWithin K
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
-/
theorem cofinite_le_codiscrete [CompactSpace X] : cofinite ≤ codiscrete X := by
  simpa using! isCompact_univ.cofinite_inf_le_codiscreteWithin
/-
**codiscrete_eq_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：codiscrete_eq_cofinite [T1Space X] [CompactSpace X] : codiscrete X = cofin
ite
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsCompact.codiscreteWithin_eq`：codiscreteWithin_eq [T1Space X] (hK : IsC
ompact K) : codiscreteWithin K = cofinite ⊓ 𝓟 K
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
-/
theorem codiscrete_eq_cofinite [T1Space X] [CompactSpace X] : codiscrete X = cofinite := by
  simpa using! isCompact_univ.codiscreteWithin_eq

end codiscrete_filter

/-! ### Finite union of discrete closed sets -/

section discrete_union

/-- The union of finitely many discrete closed subsets is discrete. -/
/-
**IsDiscrete.iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDiscrete.iUnion {ι : Sort*} [Finite ι] {s : ι -> Set X} (hs : forall i, 
IsDiscrete (s i)) (hsc : forall i, IsClosed (s i)) : IsDiscrete (⋃ i, s i)
参数：hs : forall i, IsDiscrete (s i)；hsc : forall i, IsClosed (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `compl_mem_codiscrete_iff`：compl_mem_codiscrete_iff {S : Set X} : Sᶜ in c
odiscrete X ↔ IsClosed S ∧ IsDiscrete S

--- 原说明 ---
The union of finitely many discrete closed subsets is discrete.
-/
theorem IsDiscrete.iUnion {ι : Sort*} [Finite ι] {s : ι → Set X} (hs : ∀ i, IsDiscrete (s i))
    (hsc : ∀ i, IsClosed (s i)) : IsDiscrete (⋃ i, s i) := by
  suffices (⋃ i, s i)ᶜ ∈ codiscrete X from (compl_mem_codiscrete_iff.mp this).2
  simp [compl_mem_codiscrete_iff, *]

/-- The union of two discrete closed subsets is discrete. -/
/-
**IsDiscrete.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDiscrete.union {s t : Set X} (hs : IsDiscrete s) (ht : IsDiscrete t) (hs
c : IsClosed s) (ht : IsClosed t) : IsDiscrete (s union t)
参数：hs : IsDiscrete s；ht : IsDiscrete t；hsc : IsClosed s；ht : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `IsDiscrete.iUnion`：IsDiscrete.iUnion {ι : Sort*} [Finite ι] {s : ι -> Se
t X} (hs : forall i, IsDiscrete (s i)) (hsc : forall i, IsClosed (s i)) : IsDisc
rete (⋃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The union of two discrete closed subsets is discrete.
-/
theorem IsDiscrete.union {s t : Set X} (hs : IsDiscrete s) (ht : IsDiscrete t)
    (hsc : IsClosed s) (ht : IsClosed t) : IsDiscrete (s ∪ t) := by
  rw [union_eq_iUnion]
  exact .iUnion (by simp [*]) (by simp [*])

/-- The union of finitely many discrete closed subsets is discrete. -/
/-
**IsDiscrete.biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDiscrete.biUnion {ι : Type*} {I : Set ι} {s : ι -> Set X} (hI : I.Finite
) (hs : forall i in I, IsDiscrete (s i)) (hsc : forall i in I, IsClosed (s i)) :
 IsDiscrete (⋃ i in I, s i)
参数：hI : I.Finite；hs : forall i in I, IsDiscrete (s i)；hsc : forall i in I, IsClo
sed (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `IsDiscrete.iUnion`：IsDiscrete.iUnion {ι : Sort*} [Finite ι] {s : ι -> Se
t X} (hs : forall i, IsDiscrete (s i)) (hsc : forall i, IsClosed (s i)) : IsDisc
rete (⋃…

--- 原说明 ---
The union of finitely many discrete closed subsets is discrete.
-/
theorem IsDiscrete.biUnion {ι : Type*} {I : Set ι} {s : ι → Set X} (hI : I.Finite)
    (hs : ∀ i ∈ I, IsDiscrete (s i)) (hsc : ∀ i ∈ I, IsClosed (s i)) :
    IsDiscrete (⋃ i ∈ I, s i) := by
  have := hI.to_subtype
  simp only [biUnion_eq_iUnion, Subtype.forall'] at *
  exact .iUnion hs hsc

/-- The union of finitely many discrete closed subsets is discrete. -/
/-
**IsDiscrete.biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDiscrete.biUnion_finset {ι : Type*} {I : Finset ι} {s : ι -> Set X} (hs 
: forall i in I, IsDiscrete (s i)) (hsc : forall i in I, IsClosed (s i)) : IsDis
crete (⋃ i in I, s i)
参数：hs : forall i in I, IsDiscrete (s i)；hsc : forall i in I, IsClosed (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscrete.biUnion`：IsDiscrete.biUnion {ι : Type*} {I : Set ι} {s : ι ->
 Set X} (hI : I.Finite) (hs : forall i in I, IsDiscrete (s i)) (hsc : forall i i
n I, IsC…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite

--- 原说明 ---
The union of finitely many discrete closed subsets is discrete.
-/
theorem IsDiscrete.biUnion_finset {ι : Type*} {I : Finset ι} {s : ι → Set X}
    (hs : ∀ i ∈ I, IsDiscrete (s i)) (hsc : ∀ i ∈ I, IsClosed (s i)) :
    IsDiscrete (⋃ i ∈ I, s i) :=
  .biUnion I.finite_toSet hs hsc

/-- The union of finitely many discrete closed subsets is discrete. -/
@[deprecated IsDiscrete.union (since := "2026-05-13")]
/-
**discreteTopology_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_union {S T : Set X} (hs : DiscreteTopology S) (ht : Discr
eteTopology T) (hs' : IsClosed S) (ht' : IsClosed T) : DiscreteTopology ↑(S unio
n T)
参数：hs : DiscreteTopology S；ht : DiscreteTopology T；hs' : IsClosed S；ht' : IsClos
ed T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isDiscrete_iff_discreteTopology`：isDiscrete_iff_discreteTopology : IsDis
crete s ↔ DiscreteTopology s
· 使用定理 `IsDiscrete.union`：IsDiscrete.union {s t : Set X} (hs : IsDiscrete s) (ht
 : IsDiscrete t) (hsc : IsClosed s) (ht : IsClosed t) : IsDiscrete (s union t)

--- 原说明 ---
The union of finitely many discrete closed subsets is discrete.
-/
theorem discreteTopology_union {S T : Set X} (hs : DiscreteTopology S) (ht : DiscreteTopology T)
    (hs' : IsClosed S) (ht' : IsClosed T) : DiscreteTopology ↑(S ∪ T) := by
  rw [← isDiscrete_iff_discreteTopology] at *
  exact hs.union ht hs' ht'

/-- The union of finitely many discrete closed subsets is discrete. -/
@[deprecated IsDiscrete.biUnion_finset (since := "2026-05-13")]
/-
**discreteTopology_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_biUnion_finset {ι : Type*} {I : Finset ι} {s : ι -> Set X
} (hs : forall i in I, DiscreteTopology (s i)) (hs' : forall i in I, IsClosed (s
 i)) : DiscreteTopology (⋃ i in I, s i)
参数：hs : forall i in I, DiscreteTopology (s i)；hs' : forall i in I, IsClosed (s i
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscrete.biUnion_finset`：IsDiscrete.biUnion_finset {ι : Type*} {I : Fi
nset ι} {s : ι -> Set X} (hs : forall i in I, IsDiscrete (s i)) (hsc : forall i 
in I, IsClosed …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
The union of finitely many discrete closed subsets is discrete.
-/
theorem discreteTopology_biUnion_finset {ι : Type*} {I : Finset ι} {s : ι → Set X}
    (hs : ∀ i ∈ I, DiscreteTopology (s i)) (hs' : ∀ i ∈ I, IsClosed (s i)) :
    DiscreteTopology (⋃ i ∈ I, s i) := by
  simp only [← isDiscrete_iff_discreteTopology] at *
  exact .biUnion_finset hs hs'

/-- The union of finitely many discrete closed subsets is discrete. -/
@[deprecated IsDiscrete.iUnion (since := "2026-05-13")]
/-
**discreteTopology_iUnion_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_iUnion_finite {ι : Type*} [Finite ι] {s : ι -> Set X} (hs
 : forall i, DiscreteTopology (s i)) (hs' : forall i, IsClosed (s i)) : Discrete
Topology (⋃ i, s i)
参数：hs : forall i, DiscreteTopology (s i)；hs' : forall i, IsClosed (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscrete.iUnion`：IsDiscrete.iUnion {ι : Sort*} [Finite ι] {s : ι -> Se
t X} (hs : forall i, IsDiscrete (s i)) (hsc : forall i, IsClosed (s i)) : IsDisc
rete (⋃…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
The union of finitely many discrete closed subsets is discrete.
-/
theorem discreteTopology_iUnion_finite {ι : Type*} [Finite ι] {s : ι → Set X}
    (hs : ∀ i, DiscreteTopology (s i)) (hs' : ∀ i, IsClosed (s i)) :
    DiscreteTopology (⋃ i, s i) := by
  simp only [← isDiscrete_iff_discreteTopology] at *
  exact .iUnion hs hs'

end discrete_union

