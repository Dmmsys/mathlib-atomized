/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SetFamily.Compression.Down
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Shattering families

This file defines the shattering property and VC-dimension of set families.

## Main declarations

* `Finset.Shatters`: The shattering property.
* `Finset.shatterer`: The set family of sets shattered by a set family.
* `Finset.vcDim`: The Vapnik-Chervonenkis dimension.

## TODO

* Order-shattering
* Strong shattering
-/

@[expose] public section

open scoped FinsetFamily

namespace Finset
variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α}

/-- A set family `𝒜` shatters a set `s` if all subsets of `s` can be obtained as the intersection
of `s` and some element of the set family, and we denote this `𝒜.Shatters s`. We also say that `s`
is *traced* by `𝒜`. -/
/-
**Finset.Shatters** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：Shatters (𝒜 : Finset (Finset α)) (s : Finset α) : Prop
参数：𝒜 : Finset (Finset α)；s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set family `𝒜` shatters a set `s` if all subsets of `s` can be obtained as the
 intersection
of `s` and some element of the set family, and we denote this `𝒜.Shatters s`. We
 also say that `s`
is *traced* by `𝒜`.
-/
def Shatters (𝒜 : Finset (Finset α)) (s : Finset α) : Prop := ∀ ⦃t⦄, t ⊆ s → ∃ u ∈ 𝒜, s ∩ u = t
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidablePred 𝒜.Shatters := fun _s ↦ decidableForallOfDecidableSubsets
/-
**Finset.Shatters.exists_inter_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Sh
atters`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finse
t α} {a : α},   𝒜.Shatters s → a ∈ s → ∃ t ∈ 𝒜, s ∩ t = {a}
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
-/
lemma Shatters.exists_inter_eq_singleton (hs : Shatters 𝒜 s) (ha : a ∈ s) : ∃ t ∈ 𝒜, s ∩ t = {a} :=
  hs <| singleton_subset_iff.2 ha
/-
**Finset.Shatters.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Shatters`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s : Fin
set α}, 𝒜 ⊆ ℬ → 𝒜.Shatters s → ℬ.Shatters s
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Shatters.mono_left (h : 𝒜 ⊆ ℬ) (h𝒜 : 𝒜.Shatters s) : ℬ.Shatters s :=
  fun _t ht ↦ let ⟨u, hu, hut⟩ := h𝒜 ht; ⟨u, h hu, hut⟩
/-
**Finset.Shatters.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Shatters`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {s t : Fin
set α}, t ⊆ s → 𝒜.Shatters s → 𝒜.Shatters t
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_congr_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α}, b
 ⊓ c ≤ a → a ⊓ c ≤ b → a ⊓ c = b ⊓ c
· 使用定理 `inf_le_of_left_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α},
 a ≤ c → a ⊓ b ≤ c
-/
lemma Shatters.mono_right (h : t ⊆ s) (hs : 𝒜.Shatters s) : 𝒜.Shatters t := fun u hu ↦ by
  obtain ⟨v, hv, rfl⟩ := hs (hu.trans h); exact ⟨v, hv, inf_congr_right hu <| inf_le_of_left_le h⟩
/-
**Finset.Shatters.exists_superset** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Shatters`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finse
t α}, 𝒜.Shatters s → ∃ t ∈ 𝒜, s ⊆ t
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.inter_eq_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fin
set α}, s ∩ t = s ↔ s ⊆ t
-/
lemma Shatters.exists_superset (h : 𝒜.Shatters s) : ∃ t ∈ 𝒜, s ⊆ t :=
  let ⟨t, ht, hst⟩ := h Subset.rfl; ⟨t, ht, inter_eq_left.1 hst⟩
/-
**Finset.shatters_of_forall_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：shatters_of_forall_subset (h : forall t, t subseteq s -> t in 𝒜) : 𝒜.Shatt
ers s
参数：h : forall t, t subseteq s -> t in 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.inter_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fi
nset α}, t ∩ s = s ↔ s ⊆ t
-/
lemma shatters_of_forall_subset (h : ∀ t, t ⊆ s → t ∈ 𝒜) : 𝒜.Shatters s :=
  fun t ht ↦ ⟨t, h _ ht, inter_eq_right.2 ht⟩
/-
**Finset.Shatters.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Shatters`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finse
t α}, 𝒜.Shatters s → 𝒜.Nonempty
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
protected lemma Shatters.nonempty (h : 𝒜.Shatters s) : 𝒜.Nonempty :=
  let ⟨t, ht, _⟩ := h Subset.rfl; ⟨t, ht⟩
/-
**Finset.shatters_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)}, 𝒜.Shatter
s ∅ ↔ 𝒜.Nonempty
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Shatters.nonempty`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : F
inset (Finset α)} {s : Finset α}, 𝒜.Shatters s → 𝒜.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.empty_inter`：empty_inter (s : Finset α) : ∅ inter s = ∅
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.subset_empty`：∀ {α : Type u_1} {s : Finset α}, s ⊆ ∅ ↔ s = ∅
-/
@[simp] lemma shatters_empty : 𝒜.Shatters ∅ ↔ 𝒜.Nonempty :=
  ⟨Shatters.nonempty, fun ⟨s, hs⟩ t ht ↦ ⟨s, hs, by rwa [empty_inter, eq_comm, ← subset_empty]⟩⟩
/-
**Finset.Shatters.subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Shatters`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {s t : Fin
set α},   𝒜.Shatters s → (t ⊆ s ↔ ∃ u ∈ 𝒜, s ∩ u = t)
参数：Finset α；t ⊆ s ↔ ∃ u ∈ 𝒜, s ∩ u = t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
-/
protected lemma Shatters.subset_iff (h : 𝒜.Shatters s) : t ⊆ s ↔ ∃ u ∈ 𝒜, s ∩ u = t :=
  ⟨fun ht ↦ h ht, by rintro ⟨u, _, rfl⟩; exact inter_subset_left⟩
/-
**Finset.shatters_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：shatters_iff : 𝒜.Shatters s ↔ 𝒜.image (fun t => s inter t) = s.powerset
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Finset.Shatters.subset_iff`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 :
 Finset (Finset α)} {s t : Finset α},   𝒜.Shatters s → (t ⊆ s ↔ ∃ u ∈ 𝒜, s ∩ u =
 t)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma shatters_iff : 𝒜.Shatters s ↔ 𝒜.image (fun t ↦ s ∩ t) = s.powerset :=
  ⟨fun h ↦ by ext t; rw [mem_image, mem_powerset, h.subset_iff],
    fun h t ht ↦ by rwa [← mem_powerset, ← h, mem_image] at ht⟩
/-
**Finset.univ_shatters** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：univ_shatters [Fintype α] : univ.Shatters s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.shatters_of_forall_subset`：shatters_of_forall_subset (h : forall 
t, t subseteq s -> t in 𝒜) : 𝒜.Shatters s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
lemma univ_shatters [Fintype α] : univ.Shatters s :=
  shatters_of_forall_subset fun _ _ ↦ mem_univ _
/-
**Finset.shatters_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} [inst_1 : 
Fintype α],   𝒜.Shatters Finset.univ ↔ 𝒜 = Finset.univ
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.shatters_iff`：shatters_iff : 𝒜.Shatters s ↔ 𝒜.image (fun t => s i
nter t) = s.powerset
· 使用定理 `Finset.powerset_univ`：∀ {α : Type u_1} [inst : Fintype α], Finset.univ.p
owerset = Finset.univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.image_id'`：image_id' [DecidableEq α] : (s.image fun x => x) = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma shatters_univ [Fintype α] : 𝒜.Shatters univ ↔ 𝒜 = univ := by
  rw [shatters_iff, powerset_univ]; simp_rw [univ_inter, image_id']

/-- The set family of sets that are shattered by `𝒜`. -/
/-
**Finset.shatterer** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：shatterer (𝒜 : Finset (Finset α)) : Finset (Finset α)
参数：𝒜 : Finset (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set family of sets that are shattered by `𝒜`.
-/
def shatterer (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  {s ∈ 𝒜.biUnion powerset | 𝒜.Shatters s}
/-
**Finset.mem_shatterer** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finse
t α}, s ∈ 𝒜.shatterer ↔ 𝒜.Shatters s
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.Shatters.exists_superset`：∀ {α : Type u_1} [inst : DecidableEq α]
 {𝒜 : Finset (Finset α)} {s : Finset α}, 𝒜.Shatters s → ∃ t ∈ 𝒜, s ⊆ t
-/
@[simp] lemma mem_shatterer : s ∈ 𝒜.shatterer ↔ 𝒜.Shatters s := by
  refine mem_filter.trans <| and_iff_right_of_imp fun h ↦ ?_
  simp_rw [mem_biUnion, mem_powerset]
  exact h.exists_superset
/-
**Finset.shatterer_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 ℬ : Finset (Finset α)}, 𝒜 ⊆ ℬ →
 𝒜.shatterer ⊆ ℬ.shatterer
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.Shatters.mono_left`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 ℬ 
: Finset (Finset α)} {s : Finset α}, 𝒜 ⊆ ℬ → 𝒜.Shatters s → ℬ.Shatters s
-/
@[gcongr] lemma shatterer_mono (h : 𝒜 ⊆ ℬ) : 𝒜.shatterer ⊆ ℬ.shatterer :=
  fun _ ↦ by simpa using Shatters.mono_left h
/-
**Finset.subset_shatterer** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_shatterer (h : IsLowerSet (𝒜 : Set (Finset α))) : 𝒜 subseteq 𝒜.shat
terer
参数：h : IsLowerSet (𝒜 : Set (Finset α))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_shatterer`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finse
t (Finset α)} {s : Finset α}, s ∈ 𝒜.shatterer ↔ 𝒜.Shatters s
· 使用定理 `Finset.inter_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fi
nset α}, t ∩ s = s ↔ s ⊆ t
-/
lemma subset_shatterer (h : IsLowerSet (𝒜 : Set (Finset α))) : 𝒜 ⊆ 𝒜.shatterer :=
  fun _s hs ↦ mem_shatterer.2 fun t ht ↦ ⟨t, h ht hs, inter_eq_right.2 ht⟩
/-
**Finset.isLowerSet_shatterer** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (𝒜 : Finset (Finset α)), IsLowerSe
t ↑𝒜.shatterer
参数：𝒜 : Finset (Finset α)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.Shatters.mono_right`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 :
 Finset (Finset α)} {s t : Finset α}, t ⊆ s → 𝒜.Shatters s → 𝒜.Shatters t
-/
@[simp] lemma isLowerSet_shatterer (𝒜 : Finset (Finset α)) :
    IsLowerSet (𝒜.shatterer : Set (Finset α)) := fun s t ↦ by simpa using Shatters.mono_right
/-
**Finset.shatterer_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)}, 𝒜.shatter
er = 𝒜 ↔ IsLowerSet ↑𝒜
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.isLowerSet_shatterer`：∀ {α : Type u_1} [inst : DecidableEq α] (𝒜 
: Finset (Finset α)), IsLowerSet ↑𝒜.shatterer
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用定理 `Finset.Shatters.exists_superset`：∀ {α : Type u_1} [inst : DecidableEq α]
 {𝒜 : Finset (Finset α)} {s : Finset α}, 𝒜.Shatters s → ∃ t ∈ 𝒜, s ⊆ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_shatterer`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finse
t (Finset α)} {s : Finset α}, s ∈ 𝒜.shatterer ↔ 𝒜.Shatters s
· 使用引理 `Finset.subset_shatterer`：subset_shatterer (h : IsLowerSet (𝒜 : Set (Fins
et α))) : 𝒜 subseteq 𝒜.shatterer
-/
@[simp] lemma shatterer_eq : 𝒜.shatterer = 𝒜 ↔ IsLowerSet (𝒜 : Set (Finset α)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Subset.antisymm (fun s hs ↦ ?_) <| subset_shatterer h⟩
  · rw [← h]
    exact isLowerSet_shatterer _
  · obtain ⟨t, ht, hst⟩ := (mem_shatterer.1 hs).exists_superset
    exact h hst ht
/-
**Finset.shatterer_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)}, 𝒜.shatter
er.shatterer = 𝒜.shatterer
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma shatterer_idem : 𝒜.shatterer.shatterer = 𝒜.shatterer := by simp
/-
**Finset.shatters_shatterer** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finse
t α}, 𝒜.shatterer.Shatters s ↔ 𝒜.Shatters s
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.shatterer_idem`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Fins
et (Finset α)}, 𝒜.shatterer.shatterer = 𝒜.shatterer
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma shatters_shatterer : 𝒜.shatterer.Shatters s ↔ 𝒜.Shatters s := by
  simp_rw [← mem_shatterer, shatterer_idem]

protected alias ⟨_, Shatters.shatterer⟩ := shatters_shatterer
/-
**Finset.aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux (h : ∀ t ∈ 𝒜, a ∉ t) (ht : 𝒜.Shatters t) : a ∉ t := by
  obtain ⟨u, hu, htu⟩ := ht.exists_superset; exact notMem_mono htu <| h u hu

/-- Pajor's variant of the **Sauer-Shelah lemma**. -/
/-
**Finset.card_le_card_shatterer** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_le_card_shatterer (𝒜 : Finset (Finset α)) : #𝒜 <= #𝒜.shatterer
参数：𝒜 : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.memberFamily_induction_on`：memberFamily_induction_on {p : Finset 
(Finset α) -> Prop} (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {
∅}) (subfamily : foral…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.Shatter.0.Finset.aux`：∀ {α : Ty
pe u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {t : Finset α} {a : α},  
 (∀ t ∈ 𝒜, a ∉ t) → 𝒜.Shatters t → a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用引理 `Finset.insert_erase_invOn`：insert_erase_invOn : Set.InvOn (insert a) (fu
n s => s.erase a) {s : Finset α | a in s} {s : Finset α | a ∉ s}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_memberSubfamily_add_card_nonMemberSubfamily`：card_memberSubf
amily_add_card_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) : #(𝒜.memberSu
bfamily a) + #(𝒜.nonMemberSubfamily a) = #𝒜
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.add_le_add`：∀ {a b c d : ℕ}, a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Finset.card_union_add_card_inter`：card_union_add_card_inter (s t : Finse
t α) : #(s union t) + #(s inter t) = #s + #t
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Finset.mem_memberSubfamily`：mem_memberSubfamily : s in 𝒜.memberSubfamily
 a ↔ insert a s in 𝒜 ∧ a ∉ s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_nonMemberSubfamily`：mem_nonMemberSubfamily : s in 𝒜.nonMember
Subfamily a ↔ s in 𝒜 ∧ a ∉ s
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Pajor's variant of the **Sauer-Shelah lemma**.
-/
lemma card_le_card_shatterer (𝒜 : Finset (Finset α)) : #𝒜 ≤ #𝒜.shatterer := by
  refine memberFamily_induction_on 𝒜 ?_ ?_ ?_
  · simp
  · rfl
  intro a 𝒜 ih₀ ih₁
  set ℬ : Finset (Finset α) :=
    ((memberSubfamily a 𝒜).shatterer ∩ (nonMemberSubfamily a 𝒜).shatterer).image (insert a)
  have hℬ : #ℬ = #((memberSubfamily a 𝒜).shatterer ∩ (nonMemberSubfamily a 𝒜).shatterer) := by
    refine card_image_of_injOn <| insert_erase_invOn.2.injOn.mono ?_
    simp only [coe_inter, Set.subset_def, Set.mem_inter_iff, mem_coe, Set.mem_ofPred_eq, and_imp,
      mem_shatterer]
    exact fun s _ ↦ aux (fun t ht ↦ (mem_filter.1 ht).2)
  rw [← card_memberSubfamily_add_card_nonMemberSubfamily a]
  refine (Nat.add_le_add ih₁ ih₀).trans ?_
  rw [← card_union_add_card_inter, ← hℬ, ← card_union_of_disjoint]
  swap
  · simp only [ℬ, disjoint_left, mem_union, mem_shatterer, mem_image, not_exists, not_and]
    rintro _ (hs | hs) s - rfl
    · exact aux (fun t ht ↦ (mem_memberSubfamily.1 ht).2) hs <| mem_insert_self _ _
    · exact aux (fun t ht ↦ (mem_nonMemberSubfamily.1 ht).2) hs <| mem_insert_self _ _
  refine card_mono <| union_subset (union_subset ?_ <| shatterer_mono <| filter_subset _ _) ?_
  · simp only [subset_iff, mem_shatterer]
    rintro s hs t ht
    obtain ⟨u, hu, rfl⟩ := hs ht
    rw [mem_memberSubfamily] at hu
    refine ⟨insert a u, hu.1, inter_insert_of_notMem fun ha ↦ ?_⟩
    obtain ⟨v, hv, hsv⟩ := hs.exists_inter_eq_singleton ha
    rw [mem_memberSubfamily] at hv
    rw [← singleton_subset_iff (a := a), ← hsv] at hv
    exact hv.2 inter_subset_right
  · refine forall_mem_image.2 fun s hs ↦ mem_shatterer.2 fun t ht ↦ ?_
    simp only [mem_inter, mem_shatterer] at hs
    rw [subset_insert_iff] at ht
    by_cases ha : a ∈ t
    · obtain ⟨u, hu, hsu⟩ := hs.1 ht
      rw [mem_memberSubfamily] at hu
      refine ⟨_, hu.1, ?_⟩
      rw [← insert_inter_distrib, hsu, insert_erase ha]
    · obtain ⟨u, hu, hsu⟩ := hs.2 ht
      rw [mem_nonMemberSubfamily] at hu
      refine ⟨_, hu.1, ?_⟩
      rwa [insert_inter_of_notMem hu.2, hsu, erase_eq_self]
/-
**Finset.Shatters.of_compression** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Shatters`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finse
t α} {a : α},   (Down.compression a 𝒜).Shatters s → 𝒜.Shatters s
参数：Finset α；Down.compression a 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Down.mem_compression`：mem_compression : s in 𝓓 a 𝒜 ↔ s in 𝒜 ∧ s.erase a 
in 𝒜 ∨ s ∉ 𝒜 ∧ insert a s in 𝒜
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : 
insert a s subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.inter_erase`：inter_erase (a : α) (s t : Finset α) : s inter t.era
se a = (s inter t).erase a
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.insert_eq_self`：insert_eq_self : insert a s = s ↔ a in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.inter_insert_of_notMem`：inter_insert_of_notMem {s₁ s₂ : Finset α}
 {a : α} (h : a ∉ s₁) : s₁ inter insert a s₂ = s₁ inter s₂
-/
lemma Shatters.of_compression (hs : (𝓓 a 𝒜).Shatters s) : 𝒜.Shatters s := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := hs ht
  rw [Down.mem_compression] at hu
  obtain hu | hu := hu
  · exact ⟨u, hu.1, rfl⟩
  by_cases ha : a ∈ s
  · obtain ⟨v, hv, hsv⟩ := hs <| insert_subset ha ht
    rw [Down.mem_compression] at hv
    obtain hv | hv := hv
    · refine ⟨erase v a, hv.2, ?_⟩
      rw [inter_erase, hsv, erase_insert]
      rintro ha
      rw [insert_eq_self.2 (mem_inter.1 ha).2] at hu
      exact hu.1 hu.2
    rw [insert_eq_self.2 <| inter_subset_right (s₁ := s) ?_] at hv
    cases hv.1 hv.2
    rw [hsv]
    exact mem_insert_self _ _
  · refine ⟨insert a u, hu.2, ?_⟩
    rw [inter_insert_of_notMem ha]
/-
**Finset.shatterer_compress_subset_shatterer** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：shatterer_compress_subset_shatterer (a : α) (𝒜 : Finset (Finset α)) : (𝓓 a
 𝒜).shatterer subseteq 𝒜.shatterer
参数：a : α；𝒜 : Finset (Finset α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.Shatters.of_compression`：∀ {α : Type u_1} [inst : DecidableEq α] 
{𝒜 : Finset (Finset α)} {s : Finset α} {a : α},   (Down.compression a 𝒜).Shatter
s s → 𝒜.Shatters s
-/
lemma shatterer_compress_subset_shatterer (a : α) (𝒜 : Finset (Finset α)) :
    (𝓓 a 𝒜).shatterer ⊆ 𝒜.shatterer := by
  simp only [subset_iff, mem_shatterer]; exact fun s hs ↦ hs.of_compression

/-! ### Vapnik-Chervonenkis dimension -/

/-- The Vapnik-Chervonenkis dimension of a set family is the maximal size of a set it shatters. -/
/-
**Finset.vcDim** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：vcDim (𝒜 : Finset (Finset α)) : Nat
参数：𝒜 : Finset (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Vapnik-Chervonenkis dimension of a set family is the maximal size of a set i
t shatters.
-/
def vcDim (𝒜 : Finset (Finset α)) : ℕ := 𝒜.shatterer.sup card
/-
**Finset.vcDim_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 ℬ : Finset (Finset α)}, 𝒜 ⊆ ℬ →
 𝒜.vcDim ≤ ℬ.vcDim
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `Finset.shatterer_mono`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 ℬ : Fi
nset (Finset α)}, 𝒜 ⊆ ℬ → 𝒜.shatterer ⊆ ℬ.shatterer
-/
@[gcongr] lemma vcDim_mono (h𝒜ℬ : 𝒜 ⊆ ℬ) : 𝒜.vcDim ≤ ℬ.vcDim := by unfold vcDim; gcongr
/-
**Finset.Shatters.card_le_vcDim** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Shatters`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finse
t α}, 𝒜.Shatters s → s.card ≤ 𝒜.vcDim
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_shatterer`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finse
t (Finset α)} {s : Finset α}, s ∈ 𝒜.shatterer ↔ 𝒜.Shatters s
-/
lemma Shatters.card_le_vcDim (hs : 𝒜.Shatters s) : #s ≤ 𝒜.vcDim := le_sup <| mem_shatterer.2 hs

/-- Down-compressing decreases the VC-dimension. -/
/-
**Finset.vcDim_compress_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：vcDim_compress_le (a : α) (𝒜 : Finset (Finset α)) : (𝓓 a 𝒜).vcDim <= 𝒜.vcD
im
参数：a : α；𝒜 : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用引理 `Finset.shatterer_compress_subset_shatterer`：shatterer_compress_subset_sh
atterer (a : α) (𝒜 : Finset (Finset α)) : (𝓓 a 𝒜).shatterer subseteq 𝒜.shatterer

--- 原说明 ---
Down-compressing decreases the VC-dimension.
-/
lemma vcDim_compress_le (a : α) (𝒜 : Finset (Finset α)) : (𝓓 a 𝒜).vcDim ≤ 𝒜.vcDim :=
  sup_mono <| shatterer_compress_subset_shatterer _ _

/-- The **Sauer-Shelah lemma**. -/
/-
**Finset.card_shatterer_le_sum_vcDim** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_shatterer_le_sum_vcDim [Fintype α] : #𝒜.shatterer <= ∑ k in Iic 𝒜.vcD
im, (Fintype.card α).choose k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Finset.Shatters.card_le_vcDim`：∀ {α : Type u_1} [inst : DecidableEq α] {
𝒜 : Finset (Finset α)} {s : Finset α}, 𝒜.Shatters s → s.card ≤ 𝒜.vcDim
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_shatterer`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finse
t (Finset α)} {s : Finset α}, s ∈ 𝒜.shatterer ↔ 𝒜.Shatters s
· 使用引理 `Finset.mem_powersetCard_univ`：mem_powersetCard_univ : s in powersetCard 
k (univ : Finset α) ↔ #s = k
· 使用定理 `Finset.card_biUnion_le`：card_biUnion_le [DecidableEq M] {s : Finset ι} {
t : ι -> Finset M} : #(s.biUnion t) <= ∑ a in s, #(t a)

--- 原说明 ---
The **Sauer-Shelah lemma**.
-/
lemma card_shatterer_le_sum_vcDim [Fintype α] :
    #𝒜.shatterer ≤ ∑ k ∈ Iic 𝒜.vcDim, (Fintype.card α).choose k := by
  simp_rw [← card_univ, ← card_powersetCard]
  refine (card_le_card fun s hs ↦ mem_biUnion.2 ⟨#s, ?_⟩).trans card_biUnion_le
  exact ⟨mem_Iic.2 (mem_shatterer.1 hs).card_le_vcDim, mem_powersetCard_univ.2 rfl⟩

end Finset

