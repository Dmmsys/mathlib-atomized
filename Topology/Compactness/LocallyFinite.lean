/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact sets and compact spaces and locally finite functions
-/

@[expose] public section

open Set

variable {X ι : Type*} [TopologicalSpace X] {s : Set X}

namespace LocallyFinite

/-- If `s` is a compact set in a topological space `X` and `f : ι → Set X` is a locally finite
family of sets, then `f i ∩ s` is nonempty only for a finitely many `i`. -/
/-
**LocallyFinite.finite_nonempty_inter_compact** 是 Mathlib 中的一个定理，位于命名空间 `Locally
Finite`。
形式化陈述：finite_nonempty_inter_compact {f : ι -> Set X} (hf : LocallyFinite f) (hs 
: IsCompact s) : { i | (f i inter s).Nonempty }.Finite
参数：hf : LocallyFinite f；hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `s` is a compact set in a topological space `X` and `f : ι → Set X` is a loca
lly finite
family of sets, then `f i ∩ s` is nonempty only for a finitely many `i`.
-/
theorem finite_nonempty_inter_compact {f : ι → Set X}
    (hf : LocallyFinite f) (hs : IsCompact s) : { i | (f i ∩ s).Nonempty }.Finite := by
  choose U hxU hUf using hf
  rcases hs.elim_nhds_subcover U fun x _ => hxU x with ⟨t, -, hsU⟩
  refine (t.finite_toSet.biUnion fun x _ => hUf x).subset ?_
  rintro i ⟨x, hx⟩
  rcases mem_iUnion₂.1 (hsU hx.2) with ⟨c, hct, hcx⟩
  exact mem_biUnion hct ⟨x, hx.1, hcx⟩

/-- If `X` is a compact space, then a locally finite family of sets of `X` can have only finitely
many nonempty elements. -/
/-
**LocallyFinite.finite_nonempty_of_compact** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFin
ite`。
形式化陈述：finite_nonempty_of_compact [CompactSpace X] {f : ι -> Set X} (hf : Locally
Finite f) : { i | (f i).Nonempty }.Finite
参数：hf : LocallyFinite f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `LocallyFinite.finite_nonempty_inter_compact`：finite_nonempty_inter_compa
ct {f : ι -> Set X} (hf : LocallyFinite f) (hs : IsCompact s) : { i | (f i inter
 s).Nonempty }.Finite
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)

--- 原说明 ---
If `X` is a compact space, then a locally finite family of sets of `X` can have 
only finitely
many nonempty elements.
-/
theorem finite_nonempty_of_compact [CompactSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) : { i | (f i).Nonempty }.Finite := by
  simpa only [inter_univ] using hf.finite_nonempty_inter_compact isCompact_univ

/-- If `X` is a compact space, then a locally finite family of nonempty sets of `X` can have only
finitely many elements, `Set.Finite` version. -/
/-
**LocallyFinite.finite_of_compact** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：finite_of_compact [CompactSpace X] {f : ι -> Set X} (hf : LocallyFinite f)
 (hne : forall i, (f i).Nonempty) : (univ : Set ι).Finite
参数：hf : LocallyFinite f；hne : forall i, (f i).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LocallyFinite.finite_nonempty_of_compact`：finite_nonempty_of_compact [Co
mpactSpace X] {f : ι -> Set X} (hf : LocallyFinite f) : { i | (f i).Nonempty }.F
inite

--- 原说明 ---
If `X` is a compact space, then a locally finite family of nonempty sets of `X` 
can have only
finitely many elements, `Set.Finite` version.
-/
theorem finite_of_compact [CompactSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : (univ : Set ι).Finite := by
  simpa only [hne] using! hf.finite_nonempty_of_compact

/-- If `X` is a compact space, then a locally finite family of nonempty sets of `X` can have only
finitely many elements, `Fintype` version. -/
@[instance_reducible]
/-
**LocallyFinite.fintypeOfCompact** 是 Mathlib 中的一个定义，位于命名空间 `LocallyFinite`。
形式化陈述：fintypeOfCompact [CompactSpace X] {f : ι -> Set X} (hf : LocallyFinite f) 
(hne : forall i, (f i).Nonempty) : Fintype ι
参数：hf : LocallyFinite f；hne : forall i, (f i).Nonempty。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.finite_of_compact`：finite_of_compact [CompactSpace X] {f :
 ι -> Set X} (hf : LocallyFinite f) (hne : forall i, (f i).Nonempty) : (univ : S
et ι).Finite

--- 原说明 ---
If `X` is a compact space, then a locally finite family of nonempty sets of `X` 
can have only
finitely many elements, `Fintype` version.
-/
noncomputable def fintypeOfCompact [CompactSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : Fintype ι :=
  fintypeOfFiniteUniv (hf.finite_of_compact hne)

end LocallyFinite

