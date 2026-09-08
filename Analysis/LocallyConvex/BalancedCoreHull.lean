/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.Basic

/-!
# Balanced Core and Balanced Hull

## Main definitions

* `balancedCore`: The largest balanced subset of a set `s`.
* `balancedHull`: The smallest balanced superset of a set `s`.

## Main statements

* `balancedCore_eq_iInter`: Characterization of the balanced core as an intersection over subsets.
* `nhds_basis_closed_balanced`: The closed balanced sets form a basis of the neighborhood filter.

## Implementation details

The balanced core and hull are implemented differently: for the core we take the obvious definition
of the union over all balanced sets that are contained in `s`, whereas for the hull, we take the
union over `r • s`, for `r` the scalars with `‖r‖ ≤ 1`. We show that `balancedHull` has the
defining properties of a hull in `Balanced.balancedHull_subset_of_subset` and `subset_balancedHull`.
For the core we need slightly stronger assumptions to obtain a characterization as an intersection,
this is `balancedCore_eq_iInter`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

balanced
-/

@[expose] public section


open Set Pointwise Topology Filter

variable {𝕜 E ι : Type*}

section balancedHull

section SeminormedRing

variable [SeminormedRing 𝕜]

section SMul

variable (𝕜) [SMul 𝕜 E] {s t : Set E} {x : E}

/-- The largest balanced subset of `s`. -/
/-
**balancedCore** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：balancedCore (s : Set E)
参数：s : Set E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The largest balanced subset of `s`.
-/
def balancedCore (s : Set E) :=
  ⋃₀ { t : Set E | Balanced 𝕜 t ∧ t ⊆ s }

/-- Helper definition to prove `balanced_core_eq_iInter` -/
/-
**balancedCoreAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：balancedCoreAux (s : Set E)
参数：s : Set E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper definition to prove `balanced_core_eq_iInter`
-/
def balancedCoreAux (s : Set E) :=
  ⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s

/-- The smallest balanced superset of `s`. -/
/-
**balancedHull** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：balancedHull (s : Set E)
参数：s : Set E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest balanced superset of `s`.
-/
def balancedHull (s : Set E) :=
  ⋃ (r : 𝕜) (_ : ‖r‖ ≤ 1), r • s

variable {𝕜}
/-
**balancedCore_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCore_subset (s : Set E) : balancedCore 𝕜 s subseteq s
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sUnion_subset`：sUnion_subset {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t' subseteq t) : ⋃₀ S subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem balancedCore_subset (s : Set E) : balancedCore 𝕜 s ⊆ s :=
  sUnion_subset fun _ ht => ht.2
/-
**balancedCore_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCore_empty : balancedCore 𝕜 (∅ : Set E) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `balancedCore_subset`：balancedCore_subset (s : Set E) : balancedCore 𝕜 s 
subseteq s
-/
theorem balancedCore_empty : balancedCore 𝕜 (∅ : Set E) = ∅ :=
  eq_empty_of_subset_empty (balancedCore_subset _)
/-
**mem_balancedCore_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_balancedCore_iff : x in balancedCore 𝕜 s ↔ exists t, Balanced 𝕜 t ∧ t 
subseteq s ∧ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_balancedCore_iff : x ∈ balancedCore 𝕜 s ↔ ∃ t, Balanced 𝕜 t ∧ t ⊆ s ∧ x ∈ t := by
  simp_rw [balancedCore, mem_sUnion, mem_ofPred_eq, and_assoc]
/-
**smul_balancedCore_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_balancedCore_subset (s : Set E) {a : 𝕜} (ha : ‖a‖ <= 1) : a • balance
dCore 𝕜 s subseteq balancedCore 𝕜 s
参数：s : Set E；ha : ‖a‖ <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_balancedCore_iff`：mem_balancedCore_iff : x in balancedCore 𝕜 s ↔ exi
sts t, Balanced 𝕜 t ∧ t subseteq s ∧ x in t
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem smul_balancedCore_subset (s : Set E) {a : 𝕜} (ha : ‖a‖ ≤ 1) :
    a • balancedCore 𝕜 s ⊆ balancedCore 𝕜 s := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_balancedCore_iff] at hy
  rcases hy with ⟨t, ht1, ht2, hy⟩
  exact ⟨t, ⟨ht1, ht2⟩, ht1 a ha (smul_mem_smul_set hy)⟩
/-
**balancedCore_balanced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCore_balanced (s : Set E) : Balanced 𝕜 (balancedCore 𝕜 s)
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_balancedCore_subset`：smul_balancedCore_subset (s : Set E) {a : 𝕜} (
ha : ‖a‖ <= 1) : a • balancedCore 𝕜 s subseteq balancedCore 𝕜 s
-/
theorem balancedCore_balanced (s : Set E) : Balanced 𝕜 (balancedCore 𝕜 s) := fun _ =>
  smul_balancedCore_subset s

/-- The balanced core of `t` is maximal in the sense that it contains any balanced subset
`s` of `t`. -/
/-
**Balanced.subset_balancedCore_of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.subset_balancedCore_of_subset (hs : Balanced 𝕜 s) (h : s subseteq
 t) : s subseteq balancedCore 𝕜 t
参数：hs : Balanced 𝕜 s；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S

--- 原说明 ---
The balanced core of `t` is maximal in the sense that it contains any balanced s
ubset
`s` of `t`.
-/
theorem Balanced.subset_balancedCore_of_subset (hs : Balanced 𝕜 s) (h : s ⊆ t) :
    s ⊆ balancedCore 𝕜 t :=
  subset_sUnion_of_mem ⟨hs, h⟩
/-
**Balanced.balancedCore_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Balanced.balancedCore_eq (h : Balanced 𝕜 s) : balancedCore 𝕜 s = s
参数：h : Balanced 𝕜 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `balancedCore_subset`：balancedCore_subset (s : Set E) : balancedCore 𝕜 s 
subseteq s
· 使用定理 `Balanced.subset_balancedCore_of_subset`：Balanced.subset_balancedCore_of_
subset (hs : Balanced 𝕜 s) (h : s subseteq t) : s subseteq balancedCore 𝕜 t
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
lemma Balanced.balancedCore_eq (h : Balanced 𝕜 s) : balancedCore 𝕜 s = s :=
  le_antisymm (balancedCore_subset _) (h.subset_balancedCore_of_subset subset_rfl)
/-
**mem_balancedCoreAux_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_balancedCoreAux_iff : x in balancedCoreAux 𝕜 s ↔ forall r : 𝕜, 1 <= ‖r
‖ -> x in r • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_balancedCoreAux_iff : x ∈ balancedCoreAux 𝕜 s ↔ ∀ r : 𝕜, 1 ≤ ‖r‖ → x ∈ r • s :=
  mem_iInter₂
/-
**mem_balancedHull_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_balancedHull_iff : x in balancedHull 𝕜 s ↔ exists r : 𝕜, ‖r‖ <= 1 ∧ x 
in r • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_balancedHull_iff : x ∈ balancedHull 𝕜 s ↔ ∃ r : 𝕜, ‖r‖ ≤ 1 ∧ x ∈ r • s := by
  simp [balancedHull]

/-- The balanced hull of `s` is minimal in the sense that it is contained in any balanced superset
`t` of `s`. -/
/-
**Balanced.balancedHull_subset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.balancedHull_subset_of_subset (ht : Balanced 𝕜 t) (h : s subseteq
 t) : balancedHull 𝕜 s subseteq t
参数：ht : Balanced 𝕜 t；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_balancedHull_iff`：mem_balancedHull_iff : x in balancedHull 𝕜 s ↔ exi
sts r : 𝕜, ‖r‖ <= 1 ∧ x in r • s
· 使用定理 `Balanced.smul_mem`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRin
g 𝕜] [inst_1 : SMul 𝕜 E] {s : Set E},   Balanced 𝕜 s → ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x
 : E⦄, …

--- 原说明 ---
The balanced hull of `s` is minimal in the sense that it is contained in any bal
anced superset
`t` of `s`.
-/
theorem Balanced.balancedHull_subset_of_subset (ht : Balanced 𝕜 t) (h : s ⊆ t) :
    balancedHull 𝕜 s ⊆ t := by
  intro x hx
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 hx
  exact ht.smul_mem hr (h hy)

@[mono, gcongr]
/-
**balancedHull_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedHull_mono (hst : s subseteq t) : balancedHull 𝕜 s subseteq balance
dHull 𝕜 t
参数：hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_balancedHull_iff`：mem_balancedHull_iff : x in balancedHull 𝕜 s ↔ exi
sts r : 𝕜, ‖r‖ <= 1 ∧ x in r • s
· 使用定理 `Set.smul_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
t : Set β} {a : α}, s ⊆ t → a • s ⊆ a • t
-/
theorem balancedHull_mono (hst : s ⊆ t) : balancedHull 𝕜 s ⊆ balancedHull 𝕜 t := by
  intro x hx
  rw [mem_balancedHull_iff] at *
  obtain ⟨r, hr₁, hr₂⟩ := hx
  use r
  exact ⟨hr₁, smul_set_mono hst hr₂⟩

end SMul

section Module

variable [AddCommGroup E] [Module 𝕜 E] {s : Set E}

/-
**balancedCore_zero_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCore_zero_mem (hs : (0 : E) in s) : (0 : E) in balancedCore 𝕜 s
参数：hs : (0 : E) in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_balancedCore_iff`：mem_balancedCore_iff : x in balancedCore 𝕜 s ↔ exi
sts t, Balanced 𝕜 t ∧ t subseteq s ∧ x in t
· 使用定理 `balanced_zero`：balanced_zero : Balanced 𝕜 (0 : Set E)
· 使用定理 `Set.zero_subset`：∀ {α : Type u_2} [inst : Zero α] {s : Set α}, 0 ⊆ s ↔ 0
 ∈ s
· 使用定理 `Set.zero_mem_zero`：∀ {α : Type u_2} [inst : Zero α], 0 ∈ 0
-/
theorem balancedCore_zero_mem (hs : (0 : E) ∈ s) : (0 : E) ∈ balancedCore 𝕜 s :=
  mem_balancedCore_iff.2 ⟨0, balanced_zero, zero_subset.2 hs, Set.zero_mem_zero⟩
/-
**balancedCore_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCore_nonempty_iff : (balancedCore 𝕜 s).Nonempty ↔ (0 : E) in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.zero_subset`：∀ {α : Type u_2} [inst : Zero α] {s : Set α}, 0 ⊆ s ↔ 0
 ∈ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `balancedCore_balanced`：balancedCore_balanced (s : Set E) : Balanced 𝕜 (b
alancedCore 𝕜 s)
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `balancedCore_subset`：balancedCore_subset (s : Set E) : balancedCore 𝕜 s 
subseteq s
· 使用定理 `balancedCore_zero_mem`：balancedCore_zero_mem (hs : (0 : E) in s) : (0 : 
E) in balancedCore 𝕜 s
-/
theorem balancedCore_nonempty_iff : (balancedCore 𝕜 s).Nonempty ↔ (0 : E) ∈ s :=
  ⟨fun h => zero_subset.1 <| (zero_smul_set h).superset.trans <|
    (balancedCore_balanced s (0 : 𝕜) <| norm_zero.trans_le zero_le_one).trans <|
      balancedCore_subset _,
    fun h => ⟨0, balancedCore_zero_mem h⟩⟩
/-
**Balanced.zero_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Balanced.zero_mem (hs : Balanced 𝕜 s) (hs_nonempty : s.Nonempty) : (0 : E)
 in s
参数：hs : Balanced 𝕜 s；hs_nonempty : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `balancedCore_nonempty_iff`：balancedCore_nonempty_iff : (balancedCore 𝕜 s
).Nonempty ↔ (0 : E) in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Balanced.balancedCore_eq`：Balanced.balancedCore_eq (h : Balanced 𝕜 s) : 
balancedCore 𝕜 s = s
-/
lemma Balanced.zero_mem (hs : Balanced 𝕜 s) (hs_nonempty : s.Nonempty) : (0 : E) ∈ s := by
  rw [← hs.balancedCore_eq] at hs_nonempty
  exact balancedCore_nonempty_iff.mp hs_nonempty

variable (𝕜) in
/-
**subset_balancedHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_balancedHull [NormOneClass 𝕜] {s : Set E} : s subseteq balancedHull
 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_balancedHull_iff`：mem_balancedHull_iff : x in balancedHull 𝕜 s ↔ exi
sts r : 𝕜, ‖r‖ <= 1 ∧ x in r • s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem subset_balancedHull [NormOneClass 𝕜] {s : Set E} : s ⊆ balancedHull 𝕜 s := fun _ hx =>
  mem_balancedHull_iff.2 ⟨1, norm_one.le, _, hx, one_smul _ _⟩
/-
**balancedHull.balanced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedHull.balanced (s : Set E) : Balanced 𝕜 (balancedHull 𝕜 s)
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.smul_set_iUnion₂`：smul_set_iUnion₂ (a : α) (s : forall i, κ i -> Set
 β) : a • ⋃ i, ⋃ j, s i j = ⋃ i, ⋃ j, a • s i j
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用引理 `mul_le_one₀`：mul_le_one₀ [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (h
b : b <= 1) : a * b <= 1
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
theorem balancedHull.balanced (s : Set E) : Balanced 𝕜 (balancedHull 𝕜 s) := by
  intro a ha
  simp_rw [balancedHull, smul_set_iUnion₂, subset_def, mem_iUnion₂]
  rintro x ⟨r, hr, hx⟩
  rw [← smul_assoc] at hx
  exact ⟨a • r, (norm_mul_le _ _).trans (mul_le_one₀ ha (norm_nonneg r) hr), hx⟩

open Balanced in
/-
**balancedHull_add_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedHull_add_subset [NormOneClass 𝕜] {t : Set E} : balancedHull 𝕜 (s +
 t) subseteq balancedHull 𝕜 s + balancedHull 𝕜 t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Balanced.balancedHull_subset_of_subset`：Balanced.balancedHull_subset_of_
subset (ht : Balanced 𝕜 t) (h : s subseteq t) : balancedHull 𝕜 s subseteq t
· 使用定理 `Balanced.add`：Balanced.add (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Bal
anced 𝕜 (s + t)
· 使用定理 `balancedHull.balanced`：balancedHull.balanced (s : Set E) : Balanced 𝕜 (b
alancedHull 𝕜 s)
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
· 使用定理 `subset_balancedHull`：subset_balancedHull [NormOneClass 𝕜] {s : Set E} : 
s subseteq balancedHull 𝕜 s
-/
theorem balancedHull_add_subset [NormOneClass 𝕜] {t : Set E} :
    balancedHull 𝕜 (s + t) ⊆ balancedHull 𝕜 s + balancedHull 𝕜 t :=
  balancedHull_subset_of_subset (add (balancedHull.balanced _) (balancedHull.balanced _))
    (add_subset_add (subset_balancedHull _) (subset_balancedHull _))

end Module

end SeminormedRing

section NormedField

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

@[simp]
/-
**balancedCoreAux_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCoreAux_empty : balancedCoreAux 𝕜 (∅ : Set E) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem balancedCoreAux_empty : balancedCoreAux 𝕜 (∅ : Set E) = ∅ := by
  simp_rw [balancedCoreAux, iInter₂_eq_empty_iff, smul_set_empty]
  exact fun _ => ⟨1, norm_one.ge, notMem_empty _⟩
/-
**balancedCoreAux_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCoreAux_subset (s : Set E) : balancedCoreAux 𝕜 s subseteq s
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_balancedCoreAux_iff`：mem_balancedCoreAux_iff : x in balancedCoreAux 
𝕜 s ↔ forall r : 𝕜, 1 <= ‖r‖ -> x in r • s
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
theorem balancedCoreAux_subset (s : Set E) : balancedCoreAux 𝕜 s ⊆ s := fun x hx => by
  simpa only [one_smul] using mem_balancedCoreAux_iff.1 hx 1 norm_one.ge
/-
**balancedCoreAux_balanced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCoreAux_balanced (h0 : (0 : E) in balancedCoreAux 𝕜 s) : Balanced 
𝕜 (balancedCoreAux 𝕜 s)
参数：h0 : (0 : E) in balancedCoreAux 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_balancedCoreAux_iff`：mem_balancedCoreAux_iff : x in balancedCoreAux 
𝕜 s ↔ forall r : 𝕜, 1 <= ‖r‖ -> x in r • s
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `one_le_mul_of_one_le_of_one_le`：one_le_mul_of_one_le_of_one_le [ZeroLEOn
eClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b) : (1 : M₀) <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_le_inv₀`：one_le_inv₀ (ha : 0 < a) : 1 <= a⁻¹ ↔ a <= 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `Set.mem_inv_smul_set_iff₀`：mem_inv_smul_set_iff₀ (ha : a != 0) (A : Set 
β) (x : β) : x in a⁻¹ • A ↔ a • x in A
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
theorem balancedCoreAux_balanced (h0 : (0 : E) ∈ balancedCoreAux 𝕜 s) :
    Balanced 𝕜 (balancedCoreAux 𝕜 s) := by
  rintro a ha x ⟨y, hy, rfl⟩
  obtain rfl | h := eq_or_ne a 0
  · simp_rw [zero_smul, h0]
  rw [mem_balancedCoreAux_iff] at hy ⊢
  intro r hr
  have h'' : 1 ≤ ‖a⁻¹ • r‖ := by
    rw [norm_smul, norm_inv]
    exact one_le_mul_of_one_le_of_one_le ((one_le_inv₀ (norm_pos_iff.mpr h)).2 ha) hr
  have h' := hy (a⁻¹ • r) h''
  rwa [smul_assoc, mem_inv_smul_set_iff₀ h] at h'
/-
**balancedCoreAux_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCoreAux_maximal (h : t subseteq s) (ht : Balanced 𝕜 t) : t subsete
q balancedCoreAux 𝕜 s
参数：h : t subseteq s；ht : Balanced 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_balancedCoreAux_iff`：mem_balancedCoreAux_iff : x in balancedCoreAux 
𝕜 s ↔ forall r : 𝕜, 1 <= ‖r‖ -> x in r • s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Balanced.smul_mem`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRin
g 𝕜] [inst_1 : SMul 𝕜 E] {s : Set E},   Balanced 𝕜 s → ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x
 : E⦄, …
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `inv_le_one_of_one_le₀`：inv_le_one_of_one_le₀ (ha : 1 <= a) : a⁻¹ <= 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem balancedCoreAux_maximal (h : t ⊆ s) (ht : Balanced 𝕜 t) : t ⊆ balancedCoreAux 𝕜 s := by
  refine fun x hx => mem_balancedCoreAux_iff.2 fun r hr => ?_
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp <| zero_lt_one.trans_le hr)]
  refine h (ht.smul_mem ?_ hx)
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hr
/-
**balancedCore_subset_balancedCoreAux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCore_subset_balancedCoreAux : balancedCore 𝕜 s subseteq balancedCo
reAux 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `balancedCoreAux_maximal`：balancedCoreAux_maximal (h : t subseteq s) (ht 
: Balanced 𝕜 t) : t subseteq balancedCoreAux 𝕜 s
· 使用定理 `balancedCore_subset`：balancedCore_subset (s : Set E) : balancedCore 𝕜 s 
subseteq s
· 使用定理 `balancedCore_balanced`：balancedCore_balanced (s : Set E) : Balanced 𝕜 (b
alancedCore 𝕜 s)
-/
theorem balancedCore_subset_balancedCoreAux : balancedCore 𝕜 s ⊆ balancedCoreAux 𝕜 s :=
  balancedCoreAux_maximal (balancedCore_subset s) (balancedCore_balanced s)
/-
**balancedCore_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCore_eq_iInter (hs : (0 : E) in s) : balancedCore 𝕜 s = ⋂ (r : 𝕜) 
(_ : 1 <= ‖r‖), r • s
参数：hs : (0 : E) in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `balancedCore_subset_balancedCoreAux`：balancedCore_subset_balancedCoreAux
 : balancedCore 𝕜 s subseteq balancedCoreAux 𝕜 s
· 使用定理 `Balanced.subset_balancedCore_of_subset`：Balanced.subset_balancedCore_of_
subset (hs : Balanced 𝕜 s) (h : s subseteq t) : s subseteq balancedCore 𝕜 t
· 使用定理 `balancedCoreAux_balanced`：balancedCoreAux_balanced (h0 : (0 : E) in bala
ncedCoreAux 𝕜 s) : Balanced 𝕜 (balancedCoreAux 𝕜 s)
· 使用定理 `balancedCore_zero_mem`：balancedCore_zero_mem (hs : (0 : E) in s) : (0 : 
E) in balancedCore 𝕜 s
· 使用定理 `balancedCoreAux_subset`：balancedCoreAux_subset (s : Set E) : balancedCor
eAux 𝕜 s subseteq s
-/
theorem balancedCore_eq_iInter (hs : (0 : E) ∈ s) :
    balancedCore 𝕜 s = ⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s := by
  refine balancedCore_subset_balancedCoreAux.antisymm ?_
  refine (balancedCoreAux_balanced ?_).subset_balancedCore_of_subset (balancedCoreAux_subset s)
  exact balancedCore_subset_balancedCoreAux (balancedCore_zero_mem hs)
/-
**subset_balancedCore** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_balancedCore (ht : (0 : E) in t) (hst : forall a : 𝕜, ‖a‖ <= 1 -> a
 • s subseteq t) : s subseteq balancedCore 𝕜 t
参数：ht : (0 : E) in t；hst : forall a : 𝕜, ‖a‖ <= 1 -> a • s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `balancedCore_eq_iInter`：balancedCore_eq_iInter (hs : (0 : E) in s) : bal
ancedCore 𝕜 s = ⋂ (r : 𝕜) (_ : 1 <= ‖r‖), r • s
· 使用定理 `Set.subset_iInter₂`：subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set
 α} (h : forall i j, s subseteq t i j) : s subseteq ⋂ (i) (j), t i j
· 使用引理 `Set.subset_smul_set_iff₀`：subset_smul_set_iff₀ (ha : a != 0) {A B : Set 
β} : A subseteq a • B ↔ a⁻¹ • A subseteq B
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `inv_le_one_of_one_le₀`：inv_le_one_of_one_le₀ (ha : 1 <= a) : a⁻¹ <= 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem subset_balancedCore (ht : (0 : E) ∈ t) (hst : ∀ a : 𝕜, ‖a‖ ≤ 1 → a • s ⊆ t) :
    s ⊆ balancedCore 𝕜 t := by
  rw [balancedCore_eq_iInter ht]
  refine subset_iInter₂ fun a ha ↦ ?_
  rw [subset_smul_set_iff₀ (norm_pos_iff.mp <| zero_lt_one.trans_le ha)]
  apply hst
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ ha

end NormedField

end balancedHull

/-! ### Topological properties -/


section Topology

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousSMul 𝕜 E] {U : Set E}

/-
**IsClosed.balancedCore** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NormedDivisionRing 𝕜] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] [Cont
inuousSMul 𝕜 E] {U : Set E}, IsClosed U → IsClosed (balancedCore 𝕜 U)
参数：balancedCore 𝕜 U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `balancedCore_eq_iInter`：balancedCore_eq_iInter (hs : (0 : E) in s) : bal
ancedCore 𝕜 s = ⋂ (r : 𝕜) (_ : 1 <= ‖r‖), r • s
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `isClosedMap_smul_of_ne_zero`：isClosedMap_smul_of_ne_zero {c : G₀} (hc : 
c != 0) : IsClosedMap fun x : α => c • x
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `balancedCore_nonempty_iff`：balancedCore_nonempty_iff : (balancedCore 𝕜 s
).Nonempty ↔ (0 : E) in s
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
-/
protected theorem IsClosed.balancedCore (hU : IsClosed U) : IsClosed (balancedCore 𝕜 U) := by
  by_cases h : (0 : E) ∈ U
  · rw [balancedCore_eq_iInter h]
    refine isClosed_iInter fun a => ?_
    refine isClosed_iInter fun ha => ?_
    have ha' := lt_of_lt_of_le zero_lt_one ha
    rw [norm_pos_iff] at ha'
    exact isClosedMap_smul_of_ne_zero ha' U hU
  · have : balancedCore 𝕜 U = ∅ := by
      contrapose! h
      exact balancedCore_nonempty_iff.mp h
    rw [this]
    exact isClosed_empty

omit [ContinuousSMul 𝕜 E] in
/-
**IsOpen.balancedHull** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NormedDivisionRing 𝕜] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] [Cont
inuousConstSMul 𝕜 E] {s : Set E}, IsOpen s → 0 ∈ s → IsOpen (balancedHull 𝕜 s)
参数：balancedHull 𝕜 s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion₂_mono'`：iUnion₂_mono' {s : forall i, κ i -> Set α} {t : foral
l i', κ' i' -> Set α} (h : forall i j, exists i' j', s i j subseteq t i' j') : ⋃
 (i) (j…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_prop`：∀ {b a : Prop}, (∃ (_ : a), b) ↔ a ∧ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `balancedHull.eq_1`：∀ (𝕜 : Type u_1) {E : Type u_2} [inst : SeminormedRin
g 𝕜] [inst_1 : SMul 𝕜 E] (s : Set E),   balancedHull 𝕜 s = ⋃ r, ⋃ (_ : ‖r‖ ≤ 1),
 r • s
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `IsOpen.smul₀`：IsOpen.smul₀ {c : G₀} {s : Set α} (hs : IsOpen s) (hc : c 
!= 0) : IsOpen (c • s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem IsOpen.balancedHull [ContinuousConstSMul 𝕜 E] {s : Set E} (hs : IsOpen s)
    (hzero : 0 ∈ s) : IsOpen (balancedHull 𝕜 s) := by
  have : (⋃ r : 𝕜, ⋃ (_ : ‖r‖ ≤ 1), r • s) = (⋃ r : 𝕜, ⋃ (_ : ‖r‖ ≤ 1 ∧ r ≠ 0), r • s) := by
    refine subset_antisymm (Set.iUnion₂_mono' fun r hr ↦ ?_) (Set.iUnion₂_mono' (by grind))
    obtain rfl | hr_ne := eq_or_ne r 0
    · exact ⟨1, by simp, by simpa [Set.zero_smul_set ⟨0, hzero⟩]⟩
    · use r
  rw [balancedHull, this]
  exact isOpen_biUnion (fun r hr ↦ hs.smul₀ hr.2)

-- We don't have a `NontriviallyNormedDivisionRing`, so we use a `NeBot` assumption instead
variable [NeBot (𝓝[≠] (0 : 𝕜))]
/-
**balancedCore_mem_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedCore_mem_nhds_zero (hU : U in 𝓝 (0 : E)) : balancedCore 𝕜 U in 𝓝 (
0 : E)
参数：hU : U in 𝓝 (0 : E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.Tendsto.basis_left`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4
} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β}   {f : α → β}
, Filter.Tendst…
· 使用定理 `Filter.HasBasis.prod_nhds`：Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px
 : ιX -> Prop} {py : ιY -> Prop} {sx : ιX -> Set X} {sy : ιY -> Set Y} {x : X} {
y : Y} (hx : (𝓝…
· 使用定理 `NormedAddGroup.nhds_zero_basis_norm_lt`：∀ {E : Type u_5} [inst : Seminor
medAddGroup E], (nhds 0).HasBasis (fun ε => 0 < ε) fun ε => {y | ‖y‖ < ε}
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_smul_mem_nhds_zero_iff`：set_smul_mem_nhds_zero_iff {s : Set α} {c : 
G₀} (hc : c != 0) : c • s in 𝓝 (0 : α) ↔ s in 𝓝 (0 : α)
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_balancedCore`：subset_balancedCore (ht : (0 : E) in t) (hst : fora
ll a : 𝕜, ‖a‖ <= 1 -> a • s subseteq t) : s subseteq balancedCore 𝕜 t
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul'`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 :
 Preorder α] {a b c d : α} [PosMulStrictMono α]   [MulPosMono α], a ≤ b → c < d 
→…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
（共 31 条，此处仅展示前 30 条）
-/
theorem balancedCore_mem_nhds_zero (hU : U ∈ 𝓝 (0 : E)) : balancedCore 𝕜 U ∈ 𝓝 (0 : E) := by
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
  obtain ⟨r, V, hr, hV, hrVU⟩ : ∃ (r : ℝ) (V : Set E),
      0 < r ∧ V ∈ 𝓝 (0 : E) ∧ ∀ (c : 𝕜) (y : E), ‖c‖ < r → y ∈ V → c • y ∈ U := by
    have h : Filter.Tendsto (fun x : 𝕜 × E => x.fst • x.snd) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_smul.tendsto' (0, 0) _ (smul_zero _)
    simpa only [← Prod.exists', ← Prod.forall', ← and_imp, ← and_assoc, exists_prop] using!
      h.basis_left (NormedAddGroup.nhds_zero_basis_norm_lt.prod_nhds (𝓝 _).basis_sets) U hU
  obtain ⟨y, hyr, hy₀⟩ : ∃ y : 𝕜, ‖y‖ < r ∧ y ≠ 0 :=
    Filter.nonempty_of_mem <|
      (nhdsWithin_hasBasis NormedAddGroup.nhds_zero_basis_norm_lt {0}ᶜ).mem_of_mem hr
  have : y • V ∈ 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hy₀).mpr hV
  -- It remains to show that `y • V ⊆ balancedCore 𝕜 U`
  refine Filter.mem_of_superset this (subset_balancedCore (mem_of_mem_nhds hU) fun a ha => ?_)
  rw [smul_smul]
  rintro _ ⟨z, hz, rfl⟩
  refine hrVU _ _ ?_ hz
  rw [norm_mul, ← one_mul r]
  exact mul_lt_mul' ha hyr (norm_nonneg y) one_pos

variable (𝕜 E)
/-
**nhds_basis_balanced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s : Set E => s in 𝓝 (0 : E
) ∧ Balanced 𝕜 s) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `balancedCore_mem_nhds_zero`：balancedCore_mem_nhds_zero (hU : U in 𝓝 (0 :
 E)) : balancedCore 𝕜 U in 𝓝 (0 : E)
· 使用定理 `balancedCore_balanced`：balancedCore_balanced (s : Set E) : Balanced 𝕜 (b
alancedCore 𝕜 s)
· 使用定理 `balancedCore_subset`：balancedCore_subset (s : Set E) : balancedCore 𝕜 s 
subseteq s
-/
theorem nhds_basis_balanced :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ Balanced 𝕜 s) id :=
  Filter.hasBasis_self.mpr fun s hs =>
    ⟨balancedCore 𝕜 s, balancedCore_mem_nhds_zero hs, balancedCore_balanced s,
      balancedCore_subset s⟩
/-
**nhds_basis_closed_balanced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_closed_balanced [RegularSpace E] : (𝓝 (0 : E)).HasBasis (fun s 
: Set E => s in 𝓝 (0 : E) ∧ IsClosed s ∧ Balanced 𝕜 s) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `balancedCore_mem_nhds_zero`：balancedCore_mem_nhds_zero (hU : U in 𝓝 (0 :
 E)) : balancedCore 𝕜 U in 𝓝 (0 : E)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsClosed.balancedCore`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NormedDiv
isionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : 
Topological…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `balancedCore_balanced`：balancedCore_balanced (s : Set E) : Balanced 𝕜 (b
alancedCore 𝕜 s)
· 使用定理 `balancedCore_subset`：balancedCore_subset (s : Set E) : balancedCore 𝕜 s 
subseteq s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
theorem nhds_basis_closed_balanced [RegularSpace E] :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ IsClosed s ∧ Balanced 𝕜 s) id := by
  refine
    (closed_nhds_basis 0).to_hasBasis (fun s hs => ?_) fun s hs => ⟨s, ⟨hs.1, hs.2.1⟩, rfl.subset⟩
  refine ⟨balancedCore 𝕜 s, ⟨balancedCore_mem_nhds_zero hs.1, ?_⟩, balancedCore_subset s⟩
  exact ⟨hs.2.balancedCore, balancedCore_balanced s⟩

end Topology

