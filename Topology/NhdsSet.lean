/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
module

public import Mathlib.Topology.Neighborhoods

/-!
# Neighborhoods of a set

In this file we define the filter `𝓝ˢ s` or `nhdsSet s` consisting of all neighborhoods of a set
`s`.

## Main Properties

There are a couple different notions equivalent to `s ∈ 𝓝ˢ t`:
* `s ⊆ interior t` using `subset_interior_iff_mem_nhdsSet`
* `∀ x : X, x ∈ t → s ∈ 𝓝 x` using `mem_nhdsSet_iff_forall`
* `∃ U : Set X, IsOpen U ∧ t ⊆ U ∧ U ⊆ s` using `mem_nhdsSet_iff_exists`

Furthermore, we have the following results:
* `monotone_nhdsSet`: `𝓝ˢ` is monotone
* In T₁-spaces, `𝓝ˢ` is strictly monotone and hence injective:
  `strict_mono_nhdsSet`/`injective_nhdsSet`. These results are in
  `Mathlib/Topology/Separation/Basic.lean`.
-/

public section

open Set Filter Topology

variable {α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Filter X}
  {s t s₁ s₂ t₁ t₂ : Set X} {x : X}

/-
**nhdsSet_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_diagonal (X) [TopologicalSpace (X × X)] : 𝓝ˢ (diagonal X) = ⨆ (x :
 X), 𝓝 (x, x)
参数：X；X × X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Set X), 
nhdsSet s = sSup (nhds '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_diag`：range_diag : range Function.diag = diagonal α
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem nhdsSet_diagonal (X) [TopologicalSpace (X × X)] :
    𝓝ˢ (diagonal X) = ⨆ (x : X), 𝓝 (x, x) := by
  rw [nhdsSet, ← range_diag, ← range_comp]
  rfl
/-
**mem_nhdsSet_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : X, x in t -> s in 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhdsSet_iff_forall : s ∈ 𝓝ˢ t ↔ ∀ x : X, x ∈ t → s ∈ 𝓝 x := by
  simp_rw [nhdsSet, Filter.mem_sSup, forall_mem_image]
/-
**nhdsSet_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSet_le : 𝓝ˢ s <= f ↔ forall x in s, 𝓝 x <= f
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nhdsSet_le : 𝓝ˢ s ≤ f ↔ ∀ x ∈ s, 𝓝 x ≤ f := by simp [nhdsSet]
/-
**bUnion_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bUnion_mem_nhdsSet {t : X -> Set X} (h : forall x in s, t x in 𝓝 x) : (⋃ x
 in s, t x) in 𝓝ˢ s
参数：h : forall x in s, t x in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.subset_iUnion₂`：subset_iUnion₂ {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : s i j subseteq ⋃ (i') (j'), s i' j'
-/
theorem bUnion_mem_nhdsSet {t : X → Set X} (h : ∀ x ∈ s, t x ∈ 𝓝 x) : (⋃ x ∈ s, t x) ∈ 𝓝ˢ s :=
  mem_nhdsSet_iff_forall.2 fun x hx => mem_of_superset (h x hx) <|
    subset_iUnion₂ (s := fun x _ => t x) x hx
/-
**subset_interior_iff_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_iff_mem_nhdsSet : s subseteq interior t ↔ t in 𝓝ˢ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subset_interior_iff_mem_nhdsSet : s ⊆ interior t ↔ t ∈ 𝓝ˢ s := by
  simp_rw [mem_nhdsSet_iff_forall, subset_interior_iff_nhds]
/-
**disjoint_principal_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_principal_nhdsSet : Disjoint (𝓟 s) (𝓝ˢ t) ↔ Disjoint (closure s) 
t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.disjoint_principal_left`：disjoint_principal_left {f : Filter α} {
s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_interior_iff_mem_nhdsSet`：subset_interior_iff_mem_nhdsSet : s sub
seteq interior t ↔ t in 𝓝ˢ s
· 使用定理 `interior_compl`：interior_compl : interior sᶜ = (closure s)ᶜ
· 使用引理 `Set.subset_compl_iff_disjoint_left`：subset_compl_iff_disjoint_left : s s
ubseteq tᶜ ↔ Disjoint t s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_principal_nhdsSet : Disjoint (𝓟 s) (𝓝ˢ t) ↔ Disjoint (closure s) t := by
  rw [disjoint_principal_left, ← subset_interior_iff_mem_nhdsSet, interior_compl,
    subset_compl_iff_disjoint_left]
/-
**disjoint_nhdsSet_principal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhdsSet_principal : Disjoint (𝓝ˢ s) (𝓟 t) ↔ Disjoint s (closure t
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `disjoint_principal_nhdsSet`：disjoint_principal_nhdsSet : Disjoint (𝓟 s) 
(𝓝ˢ t) ↔ Disjoint (closure s) t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_nhdsSet_principal : Disjoint (𝓝ˢ s) (𝓟 t) ↔ Disjoint s (closure t) := by
  rw [disjoint_comm, disjoint_principal_nhdsSet, disjoint_comm]
/-
**mem_nhdsSet_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsSet_iff_exists : s in 𝓝ˢ t ↔ exists U : Set X, IsOpen U ∧ t subset
eq U ∧ U subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_interior_iff_mem_nhdsSet`：subset_interior_iff_mem_nhdsSet : s sub
seteq interior t ↔ t in 𝓝ˢ s
· 使用定理 `subset_interior_iff`：subset_interior_iff : t subseteq interior s ↔ exist
s U, IsOpen U ∧ t subseteq U ∧ U subseteq s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nhdsSet_iff_exists : s ∈ 𝓝ˢ t ↔ ∃ U : Set X, IsOpen U ∧ t ⊆ U ∧ U ⊆ s := by
  rw [← subset_interior_iff_mem_nhdsSet, subset_interior_iff]

/-- A proposition is true on a set neighborhood of `s` iff it is true on a larger open set -/
/-
**eventually_nhdsSet_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhdsSet_iff_exists {p : X -> Prop} : (forallᶠ x in 𝓝ˢ s, p x) ↔
 exists t, IsOpen t ∧ s subseteq t ∧ forall x, x in t -> p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsSet_iff_exists`：mem_nhdsSet_iff_exists : s in 𝓝ˢ t ↔ exists U : 
Set X, IsOpen U ∧ t subseteq U ∧ U subseteq s

--- 原说明 ---
A proposition is true on a set neighborhood of `s` iff it is true on a larger op
en set
-/
theorem eventually_nhdsSet_iff_exists {p : X → Prop} :
    (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∃ t, IsOpen t ∧ s ⊆ t ∧ ∀ x, x ∈ t → p x :=
  mem_nhdsSet_iff_exists

/-- A proposition is true on a set neighborhood of `s`
iff it is eventually true near each point in the set. -/
/-
**eventually_nhdsSet_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhdsSet_iff_forall {p : X -> Prop} : (forallᶠ x in 𝓝ˢ s, p x) ↔
 forall x, x in s -> forallᶠ y in 𝓝 x, p y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x

--- 原说明 ---
A proposition is true on a set neighborhood of `s`
iff it is eventually true near each point in the set.
-/
theorem eventually_nhdsSet_iff_forall {p : X → Prop} :
    (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, p y :=
  mem_nhdsSet_iff_forall
/-
**hasBasis_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U => IsOpen U ∧ s subs
eteq U) fun U => U
参数：s : Set X。
该定理/引理给出了一组等式。
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
theorem hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U => IsOpen U ∧ s ⊆ U) fun U => U :=
  ⟨fun t => by simp [mem_nhdsSet_iff_exists, and_assoc]⟩

@[simp]
/-
**lift'_nhdsSet_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] (s : Set X), (nhdsSet s).lift
' interior = nhdsSet s
参数：s : Set X；nhdsSet s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.lift'_interior_eq_self`：∀ {X : Type u} [inst : Topologic
alSpace X] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBa
sis p s → (∀ (i : ι), p i → …
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma lift'_nhdsSet_interior (s : Set X) : (𝓝ˢ s).lift' interior = 𝓝ˢ s :=
  (hasBasis_nhdsSet s).lift'_interior_eq_self fun _ ↦ And.left
/-
**Filter.HasBasis.nhdsSet_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.nhdsSet_interior {ι : Sort*} {p : ι -> Prop} {s : ι -> Set
 X} {t : Set X} (h : (𝓝ˢ t).HasBasis p s) : (𝓝ˢ t).HasBasis p (interior <| s ·)
参数：h : (𝓝ˢ t).HasBasis p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.HasBasis.lift'_interior`：∀ {X : Type u} [inst : TopologicalSpace 
X] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBasis p s 
→ (l.lift' interior)…
· 使用定理 `lift'_nhdsSet_interior`：∀ {X : Type u_2} [inst : TopologicalSpace X] (s 
: Set X), (nhdsSet s).lift' interior = nhdsSet s
-/
lemma Filter.HasBasis.nhdsSet_interior {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {t : Set X}
    (h : (𝓝ˢ t).HasBasis p s) : (𝓝ˢ t).HasBasis p (interior <| s ·) :=
  lift'_nhdsSet_interior t ▸ h.lift'_interior
/-
**IsOpen.mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t subseteq s
参数：hU : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_interior_iff_mem_nhdsSet`：subset_interior_iff_mem_nhdsSet : s sub
seteq interior t ↔ t in 𝓝ˢ s
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsOpen.mem_nhdsSet (hU : IsOpen s) : s ∈ 𝓝ˢ t ↔ t ⊆ s := by
  rw [← subset_interior_iff_mem_nhdsSet, hU.interior_eq]

/-- An open set belongs to its own set neighborhoods filter. -/
/-
**IsOpen.mem_nhdsSet_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.mem_nhdsSet_self (ho : IsOpen s) : s in 𝓝ˢ s
参数：ho : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
An open set belongs to its own set neighborhoods filter.
-/
theorem IsOpen.mem_nhdsSet_self (ho : IsOpen s) : s ∈ 𝓝ˢ s := ho.mem_nhdsSet.mpr Subset.rfl
/-
**principal_le_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：principal_le_nhdsSet : 𝓟 s <= 𝓝ˢ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `subset_interior_iff_mem_nhdsSet`：subset_interior_iff_mem_nhdsSet : s sub
seteq interior t ↔ t in 𝓝ˢ s
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem principal_le_nhdsSet : 𝓟 s ≤ 𝓝ˢ s := fun _s hs =>
  (subset_interior_iff_mem_nhdsSet.mpr hs).trans interior_subset
/-
**subset_of_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_of_mem_nhdsSet (h : t in 𝓝ˢ s) : s subseteq t
参数：h : t in 𝓝ˢ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `principal_le_nhdsSet`：principal_le_nhdsSet : 𝓟 s <= 𝓝ˢ s
-/
theorem subset_of_mem_nhdsSet (h : t ∈ 𝓝ˢ s) : s ⊆ t := principal_le_nhdsSet h
/-
**Filter.Eventually.self_of_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.self_of_nhdsSet {p : X -> Prop} (h : forallᶠ x in 𝓝ˢ s, 
p x) : forall x in s, p x
参数：h : forallᶠ x in 𝓝ˢ s, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `principal_le_nhdsSet`：principal_le_nhdsSet : 𝓟 s <= 𝓝ˢ s
-/
theorem Filter.Eventually.self_of_nhdsSet {p : X → Prop} (h : ∀ᶠ x in 𝓝ˢ s, p x) : ∀ x ∈ s, p x :=
  principal_le_nhdsSet h

nonrec theorem Filter.EventuallyEq.self_of_nhdsSet {Y} {f g : X → Y} (h : f =ᶠ[𝓝ˢ s] g) :
    EqOn f g s :=
  h.self_of_nhdsSet

@[simp]
/-
**nhdsSet_eq_principal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_eq_principal_iff : 𝓝ˢ s = 𝓟 s ↔ IsOpen s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `principal_le_nhdsSet`：principal_le_nhdsSet : 𝓟 s <= 𝓝ˢ s
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nhdsSet_eq_principal_iff : 𝓝ˢ s = 𝓟 s ↔ IsOpen s := by
  rw [← principal_le_nhdsSet.ge_iff_eq', le_principal_iff, mem_nhdsSet_iff_forall,
    isOpen_iff_mem_nhds]

alias ⟨_, IsOpen.nhdsSet_eq⟩ := nhdsSet_eq_principal_iff

@[simp]
/-
**nhdsSet_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_interior : 𝓝ˢ (interior s) = 𝓟 (interior s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.nhdsSet_eq`：∀ {X : Type u_2} [inst : TopologicalSpace X] {s : Set
 X}, IsOpen s → nhdsSet s = Filter.principal s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem nhdsSet_interior : 𝓝ˢ (interior s) = 𝓟 (interior s) :=
  isOpen_interior.nhdsSet_eq

@[simp]
/-
**nhdsSet_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x := by simp [nhdsSet]
/-
**mem_nhdsSet_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsSet_interior : s in 𝓝ˢ (interior s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `subset_interior_iff_mem_nhdsSet`：subset_interior_iff_mem_nhdsSet : s sub
seteq interior t ↔ t in 𝓝ˢ s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem mem_nhdsSet_interior : s ∈ 𝓝ˢ (interior s) :=
  subset_interior_iff_mem_nhdsSet.mp Subset.rfl

@[simp]
/-
**nhdsSet_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.nhdsSet_eq`：∀ {X : Type u_2} [inst : TopologicalSpace X] {s : Set
 X}, IsOpen s → nhdsSet s = Filter.principal s
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
-/
theorem nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥ := by rw [isOpen_empty.nhdsSet_eq, principal_empty]
/-
**mem_nhdsSet_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsSet_empty : s in 𝓝ˢ (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_empty`：nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥
-/
theorem mem_nhdsSet_empty : s ∈ 𝓝ˢ (∅ : Set X) := by simp

@[simp]
/-
**nhdsSet_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSet_eq_bot_iff {α : Type*} [TopologicalSpace α] {s : Set α} : 𝓝ˢ s = ⊥
 ↔ s = ∅ where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_empty`：nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma nhdsSet_eq_bot_iff {α : Type*} [TopologicalSpace α] {s : Set α} :
    𝓝ˢ s = ⊥ ↔ s = ∅ where
  mp := by simp [← empty_mem_iff_bot, mem_nhdsSet_iff_forall, eq_empty_iff_forall_notMem]
  mpr := by simp +contextual
/-
**nhdsSet_neBot_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSet_neBot_iff {α : Type*} [TopologicalSpace α] {s : Set α} : (𝓝ˢ s).Ne
Bot ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nhdsSet_neBot_iff {α : Type*} [TopologicalSpace α] {s : Set α} :
    (𝓝ˢ s).NeBot ↔ s.Nonempty :=
  not_iff_not.mp <| by simp [not_nonempty_iff_eq_empty]

alias ⟨Set.Nonempty.nhdsSet_neBot, _⟩ := nhdsSet_neBot_iff

@[simp]
/-
**nhdsSet_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_univ : 𝓝ˢ (univ : Set X) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.nhdsSet_eq`：∀ {X : Type u_2} [inst : TopologicalSpace X] {s : Set
 X}, IsOpen s → nhdsSet s = Filter.principal s
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
-/
theorem nhdsSet_univ : 𝓝ˢ (univ : Set X) = ⊤ := by rw [isOpen_univ.nhdsSet_eq, principal_univ]

@[gcongr, mono]
/-
**nhdsSet_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem nhdsSet_mono (h : s ⊆ t) : 𝓝ˢ s ≤ 𝓝ˢ t :=
  sSup_le_sSup <| image_mono h
/-
**monotone_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_nhdsSet : Monotone (𝓝ˢ : Set X -> Filter X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
-/
theorem monotone_nhdsSet : Monotone (𝓝ˢ : Set X → Filter X) := fun _ _ => nhdsSet_mono
/-
**nhds_le_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_le_nhdsSet (h : x in s) : 𝓝 x <= 𝓝ˢ s
参数：h : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem nhds_le_nhdsSet (h : x ∈ s) : 𝓝 x ≤ 𝓝ˢ s :=
  le_sSup <| mem_image_of_mem _ h
/-
**tendsto_nhdsSet_of_tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhdsSet_of_tendsto_nhds {f : α -> X} {l : Filter α} {x : X} (hx : 
x in s) (hf : Tendsto f l (𝓝 x)) : Tendsto f l (𝓝ˢ s)
参数：hx : x in s；hf : Tendsto f l (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `nhds_le_nhdsSet`：nhds_le_nhdsSet (h : x in s) : 𝓝 x <= 𝓝ˢ s
-/
theorem tendsto_nhdsSet_of_tendsto_nhds {f : α → X} {l : Filter α} {x : X} (hx : x ∈ s)
    (hf : Tendsto f l (𝓝 x)) :
    Tendsto f l (𝓝ˢ s) :=
  hf.trans (nhds_le_nhdsSet hx)

@[simp]
/-
**nhdsSet_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_union (s t : Set X) : 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ t
参数：s t : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `sSup_union`：sSup_union {s t : Set α} : sSup (s union t) = sSup s ⊔ sSup 
t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsSet_union (s t : Set X) : 𝓝ˢ (s ∪ t) = 𝓝ˢ s ⊔ 𝓝ˢ t := by
  simp only [nhdsSet, image_union, sSup_union]
/-
**union_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：union_mem_nhdsSet (h₁ : s₁ in 𝓝ˢ t₁) (h₂ : s₂ in 𝓝ˢ t₂) : s₁ union s₂ in 𝓝
ˢ (t₁ union t₂)
参数：h₁ : s₁ in 𝓝ˢ t₁；h₂ : s₂ in 𝓝ˢ t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_union`：nhdsSet_union (s t : Set X) : 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ 
t
· 使用定理 `Filter.union_mem_sup`：union_mem_sup {f g : Filter α} {s t : Set α} (hs :
 s in f) (ht : t in g) : s union t in f ⊔ g
-/
theorem union_mem_nhdsSet (h₁ : s₁ ∈ 𝓝ˢ t₁) (h₂ : s₂ ∈ 𝓝ˢ t₂) : s₁ ∪ s₂ ∈ 𝓝ˢ (t₁ ∪ t₂) := by
  rw [nhdsSet_union]
  exact union_mem_sup h₁ h₂

@[simp]
/-
**nhdsSet_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_insert (x : X) (s : Set X) : 𝓝ˢ (insert x s) = 𝓝 x ⊔ 𝓝ˢ s
参数：x : X；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `nhdsSet_union`：nhdsSet_union (s t : Set X) : 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ 
t
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
-/
theorem nhdsSet_insert (x : X) (s : Set X) : 𝓝ˢ (insert x s) = 𝓝 x ⊔ 𝓝ˢ s := by
  rw [insert_eq, nhdsSet_union, nhdsSet_singleton]

/-- This inequality cannot be improved to an equality. For instance,
if `X` has two elements and the coarse topology and `s` and `t` are distinct singletons then
`𝓝ˢ (s ∩ t) = ⊥` while `𝓝ˢ s ⊓ 𝓝ˢ t = ⊤` and those are different. -/
/-
**nhdsSet_inter_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_inter_le (s t : Set X) : 𝓝ˢ (s inter t) <= 𝓝ˢ s ⊓ 𝓝ˢ t
参数：s t : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `monotone_nhdsSet`：monotone_nhdsSet : Monotone (𝓝ˢ : Set X -> Filter X)

--- 原说明 ---
This inequality cannot be improved to an equality. For instance,
if `X` has two elements and the coarse topology and `s` and `t` are distinct sin
gletons then
`𝓝ˢ (s ∩ t) = ⊥` while `𝓝ˢ s ⊓ 𝓝ˢ t = ⊤` and those are different.
-/
theorem nhdsSet_inter_le (s t : Set X) : 𝓝ˢ (s ∩ t) ≤ 𝓝ˢ s ⊓ 𝓝ˢ t :=
  (monotone_nhdsSet (X := X)).map_inf_le s t
/-
**nhdsSet_iInter_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_iInter_le {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋂ i, s i) <= ⨅ i, 𝓝ˢ 
(s i)
参数：s : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_iInf_le`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [in
st : CompleteLattice α] {s : ι → α} [inst_1 : CompleteLattice β]   {f : α → β}, 
Monotone f…
· 使用定理 `monotone_nhdsSet`：monotone_nhdsSet : Monotone (𝓝ˢ : Set X -> Filter X)
-/
theorem nhdsSet_iInter_le {ι : Sort*} (s : ι → Set X) : 𝓝ˢ (⋂ i, s i) ≤ ⨅ i, 𝓝ˢ (s i) :=
  (monotone_nhdsSet (X := X)).map_iInf_le
/-
**nhdsSet_sInter_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_sInter_le (s : Set (Set X)) : 𝓝ˢ (⋂₀ s) <= ⨅ x in s, 𝓝ˢ x
参数：s : Set (Set X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_sInf_le`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLa
ttice α] [inst_1 : CompleteLattice β] {s : Set α} {f : α → β},   Monotone f → f 
(sInf s) ≤…
· 使用定理 `monotone_nhdsSet`：monotone_nhdsSet : Monotone (𝓝ˢ : Set X -> Filter X)
-/
theorem nhdsSet_sInter_le (s : Set (Set X)) : 𝓝ˢ (⋂₀ s) ≤ ⨅ x ∈ s, 𝓝ˢ x :=
  (monotone_nhdsSet (X := X)).map_sInf_le

variable (s) in
/-
**IsClosed.nhdsSet_le_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.nhdsSet_le_sup (h : IsClosed t) : 𝓝ˢ s <= 𝓝ˢ (s inter t) ⊔ 𝓟 (tᶜ)
参数：h : IsClosed t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `nhdsSet_union`：nhdsSet_union (s t : Set X) : 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ 
t
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `IsOpen.nhdsSet_eq`：∀ {X : Type u_2} [inst : TopologicalSpace X] {s : Set
 X}, IsOpen s → nhdsSet s = Filter.principal s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
theorem IsClosed.nhdsSet_le_sup (h : IsClosed t) : 𝓝ˢ s ≤ 𝓝ˢ (s ∩ t) ⊔ 𝓟 (tᶜ) :=
  calc
    𝓝ˢ s = 𝓝ˢ (s ∩ t ∪ s ∩ tᶜ) := by rw [Set.inter_union_compl s t]
    _ = 𝓝ˢ (s ∩ t) ⊔ 𝓝ˢ (s ∩ tᶜ) := by rw [nhdsSet_union]
    _ ≤ 𝓝ˢ (s ∩ t) ⊔ 𝓝ˢ (tᶜ) := by nth_grw 2 [inter_subset_right]
    _ = 𝓝ˢ (s ∩ t) ⊔ 𝓟 (tᶜ) := by rw [h.isOpen_compl.nhdsSet_eq]

variable (s) in
/-
**IsClosed.nhdsSet_le_sup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.nhdsSet_le_sup' (h : IsClosed t) : 𝓝ˢ s <= 𝓝ˢ (t inter s) ⊔ 𝓟 (tᶜ
)
参数：h : IsClosed t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `IsClosed.nhdsSet_le_sup`：IsClosed.nhdsSet_le_sup (h : IsClosed t) : 𝓝ˢ s
 <= 𝓝ˢ (s inter t) ⊔ 𝓟 (tᶜ)
-/
theorem IsClosed.nhdsSet_le_sup' (h : IsClosed t) :
    𝓝ˢ s ≤ 𝓝ˢ (t ∩ s) ⊔ 𝓟 (tᶜ) := by rw [Set.inter_comm]; exact h.nhdsSet_le_sup s
/-
**Filter.Eventually.eventually_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.eventually_nhdsSet {p : X -> Prop} (h : forallᶠ y in 𝓝ˢ 
s, p y) : forallᶠ y in 𝓝ˢ s, forallᶠ x in 𝓝 y, p x
参数：h : forallᶠ y in 𝓝ˢ s, p y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsSet_iff_forall`：eventually_nhdsSet_iff_forall {p : X -> P
rop} : (forallᶠ x in 𝓝ˢ s, p x) ↔ forall x, x in s -> forallᶠ y in 𝓝 x, p y
· 使用定理 `Filter.Eventually.eventually_nhds`：Filter.Eventually.eventually_nhds {p 
: X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p
 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Filter.Eventually.eventually_nhdsSet {p : X → Prop} (h : ∀ᶠ y in 𝓝ˢ s, p y) :
    ∀ᶠ y in 𝓝ˢ s, ∀ᶠ x in 𝓝 y, p x :=
  eventually_nhdsSet_iff_forall.mpr fun x x_in ↦
    (eventually_nhdsSet_iff_forall.mp h x x_in).eventually_nhds
/-
**Filter.Eventually.union_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.union_nhdsSet {p : X -> Prop} : (forallᶠ x in 𝓝ˢ (s unio
n t), p x) ↔ (forallᶠ x in 𝓝ˢ s, p x) ∧ forallᶠ x in 𝓝ˢ t, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_union`：nhdsSet_union (s t : Set X) : 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ 
t
· 使用定理 `Filter.eventually_sup`：eventually_sup {p : α -> Prop} {f g : Filter α} :
 (forallᶠ x in f ⊔ g, p x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.Eventually.union_nhdsSet {p : X → Prop} :
    (∀ᶠ x in 𝓝ˢ (s ∪ t), p x) ↔ (∀ᶠ x in 𝓝ˢ s, p x) ∧ ∀ᶠ x in 𝓝ˢ t, p x := by
  rw [nhdsSet_union, eventually_sup]
/-
**Filter.Eventually.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.union {p : X -> Prop} (hs : forallᶠ x in 𝓝ˢ s, p x) (ht 
: forallᶠ x in 𝓝ˢ t, p x) : forallᶠ x in 𝓝ˢ (s union t), p x
参数：hs : forallᶠ x in 𝓝ˢ s, p x；ht : forallᶠ x in 𝓝ˢ t, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Eventually.union_nhdsSet`：Filter.Eventually.union_nhdsSet {p : X 
-> Prop} : (forallᶠ x in 𝓝ˢ (s union t), p x) ↔ (forallᶠ x in 𝓝ˢ s, p x) ∧ foral
lᶠ x in 𝓝ˢ t, p x
-/
theorem Filter.Eventually.union {p : X → Prop} (hs : ∀ᶠ x in 𝓝ˢ s, p x) (ht : ∀ᶠ x in 𝓝ˢ t, p x) :
    ∀ᶠ x in 𝓝ˢ (s ∪ t), p x :=
  Filter.Eventually.union_nhdsSet.mpr ⟨hs, ht⟩
/-
**nhdsSet_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_iUnion {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋃ i, s i) = ⨆ i, 𝓝ˢ (s i
)
参数：s : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `sSup_iUnion`：sSup_iUnion (t : ι -> Set β) : sSup (⋃ i, t i) = ⨆ i, sSup 
(t i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsSet_iUnion {ι : Sort*} (s : ι → Set X) : 𝓝ˢ (⋃ i, s i) = ⨆ i, 𝓝ˢ (s i) := by
  simp only [nhdsSet, image_iUnion, sSup_iUnion (β := Filter X)]
/-
**eventually_nhdsSet_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhdsSet_iUnion {ι : Sort*} {s : ι -> Set X} {P : X -> Prop} : (
forallᶠ x in 𝓝ˢ (⋃ i, s i), P x) ↔ forall i, forallᶠ x in 𝓝ˢ (s i), P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_iUnion`：nhdsSet_iUnion {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋃ i, s
 i) = ⨆ i, 𝓝ˢ (s i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_nhdsSet_iUnion₂ {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {P : X → Prop} :
    (∀ᶠ x in 𝓝ˢ (⋃ (i) (_ : p i), s i), P x) ↔ ∀ i, p i → ∀ᶠ x in 𝓝ˢ (s i), P x := by
  simp only [nhdsSet_iUnion, eventually_iSup]
/-
**eventually_nhdsSet_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhdsSet_iUnion {ι : Sort*} {s : ι -> Set X} {P : X -> Prop} : (
forallᶠ x in 𝓝ˢ (⋃ i, s i), P x) ↔ forall i, forallᶠ x in 𝓝ˢ (s i), P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_iUnion`：nhdsSet_iUnion {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋃ i, s
 i) = ⨆ i, 𝓝ˢ (s i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_nhdsSet_iUnion {ι : Sort*} {s : ι → Set X} {P : X → Prop} :
    (∀ᶠ x in 𝓝ˢ (⋃ i, s i), P x) ↔ ∀ i, ∀ᶠ x in 𝓝ˢ (s i), P x := by
  simp only [nhdsSet_iUnion, eventually_iSup]
