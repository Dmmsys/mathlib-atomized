/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Defs.Sequences
public import Mathlib.Topology.UniformSpace.Closeds
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.Sequences

/-! # Hemicontinuity

This files provides basic facts about upper and lower hemicontinuity of correspondences
`f : α → Set β`.
-/

public section

open Set Filter Topology

variable {α β : Type*} [TopologicalSpace α]
variable {f g : α → Set β} {s : Set α} {x : α}

section facts

variable [TopologicalSpace β]

/-! ### Basic facts -/

/-
**upperHemicontinuousWithinAt_iff_forall_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousWithinAt_iff_forall_isOpen : UpperHemicontinuousWithinA
t f s x ↔ forall u, IsOpen u -> f x subseteq u -> forallᶠ x' in 𝓝[s] x, f x' sub
seteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuousWithinAt_iff`：upperHemicontinuousWithinAt_iff {f : α 
-> Set β} {s : Set α} {x : α} : UpperHemicontinuousWithinAt f s x ↔ forall t, t 
in 𝓝ˢ (f x) -> forall…
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
### Basic facts
-/
lemma upperHemicontinuousWithinAt_iff_forall_isOpen :
    UpperHemicontinuousWithinAt f s x ↔ ∀ u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝[s] x, f x' ⊆ u := by
  rw [upperHemicontinuousWithinAt_iff, hasBasis_nhdsSet _ |>.forall_iff ?mono]
  case mono => exact fun t₁ t₂ ht h ↦ h.mp <| .of_forall fun x' ↦ by gcongr
  simp only [and_imp]
  apply forall₂_congr
  simp +contextual [← subset_interior_iff_mem_nhdsSet, IsOpen.interior_eq]

alias ⟨UpperHemicontinuousWithinAt.forall_isOpen, UpperHemicontinuousWithinAt.of_forall_isOpen⟩ :=
  upperHemicontinuousWithinAt_iff_forall_isOpen
/-
**upperHemicontinuousOn_iff_forall_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousOn_iff_forall_isOpen : UpperHemicontinuousOn f s ↔ fora
ll x in s, forall u, IsOpen u -> f x subseteq u -> forallᶠ x' in 𝓝[s] x, f x' su
bseteq u
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
lemma upperHemicontinuousOn_iff_forall_isOpen :
    UpperHemicontinuousOn f s ↔ ∀ x ∈ s, ∀ u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝[s] x, f x' ⊆ u := by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuousOn.forall_isOpen, UpperHemicontinuousOn.of_forall_isOpen⟩ :=
  upperHemicontinuousOn_iff_forall_isOpen
/-
**upperHemicontinuousAt_iff_forall_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousAt_iff_forall_isOpen : UpperHemicontinuousAt f x ↔ fora
ll u, IsOpen u -> f x subseteq u -> forallᶠ x' in 𝓝 x, f x' subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用引理 `upperHemicontinuousWithinAt_iff_forall_isOpen`：upperHemicontinuousWithin
At_iff_forall_isOpen : UpperHemicontinuousWithinAt f s x ↔ forall u, IsOpen u ->
 f x subseteq u -> forallᶠ x' in 𝓝[…
-/
lemma upperHemicontinuousAt_iff_forall_isOpen :
    UpperHemicontinuousAt f x ↔ ∀ u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝 x, f x' ⊆ u := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_forall_isOpen (s := Set.univ)

alias ⟨UpperHemicontinuousAt.forall_isOpen, UpperHemicontinuousAt.of_forall_isOpen⟩ :=
  upperHemicontinuousAt_iff_forall_isOpen
/-
**upperHemicontinuous_iff_forall_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_iff_forall_isOpen : UpperHemicontinuous f ↔ forall x u
, IsOpen u -> f x subseteq u -> forallᶠ x' in 𝓝 x, f x' subseteq u
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperHemicontinuous_iff_forall_isOpen :
    UpperHemicontinuous f ↔ ∀ x u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝 x, f x' ⊆ u := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuous.forall_isOpen, UpperHemicontinuous.of_forall_isOpen⟩ :=
  upperHemicontinuous_iff_forall_isOpen

/-! ### Characterization in terms of preimages of intervals of sets -/

/-
**upperHemicontinuousWithinAt_iff_preimage_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousWithinAt_iff_preimage_Iic : UpperHemicontinuousWithinAt
 f s x ↔ forall u in 𝓝ˢ (f x), f ⁻¹' Iic u in 𝓝[s] x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `Filter.Eventually.mono._gcongr_1`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α}, (∀ (x : α), p x → q x) → (∀ᶠ (x : α) in f, p x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.Iic_subset_Iic._gcongr_3`：∀ {α : Type u_1} [inst : Preorder α] {a b 
: α}, a ≤ b → Set.Iic a ⊆ Set.Iic b
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Characterization in terms of preimages of intervals of sets
-/
lemma upperHemicontinuousWithinAt_iff_preimage_Iic :
    UpperHemicontinuousWithinAt f s x ↔ ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' Iic u ∈ 𝓝[s] x := by
  simp_rw [upperHemicontinuousWithinAt_iff]
  rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₁, hasBasis_nhdsSet (f x) |>.forall_iff ?h₂]
  case h₂ =>
    intro s t hst
    gcongr
  case h₁ =>
    intro s t hst
    gcongr
  refine forall₂_congr fun u ⟨hu, hfu⟩ ↦ ?_
  simp [hu.mem_nhdsSet, eventually_iff, Iic]
/-
**upperHemicontinuousAt_iff_preimage_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousAt_iff_preimage_Iic : UpperHemicontinuousAt f x ↔ foral
l u in 𝓝ˢ (f x), f ⁻¹' Iic u in 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用引理 `upperHemicontinuousWithinAt_iff_preimage_Iic`：upperHemicontinuousWithinA
t_iff_preimage_Iic : UpperHemicontinuousWithinAt f s x ↔ forall u in 𝓝ˢ (f x), f
 ⁻¹' Iic u in 𝓝[s] x
-/
lemma upperHemicontinuousAt_iff_preimage_Iic :
    UpperHemicontinuousAt f x ↔ ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' Iic u ∈ 𝓝 x := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_preimage_Iic (s := univ)
/-
**upperHemicontinuousOn_iff_preimage_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousOn_iff_preimage_Iic : UpperHemicontinuousOn f s ↔ foral
l x in s, forall u in 𝓝ˢ (f x), f ⁻¹' Iic u in 𝓝[s] x
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
lemma upperHemicontinuousOn_iff_preimage_Iic :
    UpperHemicontinuousOn f s ↔ ∀ x ∈ s, ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' Iic u ∈ 𝓝[s] x := by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_preimage_Iic]
/-
**upperHemicontinuous_iff_preimage_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_iff_preimage_Iic : UpperHemicontinuous f ↔ forall x, f
orall u in 𝓝ˢ (f x), f ⁻¹' Iic u in 𝓝 x
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperHemicontinuous_iff_preimage_Iic :
    UpperHemicontinuous f ↔ ∀ x, ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' Iic u ∈ 𝓝 x := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_preimage_Iic]

/-- A correspondence `f : α → Set β` is upper hemicontinuous if and only if its *upper inverse*
(i.e., `u : Set β ↦ f ⁻¹' (Iic u)`, note that `f ⁻¹' (Iic u) = {x | f x ⊆ u}`) sends open sets
to open sets. -/
/-
**upperHemicontinuous_iff_isOpen_preimage_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_iff_isOpen_preimage_Iic : UpperHemicontinuous f ↔ fora
ll u, IsOpen u -> IsOpen (f ⁻¹' Iic u)
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
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.Iic_subset_Iic._gcongr_3`：∀ {α : Type u_1} [inst : Preorder α] {a b 
: α}, a ≤ b → Set.Iic a ⊆ Set.Iic b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A correspondence `f : α → Set β` is upper hemicontinuous if and only if its *upp
er inverse*
(i.e., `u : Set β ↦ f ⁻¹' (Iic u)`, note that `f ⁻¹' (Iic u) = {x | f x ⊆ u}`) s
ends open sets
to open sets.
-/
lemma upperHemicontinuous_iff_isOpen_preimage_Iic :
    UpperHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen (f ⁻¹' Iic u) := by
  simp_rw [upperHemicontinuous_iff_preimage_Iic, isOpen_iff_mem_nhds (s := f ⁻¹' Iic _)]
  conv =>
    enter [1, x]
    rw [hasBasis_nhdsSet (f x) |>.forall_iff fun s t hst ↦ by gcongr]
  simp [forall_comm (α := α)]

/-- A correspondence `f : α → Set β` is upper hemicontinuous if and only if its *lower inverse*
(i.e., `u : Set β ↦ (f ⁻¹' (Iic uᶜ))ᶜ`, note that `f ⁻¹' (Iic u) = {x | (f x ∩ u).Nonempty}`)
sends closed sets to closed sets. -/
/-
**upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl : UpperHemiconti
nuous f ↔ forall u, IsClosed u -> IsClosed (f ⁻¹' Iic uᶜ)ᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用引理 `upperHemicontinuous_iff_isOpen_preimage_Iic`：upperHemicontinuous_iff_isO
pen_preimage_Iic : UpperHemicontinuous f ↔ forall u, IsOpen u -> IsOpen (f ⁻¹' I
ic u)

--- 原说明 ---
A correspondence `f : α → Set β` is upper hemicontinuous if and only if its *low
er inverse*
(i.e., `u : Set β ↦ (f ⁻¹' (Iic uᶜ))ᶜ`, note that `f ⁻¹' (Iic u) = {x | (f x ∩ u
).Nonempty}`)
sends closed sets to closed sets.
-/
lemma upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl :
    UpperHemicontinuous f ↔ ∀ u, IsClosed u → IsClosed (f ⁻¹' Iic uᶜ)ᶜ := by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact upperHemicontinuous_iff_isOpen_preimage_Iic
/-
**isClosedMap_iff_upperHemicontinuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosedMap_iff_upperHemicontinuous {f : α -> β} : IsClosedMap f ↔ UpperHe
micontinuous (f ⁻¹' {·})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isClosedMap_iff_kernImage`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f ↔ ∀ {u
 : Set X}, IsOp…
· 使用引理 `upperHemicontinuous_iff_isOpen_preimage_Iic`：upperHemicontinuous_iff_isO
pen_preimage_Iic : UpperHemicontinuous f ↔ forall u, IsOpen u -> IsOpen (f ⁻¹' I
ic u)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClosedMap_iff_upperHemicontinuous {f : α → β} :
    IsClosedMap f ↔ UpperHemicontinuous (f ⁻¹' {·}) := by
  rw [isClosedMap_iff_kernImage, upperHemicontinuous_iff_isOpen_preimage_Iic]
  aesop
/-
**lowerHemicontinuous_iff_isOpen_inter_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuous_iff_isOpen_inter_nonempty : LowerHemicontinuous f ↔ fo
rall u, IsOpen u -> IsOpen {x | (f x inter u).Nonempty}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lowerHemicontinuous_iff_isOpen_inter_nonempty :
    LowerHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen {x | (f x ∩ u).Nonempty} := by
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff, isOpen_iff_mem_nhds,
    forall_comm (α := α), mem_ofPred, Filter.Eventually]

/-- A correspondence `f : α → Set β` is lower hemicontinuous if and only if its *lower inverse*
(i.e., `u : Set β ↦ (f ⁻¹' (Iic uᶜ))ᶜ`, note that `f ⁻¹' (Iic u) = {x | (f x ∩ u).Nonempty}`)
sends open sets to open sets. -/
/-
**lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl : LowerHemicontinu
ous f ↔ forall u, IsOpen u -> IsOpen (f ⁻¹' Iic uᶜ)ᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `lowerHemicontinuous_iff_isOpen_inter_nonempty`：lowerHemicontinuous_iff_i
sOpen_inter_nonempty : LowerHemicontinuous f ↔ forall u, IsOpen u -> IsOpen {x |
 (f x inter u).Nonempty}

--- 原说明 ---
A correspondence `f : α → Set β` is lower hemicontinuous if and only if its *low
er inverse*
(i.e., `u : Set β ↦ (f ⁻¹' (Iic uᶜ))ᶜ`, note that `f ⁻¹' (Iic u) = {x | (f x ∩ u
).Nonempty}`)
sends open sets to open sets.
-/
lemma lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl :
    LowerHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen (f ⁻¹' Iic uᶜ)ᶜ := by
  have (u : Set β) : (f ⁻¹' (Iic uᶜ))ᶜ = {x | (f x ∩ u).Nonempty} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]
  simpa [this] using lowerHemicontinuous_iff_isOpen_inter_nonempty

/-- A correspondence `f : α → Set β` is lower hemicontinuous if and only if its *upper inverse*
(i.e., `u : Set β ↦ f ⁻¹' (Iic u)`, note that `f ⁻¹' (Iic u) = {x | f x ⊆ u}`) sends closed sets
to closed sets. -/
/-
**lowerHemicontinuous_iff_isClosed_preimage_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuous_iff_isClosed_preimage_Iic : LowerHemicontinuous f ↔ fo
rall u, IsClosed u -> IsClosed (f ⁻¹' Iic u)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用引理 `lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl`：lowerHemicontin
uous_iff_isOpen_compl_preimage_Iic_compl : LowerHemicontinuous f ↔ forall u, IsO
pen u -> IsOpen (f ⁻¹' Iic uᶜ)ᶜ

--- 原说明 ---
A correspondence `f : α → Set β` is lower hemicontinuous if and only if its *upp
er inverse*
(i.e., `u : Set β ↦ f ⁻¹' (Iic u)`, note that `f ⁻¹' (Iic u) = {x | f x ⊆ u}`) s
ends closed sets
to closed sets.
-/
lemma lowerHemicontinuous_iff_isClosed_preimage_Iic :
    LowerHemicontinuous f ↔ ∀ u, IsClosed u → IsClosed (f ⁻¹' Iic u) := by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl
/-
**isOpenMap_iff_lowerHemicontinuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOpenMap_iff_lowerHemicontinuous {f : α -> β} : IsOpenMap f ↔ LowerHemico
ntinuous (f ⁻¹' {·})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpenMap_iff_kernImage`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ {u : S
et X}, IsClos…
· 使用引理 `lowerHemicontinuous_iff_isClosed_preimage_Iic`：lowerHemicontinuous_iff_i
sClosed_preimage_Iic : LowerHemicontinuous f ↔ forall u, IsClosed u -> IsClosed 
(f ⁻¹' Iic u)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isOpenMap_iff_lowerHemicontinuous {f : α → β} :
    IsOpenMap f ↔ LowerHemicontinuous (f ⁻¹' {·}) := by
  rw [isOpenMap_iff_kernImage, lowerHemicontinuous_iff_isClosed_preimage_Iic]
  aesop

section singleton_maps

/-! ### Singleton maps

Functions `f : α → β` are continuous if and only if they are lower hemicontinuous if and only if
they are upper hemicontinuous. This is in the sense that the map `g : α → Set β` given by
`g x = {f x}` is both lower or upper hemicontinuous.

This section also provides dot notation to access this fact for continuous functions.
-/

variable {f : α → β} {s : Set α} {x : α}

/-
**upperHemicontinuous_singleton_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_singleton_id : UpperHemicontinuous ({·} : α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma upperHemicontinuous_singleton_id : UpperHemicontinuous ({·} : α → Set α) := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff]

@[simp]
/-
**upperHemicontinuousWithinAt_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousWithinAt_singleton_iff : UpperHemicontinuousWithinAt ({
f ·}) s x ↔ ContinuousWithinAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `UpperHemicontinuousWithinAt.comp`：UpperHemicontinuousWithinAt.comp (hf :
 UpperHemicontinuousWithinAt f s (g c)) (hg : ContinuousWithinAt g t c) (hg' : M
apsTo g t s) : UpperHe…
· 使用定理 `UpperHemicontinuous.upperHemicontinuousWithinAt`：UpperHemicontinuous.upp
erHemicontinuousWithinAt (h : UpperHemicontinuous f) (s : Set α) (x : α) : Upper
HemicontinuousWithinAt f s x
· 使用引理 `upperHemicontinuous_singleton_id`：upperHemicontinuous_singleton_id : Upp
erHemicontinuous ({·} : α -> Set α)
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
lemma upperHemicontinuousWithinAt_singleton_iff :
    UpperHemicontinuousWithinAt ({f ·}) s x ↔ ContinuousWithinAt f s x := by
  refine ⟨?_, fun hf ↦ upperHemicontinuous_singleton_id.upperHemicontinuousWithinAt _ _ |>.comp hf
    (mapsTo_image _ _)⟩
  simp only [upperHemicontinuousWithinAt_iff, nhdsSet_singleton, ContinuousWithinAt,
    tendsto_iff_forall_eventually_mem]
  intro h t ht
  filter_upwards [h t ht] with x
  exact mem_of_mem_nhds

alias ⟨_, ContinuousWithinAt.upperHemicontinuousWithinAt⟩ :=
  upperHemicontinuousWithinAt_singleton_iff

@[simp]
/-
**upperHemicontinuousAt_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousAt_singleton_iff : UpperHemicontinuousAt ({f ·}) x ↔ Co
ntinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperHemicontinuousAt_singleton_iff :
    UpperHemicontinuousAt ({f ·}) x ↔ ContinuousAt f x := by
  simp [← upperHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

alias ⟨_, ContinuousAt.upperHemicontinuousAt⟩ := upperHemicontinuousAt_singleton_iff

@[simp]
/-
**upperHemicontinuousOn_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousOn_singleton_iff : UpperHemicontinuousOn ({f ·}) s ↔ Co
ntinuousOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用引理 `upperHemicontinuousWithinAt_singleton_iff`：upperHemicontinuousWithinAt_s
ingleton_iff : UpperHemicontinuousWithinAt ({f ·}) s x ↔ ContinuousWithinAt f s 
x
-/
lemma upperHemicontinuousOn_singleton_iff :
    UpperHemicontinuousOn ({f ·}) s ↔ ContinuousOn f s :=
  forall₂_congr <| fun _ _ ↦ upperHemicontinuousWithinAt_singleton_iff

alias ⟨_, ContinuousOn.upperHemicontinuousOn⟩ := upperHemicontinuousOn_singleton_iff

@[simp]
/-
**upperHemicontinuous_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_singleton_iff : UpperHemicontinuous ({f ·}) ↔ Continuo
us f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperHemicontinuous_singleton_iff :
    UpperHemicontinuous ({f ·}) ↔ Continuous f := by
  simp [← upperHemicontinuousOn_univ_iff]

alias ⟨_, Continuous.upperHemicontinuous⟩ := upperHemicontinuous_singleton_iff
/-
**lowerHemicontinuous_singleton_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuous_singleton_id : LowerHemicontinuous ({·} : α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_inter_nonempty`：singleton_inter_nonempty : ({a} inter s).N
onempty ↔ a in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma lowerHemicontinuous_singleton_id : LowerHemicontinuous ({·} : α → Set α) := by
  intro x t ⟨ht, hne⟩
  filter_upwards [ht.mem_nhds (Set.singleton_inter_nonempty.mp hne)] with x' hx'
  exact ⟨ht, Set.singleton_inter_nonempty.mpr hx'⟩

@[simp]
/-
**lowerHemicontinuousWithinAt_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousWithinAt_singleton_iff : LowerHemicontinuousWithinAt ({
f ·}) s x ↔ ContinuousWithinAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LowerHemicontinuousWithinAt.comp`：LowerHemicontinuousWithinAt.comp (hf :
 LowerHemicontinuousWithinAt f s (g x)) (hg : ContinuousWithinAt g t x) (hg' : M
apsTo g t s) : LowerHe…
· 使用定理 `LowerHemicontinuous.lowerHemicontinuousWithinAt`：LowerHemicontinuous.low
erHemicontinuousWithinAt (h : LowerHemicontinuous f) (s : Set α) (x : α) : Lower
HemicontinuousWithinAt f s x
· 使用引理 `lowerHemicontinuous_singleton_id`：lowerHemicontinuous_singleton_id : Low
erHemicontinuous ({·} : α -> Set α)
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
lemma lowerHemicontinuousWithinAt_singleton_iff :
    LowerHemicontinuousWithinAt ({f ·}) s x ↔ ContinuousWithinAt f s x := by
  refine ⟨?_, fun hf ↦ (lowerHemicontinuous_singleton_id.lowerHemicontinuousWithinAt _ _).comp
    hf (mapsTo_image _ _)⟩
  simp only [lowerHemicontinuousWithinAt_iff, Set.singleton_inter_nonempty,
    ContinuousWithinAt, tendsto_iff_forall_eventually_mem]
  intro h t ht
  obtain ⟨u, hut, huo, hux⟩ := mem_nhds_iff.mp ht
  exact (h u huo hux).mono fun _ hx' ↦ hut hx'

alias ⟨_, ContinuousWithinAt.lowerHemicontinuousWithinAt⟩ :=
  lowerHemicontinuousWithinAt_singleton_iff

@[simp]
/-
**lowerHemicontinuousAt_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousAt_singleton_iff : LowerHemicontinuousAt ({f ·}) x ↔ Co
ntinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lowerHemicontinuousAt_singleton_iff : LowerHemicontinuousAt ({f ·}) x ↔ ContinuousAt f x := by
  simp [← lowerHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

alias ⟨_, ContinuousAt.lowerHemicontinuousAt⟩ := lowerHemicontinuousAt_singleton_iff

@[simp]
/-
**lowerHemicontinuousOn_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousOn_singleton_iff : LowerHemicontinuousOn ({f ·}) s ↔ Co
ntinuousOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用引理 `lowerHemicontinuousWithinAt_singleton_iff`：lowerHemicontinuousWithinAt_s
ingleton_iff : LowerHemicontinuousWithinAt ({f ·}) s x ↔ ContinuousWithinAt f s 
x
-/
lemma lowerHemicontinuousOn_singleton_iff : LowerHemicontinuousOn ({f ·}) s ↔ ContinuousOn f s :=
  forall₂_congr <| fun _ _ ↦ lowerHemicontinuousWithinAt_singleton_iff

alias ⟨_, ContinuousOn.lowerHemicontinuousOn⟩ := lowerHemicontinuousOn_singleton_iff

@[simp]
/-
**lowerHemicontinuous_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuous_singleton_iff : LowerHemicontinuous ({f ·}) ↔ Continuo
us f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lowerHemicontinuous_singleton_iff : LowerHemicontinuous ({f ·}) ↔ Continuous f := by
  simp [← lowerHemicontinuousOn_univ_iff]

alias ⟨_, Continuous.lowerHemicontinuous⟩ := lowerHemicontinuous_singleton_iff

end singleton_maps

/-! ### Union and intersection, and post-composition with the preimage map -/

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {f g : α → Set β} {s : Set α} {x : α}

/-- Pointwise unions of upper hemicontinuous maps are upper hemicontinuous. -/
/-
**UpperHemicontinuousWithinAt.union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousWithinAt.union (hf : UpperHemicontinuousWithinAt f s x)
 (hg : UpperHemicontinuousWithinAt g s x) : UpperHemicontinuousWithinAt (fun x =
> f x union g x) s x
参数：hf : UpperHemicontinuousWithinAt f s x；hg : UpperHemicontinuousWithinAt g s x
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuousWithinAt_iff`：upperHemicontinuousWithinAt_iff {f : α 
-> Set β} {s : Set α} {x : α} : UpperHemicontinuousWithinAt f s x ↔ forall t, t 
in 𝓝ˢ (f x) -> forall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhdsSet_union`：nhdsSet_union (s t : Set X) : 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ 
t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Pointwise unions of upper hemicontinuous maps are upper hemicontinuous.
-/
lemma UpperHemicontinuousWithinAt.union (hf : UpperHemicontinuousWithinAt f s x)
    (hg : UpperHemicontinuousWithinAt g s x) :
    UpperHemicontinuousWithinAt (fun x ↦ f x ∪ g x) s x := by
  rw [upperHemicontinuousWithinAt_iff] at hf hg ⊢
  aesop

/-- Pointwise unions of upper hemicontinuous maps are upper hemicontinuous. -/
/-
**UpperHemicontinuousOn.union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousOn.union (hf : UpperHemicontinuousOn f s) (hg : UpperHe
micontinuousOn g s) : UpperHemicontinuousOn (fun x => f x union g x) s
参数：hf : UpperHemicontinuousOn f s；hg : UpperHemicontinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuousOn_iff`：upperHemicontinuousOn_iff {f : α -> Set β} {s
 : Set α} : UpperHemicontinuousOn f s ↔ forall x in s, UpperHemicontinuousWithin
At f s x
· 使用引理 `UpperHemicontinuousWithinAt.union`：UpperHemicontinuousWithinAt.union (hf
 : UpperHemicontinuousWithinAt f s x) (hg : UpperHemicontinuousWithinAt g s x) :
 UpperHemicontinuousWit…

--- 原说明 ---
Pointwise unions of upper hemicontinuous maps are upper hemicontinuous.
-/
lemma UpperHemicontinuousOn.union (hf : UpperHemicontinuousOn f s)
    (hg : UpperHemicontinuousOn g s) : UpperHemicontinuousOn (fun x ↦ f x ∪ g x) s := by
  rw [upperHemicontinuousOn_iff] at hf hg ⊢
  exact fun x hx ↦ (hf x hx).union (hg x hx)

/-- Pointwise unions of upper hemicontinuous maps are upper hemicontinuous. -/
/-
**UpperHemicontinuousAt.union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousAt.union (hf : UpperHemicontinuousAt f x) (hg : UpperHe
micontinuousAt g x) : UpperHemicontinuousAt (fun x => f x union g x) x
参数：hf : UpperHemicontinuousAt f x；hg : UpperHemicontinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `upperHemicontinuousWithinAt_univ_iff`：upperHemicontinuousWithinAt_univ_i
ff : UpperHemicontinuousWithinAt f univ x ↔ UpperHemicontinuousAt f x
· 使用引理 `UpperHemicontinuousWithinAt.union`：UpperHemicontinuousWithinAt.union (hf
 : UpperHemicontinuousWithinAt f s x) (hg : UpperHemicontinuousWithinAt g s x) :
 UpperHemicontinuousWit…

--- 原说明 ---
Pointwise unions of upper hemicontinuous maps are upper hemicontinuous.
-/
lemma UpperHemicontinuousAt.union (hf : UpperHemicontinuousAt f x)
    (hg : UpperHemicontinuousAt g x) :
    UpperHemicontinuousAt (fun x ↦ f x ∪ g x) x := by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf hg ⊢
  exact hf.union hg

/-- Pointwise unions of upper hemicontinuous maps are upper hemicontinuous. -/
/-
**UpperHemicontinuous.union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuous.union (hf : UpperHemicontinuous f) (hg : UpperHemicont
inuous g) : UpperHemicontinuous (fun x => f x union g x)
参数：hf : UpperHemicontinuous f；hg : UpperHemicontinuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuous_iff`：upperHemicontinuous_iff {f : α -> Set β} : Uppe
rHemicontinuous f ↔ forall x, UpperHemicontinuousAt f x
· 使用引理 `UpperHemicontinuousAt.union`：UpperHemicontinuousAt.union (hf : UpperHemi
continuousAt f x) (hg : UpperHemicontinuousAt g x) : UpperHemicontinuousAt (fun 
x => f x union g …

--- 原说明 ---
Pointwise unions of upper hemicontinuous maps are upper hemicontinuous.
-/
lemma UpperHemicontinuous.union (hf : UpperHemicontinuous f) (hg : UpperHemicontinuous g) :
    UpperHemicontinuous (fun x ↦ f x ∪ g x) := by
  rw [upperHemicontinuous_iff] at hf hg ⊢
  exact fun x ↦ (hf x).union (hg x)

/-- The pointwise intersection of an upper hemicontinuous function with a fixed closed set is
upper hemicontinuous. -/
/-
**UpperHemicontinuousWithinAt.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousWithinAt.inter (hf : UpperHemicontinuousWithinAt f s x)
 {u : Set β} (hu : IsClosed u) : UpperHemicontinuousWithinAt (fun x => f x inter
 u) s x
参数：hf : UpperHemicontinuousWithinAt f s x；hu : IsClosed u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuousWithinAt_iff_forall_isOpen`：upperHemicontinuousWithin
At_iff_forall_isOpen : UpperHemicontinuousWithinAt f s x ↔ forall u, IsOpen u ->
 f x subseteq u -> forallᶠ x' in 𝓝[…
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ

--- 原说明 ---
The pointwise intersection of an upper hemicontinuous function with a fixed clos
ed set is
upper hemicontinuous.
-/
lemma UpperHemicontinuousWithinAt.inter (hf : UpperHemicontinuousWithinAt f s x)
    {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuousWithinAt (fun x ↦ f x ∩ u) s x := by
  rw [upperHemicontinuousWithinAt_iff_forall_isOpen] at hf ⊢
  intro t ht_open ht
  specialize hf (t ∪ uᶜ) (ht_open.union hu.isOpen_compl) (by grind)
  grind

/-- The pointwise intersection of an upper hemicontinuous function with a fixed closed set is
upper hemicontinuous. -/
/-
**UpperHemicontinuousOn.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousOn.inter (hf : UpperHemicontinuousOn f s) {u : Set β} (
hu : IsClosed u) : UpperHemicontinuousOn (fun x => f x inter u) s
参数：hf : UpperHemicontinuousOn f s；hu : IsClosed u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuousOn_iff`：upperHemicontinuousOn_iff {f : α -> Set β} {s
 : Set α} : UpperHemicontinuousOn f s ↔ forall x in s, UpperHemicontinuousWithin
At f s x
· 使用引理 `UpperHemicontinuousWithinAt.inter`：UpperHemicontinuousWithinAt.inter (hf
 : UpperHemicontinuousWithinAt f s x) {u : Set β} (hu : IsClosed u) : UpperHemic
ontinuousWithinAt (fun …

--- 原说明 ---
The pointwise intersection of an upper hemicontinuous function with a fixed clos
ed set is
upper hemicontinuous.
-/
lemma UpperHemicontinuousOn.inter (hf : UpperHemicontinuousOn f s) {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuousOn (fun x ↦ f x ∩ u) s := by
  rw [upperHemicontinuousOn_iff] at hf ⊢
  exact (hf · · |>.inter hu)

/-- The pointwise intersection of an upper hemicontinuous function with a fixed closed set is
upper hemicontinuous. -/
/-
**UpperHemicontinuousAt.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousAt.inter (hf : UpperHemicontinuousAt f x) {u : Set β} (
hu : IsClosed u) : UpperHemicontinuousAt (fun x => f x inter u) x
参数：hf : UpperHemicontinuousAt f x；hu : IsClosed u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `upperHemicontinuousWithinAt_univ_iff`：upperHemicontinuousWithinAt_univ_i
ff : UpperHemicontinuousWithinAt f univ x ↔ UpperHemicontinuousAt f x
· 使用引理 `UpperHemicontinuousWithinAt.inter`：UpperHemicontinuousWithinAt.inter (hf
 : UpperHemicontinuousWithinAt f s x) {u : Set β} (hu : IsClosed u) : UpperHemic
ontinuousWithinAt (fun …

--- 原说明 ---
The pointwise intersection of an upper hemicontinuous function with a fixed clos
ed set is
upper hemicontinuous.
-/
lemma UpperHemicontinuousAt.inter (hf : UpperHemicontinuousAt f x) {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuousAt (fun x ↦ f x ∩ u) x := by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hf.inter hu

/-- The pointwise intersection of an upper hemicontinuous function with a fixed closed set is
upper hemicontinuous. -/
/-
**UpperHemicontinuous.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuous.inter (hf : UpperHemicontinuous f) {u : Set β} (hu : I
sClosed u) : UpperHemicontinuous (fun x => f x inter u)
参数：hf : UpperHemicontinuous f；hu : IsClosed u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuous_iff`：upperHemicontinuous_iff {f : α -> Set β} : Uppe
rHemicontinuous f ↔ forall x, UpperHemicontinuousAt f x
· 使用引理 `UpperHemicontinuousAt.inter`：UpperHemicontinuousAt.inter (hf : UpperHemi
continuousAt f x) {u : Set β} (hu : IsClosed u) : UpperHemicontinuousAt (fun x =
> f x inter u) x

--- 原说明 ---
The pointwise intersection of an upper hemicontinuous function with a fixed clos
ed set is
upper hemicontinuous.
-/
lemma UpperHemicontinuous.inter (hf : UpperHemicontinuous f) {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuous (fun x ↦ f x ∩ u) := by
  rw [upperHemicontinuous_iff] at hf ⊢
  exact fun x ↦ (hf x).inter hu

section Inducing

variable {γ : Type*} [TopologicalSpace γ] {i : γ → β}

/-- Post-composition with the preimage of an inducing function whose range is closed preserves
upper hemicontinuity. -/
/-
**UpperHemicontinuousWithinAt.isInducing_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousWithinAt.isInducing_comp (hf : UpperHemicontinuousWithi
nAt f s x) (hi : IsInducing i) (h_cl : IsClosed (range i)) : UpperHemicontinuous
WithinAt (fun x => i ⁻¹' (f x)) s x
参数：hf : UpperHemicontinuousWithinAt f s x；hi : IsInducing i；h_cl : IsClosed (ran
ge i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHemicontinuousWithinAt.of_forall_isOpen`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace α] {f : α → Set β} {s : Set α} {x : α}   [inst_1 
: TopologicalSpace β],   (∀ (u : S…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_inter_range`：preimage_inter_range {f : α -> β} {s : Set β} 
: f ⁻¹' (s inter range f) = f ⁻¹' s
· 使用定理 `Set.preimage_subset_preimage_iff`：preimage_subset_preimage_iff {s t : Se
t α} {f : β -> α} (hs : s subseteq range f) : f ⁻¹' s subseteq f ⁻¹' t ↔ s subse
teq t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `UpperHemicontinuousWithinAt.forall_isOpen`：∀ {α : Type u_1} {β : Type u_
2} [inst : TopologicalSpace α] {f : α → Set β} {s : Set α} {x : α}   [inst_1 : T
opologicalSpace β],   UpperHemi…
· 使用引理 `UpperHemicontinuousWithinAt.inter`：UpperHemicontinuousWithinAt.inter (hf
 : UpperHemicontinuousWithinAt f s x) {u : Set β} (hu : IsClosed u) : UpperHemic
ontinuousWithinAt (fun …

--- 原说明 ---
Post-composition with the preimage of an inducing function whose range is closed
 preserves
upper hemicontinuity.
-/
lemma UpperHemicontinuousWithinAt.isInducing_comp (hf : UpperHemicontinuousWithinAt f s x)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuousWithinAt (fun x ↦ i ⁻¹' (f x)) s x := by
  refine .of_forall_isOpen fun u hu hifu ↦ ?_
  obtain ⟨v, hv, rfl⟩ := hi.isOpen_iff.mp hu
  simp_rw [← preimage_inter_range (s := f _), preimage_subset_preimage_iff inter_subset_right]
    at hifu ⊢
  exact hf.inter h_cl |>.forall_isOpen v hv hifu

/-- Post-composition with the preimage of an inducing function whose range is closed preserves
upper hemicontinuity. -/
/-
**UpperHemicontinuousOn.isInducing_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousOn.isInducing_comp (hf : UpperHemicontinuousOn f s) (hi
 : IsInducing i) (h_cl : IsClosed (range i)) : UpperHemicontinuousOn (fun x => i
 ⁻¹' (f x)) s
参数：hf : UpperHemicontinuousOn f s；hi : IsInducing i；h_cl : IsClosed (range i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuousOn_iff`：upperHemicontinuousOn_iff {f : α -> Set β} {s
 : Set α} : UpperHemicontinuousOn f s ↔ forall x in s, UpperHemicontinuousWithin
At f s x
· 使用引理 `UpperHemicontinuousWithinAt.isInducing_comp`：UpperHemicontinuousWithinAt
.isInducing_comp (hf : UpperHemicontinuousWithinAt f s x) (hi : IsInducing i) (h
_cl : IsClosed (range i)) : Upper…

--- 原说明 ---
Post-composition with the preimage of an inducing function whose range is closed
 preserves
upper hemicontinuity.
-/
lemma UpperHemicontinuousOn.isInducing_comp (hf : UpperHemicontinuousOn f s)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuousOn (fun x ↦ i ⁻¹' (f x)) s := by
  rw [upperHemicontinuousOn_iff] at hf ⊢
  exact fun x hx ↦ (hf x hx).isInducing_comp hi h_cl

/-- Post-composition with the preimage of an inducing function whose range is closed preserves
upper hemicontinuity. -/
/-
**UpperHemicontinuousAt.isInducing_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousAt.isInducing_comp (hf : UpperHemicontinuousAt f x) (hi
 : IsInducing i) (h_cl : IsClosed (range i)) : UpperHemicontinuousAt (fun x => i
 ⁻¹' (f x)) x
参数：hf : UpperHemicontinuousAt f x；hi : IsInducing i；h_cl : IsClosed (range i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UpperHemicontinuousWithinAt.isInducing_comp`：UpperHemicontinuousWithinAt
.isInducing_comp (hf : UpperHemicontinuousWithinAt f s x) (hi : IsInducing i) (h
_cl : IsClosed (range i)) : Upper…
· 使用定理 `UpperHemicontinuousAt.upperHemicontinuousWithinAt`：UpperHemicontinuousAt
.upperHemicontinuousWithinAt (s : Set α) (h : UpperHemicontinuousAt f x) : Upper
HemicontinuousWithinAt f s x

--- 原说明 ---
Post-composition with the preimage of an inducing function whose range is closed
 preserves
upper hemicontinuity.
-/
lemma UpperHemicontinuousAt.isInducing_comp (hf : UpperHemicontinuousAt f x)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuousAt (fun x ↦ i ⁻¹' (f x)) x := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    hf.upperHemicontinuousWithinAt (s := Set.univ) |>.isInducing_comp hi h_cl

/-- Post-composition with the preimage of an inducing function whose range is closed preserves
upper hemicontinuity. -/
/-
**UpperHemicontinuous.isInducing_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuous.isInducing_comp (hf : UpperHemicontinuous f) (hi : IsI
nducing i) (h_cl : IsClosed (range i)) : UpperHemicontinuous (fun x => i ⁻¹' (f 
x))
参数：hf : UpperHemicontinuous f；hi : IsInducing i；h_cl : IsClosed (range i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuous_iff`：upperHemicontinuous_iff {f : α -> Set β} : Uppe
rHemicontinuous f ↔ forall x, UpperHemicontinuousAt f x
· 使用引理 `UpperHemicontinuousAt.isInducing_comp`：UpperHemicontinuousAt.isInducing_
comp (hf : UpperHemicontinuousAt f x) (hi : IsInducing i) (h_cl : IsClosed (rang
e i)) : UpperHemicontinuous…

--- 原说明 ---
Post-composition with the preimage of an inducing function whose range is closed
 preserves
upper hemicontinuity.
-/
lemma UpperHemicontinuous.isInducing_comp (hf : UpperHemicontinuous f)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuous (fun x ↦ i ⁻¹' (f x)) := by
  rw [upperHemicontinuous_iff] at hf ⊢
  exact fun x ↦ (hf x).isInducing_comp hi h_cl

end Inducing

/-- Upper hemicontinuous functions always have closed domain.

The more general fact is that if `f` is upper hemicontinuous at `x₀` within `s`, and if
`x₀` is a cluster point of `s ∩ {x | (f x).Nonempty}`, then `(f x₀).Nonempty`. -/
/-
**UpperHemicontinuous.isClosed_domain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuous.isClosed_domain (hf : UpperHemicontinuous f) : IsClose
d {x | (f x).Nonempty}
参数：hf : UpperHemicontinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsSet_empty`：nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
Upper hemicontinuous functions always have closed domain.

The more general fact is that if `f` is upper hemicontinuous at `x₀` within `s`,
 and if
`x₀` is a cluster point of `s ∩ {x | (f x).Nonempty}`, then `(f x₀).Nonempty`.
-/
lemma UpperHemicontinuous.isClosed_domain (hf : UpperHemicontinuous f) :
    IsClosed {x | (f x).Nonempty} := by
  simp only [← isOpen_compl_iff, compl_ofPred, not_nonempty_iff_eq_empty, isOpen_iff_mem_nhds]
  intro x (hx : f x = ∅)
  simp_rw [upperHemicontinuous_iff, upperHemicontinuousAt_iff] at hf
  simpa [hx, empty_mem_iff_bot, nhdsSet_eq_bot_iff] using! hf x ∅

/-! ### Sequential characterizations -/

/-- **Sequential characterization of upper hemicontinuity**:
A set-valued function `f : α → Set β` is upper hemicontinuous at `x₀ : α` if for every pair
of sequences `x : ℕ → α` and `y : ℕ → β` such that `x` tends to `x₀` and `y n ∈ f (x n)` and
`y` tends to `y₀ : β`, then `y₀ ∈ f x₀`. This requires that there is some (sequentially) compact
set containing all `f x'` for `x'` sufficiently close to `x`.

This is a partial converse of `UpperHemicontinuousAt.mem_of_tendsto`. -/
/-
**UpperHemicontinuousAt.of_sequences** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousAt.of_sequences {x₀ : α} [(𝓝 x₀).IsCountablyGenerated] 
{K : Set β} (hK : IsSeqCompact K) (hf : forallᶠ x in 𝓝 x₀, f x subseteq K) (h : 
forall x : Nat -> α, Tendsto x atTop (𝓝 x₀) -> forall y : Nat -> β, (forall n, y
 n in f (x n)) -> forall y₀, Tendsto y atTop (𝓝 y₀) -> y₀ in f x₀) : UpperHemico
ntinuousAt f x₀
参数：𝓝 x₀；hK : IsSeqCompact K；hf : forallᶠ x in 𝓝 x₀, f x subseteq K；h : forall x 
: Nat -> α, Tendsto x atTop (𝓝 x₀) -> forall y : Nat -> β, (forall n, y n in f (
x n)) -> forall y₀, Tendsto y atTop (𝓝 y₀) -> y₀ in f x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHemicontinuousAt.of_frequently`：∀ {α : Type u_1} {β : Type u_2} [in
st : TopologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → Set β} {x : α}, 
  (∀ (t : Set β), IsClose…
· 使用定理 `Filter.exists_seq_forall_of_frequently`：exists_seq_forall_of_frequently 
{ι : Type*} {l : Filter ι} {p : ι -> Prop} [l.IsCountablyGenerated] (h : existsᶠ
 n in l, p n) : exists ns : …
· 使用定理 `IsSeqCompact.subseq_of_frequently_in`：IsSeqCompact.subseq_of_frequently_
in {s : Set X} (hs : IsSeqCompact s) {x : Nat -> X} (hx : existsᶠ n in atTop, x 
n in s) : exists a in s, e…
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
**Sequential characterization of upper hemicontinuity**:
A set-valued function `f : α → Set β` is upper hemicontinuous at `x₀ : α` if for
 every pair
of sequences `x : ℕ → α` and `y : ℕ → β` such that `x` tends to `x₀` and `y n ∈ 
f (x n)` and
`y` tends to `y₀ : β`, then `y₀ ∈ f x₀`. This requires that there is some (seque
ntially) compact
set containing all `f x'` for `x'` sufficiently close to `x`.

This is a partial converse of `UpperHemicontinuousAt.mem_of_tendsto`.
-/
lemma UpperHemicontinuousAt.of_sequences {x₀ : α} [(𝓝 x₀).IsCountablyGenerated]
    {K : Set β} (hK : IsSeqCompact K) (hf : ∀ᶠ x in 𝓝 x₀, f x ⊆ K)
    (h : ∀ x : ℕ → α, Tendsto x atTop (𝓝 x₀) →
      ∀ y : ℕ → β, (∀ n, y n ∈ f (x n)) → ∀ y₀, Tendsto y atTop (𝓝 y₀) → y₀ ∈ f x₀) :
    UpperHemicontinuousAt f x₀ := by
  refine .of_frequently fun t ht hft ↦ ?_
  obtain ⟨x, hx, hfx⟩ := exists_seq_forall_of_frequently hft
  choose y hy using hfx
  obtain ⟨y₀, hy₀, φ, hφ, hyφ⟩ := hK.subseq_of_frequently_in (x := y) <| by
    refine Eventually.frequently ?_
    filter_upwards [hx hf] with n hn
    exact hn (hy n).1
  specialize h (x ∘ φ) (hx.comp hφ.tendsto_atTop) (y ∘ φ) (fun n ↦ (hy _).1) _ hyφ
  exact ⟨y₀, h, ht.closure_eq ▸ mem_closure_of_tendsto hyφ <| .of_forall fun n ↦ (hy _).2⟩

/-- **Sequential characterization of upper hemicontinuity**:
If `β` is a regular space and `f : α → Set β` is upper hemicontinuous at `x₀` and `f x₀` is
closed, then for any sequences `x` and `y` (in `α` and `β`, respectively) tending to `x₀` and `y₀`,
respectively, if `y n ∈ f (x n)` frequently, then `y₀ ∈ f x₀`.

This is a partial converse of `UpperHemicontinuousAt.of_sequences`. -/
/-
**UpperHemicontinuousAt.mem_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousAt.mem_of_tendsto {ι : Type*} [RegularSpace β] {x₀ : α}
 {l : Filter ι} (hf : UpperHemicontinuousAt f x₀) (hf_closed : IsClosed (f x₀)) 
{x : ι -> α} (hx : Tendsto x l (𝓝 x₀)) {y : ι -> β} (hy : existsᶠ n in l, y n in
 f (x n)) {y₀ : β} (hy₀ : Tendsto y l (𝓝 y₀)) : y₀ in f x₀
参数：hf : UpperHemicontinuousAt f x₀；hf_closed : IsClosed (f x₀)；hx : Tendsto x l 
(𝓝 x₀)；hy : existsᶠ n in l, y n in f (x n)；hy₀ : Tendsto y l (𝓝 y₀)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.disjoint_iff`：∀ {α : Type u} {f g : Filter α}, Disjoint f g ↔ ∃ s
 ∈ f, ∃ t ∈ g, Disjoint s t
· 使用定理 `RegularSpace.regular`：∀ {X : Type u} {inst : TopologicalSpace X} [self :
 RegularSpace X] {s : Set X} {a : X},   IsClosed s → a ∉ s → Disjoint (nhdsSet s
) (nhds a)
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Disjoint.notMem_of_mem_left`：∀ {α : Type u} {s t : Set α}, Disjoint s t 
→ ∀ ⦃a : α⦄, a ∈ s → a ∉ t

--- 原说明 ---
**Sequential characterization of upper hemicontinuity**:
If `β` is a regular space and `f : α → Set β` is upper hemicontinuous at `x₀` an
d `f x₀` is
closed, then for any sequences `x` and `y` (in `α` and `β`, respectively) tendin
g to `x₀` and `y₀`,
respectively, if `y n ∈ f (x n)` frequently, then `y₀ ∈ f x₀`.

This is a partial converse of `UpperHemicontinuousAt.of_sequences`.
-/
lemma UpperHemicontinuousAt.mem_of_tendsto {ι : Type*} [RegularSpace β] {x₀ : α}
    {l : Filter ι} (hf : UpperHemicontinuousAt f x₀) (hf_closed : IsClosed (f x₀))
    {x : ι → α} (hx : Tendsto x l (𝓝 x₀))
    {y : ι → β} (hy : ∃ᶠ n in l, y n ∈ f (x n)) {y₀ : β} (hy₀ : Tendsto y l (𝓝 y₀)) :
    y₀ ∈ f x₀ := by
  by_contra
  obtain ⟨s, hs, t, ht, hst⟩ := Filter.disjoint_iff.mp <| RegularSpace.regular hf_closed this
  suffices ∃ᶠ n in l, y n ∈ s by
    apply this
    filter_upwards [hy₀ ht] with n hn hyn
    exact hst.notMem_of_mem_left hyn hn
  apply hy.mp
  filter_upwards [hx (hf s hs)] with n hn hyn
  simp only [← subset_interior_iff_mem_nhdsSet, preimage_ofPred_eq, mem_ofPred_eq] at hn
  exact interior_subset <| hn hyn

/-- **Sequential characterization of lower hemicontinuity**:
A set-valued function `f : α → Set β` is lower hemicontinuous at `x₀ : α` if for every sequence
`x : ℕ → α` tending to `x₀` and every `y₀ ∈ f x₀`, there exists a sequence `y : ℕ → β` with
`y n ∈ f (x n)` for all `n` that tends to `y₀`. -/
/-
**LowerHemicontinuousAt.of_sequences** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousAt.of_sequences {x₀ : α} [(𝓝 x₀).IsCountablyGenerated] 
(h : forall x : Nat -> α, Tendsto x atTop (𝓝 x₀) -> forall y₀ in f x₀, exists y 
: Nat -> β, (forall n, y n in f (x n)) ∧ Tendsto y atTop (𝓝 y₀)) : LowerHemicont
inuousAt f x₀
参数：𝓝 x₀；h : forall x : Nat -> α, Tendsto x atTop (𝓝 x₀) -> forall y₀ in f x₀, ex
ists y : Nat -> β, (forall n, y n in f (x n)) ∧ Tendsto y atTop (𝓝 y₀)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lowerHemicontinuousAt_iff`：lowerHemicontinuousAt_iff {f : α -> Set β} {x
 : α} : LowerHemicontinuousAt f x ↔ forall u, IsOpen u -> ((f x) inter u).Nonemp
ty -> forallᶠ x…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Filter.exists_seq_forall_of_frequently`：exists_seq_forall_of_frequently 
{ι : Type*} {l : Filter ι} {p : ι -> Prop} [l.IsCountablyGenerated] (h : existsᶠ
 n in l, p n) : exists ns : …
· 使用定理 `Filter.not_eventually`：not_eventually {p : α -> Prop} {f : Filter α} : (
¬forallᶠ x in f, p x) ↔ existsᶠ x in f, ¬p x
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
**Sequential characterization of lower hemicontinuity**:
A set-valued function `f : α → Set β` is lower hemicontinuous at `x₀ : α` if for
 every sequence
`x : ℕ → α` tending to `x₀` and every `y₀ ∈ f x₀`, there exists a sequence `y : 
ℕ → β` with
`y n ∈ f (x n)` for all `n` that tends to `y₀`.
-/
lemma LowerHemicontinuousAt.of_sequences {x₀ : α} [(𝓝 x₀).IsCountablyGenerated]
    (h : ∀ x : ℕ → α, Tendsto x atTop (𝓝 x₀) →
      ∀ y₀ ∈ f x₀, ∃ y : ℕ → β, (∀ n, y n ∈ f (x n)) ∧ Tendsto y atTop (𝓝 y₀)) :
    LowerHemicontinuousAt f x₀ := by
  rw [lowerHemicontinuousAt_iff]
  intro U hU ⟨y₀, hy₀f, hy₀U⟩
  by_contra hc
  rw [Filter.not_eventually] at hc
  obtain ⟨x, hx, hxU⟩ := exists_seq_forall_of_frequently hc
  obtain ⟨y, hy_mem, hy_lim⟩ := h x hx y₀ hy₀f
  obtain ⟨n, hn⟩ := (hy_lim.eventually (hU.mem_nhds hy₀U)).exists
  exact hxU n ⟨y n, hy_mem n, hn⟩

/-- **Sequential characterization of lower hemicontinuity**:
If `f : α → Set β` is lower hemicontinuous at `x₀`, `y₀ ∈ f x₀`, `𝓝 y₀` is countably generated, and
`x : ℕ → α` tends to `x₀`, then there is a companion sequence `y : ℕ → β` that tends to `y₀` with
`y n ∈ f (x n)` for all sufficiently large `n`.

This is a partial converse of `LowerHemicontinuousAt.of_sequences`. -/
/-
**LowerHemicontinuousAt.exists_seq_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousAt.exists_seq_tendsto {x₀ : α} (hf : LowerHemicontinuou
sAt f x₀) {x : Nat -> α} (hx : Tendsto x atTop (𝓝 x₀)) {y₀ : β} (hy₀ : y₀ in f x
₀) [(𝓝 y₀).IsCountablyGenerated] : exists y : Nat -> β, (forallᶠ n in atTop, y n
 in f (x n)) ∧ Tendsto y atTop (𝓝 y₀)
参数：hf : LowerHemicontinuousAt f x₀；hx : Tendsto x atTop (𝓝 x₀)；hy₀ : y₀ in f x₀；
𝓝 y₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.exists_antitone_subbasis`：∀ {α : Type u_1} {ι' : Sort u_
5} {f : Filter α} [h : f.IsCountablyGenerated] {p : ι' → Prop} {s : ι' → Set α},
   f.HasBasis p s → ∃ x, (∀ (i…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lowerHemicontinuousAt_iff`：lowerHemicontinuousAt_iff {f : α -> Set β} {x
 : α} : LowerHemicontinuousAt f x ↔ forall u, IsOpen u -> ((f x) inter u).Nonemp
ty -> forallᶠ x…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Nat.findGreatest_spec`：findGreatest_spec (hmb : m <= n) (hm : P m) : P (
Nat.findGreatest P n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.HasAntitoneBasis.antitone`：∀ {α : Type u_1} {ι'' : Type u_6} [ins
t : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → Ant
itone s
· 使用引理 `Nat.le_findGreatest`：le_findGreatest (hmb : m <= n) (hm : P m) : m <= Na
t.findGreatest P n

--- 原说明 ---
**Sequential characterization of lower hemicontinuity**:
If `f : α → Set β` is lower hemicontinuous at `x₀`, `y₀ ∈ f x₀`, `𝓝 y₀` is count
ably generated, and
`x : ℕ → α` tends to `x₀`, then there is a companion sequence `y : ℕ → β` that t
ends to `y₀` with
`y n ∈ f (x n)` for all sufficiently large `n`.

This is a partial converse of `LowerHemicontinuousAt.of_sequences`.
-/
lemma LowerHemicontinuousAt.exists_seq_tendsto {x₀ : α} (hf : LowerHemicontinuousAt f x₀)
    {x : ℕ → α} (hx : Tendsto x atTop (𝓝 x₀)) {y₀ : β} (hy₀ : y₀ ∈ f x₀)
    [(𝓝 y₀).IsCountablyGenerated] :
    ∃ y : ℕ → β, (∀ᶠ n in atTop, y n ∈ f (x n)) ∧ Tendsto y atTop (𝓝 y₀) := by
  classical
  obtain ⟨U, hU, hUbasis⟩ := (nhds_basis_opens y₀).exists_antitone_subbasis
  have hev (k) : ∀ᶠ n in atTop, (f (x n) ∩ U k).Nonempty :=
    hx.eventually <| (lowerHemicontinuousAt_iff.mp hf) (U k) (hU k).2 ⟨y₀, hy₀, (hU k).1⟩
  -- For each `n`, find the largest `k ≤ n` where `U k` intersects `f (x n)`.
  let g : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun k ↦ (f (x n) ∩ U k).Nonempty) n
  have key (n k) (hkn : k ≤ n) (hk : (f (x n) ∩ U k).Nonempty) : (f (x n) ∩ U (g n)).Nonempty :=
    Nat.findGreatest_spec (P := fun k ↦ (f (x n) ∩ U k).Nonempty) hkn hk
  -- Define `y n` to be some element of `f (x n) ∩ U (g n)` (or be arbitrary)
  let y : ℕ → β := fun n ↦ if h : (f (x n) ∩ U (g n)).Nonempty then h.some else y₀
  have hy (n) (h : (f (x n) ∩ U (g n)).Nonempty) : y n ∈ f (x n) ∩ U (g n) := by
    simpa only [y, dif_pos h] using h.some_mem
  refine ⟨y, (hev 0).mono (by grind), ?_⟩
  -- Have to show for all `k`, eventually, all `y n ∈ U k`.
  rw [hUbasis.tendsto_right_iff]
  intro k _
  filter_upwards [hev k, eventually_ge_atTop k] with n hk hkn
  exact hUbasis.antitone (Nat.le_findGreatest hkn hk) (hy n (key n k hkn hk)).2

/-- **Lower hemicontinuity along a countably generated filter** (subsequence form):
if `f : α → Set β` is lower hemicontinuous at `x₀`, `y₀ ∈ f x₀`, `𝓝 y₀` is countably generated and
`x : ι → α` tends to `x₀` along a nontrivial countably generated filter `l`, then some sequence
`u : ℕ → ι` converging to `l` admits a companion `y : ℕ → β` tending to `y₀` with
`y k ∈ f (x (u k))` eventually.

For a general filter one must pass to the subsequence `u`: the "same-index" conclusion already
fails for `l = pure i₀` (which is `NeBot` and countably generated). When `l = atTop` one may take
`u = id`, recovering `LowerHemicontinuousAt.exists_seq_tendsto`. -/
/-
**LowerHemicontinuousAt.exists_subseq_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousAt.exists_subseq_tendsto {ι : Type*} {l : Filter ι} [l.
NeBot] [l.IsCountablyGenerated] {x₀ : α} (hf : LowerHemicontinuousAt f x₀) {x : 
ι -> α} (hx : Tendsto x l (𝓝 x₀)) {y₀ : β} (hy₀ : y₀ in f x₀) [(𝓝 y₀).IsCountabl
yGenerated] : exists (u : Nat -> ι) (y : Nat -> β), Tendsto u atTop l ∧ (forallᶠ
 k in atTop, y k in f (x (u k))) ∧ Tendsto y atTop (𝓝 y₀)
参数：hf : LowerHemicontinuousAt f x₀；hx : Tendsto x l (𝓝 x₀)；hy₀ : y₀ in f x₀；𝓝 y₀
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用引理 `LowerHemicontinuousAt.exists_seq_tendsto`：LowerHemicontinuousAt.exists_s
eq_tendsto {x₀ : α} (hf : LowerHemicontinuousAt f x₀) {x : Nat -> α} (hx : Tends
to x atTop (𝓝 x₀)) {y₀ : β} (h…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …

--- 原说明 ---
**Lower hemicontinuity along a countably generated filter** (subsequence form):
if `f : α → Set β` is lower hemicontinuous at `x₀`, `y₀ ∈ f x₀`, `𝓝 y₀` is count
ably generated and
`x : ι → α` tends to `x₀` along a nontrivial countably generated filter `l`, the
n some sequence
`u : ℕ → ι` converging to `l` admits a companion `y : ℕ → β` tending to `y₀` wit
h
`y k ∈ f (x (u k))` eventually.

For a general filter one must pass to the subsequence `u`: the "same-index" conc
lusion already
fails for `l = pure i₀` (which is `NeBot` and countably generated). When `l = at
Top` one may take
`u = id`, recovering `LowerHemicontinuousAt.exists_seq_tendsto`.
-/
lemma LowerHemicontinuousAt.exists_subseq_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    [l.IsCountablyGenerated] {x₀ : α} (hf : LowerHemicontinuousAt f x₀) {x : ι → α}
    (hx : Tendsto x l (𝓝 x₀)) {y₀ : β} (hy₀ : y₀ ∈ f x₀) [(𝓝 y₀).IsCountablyGenerated] :
    ∃ (u : ℕ → ι) (y : ℕ → β), Tendsto u atTop l ∧
      (∀ᶠ k in atTop, y k ∈ f (x (u k))) ∧ Tendsto y atTop (𝓝 y₀) := by
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto l
  obtain ⟨y, hy_mem, hy_lim⟩ := hf.exists_seq_tendsto (hx.comp hu) hy₀
  exact ⟨u, y, hu, hy_mem, hy_lim⟩



end facts

/-! ### Open lower sections -/

/-- A correspondence `f : α → Set β` has open lower sections if and only if its *lower inverse*
(i.e., `b : β ↦ (f ⁻¹' Iic {b}ᶜ)ᶜ = {x | b ∈ f x}`) sends every point to an open set. -/
/-
**hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl : HasOpenLowerSec
tions f ↔ forall b, IsOpen (f ⁻¹' Iic {b}ᶜ)ᶜ
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A correspondence `f : α → Set β` has open lower sections if and only if its *low
er inverse*
(i.e., `b : β ↦ (f ⁻¹' Iic {b}ᶜ)ᶜ = {x | b ∈ f x}`) sends every point to an open
 set.
-/
lemma hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl :
    HasOpenLowerSections f ↔ ∀ b, IsOpen (f ⁻¹' Iic {b}ᶜ)ᶜ := by
  have h (b : β) : (f ⁻¹' (Iic {b}ᶜ))ᶜ = {x | b ∈ f x} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff]
  simp_rw [h, hasOpenLowerSections_iff_isOpen]

/-- A correspondence `f : α → Set β` has open lower sections if and only if its *upper inverse*
(i.e., `b : β ↦ f ⁻¹' (Iic {b}ᶜ) = {x | b ∉ f x}`) sends every point to a closed set. -/
/-
**hasOpenLowerSections_iff_isClosed_preimage_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasOpenLowerSections_iff_isClosed_preimage_Iic : HasOpenLowerSections f ↔ 
forall b, IsClosed (f ⁻¹' Iic {b}ᶜ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl`：hasOpenLowerSe
ctions_iff_isOpen_compl_preimage_Iic_compl : HasOpenLowerSections f ↔ forall b, 
IsOpen (f ⁻¹' Iic {b}ᶜ)ᶜ

--- 原说明 ---
A correspondence `f : α → Set β` has open lower sections if and only if its *upp
er inverse*
(i.e., `b : β ↦ f ⁻¹' (Iic {b}ᶜ) = {x | b ∉ f x}`) sends every point to a closed
 set.
-/
lemma hasOpenLowerSections_iff_isClosed_preimage_Iic :
    HasOpenLowerSections f ↔ ∀ b, IsClosed (f ⁻¹' Iic {b}ᶜ) := by
  simp_rw [← isOpen_compl_iff]
  exact hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl

/-! ### Open Graphs -/

/-- A lower hemicontinuous function intersected with a function with an open graph is lower
hemicontinuous. -/
/-
**LowerHemicontinuous.inter_hasOpenCGraph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LowerHemicontinuous.inter_hasOpenCGraph [TopologicalSpace β] {f g : α -> S
et β} (hf : LowerHemicontinuous f) (hg : HasOpenCGraph g) : LowerHemicontinuous 
(fun x => f x inter g x)
参数：hf : LowerHemicontinuous f；hg : HasOpenCGraph g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_prod_iff`：isOpen_prod_iff {s : Set (X × Y)} : IsOpen s ↔ forall a
 b, (a, b) in s -> exists u v, IsOpen u ∧ IsOpen v ∧ a in u ∧ b in v ∧ u ×ˢ v su
bsete…
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)

--- 原说明 ---
A lower hemicontinuous function intersected with a function with an open graph i
s lower
hemicontinuous.
-/
lemma LowerHemicontinuous.inter_hasOpenCGraph [TopologicalSpace β] {f g : α → Set β}
    (hf : LowerHemicontinuous f) (hg : HasOpenCGraph g) :
    LowerHemicontinuous (fun x ↦ f x ∩ g x) := by
  simp_rw [lowerHemicontinuous_iff_isOpen_inter_nonempty] at ⊢ hf
  intro t ht
  rw [isOpen_iff_forall_mem_open]
  intro x ⟨y, ⟨hyf, hyg⟩, hyt⟩
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := (isOpen_prod_iff.mp hg) x y hyg
  refine ⟨U ∩ {x' | (f x' ∩ (t ∩ V)).Nonempty}, ?_, hU.inter (hf _ (ht.inter hV)),
      ⟨hxU, y, hyf, hyt, hyV⟩⟩
  intro x' ⟨hx'U, z, hzf, hzt, hzV⟩
  exact ⟨z, ⟨hzf, hUV (Set.mk_mem_prod hx'U hzV)⟩, hzt⟩

/-! ### Uniform Limits

Like continuity, hemicontinuity is preserved under certain uniform limits, where the uniformity on
the target `Set β` is the Hausdorff uniformity. In this section, we prove this result for both
lower hemicontinuous and upper hemicontinuous limits.
-/

section limits

variable {ι : Type*} {F : ι → α → Set β} {l : Filter ι} [NeBot l]
variable [UniformSpace β]
open UniformSpace
attribute [local instance] UniformSpace.hausdorff

/-- A net of lower hemicontinuous set-valued functions converging uniformly on `s` (along a
filter `l`) in the Hausdorff uniformity has a lower hemicontinuous limit on `s` -/
/-
**TendstoUniformlyOn.lowerHemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.lowerHemicontinuousOn (htendsto : TendstoUniformlyOn F 
f l s) (hF : forall n, LowerHemicontinuousOn (F n) s) : LowerHemicontinuousOn f 
s
参数：htendsto : TendstoUniformlyOn F f l s；hF : forall n, LowerHemicontinuousOn (F
 n) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lowerHemicontinuousOn_iff`：lowerHemicontinuousOn_iff {f : α -> Set β} {s
 : Set α} : LowerHemicontinuousOn f s ↔ forall x in s, LowerHemicontinuousWithin
At f s x
· 使用引理 `lowerHemicontinuousWithinAt_iff`：lowerHemicontinuousWithinAt_iff {f : α 
-> Set β} {s : Set α} {x : α} : LowerHemicontinuousWithinAt f s x ↔ forall u, Is
Open u -> ((f x) inte…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniformSpace.mem_nhds_iff`：UniformSpace.mem_nhds_iff {x : α} {s : Set α}
 : s in 𝓝 x ↔ exists V in 𝓤 α, ball x V subseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.mem_lift'_sets`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h
 : Set α → Set β},   Monotone h → ∀ {s : Set β}, s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ 
s
· 使用定理 `monotone_hausdorffEntourage`：monotone_hausdorffEntourage : Monotone (hau
sdorffEntourage (α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mem_hausdorffEntourage`：mem_hausdorffEntourage (U : SetRel α α) (s t : S
et α) : (s, t) in hausdorffEntourage U ↔ s subseteq U.preimage t ∧ t subseteq U.
image s
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `uniformity_hasBasis_open`：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun
 V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
· 使用引理 `UniformSpace.mem_ball_self`：mem_ball_self (x : α) {V : SetRel α α} : V i
n 𝓤 α -> x in ball x V
· 使用引理 `UniformSpace.isOpen_ball`：isOpen_ball (x : α) {V : SetRel α α} (hV : IsO
pen V) : IsOpen (ball x V)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a

--- 原说明 ---
A net of lower hemicontinuous set-valued functions converging uniformly on `s` (
along a
filter `l`) in the Hausdorff uniformity has a lower hemicontinuous limit on `s`
-/
theorem TendstoUniformlyOn.lowerHemicontinuousOn (htendsto : TendstoUniformlyOn F f l s)
    (hF : ∀ n, LowerHemicontinuousOn (F n) s) : LowerHemicontinuousOn f s := by
  rw [lowerHemicontinuousOn_iff]
  intro x₀ hx₀s
  rw [lowerHemicontinuousWithinAt_iff]
  intro V hV ⟨y₀, hy₀f, hy₀V⟩
  -- Obtain entourages W, U ∈ 𝓤 β with U ○ U ○ U ⊆ W
  obtain ⟨W, hW, hWsub⟩ := UniformSpace.mem_nhds_iff.mp (hV.mem_nhds hy₀V)
  obtain ⟨U₁, hU₁, hU₁sym, hU₁comp⟩ := comp_symm_mem_uniformity_sets hW
  obtain ⟨U, hU, hUsym, hUcomp⟩ := comp_symm_mem_uniformity_sets hU₁
  have hU_le_U₁ : U ⊆ U₁ := fun _p hp => hUcomp ⟨_, refl_mem_uniformity hU, hp⟩
  -- Eventually, ⟨f x, F N x⟩ ∈ hausdorffEntourage U for all x ∈ s
  have hHU : hausdorffEntourage U ∈ @uniformity (Set β) (UniformSpace.hausdorff (α := β)) :=
    (mem_lift'_sets monotone_hausdorffEntourage).mpr ⟨U, hU, le_refl _⟩
  obtain ⟨N, hN⟩ := (htendsto (hausdorffEntourage U) hHU).exists
  -- In which case, ⟨y₀, z₀⟩ ∈ U for some z₀ ∈ F N x₀
  obtain ⟨z₀, hz₀FN, hz₀y₀⟩ :=
    ((mem_hausdorffEntourage U (f x₀) (F N x₀)).mp (hN x₀ hx₀s)).1 hy₀f
  -- By lower hemicontinuity, a ball around z₀ intersects all x in a neighborhood of x₀
  obtain ⟨U', ⟨hU'mem, hU'open⟩, hU'sub⟩ := uniformity_hasBasis_open.mem_iff.mp hU
  have hmeet₀ : (F N x₀ ∩ ball z₀ U').Nonempty := ⟨z₀, hz₀FN, mem_ball_self z₀ hU'mem⟩
  have hSmeet : ∀ᶠ x in 𝓝[s] x₀, (F N x ∩ ball z₀ U').Nonempty :=
    lowerHemicontinuousWithinAt_iff.mp (hF _ _ hx₀s) _ (isOpen_ball _ hU'open) hmeet₀
  filter_upwards [hSmeet, self_mem_nhdsWithin] with x ⟨w, hwFN, hwball⟩ hx_s
  obtain ⟨v, hvf, hvw⟩ := ((mem_hausdorffEntourage U (f x) (F N x)).mp (hN x hx_s)).2 hwFN
  exact ⟨v, hvf, hWsub <| hU₁comp
    ⟨w, hUcomp ⟨z₀, hz₀y₀, hU'sub hwball⟩, hU_le_U₁ (hUsym.symm _ _ hvw)⟩⟩

/-- If a net of upper hemicontinuous set-valued functions converges uniformly
(along a filter `l`) in the Hausdorff uniformity to a set-valued function `f` with
compact values, then `f` is upper hemicontinuous -/
/-
**TendstoUniformlyOn.upperHemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.upperHemicontinuousOn (htendsto : TendstoUniformlyOn F 
f l s) (hF : forall n, UpperHemicontinuousOn (F n) s) (hf_compact : forall x in 
s, IsCompact (f x)) : UpperHemicontinuousOn f s
参数：htendsto : TendstoUniformlyOn F f l s；hF : forall n, UpperHemicontinuousOn (F
 n) s；hf_compact : forall x in s, IsCompact (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuousOn_iff_forall_isOpen`：upperHemicontinuousOn_iff_foral
l_isOpen : UpperHemicontinuousOn f s ↔ forall x in s, forall u, IsOpen u -> f x 
subseteq u -> forallᶠ x' in 𝓝…
· 使用定理 `lebesgue_number_of_compact_open`：lebesgue_number_of_compact_open {K U : 
Set α} (hK : IsCompact K) (hU : IsOpen U) (hKU : K subseteq U) : exists V in 𝓤 α
, IsOpen V ∧ forall x…
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `uniformity_hasBasis_open`：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun
 V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.mem_lift'_sets`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h
 : Set α → Set β},   Monotone h → ∀ {s : Set β}, s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ 
s
· 使用定理 `monotone_hausdorffEntourage`：monotone_hausdorffEntourage : Monotone (hau
sdorffEntourage (α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mem_hausdorffEntourage`：mem_hausdorffEntourage (U : SetRel α α) (s t : S
et α) : (s, t) in hausdorffEntourage U ↔ s subseteq U.preimage t ∧ t subseteq U.
image s
· 使用定理 `UpperHemicontinuousWithinAt.forall_isOpen`：∀ {α : Type u_1} {β : Type u_
2} [inst : TopologicalSpace α] {f : α → Set β} {s : Set α} {x : α}   [inst_1 : T
opologicalSpace β],   UpperHemi…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `IsOpen.relImage`：IsOpen.relImage [TopologicalSpace α] [TopologicalSpace 
β] {s : SetRel α β} (hs : IsOpen s) {t : Set α} : IsOpen (s.image t)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a

--- 原说明 ---
If a net of upper hemicontinuous set-valued functions converges uniformly
(along a filter `l`) in the Hausdorff uniformity to a set-valued function `f` wi
th
compact values, then `f` is upper hemicontinuous
-/
theorem TendstoUniformlyOn.upperHemicontinuousOn (htendsto : TendstoUniformlyOn F f l s)
      (hF : ∀ n, UpperHemicontinuousOn (F n) s) (hf_compact : ∀ x ∈ s, IsCompact (f x)) :
    UpperHemicontinuousOn f s := by
  -- A function `f` is upper hemicontinuous at `x₀` if for all open `u` with `f x₀ ⊆ u`, then
  -- `f x ⊆ u` for all `x` near `x₀`
  rw [upperHemicontinuousOn_iff_forall_isOpen]
  intro x₀ hx₀s u hu hx₀u
  -- Find an open entourage `U` such that `U ○ U.symm ⊆ u`
  obtain ⟨W, hW, _, hWu⟩ := lebesgue_number_of_compact_open (hf_compact x₀ hx₀s) hu hx₀u
  obtain ⟨V, hV, hVsym, hVcomp⟩ := comp_symm_mem_uniformity_sets hW
  obtain ⟨U, ⟨hUmem, hUopen⟩, hUsub⟩ := uniformity_hasBasis_open.mem_iff.mp hV
  -- Then choose a sufficiently large `N` such that `⟨f x, F N x⟩ ∈ hausdorffEntourage U`
  -- for all `x ∈ s`
  have hHU : hausdorffEntourage U ∈ @uniformity _ (UniformSpace.hausdorff (α := β)) :=
    (mem_lift'_sets monotone_hausdorffEntourage).mpr ⟨U, hUmem, le_refl _⟩
  obtain ⟨N, hN⟩ := (htendsto (hausdorffEntourage U) hHU).exists
  have hFN_image : F N x₀ ⊆ U.image (f x₀) := ((mem_hausdorffEntourage ..).mp (hN x₀ hx₀s)).2
  -- Upper hemicontinuity implies `F N x ⊆ U.image (f x₀)` for `x` near `x₀`
  simp_rw [upperHemicontinuousOn_iff] at hF
  have hFN_uhc : ∀ᶠ x in 𝓝[s] x₀, F N x ⊆ U.image (f x₀) :=
    (hF N x₀ hx₀s).forall_isOpen _ hUopen.relImage hFN_image
  -- For such a nearby `x`, show `f x ⊆ u` by taking `y ∈ f x`,
  filter_upwards [hFN_uhc, self_mem_nhdsWithin] with x hFNx hx_s
  intro y hy
  -- finding a `z ∈ F N x` such that `(y, z) ∈ U` and then some `y₀ ∈ f x₀` such that `⟨y₀, z⟩ ∈ U`
  obtain ⟨z, hzFN, hyz⟩ := ((mem_hausdorffEntourage U (f x) (F N x)).mp (hN x hx_s)).1 hy
  obtain ⟨y₀, hy₀f, hy₀z⟩ := hFNx hzFN
  -- then use that `U ○ U.symm ⊆ u` to conclude
  exact hWu y₀ hy₀f (hVcomp ⟨z, hUsub hy₀z, hVsym.symm _ _ (hUsub hyz)⟩)

/-- A net of lower hemicontinuous set-valued functions converging uniformly (along a
filter `l`) in the Hausdorff uniformity has a lower hemicontinuous limit -/
/-
**TendstoUniformly.lowerHemicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformly.lowerHemicontinuous (htendsto : TendstoUniformly F f l) (
hF : forall n, LowerHemicontinuous (F n)) : LowerHemicontinuous f
参数：htendsto : TendstoUniformly F f l；hF : forall n, LowerHemicontinuous (F n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lowerHemicontinuousOn_univ_iff`：lowerHemicontinuousOn_univ_iff : LowerHe
micontinuousOn f univ ↔ LowerHemicontinuous f
· 使用定理 `TendstoUniformlyOn.lowerHemicontinuousOn`：TendstoUniformlyOn.lowerHemico
ntinuousOn (htendsto : TendstoUniformlyOn F f l s) (hF : forall n, LowerHemicont
inuousOn (F n) s) : LowerHemic…
· 使用定理 `TendstoUniformly.tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type u_2} {ι 
: Type u_4} [inst : UniformSpace β] {F : ι → α → β} {f : α → β} {s : Set α}   {p
 : Filter ι}, TendstoUnif…
· 使用定理 `LowerHemicontinuous.lowerHemicontinuousOn`：LowerHemicontinuous.lowerHemi
continuousOn (h : LowerHemicontinuous f) (s : Set α) : LowerHemicontinuousOn f s

--- 原说明 ---
A net of lower hemicontinuous set-valued functions converging uniformly (along a
filter `l`) in the Hausdorff uniformity has a lower hemicontinuous limit
-/
theorem TendstoUniformly.lowerHemicontinuous (htendsto : TendstoUniformly F f l)
    (hF : ∀ n, LowerHemicontinuous (F n)) : LowerHemicontinuous f := by
  rw [← lowerHemicontinuousOn_univ_iff]
  exact htendsto.tendstoUniformlyOn.lowerHemicontinuousOn (fun n ↦ (hF n).lowerHemicontinuousOn _)

/-- If a net of upper hemicontinuous set-valued functions converges uniformly
(along a filter `l`) in the Hausdorff uniformity to a set-valued function `f` with
compact values, then `f` is upper hemicontinuous -/
/-
**TendstoUniformly.upperHemicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformly.upperHemicontinuous (htendsto : TendstoUniformly F f l) (
hF : forall n, UpperHemicontinuous (F n)) (hf_compact : forall x, IsCompact (f x
)) : UpperHemicontinuous f
参数：htendsto : TendstoUniformly F f l；hF : forall n, UpperHemicontinuous (F n)；hf
_compact : forall x, IsCompact (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `upperHemicontinuousOn_univ_iff`：upperHemicontinuousOn_univ_iff : UpperHe
micontinuousOn f univ ↔ UpperHemicontinuous f
· 使用定理 `TendstoUniformlyOn.upperHemicontinuousOn`：TendstoUniformlyOn.upperHemico
ntinuousOn (htendsto : TendstoUniformlyOn F f l s) (hF : forall n, UpperHemicont
inuousOn (F n) s) (hf_compact …
· 使用定理 `TendstoUniformly.tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type u_2} {ι 
: Type u_4} [inst : UniformSpace β] {F : ι → α → β} {f : α → β} {s : Set α}   {p
 : Filter ι}, TendstoUnif…
· 使用定理 `UpperHemicontinuous.upperHemicontinuousOn`：UpperHemicontinuous.upperHemi
continuousOn (h : UpperHemicontinuous f) (s : Set α) : UpperHemicontinuousOn f s

--- 原说明 ---
If a net of upper hemicontinuous set-valued functions converges uniformly
(along a filter `l`) in the Hausdorff uniformity to a set-valued function `f` wi
th
compact values, then `f` is upper hemicontinuous
-/
theorem TendstoUniformly.upperHemicontinuous (htendsto : TendstoUniformly F f l)
    (hF : ∀ n, UpperHemicontinuous (F n)) (hf_compact : ∀ x, IsCompact (f x)) :
    UpperHemicontinuous f := by
  rw [← upperHemicontinuousOn_univ_iff]
  exact htendsto.tendstoUniformlyOn.upperHemicontinuousOn
    (fun n ↦ (hF n).upperHemicontinuousOn _) (fun x _ ↦ hf_compact x)

end limits

