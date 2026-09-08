/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Closure

/-!
# Neighborhoods in topological spaces

Each point `x` of `X` gets a neighborhood filter `𝓝 x`.

## Tags

neighborhood
-/

public section

open Set Filter Topology

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Sort v} {α : Type*} {x : X} {s t : Set X}

set_option backward.isDefEq.respectTransparency false in
/-
**nhds_def'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_def' (x : X) : 𝓝 x = ⨅ (s : Set X) (_ : IsOpen s) (_ : x in s), 𝓟 s
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_def`：∀ {X : Type u_3} [inst : TopologicalSpace X] (x : X), nhds x =
 ⨅ s ∈ {s | x ∈ s ∧ IsOpen s}, Filter.principal s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iInf_and`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : 
p ∧ q → α}, iInf s = ⨅ (h₁ : p), ⨅ (h₂ : q), s ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_def' (x : X) : 𝓝 x = ⨅ (s : Set X) (_ : IsOpen s) (_ : x ∈ s), 𝓟 s := by
  simp only [nhds_def, mem_ofPred_eq, @and_comm (x ∈ _), iInf_and]

/-- The open sets containing `x` are a basis for the neighborhood filter. See `nhds_basis_opens'`
for a variant using open neighborhoods instead. -/
/-
**nhds_basis_opens** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set X => x in s ∧ IsOpe
n s) fun s => s
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_def`：∀ {X : Type u_3} [inst : TopologicalSpace X] (x : X), nhds x =
 ⨅ s ∈ {s | x ∈ s ∧ IsOpen s}, Filter.principal s
· 使用定理 `Filter.hasBasis_biInf_principal`：hasBasis_biInf_principal {s : β -> Set 
α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· >= ·)) S) (ne : S.Nonempty) : (⨅ i in 
S, 𝓟 (s i)).HasBasis …
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ

--- 原说明 ---
The open sets containing `x` are a basis for the neighborhood filter. See `nhds_
basis_opens'`
for a variant using open neighborhoods instead.
-/
theorem nhds_basis_opens (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsOpen s) fun s => s := by
  rw [nhds_def]
  exact hasBasis_biInf_principal
    (fun s ⟨has, hs⟩ t ⟨hat, ht⟩ =>
      ⟨s ∩ t, ⟨⟨has, hat⟩, IsOpen.inter hs ht⟩, ⟨inter_subset_left, inter_subset_right⟩⟩)
    ⟨univ, ⟨mem_univ x, isOpen_univ⟩⟩
/-
**nhds_basis_closeds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_closeds (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∉ s ∧ IsCl
osed s) compl
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nhds_basis_closeds (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∉ s ∧ IsClosed s) compl :=
  ⟨fun t => (nhds_basis_opens x).mem_iff.trans <|
    compl_surjective.exists.trans <| by simp only [isOpen_compl_iff, mem_compl_iff]⟩

@[simp]
/-
**lift'_nhds_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] (x : X), (nhds x).lift' interio
r = nhds x
参数：x : X；nhds x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.lift'_interior_eq_self`：∀ {X : Type u} [inst : Topologic
alSpace X] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBa
sis p s → (∀ (i : ι), p i → …
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem lift'_nhds_interior (x : X) : (𝓝 x).lift' interior = 𝓝 x :=
  (nhds_basis_opens x).lift'_interior_eq_self fun _ ↦ And.right
/-
**Filter.HasBasis.nhds_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.nhds_interior {x : X} {p : ι -> Prop} {s : ι -> Set X} (h 
: (𝓝 x).HasBasis p s) : (𝓝 x).HasBasis p (interior <| s ·)
参数：h : (𝓝 x).HasBasis p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.HasBasis.lift'_interior`：∀ {X : Type u} [inst : TopologicalSpace 
X] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBasis p s 
→ (l.lift' interior)…
· 使用定理 `lift'_nhds_interior`：∀ {X : Type u} [inst : TopologicalSpace X] (x : X),
 (nhds x).lift' interior = nhds x
-/
theorem Filter.HasBasis.nhds_interior {x : X} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasis p (interior <| s ·) :=
  lift'_nhds_interior x ▸ h.lift'_interior

/-- A filter lies below the neighborhood filter at `x` iff it contains every open set around `x`. -/
/-
**le_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_nhds_iff {f} : f <= 𝓝 x ↔ forall s : Set X, x in s -> IsOpen s -> s in 
f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_def`：∀ {X : Type u_3} [inst : TopologicalSpace X] (x : X), nhds x =
 ⨅ s ∈ {s | x ∈ s ∧ IsOpen s}, Filter.principal s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A filter lies below the neighborhood filter at `x` iff it contains every open se
t around `x`.
-/
theorem le_nhds_iff {f} : f ≤ 𝓝 x ↔ ∀ s : Set X, x ∈ s → IsOpen s → s ∈ f := by simp [nhds_def]

/-- To show a filter is above the neighborhood filter at `x`, it suffices to show that it is above
the principal filter of some open set `s` containing `x`. -/
/-
**nhds_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_le_of_le {f} (h : x in s) (o : IsOpen s) (sf : 𝓟 s <= f) : 𝓝 x <= f
参数：h : x in s；o : IsOpen s；sf : 𝓟 s <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_def`：∀ {X : Type u_3} [inst : TopologicalSpace X] (x : X), nhds x =
 ⨅ s ∈ {s | x ∈ s ∧ IsOpen s}, Filter.principal s
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…

--- 原说明 ---
To show a filter is above the neighborhood filter at `x`, it suffices to show th
at it is above
the principal filter of some open set `s` containing `x`.
-/
theorem nhds_le_of_le {f} (h : x ∈ s) (o : IsOpen s) (sf : 𝓟 s ≤ f) : 𝓝 x ≤ f := by
  rw [nhds_def]; exact iInf₂_le_of_le s ⟨h, o⟩ sf
/-
**mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  (nhds_basis_opens x).mem_iff.trans <| exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩

/-- A predicate is true in a neighborhood of `x` iff it is true for all the points in an open set
containing `x`. -/
/-
**eventually_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in 𝓝 x, p y) ↔ exists t :
 Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A predicate is true in a neighborhood of `x` iff it is true for all the points i
n an open set
containing `x`.
-/
theorem eventually_nhds_iff {p : X → Prop} :
    (∀ᶠ y in 𝓝 x, p y) ↔ ∃ t : Set X, (∀ y ∈ t, p y) ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff.trans <| by simp only [subset_def, mem_ofPred_eq]
/-
**frequently_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frequently_nhds_iff {p : X -> Prop} : (existsᶠ y in 𝓝 x, p y) ↔ forall U :
 Set X, x in U -> IsOpen U -> exists y in U, p y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
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
theorem frequently_nhds_iff {p : X → Prop} :
    (∃ᶠ y in 𝓝 x, p y) ↔ ∀ U : Set X, x ∈ U → IsOpen U → ∃ y ∈ U, p y :=
  (nhds_basis_opens x).frequently_iff.trans <| by simp
/-
**mem_interior_iff_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_interior_iff_mem_nhds : x in interior s ↔ s in 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_interior`：mem_interior : x in interior s ↔ exists t subseteq s, IsOp
en t ∧ x in t
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
-/
theorem mem_interior_iff_mem_nhds : x ∈ interior s ↔ s ∈ 𝓝 x :=
  mem_interior.trans mem_nhds_iff.symm
/-
**map_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nhds {f : X -> α} : map f (𝓝 x) = ⨅ s in { s : Set X | x in s ∧ IsOpen
 s }, 𝓟 (f '' s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
-/
theorem map_nhds {f : X → α} :
    map f (𝓝 x) = ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 (f '' s) :=
  ((nhds_basis_opens x).map f).eq_biInf
/-
**mem_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_of_mem_nhds : s in 𝓝 x -> x in s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
-/
theorem mem_of_mem_nhds : s ∈ 𝓝 x → x ∈ s := fun H =>
  let ⟨_t, ht, _, hs⟩ := mem_nhds_iff.1 H; ht hs

/-- If a predicate is true in a neighborhood of `x`, then it is true for `x`. -/
/-
**Filter.Eventually.self_of_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.self_of_nhds {p : X -> Prop} (h : forallᶠ y in 𝓝 x, p y)
 : p x
参数：h : forallᶠ y in 𝓝 x, p y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
If a predicate is true in a neighborhood of `x`, then it is true for `x`.
-/
theorem Filter.Eventually.self_of_nhds {p : X → Prop} (h : ∀ᶠ y in 𝓝 x, p y) : p x :=
  mem_of_mem_nhds h
/-
**IsOpen.mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 x
参数：hs : IsOpen s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem IsOpen.mem_nhds (hs : IsOpen s) (hx : x ∈ s) : s ∈ 𝓝 x :=
  mem_nhds_iff.2 ⟨s, Subset.refl _, hs, hx⟩
/-
**IsOpen.mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} {s : Set X}, IsOpen s →
 (s ∈ nhds x ↔ x ∈ s)
参数：s ∈ nhds x ↔ x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
protected theorem IsOpen.mem_nhds_iff (hs : IsOpen s) : s ∈ 𝓝 x ↔ x ∈ s :=
  ⟨mem_of_mem_nhds, fun hx => mem_nhds_iff.2 ⟨s, Subset.rfl, hs, hx⟩⟩
/-
**IsClosed.compl_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.compl_mem_nhds (hs : IsClosed s) (hx : x ∉ s) : sᶜ in 𝓝 x
参数：hs : IsClosed s；hx : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
-/
theorem IsClosed.compl_mem_nhds (hs : IsClosed s) (hx : x ∉ s) : sᶜ ∈ 𝓝 x :=
  hs.isOpen_compl.mem_nhds (mem_compl hx)
/-
**IsOpen.eventually_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in s) : forallᶠ x in 𝓝 x, x 
in s
参数：hs : IsOpen s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem IsOpen.eventually_mem (hs : IsOpen s) (hx : x ∈ s) :
    ∀ᶠ x in 𝓝 x, x ∈ s :=
  IsOpen.mem_nhds hs hx

/-- The open neighborhoods of `x` are a basis for the neighborhood filter. See `nhds_basis_opens`
for a variant using open sets around `x` instead. -/
/-
**nhds_basis_opens'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_opens' (x : X) : (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ Is
Open s) fun x => x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `IsOpen.mem_nhds_iff`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} 
{s : Set X}, IsOpen s → (s ∈ nhds x ↔ x ∈ s)
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s

--- 原说明 ---
The open neighborhoods of `x` are a basis for the neighborhood filter. See `nhds
_basis_opens`
for a variant using open sets around `x` instead.
-/
theorem nhds_basis_opens' (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsOpen s) fun x => x := by
  convert! nhds_basis_opens x using 2
  exact and_congr_left_iff.2 IsOpen.mem_nhds_iff

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of `s`:
it contains an open set containing `s`. -/
/-
**exists_open_set_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_open_set_nhds {U : Set X} (h : forall x in s, U in 𝓝 x) : exists V 
: Set X, s subseteq V ∧ IsOpen V ∧ V subseteq U
参数：h : forall x in s, U in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of
 `s`:
it contains an open set containing `s`.
-/
theorem exists_open_set_nhds {U : Set X} (h : ∀ x ∈ s, U ∈ 𝓝 x) :
    ∃ V : Set X, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  ⟨interior U, fun x hx => mem_interior_iff_mem_nhds.2 <| h x hx, isOpen_interior, interior_subset⟩

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of s:
it contains an open set containing `s`. -/
/-
**exists_open_set_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_open_set_nhds' {U : Set X} (h : U in ⨆ x in s, 𝓝 x) : exists V : Se
t X, s subseteq V ∧ IsOpen V ∧ V subseteq U
参数：h : U in ⨆ x in s, 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_open_set_nhds`：exists_open_set_nhds {U : Set X} (h : forall x in 
s, U in 𝓝 x) : exists V : Set X, s subseteq V ∧ IsOpen V ∧ V subseteq U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of
 s:
it contains an open set containing `s`.
-/
theorem exists_open_set_nhds' {U : Set X} (h : U ∈ ⨆ x ∈ s, 𝓝 x) :
    ∃ V : Set X, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  exists_open_set_nhds (by simpa using h)

/-- If a predicate is true in a neighbourhood of `x`, then for `y` sufficiently close
to `x` this predicate is true in a neighbourhood of `y`. -/
/-
**Filter.Eventually.eventually_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.eventually_nhds {p : X -> Prop} (h : forallᶠ y in 𝓝 x, p
 y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p x
参数：h : forallᶠ y in 𝓝 x, p y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If a predicate is true in a neighbourhood of `x`, then for `y` sufficiently clos
e
to `x` this predicate is true in a neighbourhood of `y`.
-/
theorem Filter.Eventually.eventually_nhds {p : X → Prop} (h : ∀ᶠ y in 𝓝 x, p y) :
    ∀ᶠ y in 𝓝 x, ∀ᶠ x in 𝓝 y, p x :=
  let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h
  eventually_nhds_iff.2 ⟨t, fun _x hx => eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩

@[simp]
/-
**eventually_eventually_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_eventually_nhds {p : X -> Prop} : (forallᶠ y in 𝓝 x, forallᶠ x 
in 𝓝 y, p x) ↔ forallᶠ x in 𝓝 x, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `Filter.Eventually.eventually_nhds`：Filter.Eventually.eventually_nhds {p 
: X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p
 x
-/
theorem eventually_eventually_nhds {p : X → Prop} :
    (∀ᶠ y in 𝓝 x, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝 x, p x :=
  ⟨fun h => h.self_of_nhds, fun h => h.eventually_nhds⟩

@[simp]
/-
**frequently_frequently_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frequently_frequently_nhds {p : X -> Prop} : (existsᶠ x' in 𝓝 x, existsᶠ x
'' in 𝓝 x', p x'') ↔ existsᶠ x in 𝓝 x, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_frequently_nhds {p : X → Prop} :
    (∃ᶠ x' in 𝓝 x, ∃ᶠ x'' in 𝓝 x', p x'') ↔ ∃ᶠ x in 𝓝 x, p x := by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_eventually_nhds]

@[simp]
/-
**eventually_mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_mem_nhds_iff : (forallᶠ x' in 𝓝 x, s in 𝓝 x') ↔ s in 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_eventually_nhds`：eventually_eventually_nhds {p : X -> Prop} :
 (forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝 x, p x
-/
theorem eventually_mem_nhds_iff : (∀ᶠ x' in 𝓝 x, s ∈ 𝓝 x') ↔ s ∈ 𝓝 x :=
  eventually_eventually_nhds

@[simp]
/-
**nhds_bind_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_bind_nhds : (𝓝 x).bind 𝓝 = 𝓝 x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `eventually_eventually_nhds`：eventually_eventually_nhds {p : X -> Prop} :
 (forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝 x, p x
-/
theorem nhds_bind_nhds : (𝓝 x).bind 𝓝 = 𝓝 x :=
  Filter.ext fun _ => eventually_eventually_nhds

@[simp]
/-
**eventually_eventuallyEq_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_eventuallyEq_nhds {f g : X -> α} : (forallᶠ y in 𝓝 x, f =ᶠ[𝓝 y]
 g) ↔ f =ᶠ[𝓝 x] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_eventually_nhds`：eventually_eventually_nhds {p : X -> Prop} :
 (forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝 x, p x
-/
theorem eventually_eventuallyEq_nhds {f g : X → α} :
    (∀ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g) ↔ f =ᶠ[𝓝 x] g :=
  eventually_eventually_nhds
/-
**Filter.EventuallyEq.eq_of_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.eq_of_nhds {f g : X -> α} (h : f =ᶠ[𝓝 x] g) : f x = g 
x
参数：h : f =ᶠ[𝓝 x] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
-/
theorem Filter.EventuallyEq.eq_of_nhds {f g : X → α} (h : f =ᶠ[𝓝 x] g) : f x = g x :=
  h.self_of_nhds

@[simp]
/-
**eventually_eventuallyLE_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_eventuallyLE_nhds [LE α] {f g : X -> α} : (forallᶠ y in 𝓝 x, f 
<=ᶠ[𝓝 y] g) ↔ f <=ᶠ[𝓝 x] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_eventually_nhds`：eventually_eventually_nhds {p : X -> Prop} :
 (forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝 x, p x
-/
theorem eventually_eventuallyLE_nhds [LE α] {f g : X → α} :
    (∀ᶠ y in 𝓝 x, f ≤ᶠ[𝓝 y] g) ↔ f ≤ᶠ[𝓝 x] g :=
  eventually_eventually_nhds

/-- If two functions are equal in a neighbourhood of `x`, then for `y` sufficiently close
to `x` these functions are equal in a neighbourhood of `y`. -/
/-
**Filter.EventuallyEq.eventuallyEq_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.eventuallyEq_nhds {f g : X -> α} (h : f =ᶠ[𝓝 x] g) : f
orallᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g
参数：h : f =ᶠ[𝓝 x] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.eventually_nhds`：Filter.Eventually.eventually_nhds {p 
: X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p
 x

--- 原说明 ---
If two functions are equal in a neighbourhood of `x`, then for `y` sufficiently 
close
to `x` these functions are equal in a neighbourhood of `y`.
-/
theorem Filter.EventuallyEq.eventuallyEq_nhds {f g : X → α} (h : f =ᶠ[𝓝 x] g) :
    ∀ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g :=
  h.eventually_nhds

/-- If `f x ≤ g x` in a neighbourhood of `x`, then for `y` sufficiently close to `x` we have
`f x ≤ g x` in a neighbourhood of `y`. -/
/-
**Filter.EventuallyLE.eventuallyLE_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyLE.eventuallyLE_nhds [LE α] {f g : X -> α} (h : f <=ᶠ[𝓝 x
] g) : forallᶠ y in 𝓝 x, f <=ᶠ[𝓝 y] g
参数：h : f <=ᶠ[𝓝 x] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.eventually_nhds`：Filter.Eventually.eventually_nhds {p 
: X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p
 x

--- 原说明 ---
If `f x ≤ g x` in a neighbourhood of `x`, then for `y` sufficiently close to `x`
 we have
`f x ≤ g x` in a neighbourhood of `y`.
-/
theorem Filter.EventuallyLE.eventuallyLE_nhds [LE α] {f g : X → α} (h : f ≤ᶠ[𝓝 x] g) :
    ∀ᶠ y in 𝓝 x, f ≤ᶠ[𝓝 y] g :=
  h.eventually_nhds
/-
**all_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：all_mem_nhds (x : X) (P : Set X -> Prop) (hP : forall s t, s subseteq t ->
 P s -> P t) : (forall s in 𝓝 x, P s) ↔ forall s, IsOpen s -> x in s -> P s
参数：x : X；P : Set X -> Prop；hP : forall s t, s subseteq t -> P s -> P t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
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
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem all_mem_nhds (x : X) (P : Set X → Prop) (hP : ∀ s t, s ⊆ t → P s → P t) :
    (∀ s ∈ 𝓝 x, P s) ↔ ∀ s, IsOpen s → x ∈ s → P s :=
  ((nhds_basis_opens x).forall_iff hP).trans <| by simp only [@and_comm (x ∈ _), and_imp]
/-
**all_mem_nhds_filter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：all_mem_nhds_filter (x : X) (f : Set X -> Set α) (hf : forall s t, s subse
teq t -> f s subseteq f t) (l : Filter α) : (forall s in 𝓝 x, f s in l) ↔ forall
 s, IsOpen s -> x in s -> f s in l
参数：x : X；f : Set X -> Set α；hf : forall s t, s subseteq t -> f s subseteq f t；l 
: Filter α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `all_mem_nhds`：all_mem_nhds (x : X) (P : Set X -> Prop) (hP : forall s t,
 s subseteq t -> P s -> P t) : (forall s in 𝓝 x, P s) ↔ forall s, IsOpen s -> x 
in…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem all_mem_nhds_filter (x : X) (f : Set X → Set α) (hf : ∀ s t, s ⊆ t → f s ⊆ f t)
    (l : Filter α) : (∀ s ∈ 𝓝 x, f s ∈ l) ↔ ∀ s, IsOpen s → x ∈ s → f s ∈ l :=
  all_mem_nhds _ _ fun s t ssubt h => mem_of_superset h (hf s t ssubt)
/-
**tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds {f : α -> X} {l : Filter α} : Tendsto f l (𝓝 x) ↔ forall s, I
sOpen s -> x in s -> f ⁻¹' s in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `all_mem_nhds_filter`：all_mem_nhds_filter (x : X) (f : Set X -> Set α) (h
f : forall s t, s subseteq t -> f s subseteq f t) (l : Filter α) : (forall s in 
𝓝 x, f s …
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem tendsto_nhds {f : α → X} {l : Filter α} :
    Tendsto f l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → f ⁻¹' s ∈ l :=
  all_mem_nhds_filter _ _ (fun _ _ h => preimage_mono h) _
/-
**tendsto_atTop_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_nhds [Nonempty α] [SemilatticeSup α] {f : α -> X} : Tendsto 
f atTop (𝓝 x) ↔ forall U : Set X, x in U -> IsOpen U -> exists N, forall n, N <=
 n -> f n in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_atTop_nhds [Nonempty α] [SemilatticeSup α] {f : α → X} :
    Tendsto f atTop (𝓝 x) ↔ ∀ U : Set X, x ∈ U → IsOpen U → ∃ N, ∀ n, N ≤ n → f n ∈ U :=
  (atTop_basis.tendsto_iff (nhds_basis_opens x)).trans <| by
    simp only [and_imp, true_and, mem_Ici]
/-
**tendsto_const_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ : α => x) f (𝓝 x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhds`：tendsto_nhds {f : α -> X} {l : Filter α} : Tendsto f l (𝓝 
x) ↔ forall s, IsOpen s -> x in s -> f ⁻¹' s in l
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem tendsto_const_nhds {f : Filter α} : Tendsto (fun _ : α => x) f (𝓝 x) :=
  tendsto_nhds.mpr fun _ _ ha => univ_mem' fun _ => ha
/-
**tendsto_atTop_of_eventually_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_of_eventually_const {ι : Type*} [Preorder ι] {u : ι -> X} {i
₀ : ι} (h : forall i >= i₀, u i = x) : Tendsto u atTop (𝓝 x)
参数：h : forall i >= i₀, u i = x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem tendsto_atTop_of_eventually_const {ι : Type*} [Preorder ι]
    {u : ι → X} {i₀ : ι} (h : ∀ i ≥ i₀, u i = x) : Tendsto u atTop (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm ((eventually_ge_atTop i₀).mono h)) tendsto_const_nhds
/-
**tendsto_atBot_of_eventually_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atBot_of_eventually_const {ι : Type*} [Preorder ι] {u : ι -> X} {i
₀ : ι} (h : forall i <= i₀, u i = x) : Tendsto u atBot (𝓝 x)
参数：h : forall i <= i₀, u i = x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)
-/
theorem tendsto_atBot_of_eventually_const {ι : Type*} [Preorder ι]
    {u : ι → X} {i₀ : ι} (h : ∀ i ≤ i₀, u i = x) : Tendsto u atBot (𝓝 x) :=
  tendsto_atTop_of_eventually_const (ι := ιᵒᵈ) h
/-
**pure_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_pure`：mem_pure {a : α} {s : Set α} : s in (pure a : Filter α)
 ↔ a in s
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem pure_le_nhds : pure ≤ (𝓝 : X → Filter X) := fun _ _ hs => mem_pure.2 <| mem_of_mem_nhds hs
/-
**tendsto_pure_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pure_nhds (f : α -> X) (a : α) : Tendsto f (pure a) (𝓝 (f a))
参数：f : α -> X；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem tendsto_pure_nhds (f : α → X) (a : α) : Tendsto f (pure a) (𝓝 (f a)) :=
  (tendsto_pure_pure f a).mono_right (pure_le_nhds _)
/-
**OrderTop.tendsto_atTop_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderTop.tendsto_atTop_nhds [PartialOrder α] [OrderTop α] (f : α -> X) : T
endsto f atTop (𝓝 (f ⊤))
参数：f : α -> X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.tendsto_atTop_pure`：tendsto_atTop_pure [PartialOrder α] [OrderTop
 α] (f : α -> β) : Tendsto f atTop (pure <| f ⊤)
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem OrderTop.tendsto_atTop_nhds [PartialOrder α] [OrderTop α] (f : α → X) :
    Tendsto f atTop (𝓝 (f ⊤)) :=
  (tendsto_atTop_pure f).mono_right (pure_le_nhds _)

@[simp]
/-
**nhds_neBot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nhds_neBot : NeBot (𝓝 x)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.neBot_of_le`：neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f 
<= g) : NeBot g
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
instance nhds_neBot : NeBot (𝓝 x) :=
  neBot_of_le (pure_le_nhds x)
/-
**tendsto_nhds_of_eventually_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_of_eventually_eq {l : Filter α} {f : α -> X} (h : forallᶠ x' 
in l, f x' = x) : Tendsto f l (𝓝 x)
参数：h : forallᶠ x' in l, f x' = x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem tendsto_nhds_of_eventually_eq {l : Filter α} {f : α → X} (h : ∀ᶠ x' in l, f x' = x) :
    Tendsto f l (𝓝 x) :=
  tendsto_const_nhds.congr' (.symm h)
/-
**Filter.EventuallyEq.tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.tendsto {l : Filter α} {f : α -> X} (hf : f =ᶠ[l] fun 
_ => x) : Tendsto f l (𝓝 x)
参数：hf : f =ᶠ[l] fun _ => x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
-/
theorem Filter.EventuallyEq.tendsto {l : Filter α} {f : α → X} (hf : f =ᶠ[l] fun _ ↦ x) :
    Tendsto f l (𝓝 x) :=
  tendsto_nhds_of_eventually_eq hf

/-! ### Interior, closure and frontier in terms of neighborhoods -/

/-
**interior_eq_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_eq_nhds' : interior s = { x | s in 𝓝 x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Interior, closure and frontier in terms of neighborhoods
-/
theorem interior_eq_nhds' : interior s = { x | s ∈ 𝓝 x } :=
  Set.ext fun x => by simp only [mem_interior, mem_nhds_iff, mem_ofPred_eq]
/-
**interior_eq_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_eq_nhds : interior s = { x | 𝓝 x <= 𝓟 s }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `interior_eq_nhds'`：interior_eq_nhds' : interior s = { x | s in 𝓝 x }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem interior_eq_nhds : interior s = { x | 𝓝 x ≤ 𝓟 s } :=
  interior_eq_nhds'.trans <| by simp only [le_principal_iff]

@[simp]
/-
**interior_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_mem_nhds : interior s in 𝓝 x ↔ s in 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
-/
theorem interior_mem_nhds : interior s ∈ 𝓝 x ↔ s ∈ 𝓝 x :=
  ⟨fun h => mem_of_superset h interior_subset, fun h =>
    IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.2 h)⟩
/-
**interior_setOfPred_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_setOfPred_eq {p : X -> Prop} : interior { x | p x } = { x | foral
lᶠ y in 𝓝 x, p y }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_eq_nhds'`：interior_eq_nhds' : interior s = { x | s in 𝓝 x }
-/
theorem interior_setOfPred_eq {p : X → Prop} : interior { x | p x } = { x | ∀ᶠ y in 𝓝 x, p y } :=
  interior_eq_nhds'

@[deprecated (since := "2026-07-09")]
alias interior_setOf_eq := interior_setOfPred_eq
/-
**isOpen_setOfPred_eventually_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_setOfPred_eventually_nhds {p : X -> Prop} : IsOpen { x | forallᶠ y 
in 𝓝 x, p y }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isOpen_setOfPred_eventually_nhds {p : X → Prop} : IsOpen { x | ∀ᶠ y in 𝓝 x, p y } := by
  simp only [← interior_setOfPred_eq, isOpen_interior]

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_eventually_nhds := isOpen_setOfPred_eventually_nhds
/-
**subset_interior_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_iff_nhds {V : Set X} : s subseteq interior V ↔ forall x in
 s, V in 𝓝 x
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
theorem subset_interior_iff_nhds {V : Set X} : s ⊆ interior V ↔ ∀ x ∈ s, V ∈ 𝓝 x := by
  simp_rw [subset_def, mem_interior_iff_mem_nhds]
/-
**isOpen_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iff_nhds : IsOpen s ↔ forall x in s, 𝓝 x <= 𝓟 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `subset_interior_iff_isOpen`：subset_interior_iff_isOpen : s subseteq inte
rior s ↔ IsOpen s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_eq_nhds`：interior_eq_nhds : interior s = { x | 𝓝 x <= 𝓟 s }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff_nhds : IsOpen s ↔ ∀ x ∈ s, 𝓝 x ≤ 𝓟 s :=
  calc
    IsOpen s ↔ s ⊆ interior s := subset_interior_iff_isOpen.symm
    _ ↔ ∀ x ∈ s, 𝓝 x ≤ 𝓟 s := by simp_rw [interior_eq_nhds, subset_def, mem_ofPred]
/-
**TopologicalSpace.ext_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TopologicalSpace.ext_iff_nhds {X} {t t' : TopologicalSpace X} : t = t' ↔ f
orall x, @nhds _ t x = @nhds _ t' x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isOpen_iff_nhds`：isOpen_iff_nhds : IsOpen s ↔ forall x in s, 𝓝 x <= 𝓟 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem TopologicalSpace.ext_iff_nhds {X} {t t' : TopologicalSpace X} :
    t = t' ↔ ∀ x, @nhds _ t x = @nhds _ t' x :=
  ⟨fun H _ ↦ congrFun (congrArg _ H) _, fun H ↦ by ext; simp_rw [@isOpen_iff_nhds _ _ _, H]⟩

alias ⟨_, TopologicalSpace.ext_nhds⟩ := TopologicalSpace.ext_iff_nhds
/-
**isOpen_iff_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s in 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isOpen_iff_nhds`：isOpen_iff_nhds : IsOpen s ↔ forall x in s, 𝓝 x <= 𝓟 s
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a → b ↔ a → c)
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem isOpen_iff_mem_nhds : IsOpen s ↔ ∀ x ∈ s, s ∈ 𝓝 x :=
  isOpen_iff_nhds.trans <| forall_congr' fun _ => imp_congr_right fun _ => le_principal_iff

/-- A set `s` is open iff for every point `x` in `s` and every `y` close to `x`, `y` is in `s`. -/
/-
**isOpen_iff_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iff_eventually : IsOpen s ↔ forall x, x in s -> forallᶠ y in 𝓝 x, y
 in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x

--- 原说明 ---
A set `s` is open iff for every point `x` in `s` and every `y` close to `x`, `y`
 is in `s`.
-/
theorem isOpen_iff_eventually : IsOpen s ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, y ∈ s :=
  isOpen_iff_mem_nhds
/-
**isOpen_singleton_iff_nhds_eq_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_singleton_iff_nhds_eq_pure (x : X) : IsOpen ({x} : Set X) ↔ 𝓝 x = p
ure x
参数：x : X。
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
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_singleton_iff_nhds_eq_pure (x : X) : IsOpen ({x} : Set X) ↔ 𝓝 x = pure x := by
  simp [← (pure_le_nhds _).ge_iff_eq', isOpen_iff_mem_nhds]
/-
**isOpen_singleton_iff_punctured_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_singleton_iff_punctured_nhds (x : X) : IsOpen ({x} : Set X) ↔ 𝓝[!=]
 x = ⊥
参数：x : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_singleton_iff_nhds_eq_pure`：isOpen_singleton_iff_nhds_eq_pure (x 
: X) : IsOpen ({x} : Set X) ↔ 𝓝 x = pure x
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mem_iff_inf_principal_compl`：mem_iff_inf_principal_compl {f : Fil
ter α} {s : Set α} : s in f ↔ f ⊓ 𝓟 sᶜ = ⊥
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_singleton_iff_punctured_nhds (x : X) : IsOpen ({x} : Set X) ↔ 𝓝[≠] x = ⊥ := by
  rw [isOpen_singleton_iff_nhds_eq_pure, nhdsWithin, ← mem_iff_inf_principal_compl,
      le_antisymm_iff]
  simp [pure_le_nhds x]
/-
**mem_closure_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_frequently : x in closure s ↔ existsᶠ x in 𝓝 x, x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Frequently.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Frequently p f = ¬∀ᶠ (x : α) in f, ¬p x
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `closure_eq_compl_interior_compl`：closure_eq_compl_interior_compl : closu
re s = (interior sᶜ)ᶜ
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Set.compl_def`：compl_def (s : Set α) : sᶜ = { x | x ∉ s }
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closure_iff_frequently : x ∈ closure s ↔ ∃ᶠ x in 𝓝 x, x ∈ s := by
  rw [Filter.Frequently, Filter.Eventually, ← mem_interior_iff_mem_nhds,
    closure_eq_compl_interior_compl, mem_compl_iff, compl_def]

alias ⟨_, Filter.Frequently.mem_closure⟩ := mem_closure_iff_frequently

/-- A set `s` is closed iff for every point `x`, if there is a point `y` close to `x` that belongs
to `s` then `x` is in `s`. -/
/-
**isClosed_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_iff_frequently : IsClosed s ↔ forall x, (existsᶠ y in 𝓝 x, y in s
) -> x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A set `s` is closed iff for every point `x`, if there is a point `y` close to `x
` that belongs
to `s` then `x` is in `s`.
-/
theorem isClosed_iff_frequently : IsClosed s ↔ ∀ x, (∃ᶠ y in 𝓝 x, y ∈ s) → x ∈ s := by
  rw [← closure_subset_iff_isClosed]
  refine forall_congr' fun x => ?_
  rw [mem_closure_iff_frequently]
/-
**nhdsWithin_neBot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsWithin_neBot : (𝓝[s] x).NeBot ↔ forall ⦃t⦄, t in 𝓝 x -> (t inter s).No
nempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.inf_neBot_iff`：inf_neBot_iff : NeBot (l ⊓ l') ↔ forall ⦃s : Set α
⦄, s in l -> forall ⦃s'⦄, s' in l' -> (s inter s').Nonempty
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
-/
lemma nhdsWithin_neBot : (𝓝[s] x).NeBot ↔ ∀ ⦃t⦄, t ∈ 𝓝 x → (t ∩ s).Nonempty := by
  rw [nhdsWithin, inf_neBot_iff]
  exact forall₂_congr fun U _ ↦
    ⟨fun h ↦ h (mem_principal_self _), fun h u hsu ↦ h.mono <| inter_subset_inter_right _ hsu⟩

@[gcongr]
/-
**nhdsWithin_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t) : 𝓝[s] x <= 𝓝[t] 
x
参数：x : X；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
theorem nhdsWithin_mono (x : X) {s t : Set X} (h : s ⊆ t) : 𝓝[s] x ≤ 𝓝[t] x :=
  inf_le_inf_left _ (principal_mono.mpr h)
/-
**IsClosed.interior_union_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.interior_union_left (_ : IsClosed s) : interior (s union t) subse
teq s union interior t
参数：_ : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior`：mem_interior : x in interior s ↔ exists t subseteq s, IsOp
en t ∧ x in t
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
-/
theorem IsClosed.interior_union_left (_ : IsClosed s) :
    interior (s ∪ t) ⊆ s ∪ interior t := fun a ⟨u, ⟨⟨hu₁, hu₂⟩, ha⟩⟩ =>
  (Classical.em (a ∈ s)).imp_right fun h =>
    mem_interior.mpr
      ⟨u ∩ sᶜ, fun _x hx => (hu₂ hx.1).resolve_left hx.2, IsOpen.inter hu₁ IsClosed.isOpen_compl,
        ⟨ha, h⟩⟩
/-
**IsClosed.interior_union_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.interior_union_right (h : IsClosed t) : interior (s union t) subs
eteq interior s union t
参数：h : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `IsClosed.interior_union_left`：IsClosed.interior_union_left (_ : IsClosed
 s) : interior (s union t) subseteq s union interior t
-/
theorem IsClosed.interior_union_right (h : IsClosed t) :
    interior (s ∪ t) ⊆ interior s ∪ t := by
  simpa only [union_comm _ t] using h.interior_union_left
/-
**IsOpen.inter_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.inter_closure (h : IsOpen s) : s inter closure t subseteq closure (
s inter t)
参数：h : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `IsClosed.interior_union_left`：IsClosed.interior_union_left (_ : IsClosed
 s) : interior (s union t) subseteq s union interior t
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
-/
theorem IsOpen.inter_closure (h : IsOpen s) : s ∩ closure t ⊆ closure (s ∩ t) :=
  compl_subset_compl.mp <| by
    simpa only [← interior_compl, compl_inter] using IsClosed.interior_union_left h.isClosed_compl
/-
**IsOpen.closure_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.closure_inter (h : IsOpen t) : closure s inter t subseteq closure (
s inter t)
参数：h : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `IsOpen.inter_closure`：IsOpen.inter_closure (h : IsOpen s) : s inter clos
ure t subseteq closure (s inter t)
-/
theorem IsOpen.closure_inter (h : IsOpen t) : closure s ∩ t ⊆ closure (s ∩ t) := by
  simpa only [inter_comm t] using h.inter_closure
/-
**Dense.open_subset_closure_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.open_subset_closure_inter (hs : Dense s) (ht : IsOpen t) : t subsete
q closure (t inter s)
参数：hs : Dense s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `IsOpen.inter_closure`：IsOpen.inter_closure (h : IsOpen s) : s inter clos
ure t subseteq closure (s inter t)
-/
theorem Dense.open_subset_closure_inter (hs : Dense s) (ht : IsOpen t) :
    t ⊆ closure (t ∩ s) :=
  calc
    t = t ∩ closure s := by rw [hs.closure_eq, inter_univ]
    _ ⊆ closure (t ∩ s) := ht.inter_closure

/-- The intersection of an open dense set with a dense set is a dense set. -/
/-
**Dense.inter_of_isOpen_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.inter_of_isOpen_left (hs : Dense s) (ht : Dense t) (hso : IsOpen s) 
: Dense (s inter t)
参数：hs : Dense s；ht : Dense t；hso : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `IsOpen.inter_closure`：IsOpen.inter_closure (h : IsOpen s) : s inter clos
ure t subseteq closure (s inter t)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a

--- 原说明 ---
The intersection of an open dense set with a dense set is a dense set.
-/
theorem Dense.inter_of_isOpen_left (hs : Dense s) (ht : Dense t) (hso : IsOpen s) :
    Dense (s ∩ t) := fun x =>
  closure_minimal hso.inter_closure isClosed_closure <| by simp [hs.closure_eq, ht.closure_eq]

/-- The intersection of a dense set with an open dense set is a dense set. -/
/-
**Dense.inter_of_isOpen_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.inter_of_isOpen_right (hs : Dense s) (ht : Dense t) (hto : IsOpen t)
 : Dense (s inter t)
参数：hs : Dense s；ht : Dense t；hto : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.inter_of_isOpen_left`：Dense.inter_of_isOpen_left (hs : Dense s) (h
t : Dense t) (hso : IsOpen s) : Dense (s inter t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
The intersection of a dense set with an open dense set is a dense set.
-/
theorem Dense.inter_of_isOpen_right (hs : Dense s) (ht : Dense t) (hto : IsOpen t) :
    Dense (s ∩ t) :=
  inter_comm t s ▸ ht.inter_of_isOpen_left hs hto
/-
**Dense.inter_nhds_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.inter_nhds_nonempty (hs : Dense s) (ht : t in 𝓝 x) : (s inter t).Non
empty
参数：hs : Dense s；ht : t in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Dense.inter_open_nonempty`：∀ {X : Type u} [inst : TopologicalSpace X] {s
 : Set X},   Dense s → ∀ (U : Set X), IsOpen U → U.Nonempty → (U ∩ s).Nonempty
-/
theorem Dense.inter_nhds_nonempty (hs : Dense s) (ht : t ∈ 𝓝 x) :
    (s ∩ t).Nonempty :=
  let ⟨U, hsub, ho, hx⟩ := mem_nhds_iff.1 ht
  (hs.inter_open_nonempty U ho ⟨x, hx⟩).mono fun _y hy => ⟨hy.2, hsub hy.1⟩
/-
**closure_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_sdiff : closure s \ closure t subseteq closure (s \ t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsOpen.inter_closure`：IsOpen.inter_closure (h : IsOpen s) : s inter clos
ure t subseteq closure (s inter t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.sdiff_subset_sdiff`：sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ su
bseteq s₂ -> t₂ subseteq t₁ -> s₁ \ t₁ subseteq s₂ \ t₂
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem closure_sdiff : closure s \ closure t ⊆ closure (s \ t) :=
  calc
    closure s \ closure t = (closure t)ᶜ ∩ closure s := by simp only [sdiff_eq, inter_comm]
    _ ⊆ closure ((closure t)ᶜ ∩ s) := (isOpen_compl_iff.mpr <| isClosed_closure).inter_closure
    _ = closure (s \ closure t) := by simp only [sdiff_eq, inter_comm]
    _ ⊆ closure (s \ t) := closure_mono <| sdiff_subset_sdiff (Subset.refl s) subset_closure

@[deprecated (since := "2026-06-03")] alias closure_diff := closure_sdiff
/-
**Filter.Frequently.mem_of_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Frequently.mem_of_closed (h : existsᶠ x in 𝓝 x, x in s) (hs : IsClo
sed s) : x in s
参数：h : existsᶠ x in 𝓝 x, x in s；hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
· 使用定理 `Filter.Frequently.mem_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {x : X} {s : Set X}, (∃ᶠ (x : X) in nhds x, x ∈ s) → x ∈ closure s
-/
theorem Filter.Frequently.mem_of_closed (h : ∃ᶠ x in 𝓝 x, x ∈ s)
    (hs : IsClosed s) : x ∈ s :=
  hs.closure_subset h.mem_closure
/-
**IsClosed.mem_of_frequently_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.mem_of_frequently_of_tendsto {f : α -> X} {b : Filter α} (hs : Is
Closed s) (h : existsᶠ x in b, f x in s) (hf : Tendsto f b (𝓝 x)) : x in s
参数：hs : IsClosed s；h : existsᶠ x in b, f x in s；hf : Tendsto f b (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mem_of_closed`：Filter.Frequently.mem_of_closed (h : ex
istsᶠ x in 𝓝 x, x in s) (hs : IsClosed s) : x in s
· 使用定理 `Filter.Tendsto.frequently`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x
 : α) in l₁, p …
-/
theorem IsClosed.mem_of_frequently_of_tendsto {f : α → X} {b : Filter α}
    (hs : IsClosed s) (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 x)) : x ∈ s :=
  (hf.frequently <| show ∃ᶠ x in b, (fun y => y ∈ s) (f x) from h).mem_of_closed hs
/-
**IsClosed.mem_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.mem_of_tendsto {f : α -> X} {b : Filter α} [NeBot b] (hs : IsClos
ed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in s
参数：hs : IsClosed s；hf : Tendsto f b (𝓝 x)；h : forallᶠ x in b, f x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.mem_of_frequently_of_tendsto`：IsClosed.mem_of_frequently_of_ten
dsto {f : α -> X} {b : Filter α} (hs : IsClosed s) (h : existsᶠ x in b, f x in s
) (hf : Tendsto f b (𝓝 x)) …
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
-/
theorem IsClosed.mem_of_tendsto {f : α → X} {b : Filter α} [NeBot b]
    (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : ∀ᶠ x in b, f x ∈ s) : x ∈ s :=
  hs.mem_of_frequently_of_tendsto h.frequently hf
/-
**mem_closure_of_frequently_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_of_frequently_of_tendsto {f : α -> X} {b : Filter α} (h : exis
tsᶠ x in b, f x in s) (hf : Tendsto f b (𝓝 x)) : x in closure s
参数：h : existsᶠ x in b, f x in s；hf : Tendsto f b (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mem_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {x : X} {s : Set X}, (∃ᶠ (x : X) in nhds x, x ∈ s) → x ∈ closure s
· 使用定理 `Filter.Tendsto.frequently`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x
 : α) in l₁, p …
-/
theorem mem_closure_of_frequently_of_tendsto {f : α → X} {b : Filter α}
    (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 x)) : x ∈ closure s :=
  (hf.frequently h).mem_closure
/-
**mem_closure_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_of_tendsto {f : α -> X} {b : Filter α} [NeBot b] (hf : Tendsto
 f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in closure s
参数：hf : Tendsto f b (𝓝 x)；h : forallᶠ x in b, f x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_of_frequently_of_tendsto`：mem_closure_of_frequently_of_tends
to {f : α -> X} {b : Filter α} (h : existsᶠ x in b, f x in s) (hf : Tendsto f b 
(𝓝 x)) : x in closure s
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
-/
theorem mem_closure_of_tendsto {f : α → X} {b : Filter α} [NeBot b]
    (hf : Tendsto f b (𝓝 x)) (h : ∀ᶠ x in b, f x ∈ s) : x ∈ closure s :=
  mem_closure_of_frequently_of_tendsto h.frequently hf

/-- Suppose that `f` sends the complement to `s` to a single point `x`, and `l` is some filter.
Then `f` tends to `x` along `l` restricted to `s` if and only if it tends to `x` along `l`. -/
/-
**tendsto_inf_principal_nhds_iff_of_forall_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inf_principal_nhds_iff_of_forall_eq {f : α -> X} {l : Filter α} {s
 : Set α} (h : forall a ∉ s, f a = x) : Tendsto f (l ⊓ 𝓟 s) (𝓝 x) ↔ Tendsto f l 
(𝓝 x)
参数：h : forall a ∉ s, f a = x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Filter.sup_principal`：sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s uni
on t)
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
Suppose that `f` sends the complement to `s` to a single point `x`, and `l` is s
ome filter.
Then `f` tends to `x` along `l` restricted to `s` if and only if it tends to `x`
 along `l`.
-/
theorem tendsto_inf_principal_nhds_iff_of_forall_eq {f : α → X} {l : Filter α} {s : Set α}
    (h : ∀ a ∉ s, f a = x) : Tendsto f (l ⊓ 𝓟 s) (𝓝 x) ↔ Tendsto f l (𝓝 x) := by
  rw [tendsto_iff_comap, tendsto_iff_comap]
  replace h : 𝓟 sᶜ ≤ comap f (𝓝 x) := by
    rintro U ⟨t, ht, htU⟩ x hx
    have : f x ∈ t := (h x hx).symm ▸ mem_of_mem_nhds ht
    exact htU this
  refine ⟨fun h' => ?_, le_trans inf_le_left⟩
  have := sup_le h' h
  rw [sup_inf_right, sup_principal, union_compl_self, principal_univ, inf_top_eq, sup_le_iff]
    at this
  exact this.1
