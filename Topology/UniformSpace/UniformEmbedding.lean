/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Separation
public import Mathlib.Topology.DenseEmbedding

/-!
# Uniform embeddings of uniform spaces.

Extension of uniform continuous functions.
-/

@[expose] public section


open Filter Function Set Uniformity Topology
open scoped SetRel

section

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {f : α → β}

/-!
### Uniform inducing maps
-/

/-
**isUniformInducing_iff_uniformSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUniformInducing_iff_uniformSpace {f : α -> β} : IsUniformInducing f ↔ ‹U
niformSpace β›.comap f = ‹UniformSpace α›
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUniformInducing_iff`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpac
e α] [inst_1 : UniformSpace β] (f : α → β),   IsUniformInducing f ↔ Filter.comap
 (fun x => …
· 使用定理 `UniformSpace.ext_iff`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, u₁ = u₂ 
↔ ∀ (s : Set (α × α)), s ∈ uniformity α ↔ s ∈ uniformity α
· 使用定理 `Filter.ext_iff`：∀ {α : Type u_1} {f g : Filter α}, f = g ↔ ∀ (s : Set α)
, s ∈ f ↔ s ∈ g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Uniform inducing maps
-/
lemma isUniformInducing_iff_uniformSpace {f : α → β} :
    IsUniformInducing f ↔ ‹UniformSpace β›.comap f = ‹UniformSpace α› := by
  rw [isUniformInducing_iff, UniformSpace.ext_iff, Filter.ext_iff]
  rfl

protected alias ⟨IsUniformInducing.comap_uniformSpace, _⟩ := isUniformInducing_iff_uniformSpace
/-
**isUniformInducing_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUniformInducing_iff' {f : α -> β} : IsUniformInducing f ↔ UniformContinu
ous f ∧ comap (Prod.map f f) (𝓤 β) <= 𝓤 α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUniformInducing_iff`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpac
e α] [inst_1 : UniformSpace β] (f : α → β),   IsUniformInducing f ↔ Filter.comap
 (fun x => …
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isUniformInducing_iff' {f : α → β} :
    IsUniformInducing f ↔ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) ≤ 𝓤 α := by
  rw [isUniformInducing_iff, UniformContinuous, tendsto_iff_comap, le_antisymm_iff, and_comm]; rfl
/-
**Filter.HasBasis.isUniformInducing_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBas
is`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : UniformSpace α] [inst_1 : UniformSpace
 β] {ι : Sort u_1} {ι' : Sort u_2}   {p : ι → Prop} {p' : ι' → Prop} {s : ι → Se
t (α × α)} {s' : ι' → Set (β × β)},   (uniformity α).HasBasis p s →     (uniform
ity β).HasBasis p' s' →       ∀ {f : α → β},         IsUniformInducing f ↔      
     (∀ (i : ι'), p' i → ∃ j, p j ∧ ∀ (x y : α), (x, y) ∈ s j → (f x, f y) ∈ s' 
i) ∧             ∀ (j : ι), p j → ∃ i, p' i ∧ ∀ (x y : α), (f x, f y) ∈ s' i → (
x, y) ∈ s j
参数：α × α；β × β；uniformity α；uniformity β；∀ (i : ι'), p' i → ∃ j, p j ∧ ∀ (x y : 
α), (x, y) ∈ s j → (f x, f y) ∈ s' i；j : ι；x y : α；f x, f y；x, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.HasBasis.uniformContinuous_iff`：Filter.HasBasis.uniformContinuous
_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι
' -> Prop} {t : ι' -> Set (…
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma Filter.HasBasis.isUniformInducing_iff {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α → β} :
    IsUniformInducing f ↔
      (∀ i, p' i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ s' i) ∧
        (∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j) := by
  simp [isUniformInducing_iff', h.uniformContinuous_iff h', (h'.comap _).le_basis_iff h, subset_def]
/-
**IsUniformInducing.mk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.mk' {f : α -> β} (h : forall s, s in 𝓤 α ↔ exists t in 𝓤
 β, forall x y : α, (f x, f y) in t -> (x, y) in s) : IsUniformInducing f
参数：h : forall s, s in 𝓤 α ↔ exists t in 𝓤 β, forall x y : α, (f x, f y) in t -> 
(x, y) in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsUniformInducing.mk' {f : α → β}
    (h : ∀ s, s ∈ 𝓤 α ↔ ∃ t ∈ 𝓤 β, ∀ x y : α, (f x, f y) ∈ t → (x, y) ∈ s) : IsUniformInducing f :=
  ⟨by simp [eq_comm, Filter.ext_iff, subset_def, h]⟩
/-
**IsUniformInducing.id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.id : IsUniformInducing (@id α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.map_def`：map_def {f : α -> γ} {g : β -> δ} : Prod.map f g = fun p :
 α × β => (f p.1, g p.2)
· 使用定理 `Prod.map_id`：∀ {α : Type u_1} {β : Type u_2}, Prod.map id id = id
· 使用定理 `Filter.comap_id`：comap_id : comap id f = f
-/
theorem IsUniformInducing.id : IsUniformInducing (@id α) :=
  ⟨by rw [← Prod.map_def, Prod.map_id, comap_id]⟩
/-
**IsUniformInducing.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.comp {g : β -> γ} (hg : IsUniformInducing g) {f : α -> β
} (hf : IsUniformInducing f) : IsUniformInducing (g ∘ f)
参数：hg : IsUniformInducing g；hf : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
-/
theorem IsUniformInducing.comp {g : β → γ} (hg : IsUniformInducing g) {f : α → β}
    (hf : IsUniformInducing f) : IsUniformInducing (g ∘ f) :=
  ⟨by rw [← hf.1, ← hg.1, comap_comap]; rfl⟩
/-
**IsUniformInducing.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.of_comp_iff {g : β -> γ} (hg : IsUniformInducing g) {f :
 α -> β} : IsUniformInducing (g ∘ f) ↔ IsUniformInducing f
参数：hg : IsUniformInducing g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUniformInducing_iff`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpac
e α] [inst_1 : UniformSpace β] (f : α → β),   IsUniformInducing f ↔ Filter.comap
 (fun x => …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `IsUniformInducing.comp`：IsUniformInducing.comp {g : β -> γ} (hg : IsUnif
ormInducing g) {f : α -> β} (hf : IsUniformInducing f) : IsUniformInducing (g ∘ 
f)
-/
theorem IsUniformInducing.of_comp_iff {g : β → γ} (hg : IsUniformInducing g) {f : α → β} :
    IsUniformInducing (g ∘ f) ↔ IsUniformInducing f := by
  refine ⟨fun h ↦ ?_, hg.comp⟩
  rw [isUniformInducing_iff, ← hg.comap_uniformity, comap_comap, ← h.comap_uniformity,
    Function.comp_def, Function.comp_def]
/-
**IsUniformInducing.basis_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.basis_uniformity {f : α -> β} (hf : IsUniformInducing f)
 {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (β × β)} (H : (𝓤 β).HasBasis p s) : (
𝓤 α).HasBasis p fun i => Prod.map f f ⁻¹' s i
参数：hf : IsUniformInducing f；β × β；H : (𝓤 β).HasBasis p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
-/
theorem IsUniformInducing.basis_uniformity {f : α → β} (hf : IsUniformInducing f) {ι : Sort*}
    {p : ι → Prop} {s : ι → Set (β × β)} (H : (𝓤 β).HasBasis p s) :
    (𝓤 α).HasBasis p fun i => Prod.map f f ⁻¹' s i :=
  hf.1 ▸ H.comap _
/-
**IsUniformInducing.cauchy_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.cauchy_map_iff {f : α -> β} (hf : IsUniformInducing f) {
F : Filter α} : Cauchy (map f F) ↔ Cauchy F
参数：hf : IsUniformInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsUniformInducing.cauchy_map_iff {f : α → β} (hf : IsUniformInducing f) {F : Filter α} :
    Cauchy (map f F) ↔ Cauchy F := by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap, ← hf.comap_uniformity]
/-
**IsUniformInducing.of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.of_comp {f : α -> β} {g : β -> γ} (hf : UniformContinuou
s f) (hg : UniformContinuous g) (hgf : IsUniformInducing (g ∘ f)) : IsUniformInd
ucing f
参数：hf : UniformContinuous f；hg : UniformContinuous g；hgf : IsUniformInducing (g 
∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `Prod.map_def`：map_def {f : α -> γ} {g : β -> δ} : Prod.map f g = fun p :
 α × β => (f p.1, g p.2)
· 使用定理 `Prod.map_comp_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : T
ype u_4} {ε : Type u_5} {ζ : Type u_6} (f : α → β) (f' : γ → δ)   (g : β → ε) (g
' : δ →…
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
-/
theorem IsUniformInducing.of_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) (hgf : IsUniformInducing (g ∘ f)) : IsUniformInducing f := by
  refine ⟨le_antisymm ?_ hf.le_comap⟩
  rw [← hgf.1, ← Prod.map_def, ← Prod.map_def, ← Prod.map_comp_map f f g g, ← comap_comap]
  exact comap_mono hg.le_comap
/-
**IsUniformInducing.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.uniformContinuous {f : α -> β} (hf : IsUniformInducing f
) : UniformContinuous f
参数：hf : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isUniformInducing_iff'`：isUniformInducing_iff' {f : α -> β} : IsUniformI
nducing f ↔ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) <= 𝓤 α
-/
theorem IsUniformInducing.uniformContinuous {f : α → β} (hf : IsUniformInducing f) :
    UniformContinuous f := (isUniformInducing_iff'.1 hf).1
/-
**IsUniformInducing.uniformContinuous_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.uniformContinuous_iff {f : α -> β} {g : β -> γ} (hg : Is
UniformInducing g) : UniformContinuous f ↔ UniformContinuous (g ∘ f)
参数：hg : IsUniformInducing g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsUniformInducing.uniformContinuous_iff {f : α → β} {g : β → γ} (hg : IsUniformInducing g) :
    UniformContinuous f ↔ UniformContinuous (g ∘ f) := by
  dsimp only [UniformContinuous, Tendsto]
  simp only [← hg.comap_uniformity, ← map_le_iff_le_comap, Filter.map_map, Function.comp_def]

@[deprecated (since := "2026-03-17")]
alias IsUniformInducing.isUniformInducing_comp_iff := IsUniformInducing.of_comp_iff
/-
**IsUniformInducing.uniformContinuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.uniformContinuousOn_iff {f : α -> β} {g : β -> γ} {S : S
et α} (hg : IsUniformInducing g) : UniformContinuousOn f S ↔ UniformContinuousOn
 (g ∘ f) S
参数：hg : IsUniformInducing g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsUniformInducing.uniformContinuousOn_iff {f : α → β} {g : β → γ} {S : Set α}
    (hg : IsUniformInducing g) :
    UniformContinuousOn f S ↔ UniformContinuousOn (g ∘ f) S := by
  dsimp only [UniformContinuousOn, Tendsto]
  rw [← hg.comap_uniformity, ← map_le_iff_le_comap, Filter.map_map, comp_def, comp_def]
/-
**IsUniformInducing.isInducing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.isInducing {f : α -> β} (h : IsUniformInducing f) : IsIn
ducing f
参数：h : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.induced`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace Y] (f : X → Y), Topology.IsInducing f
· 使用定理 `IsUniformInducing.comap_uniformSpace`：∀ {α : Type u} {β : Type v} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 UniformSpace.comap f inst…
-/
theorem IsUniformInducing.isInducing {f : α → β} (h : IsUniformInducing f) : IsInducing f := by
  obtain rfl := h.comap_uniformSpace
  exact .induced f
/-
**IsUniformInducing.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.prod {α' : Type*} {β' : Type*} [UniformSpace α'] [Unifor
mSpace β'] {e₁ : α -> α'} {e₂ : β -> β'} (h₁ : IsUniformInducing e₁) (h₂ : IsUni
formInducing e₂) : IsUniformInducing fun p : α × β => (e₁ p.1, e₂ p.2)
参数：h₁ : IsUniformInducing e₁；h₂ : IsUniformInducing e₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsUniformInducing.prod {α' : Type*} {β' : Type*} [UniformSpace α'] [UniformSpace β']
    {e₁ : α → α'} {e₂ : β → β'} (h₁ : IsUniformInducing e₁) (h₂ : IsUniformInducing e₂) :
    IsUniformInducing fun p : α × β => (e₁ p.1, e₂ p.2) :=
  ⟨by simp [Function.comp_def, uniformity_prod, ← h₁.1, ← h₂.1, comap_inf, comap_comap]⟩
/-
**IsUniformInducing.isDenseInducing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUniformInducing.isDenseInducing (h : IsUniformInducing f) (hd : DenseRan
ge f) : IsDenseInducing f where toIsInducing
参数：h : IsUniformInducing f；hd : DenseRange f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
-/
lemma IsUniformInducing.isDenseInducing (h : IsUniformInducing f) (hd : DenseRange f) :
    IsDenseInducing f where
  toIsInducing := h.isInducing
  dense := hd
/-
**SeparationQuotient.isUniformInducing_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SeparationQuotient.isUniformInducing_mk : IsUniformInducing (mk : α -> Sep
arationQuotient α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.comap_mk_uniformity`：comap_mk_uniformity : (𝓤 (Separa
tionQuotient α)).comap (Prod.map mk mk) = 𝓤 α
-/
lemma SeparationQuotient.isUniformInducing_mk :
    IsUniformInducing (mk : α → SeparationQuotient α) :=
  ⟨comap_mk_uniformity⟩
/-
**IsUniformInducing.injective** 是 Mathlib 中的一个定理，位于命名空间 `IsUniformInducing`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : UniformSpace α] [inst_1 : UniformSpace
 β] [T0Space α] {f : α → β},   IsUniformInducing f → Function.Injective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space X] {f : X → Y},   Topo
logy.IsInducing f →…
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
-/
protected theorem IsUniformInducing.injective [T0Space α] {f : α → β} (h : IsUniformInducing f) :
    Injective f :=
  h.isInducing.injective

/-!
### Uniform embeddings
-/

/-
**isUniformEmbedding_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformEmbedding_iff' {f : α -> β} : IsUniformEmbedding f ↔ Injective f 
∧ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) <= 𝓤 α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUniformEmbedding_iff`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   IsUniformEmbedding f ↔ IsUniformI
nducing f ∧ …
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用引理 `isUniformInducing_iff'`：isUniformInducing_iff' {f : α -> β} : IsUniformI
nducing f ↔ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) <= 𝓤 α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Uniform embeddings
-/
theorem isUniformEmbedding_iff' {f : α → β} :
    IsUniformEmbedding f ↔
      Injective f ∧ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) ≤ 𝓤 α := by
  rw [isUniformEmbedding_iff, and_comm, isUniformInducing_iff']
/-
**Filter.HasBasis.isUniformEmbedding_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.isUniformEmbedding_iff' {ι ι'} {p : ι -> Prop} {p' : ι' ->
 Prop} {s s'} (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α -> β} 
: IsUniformEmbedding f ↔ Injective f ∧ (forall i, p' i -> exists j, p j ∧ forall
 x y, (x, y) in s j -> (f x, f y) in s' i) ∧ (forall j, p j -> exists i, p' i ∧ 
forall x y, (f x, f y) in s' i -> (x, y) in s j)
参数：h : (𝓤 α).HasBasis p s；h' : (𝓤 β).HasBasis p' s'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUniformEmbedding_iff`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   IsUniformEmbedding f ↔ IsUniformI
nducing f ∧ …
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Filter.HasBasis.isUniformInducing_iff`：∀ {α : Type u} {β : Type v} [inst
 : UniformSpace α] [inst_1 : UniformSpace β] {ι : Sort u_1} {ι' : Sort u_2}   {p
 : ι → Prop} {p' : ι' → Pro…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.isUniformEmbedding_iff' {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α → β} :
    IsUniformEmbedding f ↔ Injective f ∧
      (∀ i, p' i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ s' i) ∧
        (∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j) := by
  rw [isUniformEmbedding_iff, and_comm, h.isUniformInducing_iff h']
/-
**Filter.HasBasis.isUniformEmbedding_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.isUniformEmbedding_iff {ι ι'} {p : ι -> Prop} {p' : ι' -> 
Prop} {s s'} (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α -> β} :
 IsUniformEmbedding f ↔ Injective f ∧ UniformContinuous f ∧ (forall j, p j -> ex
ists i, p' i ∧ forall x y, (f x, f y) in s' i -> (x, y) in s j)
参数：h : (𝓤 α).HasBasis p s；h' : (𝓤 β).HasBasis p' s'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.isUniformEmbedding_iff'`：Filter.HasBasis.isUniformEmbedd
ing_iff' {ι ι'} {p : ι -> Prop} {p' : ι' -> Prop} {s s'} (h : (𝓤 α).HasBasis p s
) (h' : (𝓤 β).HasBasis p' s')…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.HasBasis.uniformContinuous_iff`：Filter.HasBasis.uniformContinuous
_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι
' -> Prop} {t : ι' -> Set (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.HasBasis.isUniformEmbedding_iff {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α → β} :
    IsUniformEmbedding f ↔ Injective f ∧ UniformContinuous f ∧
      (∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j) := by
  simp only [h.isUniformEmbedding_iff' h', h.uniformContinuous_iff h']
/-
**isUniformEmbedding_subtype_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformEmbedding_subtype_val {p : α -> Prop} : IsUniformEmbedding (Subty
pe.val : Subtype p -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem isUniformEmbedding_subtype_val {p : α → Prop} :
    IsUniformEmbedding (Subtype.val : Subtype p → α) :=
  { comap_uniformity := rfl
    injective := Subtype.val_injective }
/-
**isUniformEmbedding_set_inclusion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformEmbedding_set_inclusion {s t : Set α} (hst : s subseteq t) : IsUn
iformEmbedding (inclusion hst) where comap_uniformity
参数：hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_subtype`：uniformity_subtype {p : α -> Prop} [UniformSpace α] 
: 𝓤 (Subtype p) = comap (fun q : Subtype p × Subtype p => (q.1.1, q.2.1)) (𝓤 α)
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem isUniformEmbedding_set_inclusion {s t : Set α} (hst : s ⊆ t) :
    IsUniformEmbedding (inclusion hst) where
  comap_uniformity := by rw [uniformity_subtype, uniformity_subtype, comap_comap]; rfl
  injective := inclusion_injective hst
/-
**IsUniformEmbedding.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.comp {g : β -> γ} (hg : IsUniformEmbedding g) {f : α ->
 β} (hf : IsUniformEmbedding f) : IsUniformEmbedding (g ∘ f) where toIsUniformIn
ducing
参数：hg : IsUniformEmbedding g；hf : IsUniformEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.comp`：IsUniformInducing.comp {g : β -> γ} (hg : IsUnif
ormInducing g) {f : α -> β} (hf : IsUniformInducing f) : IsUniformInducing (g ∘ 
f)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `IsUniformEmbedding.injective`：∀ {α : Type ua} {β : Type ub} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Func
tion.Injective f
-/
theorem IsUniformEmbedding.comp {g : β → γ} (hg : IsUniformEmbedding g) {f : α → β}
    (hf : IsUniformEmbedding f) : IsUniformEmbedding (g ∘ f) where
  toIsUniformInducing := hg.isUniformInducing.comp hf.isUniformInducing
  injective := hg.injective.comp hf.injective
/-
**IsUniformEmbedding.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.of_comp_iff {g : β -> γ} (hg : IsUniformEmbedding g) {f
 : α -> β} : IsUniformEmbedding (g ∘ f) ↔ IsUniformEmbedding f
参数：hg : IsUniformEmbedding g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUniformInducing.of_comp_iff`：IsUniformInducing.of_comp_iff {g : β -> γ
} (hg : IsUniformInducing g) {f : α -> β} : IsUniformInducing (g ∘ f) ↔ IsUnifor
mInducing f
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `IsUniformEmbedding.injective`：∀ {α : Type ua} {β : Type ub} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Func
tion.Injective f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsUniformEmbedding.of_comp_iff {g : β → γ} (hg : IsUniformEmbedding g) {f : α → β} :
    IsUniformEmbedding (g ∘ f) ↔ IsUniformEmbedding f := by
  simp_rw [isUniformEmbedding_iff, hg.isUniformInducing.of_comp_iff, hg.injective.of_comp_iff f]
/-
**IsUniformEmbedding.of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.of_comp {f : α -> β} {g : β -> γ} (hf : UniformContinuo
us f) (hg : UniformContinuous g) (hgf : IsUniformEmbedding (g ∘ f)) : IsUniformE
mbedding f
参数：hf : UniformContinuous f；hg : UniformContinuous g；hgf : IsUniformEmbedding (g
 ∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.of_comp`：IsUniformInducing.of_comp {f : α -> β} {g : β
 -> γ} (hf : UniformContinuous f) (hg : UniformContinuous g) (hgf : IsUniformInd
ucing (g ∘ f)) …
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `IsUniformEmbedding.injective`：∀ {α : Type ua} {β : Type ub} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Func
tion.Injective f
-/
theorem IsUniformEmbedding.of_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) (hgf : IsUniformEmbedding (g ∘ f)) : IsUniformEmbedding f :=
  ⟨.of_comp hf hg hgf.isUniformInducing, .of_comp hgf.injective⟩
/-
**Equiv.isUniformEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.isUniformEmbedding {α β : Type*} [UniformSpace α] [UniformSpace β] (
f : α ≃ β) (h₁ : UniformContinuous f) (h₂ : UniformContinuous f.symm) : IsUnifor
mEmbedding f
参数：f : α ≃ β；h₁ : UniformContinuous f；h₂ : UniformContinuous f.symm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUniformEmbedding_iff'`：isUniformEmbedding_iff' {f : α -> β} : IsUnifor
mEmbedding f ↔ Injective f ∧ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) <=
 𝓤 α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.prodCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_1
1} {β₂ : Type u_12} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂),   ⇑(e₁.prodCongr e₂) = Prod.m
ap ⇑e₁ ⇑e₂
· 使用定理 `Filter.map_equiv_symm`：map_equiv_symm (e : α ≃ β) (f : Filter β) : map e
.symm f = comap e f
-/
theorem Equiv.isUniformEmbedding {α β : Type*} [UniformSpace α] [UniformSpace β] (f : α ≃ β)
    (h₁ : UniformContinuous f) (h₂ : UniformContinuous f.symm) : IsUniformEmbedding f :=
  isUniformEmbedding_iff'.2 ⟨f.injective, h₁, by rwa [← Equiv.prodCongr_apply, ← map_equiv_symm]⟩
/-
**isUniformEmbedding_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformEmbedding_inl : IsUniformEmbedding (Sum.inl : α -> α oplus β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUniformEmbedding_iff'`：isUniformEmbedding_iff' {f : α -> β} : IsUnifor
mEmbedding f ↔ Injective f ∧ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) <=
 𝓤 α
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `uniformContinuous_inl`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpac
e α] [inst_1 : UniformSpace β], UniformContinuous Sum.inl
· 使用定理 `Filter.union_mem_sup`：union_mem_sup {f g : Filter α} {s t : Set α} (hs :
 s in f) (ht : t in g) : s union t in f ⊔ g
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Filter.range_mem_map`：range_mem_map : range m in map m f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem isUniformEmbedding_inl : IsUniformEmbedding (Sum.inl : α → α ⊕ β) :=
  isUniformEmbedding_iff'.2 ⟨Sum.inl_injective, uniformContinuous_inl, fun s hs =>
    ⟨Prod.map Sum.inl Sum.inl '' s ∪ range (Prod.map Sum.inr Sum.inr),
      union_mem_sup (image_mem_map hs) range_mem_map,
      fun x h => by simpa [Prod.map_apply'] using h⟩⟩
/-
**isUniformEmbedding_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformEmbedding_inr : IsUniformEmbedding (Sum.inr : β -> α oplus β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUniformEmbedding_iff'`：isUniformEmbedding_iff' {f : α -> β} : IsUnifor
mEmbedding f ↔ Injective f ∧ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) <=
 𝓤 α
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `uniformContinuous_inr`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpac
e α] [inst_1 : UniformSpace β], UniformContinuous Sum.inr
· 使用定理 `Filter.union_mem_sup`：union_mem_sup {f g : Filter α} {s t : Set α} (hs :
 s in f) (ht : t in g) : s union t in f ⊔ g
· 使用定理 `Filter.range_mem_map`：range_mem_map : range m in map m f
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem isUniformEmbedding_inr : IsUniformEmbedding (Sum.inr : β → α ⊕ β) :=
  isUniformEmbedding_iff'.2 ⟨Sum.inr_injective, uniformContinuous_inr, fun s hs =>
    ⟨range (Prod.map Sum.inl Sum.inl) ∪ Prod.map Sum.inr Sum.inr '' s,
      union_mem_sup range_mem_map (image_mem_map hs),
      fun x h => by simpa [Prod.map_apply'] using h⟩⟩

/-- If the domain of a `IsUniformInducing` map `f` is a T₀ space, then `f` is injective,
hence it is a `IsUniformEmbedding`. -/
/-
**IsUniformInducing.isUniformEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `IsUniformInduc
ing`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : UniformSpace α] [inst_1 : UniformSpace
 β] [T0Space α] {f : α → β},   IsUniformInducing f → IsUniformEmbedding f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space X] {f : X → Y},   Topo
logy.IsInducing f →…
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f

--- 原说明 ---
If the domain of a `IsUniformInducing` map `f` is a T₀ space, then `f` is inject
ive,
hence it is a `IsUniformEmbedding`.
-/
protected theorem IsUniformInducing.isUniformEmbedding [T0Space α] {f : α → β}
    (hf : IsUniformInducing f) : IsUniformEmbedding f :=
  ⟨hf, hf.isInducing.injective⟩
/-
**isUniformEmbedding_iff_isUniformInducing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformEmbedding_iff_isUniformInducing [T0Space α] {f : α -> β} : IsUnif
ormEmbedding f ↔ IsUniformInducing f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `IsUniformInducing.isUniformEmbedding`：∀ {α : Type u} {β : Type v} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] [T0Space α] {f : α → β},   IsUniform
Inducing f → IsUniformEmbe…
-/
theorem isUniformEmbedding_iff_isUniformInducing [T0Space α] {f : α → β} :
    IsUniformEmbedding f ↔ IsUniformInducing f :=
  ⟨IsUniformEmbedding.isUniformInducing, IsUniformInducing.isUniformEmbedding⟩

/-- If a map `f : α → β` sends any two distinct points to point that are **not** related by a fixed
`s ∈ 𝓤 β`, then `f` is uniform inducing with respect to the discrete uniformity on `α`:
the preimage of `𝓤 β` under `Prod.map f f` is the principal filter generated by the diagonal in
`α × α`. -/
/-
**comap_uniformity_of_spaced_out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_uniformity_of_spaced_out {α} {f : α -> β} {s : Set (β × β)} (hs : s 
in 𝓤 β) (hf : Pairwise fun x y => (f x, f y) ∉ s) : comap (Prod.map f f) (𝓤 β) =
 𝓟 SetRel.id
参数：β × β；hs : s in 𝓤 β；hf : Pairwise fun x y => (f x, f y) ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `refl_le_uniformity`：refl_le_uniformity : 𝓟 SetRel.id <= 𝓤 α

--- 原说明 ---
If a map `f : α → β` sends any two distinct points to point that are **not** rel
ated by a fixed
`s ∈ 𝓤 β`, then `f` is uniform inducing with respect to the discrete uniformity 
on `α`:
the preimage of `𝓤 β` under `Prod.map f f` is the principal filter generated by 
the diagonal in
`α × α`.
-/
theorem comap_uniformity_of_spaced_out {α} {f : α → β} {s : Set (β × β)} (hs : s ∈ 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : comap (Prod.map f f) (𝓤 β) = 𝓟 SetRel.id := by
  refine le_antisymm ?_ (@refl_le_uniformity α (UniformSpace.comap f _))
  calc
    comap (Prod.map f f) (𝓤 β) ≤ comap (Prod.map f f) (𝓟 s) := comap_mono (le_principal_iff.2 hs)
    _ = 𝓟 (Prod.map f f ⁻¹' s) := comap_principal
    _ ≤ 𝓟 SetRel.id := principal_mono.2 ?_
  rintro ⟨x, y⟩; simpa [not_imp_not] using @hf x y

/-- If a map `f : α → β` sends any two distinct points to point that are **not** related by a fixed
`s ∈ 𝓤 β`, then `f` is a uniform embedding with respect to the discrete uniformity on `α`. -/
/-
**isUniformEmbedding_of_spaced_out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformEmbedding_of_spaced_out {α} {f : α -> β} {s : Set (β × β)} (hs : 
s in 𝓤 β) (hf : Pairwise fun x y => (f x, f y) ∉ s) : @IsUniformEmbedding α β ⊥ 
‹_› f
参数：β × β；hs : s in 𝓤 β；hf : Pairwise fun x y => (f x, f y) ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `discreteTopology_bot`：discreteTopology_bot (α : Type*) : @DiscreteTopolo
gy α ⊥
· 使用定理 `IsUniformInducing.isUniformEmbedding`：∀ {α : Type u} {β : Type v} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] [T0Space α] {f : α → β},   IsUniform
Inducing f → IsUniformEmbe…
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `comap_uniformity_of_spaced_out`：comap_uniformity_of_spaced_out {α} {f : 
α -> β} {s : Set (β × β)} (hs : s in 𝓤 β) (hf : Pairwise fun x y => (f x, f y) ∉
 s) : comap (Prod.ma…

--- 原说明 ---
If a map `f : α → β` sends any two distinct points to point that are **not** rel
ated by a fixed
`s ∈ 𝓤 β`, then `f` is a uniform embedding with respect to the discrete uniformi
ty on `α`.
-/
theorem isUniformEmbedding_of_spaced_out {α} {f : α → β} {s : Set (β × β)} (hs : s ∈ 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : @IsUniformEmbedding α β ⊥ ‹_› f := by
  let _ : UniformSpace α := ⊥; have := discreteTopology_bot α
  exact IsUniformInducing.isUniformEmbedding ⟨comap_uniformity_of_spaced_out hs hf⟩
/-
**IsUniformEmbedding.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `IsUniformEmbedding`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : UniformSpace α] [inst_1 : UniformSpace
 β] {f : α → β},   IsUniformEmbedding f → Topology.IsEmbedding f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `IsUniformEmbedding.injective`：∀ {α : Type ua} {β : Type ub} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Func
tion.Injective f
-/
protected lemma IsUniformEmbedding.isEmbedding {f : α → β} (h : IsUniformEmbedding f) :
    IsEmbedding f where
  toIsInducing := h.toIsUniformInducing.isInducing
  injective := h.injective
/-
**IsUniformEmbedding.isDenseEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.isDenseEmbedding {f : α -> β} (h : IsUniformEmbedding f
) (hd : DenseRange f) : IsDenseEmbedding f
参数：h : IsUniformEmbedding f；hd : DenseRange f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
theorem IsUniformEmbedding.isDenseEmbedding {f : α → β} (h : IsUniformEmbedding f)
    (hd : DenseRange f) : IsDenseEmbedding f :=
  { h.isEmbedding with dense := hd }
/-
**isClosedEmbedding_of_spaced_out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedEmbedding_of_spaced_out {α} [TopologicalSpace α] [DiscreteTopology
 α] [T0Space β] {f : α -> β} {s : Set (β × β)} (hs : s in 𝓤 β) (hf : Pairwise fu
n x y => (f x, f y) ∉ s) : IsClosedEmbedding f
参数：β × β；hs : s in 𝓤 β；hf : Pairwise fun x y => (f x, f y) ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `isUniformEmbedding_of_spaced_out`：isUniformEmbedding_of_spaced_out {α} {
f : α -> β} {s : Set (β × β)} (hs : s in 𝓤 β) (hf : Pairwise fun x y => (f x, f 
y) ∉ s) : @IsUniformEm…
· 使用定理 `isClosed_range_of_spaced_out`：isClosed_range_of_spaced_out {ι} [T0Space 
α] {V₀ : Set (α × α)} (V₀_in : V₀ in 𝓤 α) {f : ι -> α} (hf : Pairwise fun x y =>
 (f x, f y) ∉ V₀) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DiscreteTopology.eq_bot`：∀ {α : Type u_2} {t : TopologicalSpace α} [self
 : DiscreteTopology α], t = ⊥
-/
theorem isClosedEmbedding_of_spaced_out {α} [TopologicalSpace α] [DiscreteTopology α]
    [T0Space β] {f : α → β} {s : Set (β × β)} (hs : s ∈ 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : IsClosedEmbedding f := by
  rcases @DiscreteTopology.eq_bot α _ _ with rfl; let _ : UniformSpace α := ⊥
  exact
    { (isUniformEmbedding_of_spaced_out hs hf).isEmbedding with
      isClosed_range := isClosed_range_of_spaced_out hs hf }
/-
**closure_image_mem_nhds_of_isUniformInducing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_image_mem_nhds_of_isUniformInducing {s : Set (α × α)} {e : α -> β}
 (b : β) (he₁ : IsUniformInducing e) (he₂ : IsDenseInducing e) (hs : s in 𝓤 α) :
 exists a, closure (e '' { a' | (a, a') in s }) in 𝓝 b
参数：α × α；b : β；he₁ : IsUniformInducing e；he₂ : IsDenseInducing e；hs : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `uniformity_hasBasis_open_symmetric`：uniformity_hasBasis_open_symmetric :
 HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α ∧ IsOpen V ∧ SetRel.IsSymm V) id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `DenseRange.mem_nhds`：DenseRange.mem_nhds (h : DenseRange f) (hs : s in 𝓝
 x) : exists a, f a in s
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用引理 `UniformSpace.isOpen_ball`：isOpen_ball (x : α) {V : SetRel α α} (hV : IsO
pen V) : IsOpen (ball x V)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniformSpace.mem_ball_symmetry`：mem_ball_symmetry {V : SetRel β β} [V.Is
Symm] {x y} : x in ball y V ↔ y in ball x V
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
-/
theorem closure_image_mem_nhds_of_isUniformInducing {s : Set (α × α)} {e : α → β} (b : β)
    (he₁ : IsUniformInducing e) (he₂ : IsDenseInducing e) (hs : s ∈ 𝓤 α) :
    ∃ a, closure (e '' { a' | (a, a') ∈ s }) ∈ 𝓝 b := by
  obtain ⟨U, ⟨hU, hUo, hsymm⟩, hs⟩ :
    ∃ U, (U ∈ 𝓤 β ∧ IsOpen U ∧ SetRel.IsSymm U) ∧ Prod.map e e ⁻¹' U ⊆ s := by
      rwa [← he₁.comap_uniformity, (uniformity_hasBasis_open_symmetric.comap _).mem_iff] at hs
  rcases he₂.dense.mem_nhds (UniformSpace.ball_mem_nhds b hU) with ⟨a, ha⟩
  refine ⟨a, mem_of_superset ?_ (closure_mono <| image_mono <| UniformSpace.ball_mono hs a)⟩
  have ho : IsOpen (UniformSpace.ball (e a) U) := UniformSpace.isOpen_ball (e a) hUo
  refine mem_of_superset (ho.mem_nhds <| UniformSpace.mem_ball_symmetry.2 ha) fun y hy => ?_
  refine mem_closure_iff_nhds.2 fun V hV => ?_
  rcases he₂.dense.mem_nhds (inter_mem hV (ho.mem_nhds hy)) with ⟨x, hxV, hxU⟩
  exact ⟨e x, hxV, mem_image_of_mem e hxU⟩
/-
**isUniformEmbedding_subtypeEmb** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformEmbedding_subtypeEmb (p : α -> Prop) {e : α -> β} (ue : IsUniform
Embedding e) (de : IsDenseEmbedding e) : IsUniformEmbedding (IsDenseEmbedding.su
btypeEmb p e)
参数：p : α -> Prop；ue : IsUniformEmbedding e；de : IsDenseEmbedding e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsDenseEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbedding e 
→ Function.Injec…
· 使用定理 `IsDenseEmbedding.subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbedding e → 
∀ (p : α → Pro…
-/
theorem isUniformEmbedding_subtypeEmb (p : α → Prop) {e : α → β} (ue : IsUniformEmbedding e)
    (de : IsDenseEmbedding e) : IsUniformEmbedding (IsDenseEmbedding.subtypeEmb p e) :=
  { comap_uniformity := by
      simp [comap_comap, Function.comp_def, IsDenseEmbedding.subtypeEmb, uniformity_subtype,
        ue.comap_uniformity.symm]
    injective := (de.subtype p).injective }
/-
**IsUniformEmbedding.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.prod {α' : Type*} {β' : Type*} [UniformSpace α'] [Unifo
rmSpace β'] {e₁ : α -> α'} {e₂ : β -> β'} (h₁ : IsUniformEmbedding e₁) (h₂ : IsU
niformEmbedding e₂) : IsUniformEmbedding fun p : α × β => (e₁ p.1, e₂ p.2) where
 toIsUniformInducing
参数：h₁ : IsUniformEmbedding e₁；h₂ : IsUniformEmbedding e₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.prod`：IsUniformInducing.prod {α' : Type*} {β' : Type*}
 [UniformSpace α'] [UniformSpace β'] {e₁ : α -> α'} {e₂ : β -> β'} (h₁ : IsUnifo
rmInducing e…
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `Function.Injective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_
3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Injective f → Function.Inj
ective g → Funct…
· 使用定理 `IsUniformEmbedding.injective`：∀ {α : Type ua} {β : Type ub} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Func
tion.Injective f
-/
theorem IsUniformEmbedding.prod {α' : Type*} {β' : Type*} [UniformSpace α'] [UniformSpace β']
    {e₁ : α → α'} {e₂ : β → β'} (h₁ : IsUniformEmbedding e₁) (h₂ : IsUniformEmbedding e₂) :
    IsUniformEmbedding fun p : α × β => (e₁ p.1, e₂ p.2) where
  toIsUniformInducing := h₁.isUniformInducing.prod h₂.isUniformInducing
  injective := h₁.injective.prodMap h₂.injective

/-- A set is complete iff its image under a uniform inducing map is complete. -/
/-
**isComplete_image_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isComplete_image_iff {m : α -> β} {s : Set α} (hm : IsUniformInducing m) :
 IsComplete (m '' s) ↔ IsComplete s
参数：hm : IsUniformInducing m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.filter_map_Iic`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {
t : Set β} {m : α → β},   Set.SurjOn m s t → Set.SurjOn (Filter.map m) (Set.Iic 
(Filter.princip…
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
· 使用定理 `Set.MapsTo.filter_map_Iic`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {
t : Set β} {m : α → β},   Set.MapsTo m s t → Set.MapsTo (Filter.map m) (Set.Iic 
(Filter.princip…
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `imp.swap`：∀ {a b c : Prop}, a → b → c ↔ b → a → c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.SurjOn.forall`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set 
β} {f : α → β} {p : β → Prop},   Set.SurjOn f s t → Set.MapsTo f s t → ((∀ y ∈ t
, p y) …
· 使用定理 `IsUniformInducing.cauchy_map_iff`：IsUniformInducing.cauchy_map_iff {f : 
α -> β} (hf : IsUniformInducing f) {F : Filter α} : Cauchy (map f F) ↔ Cauchy F
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A set is complete iff its image under a uniform inducing map is complete.
-/
theorem isComplete_image_iff {m : α → β} {s : Set α} (hm : IsUniformInducing m) :
    IsComplete (m '' s) ↔ IsComplete s := by
  have fact1 : SurjOn (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 <| m '' s) := surjOn_image .. |>.filter_map_Iic
  have fact2 : MapsTo (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 <| m '' s) := mapsTo_image .. |>.filter_map_Iic
  simp_rw [IsComplete, imp.swap (a := Cauchy _), ← mem_Iic (b := 𝓟 _), fact1.forall fact2,
    hm.cauchy_map_iff, exists_mem_image, map_le_iff_le_comap, hm.isInducing.nhds_eq_comap]

/-- If `f : X → Y` is an `IsUniformInducing` map, the image `f '' s` of a set `s` is complete
  if and only if `s` is complete. -/
/-
**IsUniformInducing.isComplete_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.isComplete_iff {f : α -> β} {s : Set α} (hf : IsUniformI
nducing f) : IsComplete (f '' s) ↔ IsComplete s
参数：hf : IsUniformInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isComplete_image_iff`：isComplete_image_iff {m : α -> β} {s : Set α} (hm 
: IsUniformInducing m) : IsComplete (m '' s) ↔ IsComplete s

--- 原说明 ---
If `f : X → Y` is an `IsUniformInducing` map, the image `f '' s` of a set `s` is
 complete
  if and only if `s` is complete.
-/
theorem IsUniformInducing.isComplete_iff {f : α → β} {s : Set α} (hf : IsUniformInducing f) :
    IsComplete (f '' s) ↔ IsComplete s := isComplete_image_iff hf

/-- If `f : X → Y` is an `IsUniformEmbedding`, the image `f '' s` of a set `s` is complete
  if and only if `s` is complete. -/
/-
**IsUniformEmbedding.isComplete_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.isComplete_iff {f : α -> β} {s : Set α} (hf : IsUniform
Embedding f) : IsComplete (f '' s) ↔ IsComplete s
参数：hf : IsUniformEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.isComplete_iff`：IsUniformInducing.isComplete_iff {f : 
α -> β} {s : Set α} (hf : IsUniformInducing f) : IsComplete (f '' s) ↔ IsComplet
e s
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f

--- 原说明 ---
If `f : X → Y` is an `IsUniformEmbedding`, the image `f '' s` of a set `s` is co
mplete
  if and only if `s` is complete.
-/
theorem IsUniformEmbedding.isComplete_iff {f : α → β} {s : Set α} (hf : IsUniformEmbedding f) :
    IsComplete (f '' s) ↔ IsComplete s := hf.isUniformInducing.isComplete_iff

/-- Sets of a subtype are complete iff their image under the coercion is complete. -/
/-
**Subtype.isComplete_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.isComplete_iff {p : α -> Prop} {s : Set { x // p x }} : IsComplete
 s ↔ IsComplete ((↑) '' s : Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IsUniformEmbedding.isComplete_iff`：IsUniformEmbedding.isComplete_iff {f 
: α -> β} {s : Set α} (hf : IsUniformEmbedding f) : IsComplete (f '' s) ↔ IsComp
lete s
· 使用定理 `isUniformEmbedding_subtype_val`：isUniformEmbedding_subtype_val {p : α ->
 Prop} : IsUniformEmbedding (Subtype.val : Subtype p -> α)

--- 原说明 ---
Sets of a subtype are complete iff their image under the coercion is complete.
-/
theorem Subtype.isComplete_iff {p : α → Prop} {s : Set { x // p x }} :
    IsComplete s ↔ IsComplete ((↑) '' s : Set α) :=
  isUniformEmbedding_subtype_val.isComplete_iff.symm

alias ⟨isComplete_of_complete_image, _⟩ := isComplete_image_iff
/-
**completeSpace_iff_isComplete_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completeSpace_iff_isComplete_range {f : α -> β} (hf : IsUniformInducing f)
 : CompleteSpace α ↔ IsComplete (range f)
参数：hf : IsUniformInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completeSpace_iff_isComplete_univ`：completeSpace_iff_isComplete_univ : C
ompleteSpace α ↔ IsComplete (univ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isComplete_image_iff`：isComplete_image_iff {m : α -> β} {s : Set α} (hm 
: IsUniformInducing m) : IsComplete (m '' s) ↔ IsComplete s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem completeSpace_iff_isComplete_range {f : α → β} (hf : IsUniformInducing f) :
    CompleteSpace α ↔ IsComplete (range f) := by
  rw [completeSpace_iff_isComplete_univ, ← isComplete_image_iff hf, image_univ]

alias ⟨_, IsUniformInducing.completeSpace⟩ := completeSpace_iff_isComplete_range
/-
**IsUniformInducing.isComplete_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUniformInducing.isComplete_range [CompleteSpace α] (hf : IsUniformInduci
ng f) : IsComplete (range f)
参数：hf : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `completeSpace_iff_isComplete_range`：completeSpace_iff_isComplete_range {
f : α -> β} (hf : IsUniformInducing f) : CompleteSpace α ↔ IsComplete (range f)
-/
lemma IsUniformInducing.isComplete_range [CompleteSpace α] (hf : IsUniformInducing f) :
    IsComplete (range f) :=
  (completeSpace_iff_isComplete_range hf).1 ‹_›

/-- If `f` is a surjective uniform inducing map,
then its domain is a complete space iff its codomain is a complete space.
See also `_root_.completeSpace_congr` for a version that assumes `f` to be an equivalence. -/
/-
**IsUniformInducing.completeSpace_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.completeSpace_congr {f : α -> β} (hf : IsUniformInducing
 f) (hsurj : f.Surjective) : CompleteSpace α ↔ CompleteSpace β
参数：hf : IsUniformInducing f；hsurj : f.Surjective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completeSpace_iff_isComplete_range`：completeSpace_iff_isComplete_range {
f : α -> β} (hf : IsUniformInducing f) : CompleteSpace α ↔ IsComplete (range f)
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `completeSpace_iff_isComplete_univ`：completeSpace_iff_isComplete_univ : C
ompleteSpace α ↔ IsComplete (univ : Set α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `f` is a surjective uniform inducing map,
then its domain is a complete space iff its codomain is a complete space.
See also `_root_.completeSpace_congr` for a version that assumes `f` to be an eq
uivalence.
-/
theorem IsUniformInducing.completeSpace_congr {f : α → β} (hf : IsUniformInducing f)
    (hsurj : f.Surjective) : CompleteSpace α ↔ CompleteSpace β := by
  rw [completeSpace_iff_isComplete_range hf, hsurj.range_eq, completeSpace_iff_isComplete_univ]
/-
**SeparationQuotient.completeSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeparationQuotient.completeSpace_iff : CompleteSpace (SeparationQuotient α
) ↔ CompleteSpace α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IsUniformInducing.completeSpace_congr`：IsUniformInducing.completeSpace_c
ongr {f : α -> β} (hf : IsUniformInducing f) (hsurj : f.Surjective) : CompleteSp
ace α ↔ CompleteSpace β
· 使用引理 `SeparationQuotient.isUniformInducing_mk`：SeparationQuotient.isUniformInd
ucing_mk : IsUniformInducing (mk : α -> SeparationQuotient α)
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
-/
theorem SeparationQuotient.completeSpace_iff :
    CompleteSpace (SeparationQuotient α) ↔ CompleteSpace α :=
  .symm <| isUniformInducing_mk.completeSpace_congr surjective_mk
/-
**SeparationQuotient.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparationQuotient.instCompleteSpace [CompleteSpace α] : CompleteSpace (Se
parationQuotient α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeparationQuotient.completeSpace_iff`：SeparationQuotient.completeSpace_i
ff : CompleteSpace (SeparationQuotient α) ↔ CompleteSpace α
-/
instance SeparationQuotient.instCompleteSpace [CompleteSpace α] :
    CompleteSpace (SeparationQuotient α) :=
  completeSpace_iff.2 ‹_›

/-- See also `IsUniformInducing.completeSpace_congr`
for a version that works for non-injective maps. -/
/-
**completeSpace_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completeSpace_congr {e : α ≃ β} (he : IsUniformEmbedding e) : CompleteSpac
e α ↔ CompleteSpace β
参数：he : IsUniformEmbedding e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.completeSpace_congr`：IsUniformInducing.completeSpace_c
ongr {f : α -> β} (hf : IsUniformInducing f) (hsurj : f.Surjective) : CompleteSp
ace α ↔ CompleteSpace β
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e

--- 原说明 ---
See also `IsUniformInducing.completeSpace_congr`
for a version that works for non-injective maps.
-/
theorem completeSpace_congr {e : α ≃ β} (he : IsUniformEmbedding e) :
    CompleteSpace α ↔ CompleteSpace β :=
  he.completeSpace_congr e.surjective
/-
**completeSpace_coe_iff_isComplete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completeSpace_coe_iff_isComplete {s : Set α} : CompleteSpace s ↔ IsComplet
e s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completeSpace_iff_isComplete_range`：completeSpace_iff_isComplete_range {
f : α -> β} (hf : IsUniformInducing f) : CompleteSpace α ↔ IsComplete (range f)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `isUniformEmbedding_subtype_val`：isUniformEmbedding_subtype_val {p : α ->
 Prop} : IsUniformEmbedding (Subtype.val : Subtype p -> α)
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem completeSpace_coe_iff_isComplete {s : Set α} : CompleteSpace s ↔ IsComplete s := by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_subtype_val.isUniformInducing,
    Subtype.range_coe]

alias ⟨_, IsComplete.completeSpace_coe⟩ := completeSpace_coe_iff_isComplete
/-
**IsClosed.completeSpace_coe** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsClosed.completeSpace_coe [CompleteSpace α] {s : Set α} [hs : IsClosed s]
 : CompleteSpace s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsComplete.completeSpace_coe`：∀ {α : Type u} [inst : UniformSpace α] {s 
: Set α}, IsComplete s → CompleteSpace ↑s
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
-/
instance IsClosed.completeSpace_coe [CompleteSpace α] {s : Set α} [hs : IsClosed s] :
    CompleteSpace s := hs.isComplete.completeSpace_coe
/-
**completeSpace_ulift_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completeSpace_ulift_iff : CompleteSpace (ULift α) ↔ CompleteSpace α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.completeSpace_congr`：IsUniformInducing.completeSpace_c
ongr {f : α -> β} (hf : IsUniformInducing f) (hsurj : f.Surjective) : CompleteSp
ace α ↔ CompleteSpace β
· 使用定理 `ULift.down_surjective`：down_surjective : Surjective (@down α)
-/
theorem completeSpace_ulift_iff : CompleteSpace (ULift α) ↔ CompleteSpace α :=
  IsUniformInducing.completeSpace_congr ⟨rfl⟩ ULift.down_surjective

/-- The lift of a complete space to another universe is still complete. -/
/-
**ULift.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.instCompleteSpace [CompleteSpace α] : CompleteSpace (ULift α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `completeSpace_ulift_iff`：completeSpace_ulift_iff : CompleteSpace (ULift 
α) ↔ CompleteSpace α

--- 原说明 ---
The lift of a complete space to another universe is still complete.
-/
instance ULift.instCompleteSpace [CompleteSpace α] : CompleteSpace (ULift α) :=
  completeSpace_ulift_iff.2 ‹_›
/-
**completeSpace_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completeSpace_extension {m : β -> α} (hm : IsUniformInducing m) (dense : D
enseRange m) (h : forall f : Filter β, Cauchy f -> exists x : α, map m f <= 𝓝 x)
 : CompleteSpace α
参数：hm : IsUniformInducing m；dense : DenseRange m；h : forall f : Filter β, Cauchy
 f -> exists x : α, map m f <= 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.comap_neBot`：comap_neBot {f : Filter β} {m : α -> β} (hm : forall
 t in f, exists a, m a in t) : NeBot (comap m f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_lift_sets`：mem_lift_sets (hg : Monotone g) {s : Set β} : s in
 f.lift g ↔ exists t in f, s in g t
· 使用定理 `Filter.monotone_lift'`：monotone_lift' [Preorder γ] {f : γ -> Filter α} {
g : γ -> Set α -> Set β} (hf : Monotone f) (hg : Monotone g) : Monotone fun c =>
 (f c).lift…
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
· 使用定理 `Filter.mem_lift'_sets`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h
 : Set α → Set β},   Monotone h → ∀ {s : Set β}, s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ 
s
· 使用定理 `Filter.NeBot.nonempty_of_mem`：∀ {α : Type u} {f : Filter α}, f.NeBot → ∀
 {s : Set α}, s ∈ f → s.Nonempty
· 使用定理 `DenseRange.nhdsWithin_neBot`：DenseRange.nhdsWithin_neBot {ι : Type*} {f 
: ι -> α} (h : DenseRange f) (x : α) : NeBot (𝓝[range f] x)
· 使用定理 `Filter.mem_inf_of_left`：mem_inf_of_left {f g : Filter α} {s : Set α} (h 
: s in f) : s in f ⊓ g
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `Filter.mem_prod_same_iff`：∀ {α : Type u_1} {la : Filter α} {s : Set (α ×
 α)}, s ∈ la ×ˢ la ↔ ∃ t ∈ la, t ×ˢ t ⊆ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mem_lift`：mem_lift {s : Set β} {t : Set α} (ht : t in f) (hs : s 
in g t) : s in f.lift g
· 使用定理 `symm_le_uniformity`：symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) <= 𝓤
 _
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
（共 40 条，此处仅展示前 30 条）
-/
theorem completeSpace_extension {m : β → α} (hm : IsUniformInducing m) (dense : DenseRange m)
    (h : ∀ f : Filter β, Cauchy f → ∃ x : α, map m f ≤ 𝓝 x) : CompleteSpace α :=
  ⟨fun {f : Filter α} (hf : Cauchy f) =>
    let p : Set (α × α) → Set α → Set α := fun s t => { y : α | ∃ x : α, x ∈ t ∧ (x, y) ∈ s }
    let g := (𝓤 α).lift fun s => f.lift' (p s)
    have mp₀ : Monotone p := fun _ _ h _ _ ⟨x, xs, xa⟩ => ⟨x, xs, h xa⟩
    have mp₁ : ∀ {s}, Monotone (p s) := fun h _ ⟨y, ya, yxs⟩ => ⟨y, h ya, yxs⟩
    have : f ≤ g := le_iInf₂ fun _ hs => le_iInf₂ fun _ ht =>
      le_principal_iff.mpr <| mem_of_superset ht fun x hx => ⟨x, hx, refl_mem_uniformity hs⟩
    have : NeBot g := hf.left.mono this
    have : NeBot (comap m g) :=
      comap_neBot fun _ ht =>
        let ⟨t', ht', ht_mem⟩ := (mem_lift_sets <| monotone_lift' monotone_const mp₀).mp ht
        let ⟨_, ht'', ht'_sub⟩ := (mem_lift'_sets mp₁).mp ht_mem
        let ⟨x, hx⟩ := hf.left.nonempty_of_mem ht''
        have h₀ : NeBot (𝓝[range m] x) := dense.nhdsWithin_neBot x
        have h₁ : { y | (x, y) ∈ t' } ∈ 𝓝[range m] x :=
          @mem_inf_of_left α (𝓝 x) (𝓟 (range m)) _ <| mem_nhds_left x ht'
        have h₂ : range m ∈ 𝓝[range m] x :=
          @mem_inf_of_right α (𝓝 x) (𝓟 (range m)) _ <| Subset.refl _
        have : { y | (x, y) ∈ t' } ∩ range m ∈ 𝓝[range m] x := @inter_mem α (𝓝[range m] x) _ _ h₁ h₂
        let ⟨_, xyt', b, b_eq⟩ := h₀.nonempty_of_mem this
        ⟨b, b_eq.symm ▸ ht'_sub ⟨x, hx, xyt'⟩⟩
    have : Cauchy g :=
      ⟨‹NeBot g›, fun _ hs =>
        let ⟨s₁, hs₁, comp_s₁⟩ := comp_mem_uniformity_sets hs
        let ⟨s₂, hs₂, comp_s₂⟩ := comp_mem_uniformity_sets hs₁
        let ⟨t, ht, (prod_t : t ×ˢ t ⊆ s₂)⟩ := mem_prod_same_iff.mp (hf.right hs₂)
        have hg₁ : p (preimage Prod.swap s₁) t ∈ g :=
          mem_lift (symm_le_uniformity hs₁) <| @mem_lift' α α f _ t ht
        have hg₂ : p s₂ t ∈ g := mem_lift hs₂ <| @mem_lift' α α f _ t ht
        have hg : p (Prod.swap ⁻¹' s₁) t ×ˢ p s₂ t ∈ g ×ˢ g := @prod_mem_prod α α _ _ g g hg₁ hg₂
        (g ×ˢ g).sets_of_superset hg fun ⟨_, _⟩ ⟨⟨c₁, c₁t, hc₁⟩, ⟨c₂, c₂t, hc₂⟩⟩ =>
          have : (c₁, c₂) ∈ t ×ˢ t := ⟨c₁t, c₂t⟩
          comp_s₁ <| SetRel.prodMk_mem_comp hc₁ <| comp_s₂ <|
            SetRel.prodMk_mem_comp (prod_t this) hc₂⟩
    have : Cauchy (Filter.comap m g) := ‹Cauchy g›.comap' (le_of_eq hm.comap_uniformity) ‹_›
    let ⟨x, (hx : map m (Filter.comap m g) ≤ 𝓝 x)⟩ := h _ this
    have : ClusterPt x (map m (Filter.comap m g)) :=
      (le_nhds_iff_adhp_of_cauchy (this.map hm.uniformContinuous)).mp hx
    have : ClusterPt x g := this.mono map_comap_le
    ⟨x,
      calc
        f ≤ g := by assumption
        _ ≤ 𝓝 x := le_nhds_of_cauchy_adhp ‹Cauchy g› this
        ⟩⟩
/-
**Filter.totallyBounded_map_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.totallyBounded_map_iff {f : α -> β} {F : Filter α} (hf : IsUniformI
nducing f) : (F.map f).TotallyBounded ↔ F.TotallyBounded
参数：hf : IsUniformInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.filter_totallyBounded_iff`：Filter.HasBasis.filter_totall
yBounded_iff {ι} {p : ι -> Prop} {U : ι -> SetRel α α} (H : (𝓤 α).HasBasis p U) 
{f : Filter α} : f.TotallyBound…
· 使用定理 `IsUniformInducing.basis_uniformity`：IsUniformInducing.basis_uniformity {
f : α -> β} (hf : IsUniformInducing f) {ι : Sort*} {p : ι -> Prop} {s : ι -> Set
 (β × β)} (H : (𝓤 β).Has…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.exists_subset_image_finite_and`：exists_subset_image_finite_and {f : 
α -> β} {s : Set α} {p : Set β -> Prop} : (exists t subseteq f '' s, t.Finite ∧ 
p t) ↔ exists t subseteq…
· 使用定理 `Filter.TotallyBounded.exists_subset_of_mem`：Filter.TotallyBounded.exists
_subset_of_mem {f : Filter α} (hf : f.TotallyBounded) {s : Set α} (hs : s in f) 
{U : SetRel α α} (hU : U in 𝓤 α)…
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.TotallyBounded.map`：Filter.TotallyBounded.map [UniformSpace β] {f
 : α -> β} {g : Filter α} (hg : g.TotallyBounded) (hf : UniformContinuous f) : (
g.map f).Totall…
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
-/
lemma Filter.totallyBounded_map_iff {f : α → β} {F : Filter α} (hf : IsUniformInducing f) :
    (F.map f).TotallyBounded ↔ F.TotallyBounded := by
  refine ⟨fun hs ↦ ?_, fun h ↦ h.map hf.uniformContinuous⟩
  simp_rw [(hf.basis_uniformity (basis_sets _)).filter_totallyBounded_iff]
  intro t ht
  rcases exists_subset_image_finite_and.1 (hs.exists_subset_of_mem (F.image_mem_map F.univ_mem) ht)
    with ⟨u, -, hfin, h⟩
  use u, hfin
  simp_rw [SetRel.preimage, exists_mem_image] at h
  exact h
/-
**totallyBounded_image_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_image_iff {f : α -> β} {s : Set α} (hf : IsUniformInducing 
f) : TotallyBounded (f '' s) ↔ TotallyBounded s
参数：hf : IsUniformInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Filter.totallyBounded_map_iff`：Filter.totallyBounded_map_iff {f : α -> β
} {F : Filter α} (hf : IsUniformInducing f) : (F.map f).TotallyBounded ↔ F.Total
lyBounded
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma totallyBounded_image_iff {f : α → β} {s : Set α} (hf : IsUniformInducing f) :
    TotallyBounded (f '' s) ↔ TotallyBounded s := by
  simp_rw [← totallyBounded_principal_iff, ← map_principal, totallyBounded_map_iff hf]
/-
**totallyBounded_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：totallyBounded_preimage {f : α -> β} {s : Set β} (hf : IsUniformInducing f
) (hs : TotallyBounded s) : TotallyBounded (f ⁻¹' s)
参数：hf : IsUniformInducing f；hs : TotallyBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `totallyBounded_image_iff`：totallyBounded_image_iff {f : α -> β} {s : Set
 α} (hf : IsUniformInducing f) : TotallyBounded (f '' s) ↔ TotallyBounded s
· 使用定理 `TotallyBounded.subset`：TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) (h : TotallyBounded s₂) : TotallyBounded s₁
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem totallyBounded_preimage {f : α → β} {s : Set β} (hf : IsUniformInducing f)
    (hs : TotallyBounded s) : TotallyBounded (f ⁻¹' s) :=
  (totallyBounded_image_iff hf).1 <| hs.subset <| image_preimage_subset ..
/-
**Filter.totallyBounded_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.totallyBounded_comap {f : α -> β} {F : Filter β} (hf : IsUniformInd
ucing f) (hF : F.TotallyBounded) : (F.comap f).TotallyBounded
参数：hf : IsUniformInducing f；hF : F.TotallyBounded。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.totallyBounded_map_iff`：Filter.totallyBounded_map_iff {f : α -> β
} {F : Filter α} (hf : IsUniformInducing f) : (F.map f).TotallyBounded ↔ F.Total
lyBounded
· 使用定理 `Filter.TotallyBounded.mono`：Filter.TotallyBounded.mono {f g : Filter α} 
(h : f <= g) (hg : g.TotallyBounded) : f.TotallyBounded
· 使用定理 `Filter.map_comap_le`：map_comap_le : map m (comap m g) <= g
-/
theorem Filter.totallyBounded_comap {f : α → β} {F : Filter β} (hf : IsUniformInducing f)
    (hF : F.TotallyBounded) : (F.comap f).TotallyBounded :=
  (totallyBounded_map_iff hf).1 <| hF.mono map_comap_le
/-
**CompleteSpace.sum** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CompleteSpace.sum [CompleteSpace α] [CompleteSpace β] : CompleteSpace (α o
plus β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completeSpace_iff_isComplete_univ`：completeSpace_iff_isComplete_univ : C
ompleteSpace α ↔ IsComplete (univ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_inl_union_range_inr`：range_inl_union_range_inr : range (Sum.in
l : α -> α oplus β) union range Sum.inr = univ
· 使用定理 `IsComplete.union`：∀ {α : Type u} [uniformSpace : UniformSpace α] {s t : 
Set α}, IsComplete s → IsComplete t → IsComplete (s ∪ t)
· 使用引理 `IsUniformInducing.isComplete_range`：IsUniformInducing.isComplete_range [
CompleteSpace α] (hf : IsUniformInducing f) : IsComplete (range f)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `isUniformEmbedding_inl`：isUniformEmbedding_inl : IsUniformEmbedding (Sum
.inl : α -> α oplus β)
· 使用定理 `isUniformEmbedding_inr`：isUniformEmbedding_inr : IsUniformEmbedding (Sum
.inr : β -> α oplus β)
-/
instance CompleteSpace.sum [CompleteSpace α] [CompleteSpace β] : CompleteSpace (α ⊕ β) := by
  rw [completeSpace_iff_isComplete_univ, ← range_inl_union_range_inr]
  exact isUniformEmbedding_inl.isUniformInducing.isComplete_range.union
    isUniformEmbedding_inr.isUniformInducing.isComplete_range
/-
**IsUniformEmbedding.discreteUniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.discreteUniformity [DiscreteUniformity β] {f : α -> β} 
(hf : IsUniformEmbedding f) : DiscreteUniformity α
参数：hf : IsUniformEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `DiscreteUniformity.eq_principal_setRelId`：eq_principal_setRelId : unifor
mity X = 𝓟 SetRel.id
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsUniformEmbedding.injective`：∀ {α : Type ua} {β : Type ub} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Func
tion.Injective f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsUniformEmbedding.discreteUniformity [DiscreteUniformity β] {f : α → β}
    (hf : IsUniformEmbedding f) : DiscreteUniformity α := by
  simp_rw [discreteUniformity_iff_eq_principal_setRelId, ← hf.comap_uniformity,
    DiscreteUniformity.eq_principal_setRelId, comap_principal, SetRel.id, preimage_ofPred_eq,
    hf.injective.eq_iff]

end

/-
**isUniformEmbedding_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformEmbedding_comap {α : Type*} {β : Type*} {f : α -> β} [u : Uniform
Space β] (hf : Function.Injective f) : @IsUniformEmbedding α β (UniformSpace.com
ap f u) u f
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isUniformEmbedding_comap {α : Type*} {β : Type*} {f : α → β} [u : UniformSpace β]
    (hf : Function.Injective f) : @IsUniformEmbedding α β (UniformSpace.comap f u) u f :=
  @IsUniformEmbedding.mk _ _ (UniformSpace.comap f u) _ _
    (@IsUniformInducing.mk _ _ (UniformSpace.comap f u) _ _ rfl) hf

/-- Pull back a uniform space structure by an embedding, adjusting the new uniform structure to
make sure that its topology is defeq to the original one. -/
@[instance_reducible]
/-
**Topology.IsEmbedding.comapUniformSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.comapUniformSpace {α β} [TopologicalSpace α] [u : Uni
formSpace β] (f : α -> β) (h : IsEmbedding f) : UniformSpace α
参数：f : α -> β；h : IsEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a uniform space structure by an embedding, adjusting the new uniform s
tructure to
make sure that its topology is defeq to the original one.
-/
def Topology.IsEmbedding.comapUniformSpace {α β} [TopologicalSpace α] [u : UniformSpace β]
    (f : α → β) (h : IsEmbedding f) : UniformSpace α :=
  (u.comap f).replaceTopology h.eq_induced
/-
**Embedding.to_isUniformEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Embedding.to_isUniformEmbedding {α β} [TopologicalSpace α] [u : UniformSpa
ce β] (f : α -> β) (h : IsEmbedding f) : @IsUniformEmbedding α β (h.comapUniform
Space f) u f
参数：f : α -> β；h : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
theorem Embedding.to_isUniformEmbedding {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α → β)
    (h : IsEmbedding f) : @IsUniformEmbedding α β (h.comapUniformSpace f) u f :=
  let _ := h.comapUniformSpace f
  { comap_uniformity := rfl
    injective := h.injective }

section UniformExtension

variable {α : Type*} {β : Type*} {γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {e : β → α} (h_e : IsUniformInducing e) (h_dense : DenseRange e) {f : β → γ}
  (h_f : UniformContinuous f)

local notation "ψ" => IsDenseInducing.extend (IsUniformInducing.isDenseInducing h_e h_dense) f

include h_e h_dense h_f in
/-
**uniformly_extend_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformly_extend_exists [CompleteSpace γ] (a : α) : exists c, Tendsto f (c
omap e (𝓝 a)) (𝓝 c)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.isDenseInducing`：IsUniformInducing.isDenseInducing (h 
: IsUniformInducing f) (hd : DenseRange f) : IsDenseInducing f where toIsInducin
g
· 使用定理 `cauchy_nhds`：cauchy_nhds {a : α} : Cauchy (𝓝 a)
· 使用定理 `Cauchy.comap'`：Cauchy.comap' [UniformSpace β] {f : Filter β} {m : α -> β
} (hf : Cauchy f) (hm : Filter.comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) <= 
𝓤 α…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `IsDenseInducing.comap_nhds_neBot`：comap_nhds_neBot (di : IsDenseInducing
 i) (b : β) : NeBot (comap i (𝓝 b))
· 使用定理 `Cauchy.map`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] 
[inst : UniformSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuo
…
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
-/
theorem uniformly_extend_exists [CompleteSpace γ] (a : α) : ∃ c, Tendsto f (comap e (𝓝 a)) (𝓝 c) :=
  let de := h_e.isDenseInducing h_dense
  have : Cauchy (𝓝 a) := cauchy_nhds
  have : Cauchy (comap e (𝓝 a)) :=
    this.comap' (le_of_eq h_e.comap_uniformity) (de.comap_nhds_neBot _)
  have : Cauchy (map f (comap e (𝓝 a))) := this.map h_f
  CompleteSpace.complete this
/-
**uniform_extend_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniform_extend_subtype [CompleteSpace γ] {p : α -> Prop} {e : α -> β} {f :
 α -> γ} {b : β} {s : Set α} (hf : UniformContinuous fun x : Subtype p => f x.va
l) (he : IsUniformEmbedding e) (hd : forall x : β, x in closure (range e)) (hb :
 closure (e '' s) in 𝓝 b) (hs : IsClosed s) (hp : forall x in s, p x) : exists c
, Tendsto f (comap e (𝓝 b)) (𝓝 c)
参数：hf : UniformContinuous fun x : Subtype p => f x.val；he : IsUniformEmbedding e
；hd : forall x : β, x in closure (range e)；hb : closure (e '' s) in 𝓝 b；hs : IsC
losed s；hp : forall x in s, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isDenseEmbedding`：IsUniformEmbedding.isDenseEmbedding
 {f : α -> β} (h : IsUniformEmbedding f) (hd : DenseRange f) : IsDenseEmbedding 
f
· 使用定理 `IsDenseEmbedding.subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbedding e → 
∀ (p : α → Pro…
· 使用定理 `isUniformEmbedding_subtypeEmb`：isUniformEmbedding_subtypeEmb (p : α -> P
rop) {e : α -> β} (ue : IsUniformEmbedding e) (de : IsDenseEmbedding e) : IsUnif
ormEmbedding (IsDen…
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Set.monotone_image`：monotone_image : Monotone (image f)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `uniformly_extend_exists`：uniformly_extend_exists [CompleteSpace γ] (a : 
α) : exists c, Tendsto f (comap e (𝓝 a)) (𝓝 c)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `IsDenseEmbedding.toIsDenseInducing`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbe
dding e → IsDenseInducin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_subtype_eq_comap`：nhds_subtype_eq_comap {x : X} {h : p x} : 𝓝 (⟨x, 
h⟩ : Subtype p) = comap (↑) (𝓝 x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_comap'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} {m : α → β} {f : Filter α} {g : Filter β} {i : γ → α},   Set.range i ∈ f → (Fi
lter.Tendsto (m…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)
· 使用引理 `IsDenseInducing.isInducing`：isInducing (di : IsDenseInducing i) : IsIndu
cing i
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem uniform_extend_subtype [CompleteSpace γ] {p : α → Prop} {e : α → β} {f : α → γ} {b : β}
    {s : Set α} (hf : UniformContinuous fun x : Subtype p => f x.val) (he : IsUniformEmbedding e)
    (hd : ∀ x : β, x ∈ closure (range e)) (hb : closure (e '' s) ∈ 𝓝 b) (hs : IsClosed s)
    (hp : ∀ x ∈ s, p x) : ∃ c, Tendsto f (comap e (𝓝 b)) (𝓝 c) := by
  have de : IsDenseEmbedding e := he.isDenseEmbedding hd
  have de' : IsDenseEmbedding (IsDenseEmbedding.subtypeEmb p e) := de.subtype p
  have ue' : IsUniformEmbedding (IsDenseEmbedding.subtypeEmb p e) :=
    isUniformEmbedding_subtypeEmb _ he de
  have : b ∈ closure (e '' { x | p x }) :=
    (closure_mono <| monotone_image <| hp) (mem_of_mem_nhds hb)
  let ⟨c, hc⟩ := uniformly_extend_exists ue'.isUniformInducing de'.dense hf ⟨b, this⟩
  replace hc : Tendsto (f ∘ Subtype.val (p := p)) (((𝓝 b).comap e).comap Subtype.val) (𝓝 c) := by
    simpa only [nhds_subtype_eq_comap, comap_comap, IsDenseEmbedding.subtypeEmb_coe] using! hc
  refine ⟨c, (tendsto_comap'_iff ?_).1 hc⟩
  rw [Subtype.range_coe_subtype]
  exact ⟨_, hb, by rwa [← de.isInducing.closure_eq_preimage_closure_image, hs.closure_eq]⟩

include h_e h_f in
/-
**uniformly_extend_spec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformly_extend_spec [CompleteSpace γ] (a : α) : Tendsto f (comap e (𝓝 a)
) (𝓝 (ψ a))
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.isDenseInducing`：IsUniformInducing.isDenseInducing (h 
: IsUniformInducing f) (hd : DenseRange f) : IsDenseInducing f where toIsInducin
g
· 使用定理 `tendsto_nhds_limUnder`：tendsto_nhds_limUnder {f : Filter α} {g : α -> X}
 (h : exists x, Tendsto g f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty 
f g))
· 使用定理 `uniformly_extend_exists`：uniformly_extend_exists [CompleteSpace γ] (a : 
α) : exists c, Tendsto f (comap e (𝓝 a)) (𝓝 c)
-/
theorem uniformly_extend_spec [CompleteSpace γ] (a : α) : Tendsto f (comap e (𝓝 a)) (𝓝 (ψ a)) := by
  simpa only [IsDenseInducing.extend] using
    tendsto_nhds_limUnder (uniformly_extend_exists h_e ‹_› h_f _)

include h_f in
/-
**uniformContinuous_uniformly_extend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_uniformly_extend [CompleteSpace γ] : UniformContinuous ψ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.isDenseInducing`：IsUniformInducing.isDenseInducing (h 
: IsUniformInducing f) (hd : DenseRange f) : IsDenseInducing f where toIsInducin
g
· 使用定理 `comp3_mem_uniformity`：comp3_mem_uniformity {s : SetRel α α} (hs : s in 𝓤
 α) : exists t in 𝓤 α, t ○ (t ○ t) subseteq s
· 使用定理 `Filter.NeBot.map`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α}, f.NeBo
t → ∀ (m : α → β), (Filter.map m f).NeBot
· 使用定理 `IsDenseInducing.comap_nhds_neBot`：comap_nhds_neBot (di : IsDenseInducing
 i) (b : β) : NeBot (comap i (𝓝 b))
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `uniformly_extend_spec`：uniformly_extend_spec [CompleteSpace γ] (a : α) :
 Tendsto f (comap e (𝓝 a)) (𝓝 (ψ a))
· 使用定理 `mem_nhds_right`：mem_nhds_right (y : α) {s : SetRel α α} (h : s in 𝓤 α) :
 { x : α | (x, y) in s } in 𝓝 y
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x
· 使用定理 `Filter.NeBot.nonempty_of_mem`：∀ {α : Type u} {f : Filter α}, f.NeBot → ∀
 {s : Set α}, s ∈ f → s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `interior_mem_uniformity`：interior_mem_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : interior s in 𝓤 α
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_prod_iff`：mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
 s in 𝓝 (x, y) ↔ exists u in 𝓝 x, exists v in 𝓝 y, u ×ˢ v subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem uniformContinuous_uniformly_extend [CompleteSpace γ] : UniformContinuous ψ := fun d hd =>
  let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
  have h_pnt : ∀ {a m}, m ∈ 𝓝 a → ∃ c ∈ f '' e ⁻¹' m, (c, ψ a) ∈ s ∧ (ψ a, c) ∈ s :=
    fun {a m} hm =>
    have nb : NeBot (map f (comap e (𝓝 a))) :=
      ((h_e.isDenseInducing h_dense).comap_nhds_neBot _).map _
    have :
      f '' (e ⁻¹' m) ∩ ({ c | (c, ψ a) ∈ s } ∩ { c | (ψ a, c) ∈ s }) ∈ map f (comap e (𝓝 a)) :=
      inter_mem (image_mem_map <| preimage_mem_comap <| hm)
        (uniformly_extend_spec h_e h_dense h_f _
          (inter_mem (mem_nhds_right _ hs) (mem_nhds_left _ hs)))
    nb.nonempty_of_mem this
  have : (Prod.map f f) ⁻¹' s ∈ 𝓤 β := h_f hs
  have : (Prod.map f f) ⁻¹' s ∈ comap (Prod.map e e) (𝓤 α) := by
    rwa [← h_e.comap_uniformity] at this
  let ⟨t, ht, ts⟩ := this
  show (Prod.map ψ ψ) ⁻¹' d ∈ 𝓤 α from
    mem_of_superset (interior_mem_uniformity ht) fun ⟨x₁, x₂⟩ hx_t => by
      have : interior t ∈ 𝓝 (x₁, x₂) := isOpen_interior.mem_nhds hx_t
      let ⟨m₁, hm₁, m₂, hm₂, (hm : m₁ ×ˢ m₂ ⊆ interior t)⟩ := mem_nhds_prod_iff.mp this
      obtain ⟨_, ⟨a, ha₁, rfl⟩, _, ha₂⟩ := h_pnt hm₁
      obtain ⟨_, ⟨b, hb₁, rfl⟩, hb₂, _⟩ := h_pnt hm₂
      have : Prod.map f f (a, b) ∈ s :=
        ts <| mem_preimage.2 <| interior_subset (@hm (e a, e b) ⟨ha₁, hb₁⟩)
      exact hs_comp ⟨f a, ha₂, ⟨f b, this, hb₂⟩⟩

variable [T0Space γ]

include h_f in
/-
**uniformly_extend_of_ind** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformly_extend_of_ind (b : β) : ψ (e b) = f b
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_at`：extend_eq_at [T2Space γ] (di : IsDenseIndu
cing i) {f : α -> γ} {a : α} (hf : ContinuousAt f a) : di.extend f (i a) = f a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用引理 `IsUniformInducing.isDenseInducing`：IsUniformInducing.isDenseInducing (h 
: IsUniformInducing f) (hd : DenseRange f) : IsDenseInducing f where toIsInducin
g
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
-/
theorem uniformly_extend_of_ind (b : β) : ψ (e b) = f b :=
  IsDenseInducing.extend_eq_at _ h_f.continuous.continuousAt
/-
**uniformly_extend_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformly_extend_unique {g : α -> γ} (hg : forall b, g (e b) = f b) (hc : 
Continuous g) : ψ = g
参数：hg : forall b, g (e b) = f b；hc : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_unique`：extend_unique [T2Space γ] {f : α -> γ} {g
 : β -> γ} (di : IsDenseInducing i) (hf : forall x, g (i x) = f x) (hg : Continu
ous g) : di.extend …
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用引理 `IsUniformInducing.isDenseInducing`：IsUniformInducing.isDenseInducing (h 
: IsUniformInducing f) (hd : DenseRange f) : IsDenseInducing f where toIsInducin
g
-/
theorem uniformly_extend_unique {g : α → γ} (hg : ∀ b, g (e b) = f b) (hc : Continuous g) : ψ = g :=
  IsDenseInducing.extend_unique _ hg hc

end UniformExtension

section DenseExtension

variable {α β : Type*} [UniformSpace α] [UniformSpace β]

/-
**isUniformInducing_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformInducing_val (s : Set α) : IsUniformInducing ((↑) : s -> α)
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformity_setCoe`：uniformity_setCoe {s : Set α} [UniformSpace α] : 𝓤 s 
= comap (Prod.map ((↑) : s -> α) ((↑) : s -> α)) (𝓤 α)
-/
theorem isUniformInducing_val (s : Set α) :
    IsUniformInducing ((↑) : s → α) := ⟨uniformity_setCoe⟩

@[simp]
/-
**uniformContinuous_rangeFactorization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_rangeFactorization_iff {f : α -> β} : UniformContinuous 
(rangeFactorization f) ↔ UniformContinuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用定理 `isUniformInducing_val`：isUniformInducing_val (s : Set α) : IsUniformIndu
cing ((↑) : s -> α)
-/
theorem uniformContinuous_rangeFactorization_iff {f : α → β} :
    UniformContinuous (rangeFactorization f) ↔ UniformContinuous f :=
  (isUniformInducing_val _).uniformContinuous_iff
/-
**UniformContinuous.rangeFactorization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.rangeFactorization {f : α -> β} (hf : UniformContinuous 
f) : UniformContinuous (rangeFactorization f)
参数：hf : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniformContinuous_rangeFactorization_iff`：uniformContinuous_rangeFactori
zation_iff {f : α -> β} : UniformContinuous (rangeFactorization f) ↔ UniformCont
inuous f
-/
theorem UniformContinuous.rangeFactorization {f : α → β} (hf : UniformContinuous f) :
    UniformContinuous (rangeFactorization f) :=
  uniformContinuous_rangeFactorization_iff.mpr hf

@[simp]
/-
**isUniformInducing_rangeFactorization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformInducing_rangeFactorization_iff {f : α -> β} : IsUniformInducing 
(rangeFactorization f) ↔ IsUniformInducing f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IsUniformInducing.of_comp_iff`：IsUniformInducing.of_comp_iff {g : β -> γ
} (hg : IsUniformInducing g) {f : α -> β} : IsUniformInducing (g ∘ f) ↔ IsUnifor
mInducing f
· 使用定理 `isUniformInducing_val`：isUniformInducing_val (s : Set α) : IsUniformIndu
cing ((↑) : s -> α)
-/
theorem isUniformInducing_rangeFactorization_iff {f : α → β} :
    IsUniformInducing (rangeFactorization f) ↔ IsUniformInducing f :=
  (isUniformInducing_val (range f)).of_comp_iff.symm
/-
**IsUniformInducing.rangeFactorization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.rangeFactorization {f : α -> β} (hf : IsUniformInducing 
f) : IsUniformInducing (rangeFactorization f)
参数：hf : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUniformInducing_rangeFactorization_iff`：isUniformInducing_rangeFactori
zation_iff {f : α -> β} : IsUniformInducing (rangeFactorization f) ↔ IsUniformIn
ducing f
-/
theorem IsUniformInducing.rangeFactorization {f : α → β} (hf : IsUniformInducing f) :
    IsUniformInducing (rangeFactorization f) :=
  isUniformInducing_rangeFactorization_iff.2 hf

namespace Dense

variable {s : Set α} {f : s → β}

/-
**Dense.extend_exists** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：extend_exists [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) 
(a : α) : exists b, Tendsto f (comap (↑) (𝓝 a)) (𝓝 b)
参数：hs : Dense s；hf : UniformContinuous f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformly_extend_exists`：uniformly_extend_exists [CompleteSpace γ] (a : 
α) : exists c, Tendsto f (comap e (𝓝 a)) (𝓝 c)
· 使用定理 `isUniformInducing_val`：isUniformInducing_val (s : Set α) : IsUniformIndu
cing ((↑) : s -> α)
· 使用定理 `Dense.denseRange_val`：Dense.denseRange_val (h : Dense s) : DenseRange ((
↑) : s -> X)
-/
theorem extend_exists [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) (a : α) :
    ∃ b, Tendsto f (comap (↑) (𝓝 a)) (𝓝 b) :=
  uniformly_extend_exists (isUniformInducing_val s) hs.denseRange_val hf a
/-
**Dense.extend_spec** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：extend_spec [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) (a
 : α) : Tendsto f (comap (↑) (𝓝 a)) (𝓝 (hs.extend f a))
参数：hs : Dense s；hf : UniformContinuous f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformly_extend_spec`：uniformly_extend_spec [CompleteSpace γ] (a : α) :
 Tendsto f (comap e (𝓝 a)) (𝓝 (ψ a))
· 使用定理 `isUniformInducing_val`：isUniformInducing_val (s : Set α) : IsUniformIndu
cing ((↑) : s -> α)
· 使用定理 `Dense.denseRange_val`：Dense.denseRange_val (h : Dense s) : DenseRange ((
↑) : s -> X)
-/
theorem extend_spec [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) (a : α) :
    Tendsto f (comap (↑) (𝓝 a)) (𝓝 (hs.extend f a)) :=
  uniformly_extend_spec (isUniformInducing_val s) hs.denseRange_val hf a
/-
**Dense.uniformContinuous_extend** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：uniformContinuous_extend [CompleteSpace β] (hs : Dense s) (hf : UniformCon
tinuous f) : UniformContinuous (hs.extend f)
参数：hs : Dense s；hf : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_uniformly_extend`：uniformContinuous_uniformly_extend [
CompleteSpace γ] : UniformContinuous ψ
· 使用定理 `isUniformInducing_val`：isUniformInducing_val (s : Set α) : IsUniformIndu
cing ((↑) : s -> α)
· 使用定理 `Dense.denseRange_val`：Dense.denseRange_val (h : Dense s) : DenseRange ((
↑) : s -> X)
-/
theorem uniformContinuous_extend [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) :
    UniformContinuous (hs.extend f) :=
  uniformContinuous_uniformly_extend (isUniformInducing_val s) hs.denseRange_val hf

variable [T0Space β]
/-
**Dense.extend_of_ind** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：extend_of_ind (hs : Dense s) (hf : UniformContinuous f) (x : s) : hs.exten
d f x = f x
参数：hs : Dense s；hf : UniformContinuous f；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_at`：extend_eq_at [T2Space γ] (di : IsDenseIndu
cing i) {f : α -> γ} {a : α} (hf : ContinuousAt f a) : di.extend f (i a) = f a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `Dense.isDenseInducing_val`：∀ {α : Type u_1} [inst : TopologicalSpace α] 
{s : Set α}, Dense s → IsDenseInducing Subtype.val
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
-/
theorem extend_of_ind (hs : Dense s) (hf : UniformContinuous f) (x : s) :
    hs.extend f x = f x :=
  IsDenseInducing.extend_eq_at _ hf.continuous.continuousAt

end Dense

/-
**IsDenseInducing.isUniformInducing_extend** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDenseInducing.isUniformInducing_extend {γ : Type*} [UniformSpace γ] [Com
pleteSpace β] [CompleteSpace γ] {i : α -> β} {f : α -> γ} (hid : IsDenseInducing
 i) (hi : IsUniformInducing i) (h : IsUniformInducing f) : IsUniformInducing (hi
d.extend f)
参数：hid : IsDenseInducing i；hi : IsUniformInducing i；h : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsComplete.completeSpace_coe`：∀ {α : Type u} [inst : UniformSpace α] {s 
: Set α}, IsComplete s → CompleteSpace ↑s
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsUniformInducing.comp`：IsUniformInducing.comp {g : β -> γ} (hg : IsUnif
ormInducing g) {f : α -> β} (hf : IsUniformInducing f) : IsUniformInducing (g ∘ 
f)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `isUniformEmbedding_set_inclusion`：isUniformEmbedding_set_inclusion {s t 
: Set α} (hst : s subseteq t) : IsUniformEmbedding (inclusion hst) where comap_u
niformity
· 使用定理 `IsUniformInducing.rangeFactorization`：IsUniformInducing.rangeFactorizati
on {f : α -> β} (hf : IsUniformInducing f) : IsUniformInducing (rangeFactorizati
on f)
· 使用引理 `SeparationQuotient.isUniformInducing_mk`：SeparationQuotient.isUniformInd
ucing_mk : IsUniformInducing (mk : α -> SeparationQuotient α)
· 使用定理 `DenseRange.comp`：DenseRange.comp {g : Y -> Z} {f : α -> Y} (hg : DenseRa
nge g) (hf : DenseRange f) (cg : Continuous g) : DenseRange (g ∘ f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `denseRange_inclusion_iff`：denseRange_inclusion_iff {s t : Set X} (hst : 
s subseteq t) : DenseRange (inclusion hst) ↔ t subseteq closure s
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
· 使用定理 `continuous_inclusion`：continuous_inclusion {s t : Set X} (h : s subseteq
 t) : Continuous (inclusion h)
· 使用引理 `IsUniformInducing.isDenseInducing`：IsUniformInducing.isDenseInducing (h 
: IsUniformInducing f) (hd : DenseRange f) : IsDenseInducing f where toIsInducin
g
· 使用定理 `uniformContinuous_uniformly_extend`：uniformContinuous_uniformly_extend [
CompleteSpace γ] : UniformContinuous ψ
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 60 条，此处仅展示前 30 条）
-/
lemma IsDenseInducing.isUniformInducing_extend {γ : Type*} [UniformSpace γ]
    [CompleteSpace β] [CompleteSpace γ] {i : α → β} {f : α → γ}
    (hid : IsDenseInducing i) (hi : IsUniformInducing i) (h : IsUniformInducing f) :
    IsUniformInducing (hid.extend f) := by
  let sf := SeparationQuotient.mk ∘ f
  have : CompleteSpace (closure (range sf)) :=
    isClosed_closure.isComplete.completeSpace_coe
  let ff : α → closure (range sf) := inclusion subset_closure ∘ rangeFactorization sf
  have hgu : IsUniformInducing ff :=
    (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing.comp
      (SeparationQuotient.isUniformInducing_mk.comp h).rangeFactorization
  have hgd : DenseRange ff :=
    ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
      rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
  have hg : IsDenseInducing ff := hgu.isDenseInducing hgd
  let fwd := hid.extend ff
  have hfwd : UniformContinuous fwd :=
    uniformContinuous_uniformly_extend hi hid.dense hgu.uniformContinuous
  have hg' : UniformContinuous (hg.extend i) :=
    uniformContinuous_uniformly_extend hgu hgd hi.uniformContinuous
  have key : SeparationQuotient.mk ∘ hg.extend i ∘ fwd = SeparationQuotient.mk := by
    ext x
    induction x using isClosed_property hid.dense
    · exact isClosed_eq (SeparationQuotient.continuous_mk.comp (hg'.comp hfwd).continuous)
        SeparationQuotient.continuous_mk
    · simpa [fwd, hid.extend_eq hgu.uniformContinuous.continuous]
        using hg.inseparable_extend hi.uniformContinuous.continuous.continuousAt
  have hfu : IsUniformInducing fwd := by
    refine IsUniformInducing.of_comp hfwd (SeparationQuotient.uniformContinuous_mk.comp hg') ?_
    rw [Function.comp_assoc, key]
    exact SeparationQuotient.isUniformInducing_mk
  have hrr : range (SeparationQuotient.mk ∘ hid.extend f) ⊆
      closure (range (SeparationQuotient.mk ∘ f)) := by
    refine ((SeparationQuotient.continuous_mk.comp (uniformContinuous_uniformly_extend hi hid.dense
      h.uniformContinuous).continuous).range_subset_closure_image_dense hid.dense).trans
      (closure_mono (subset_of_eq ?_))
    rw [← range_comp]
    apply congrArg range
    funext x
    simpa using (hid.inseparable_extend h.uniformContinuous.continuous.continuousAt)
  suffices Subtype.val ∘ fwd = SeparationQuotient.mk ∘ hid.extend f by
    rw [← SeparationQuotient.isUniformInducing_mk.of_comp_iff, ← this]
    exact (isUniformInducing_val _).comp hfu
  rw [← coe_comp_rangeFactorization (SeparationQuotient.mk ∘ hid.extend f),
    ← val_comp_inclusion hrr, Function.comp_assoc, Subtype.val_injective.comp_left.eq_iff]
  refine hid.extend_unique ?_ ?_
  · simp [ff, hid.inseparable_extend h.uniformContinuous.continuous.continuousAt, sf]
  · exact (continuous_inclusion hrr).comp
      (SeparationQuotient.continuous_mk.comp (uniformContinuous_uniformly_extend hi hid.dense
        h.uniformContinuous).continuous).rangeFactorization

end DenseExtension

