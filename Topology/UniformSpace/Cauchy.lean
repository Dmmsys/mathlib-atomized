/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Bases
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-!
# Theory of Cauchy filters in uniform spaces. Complete uniform spaces. Totally bounded subsets.
-/

@[expose] public section

universe u v

open Filter Function TopologicalSpace Topology Set UniformSpace Uniformity
open scoped SetRel

variable {α : Type u} {β : Type v} [uniformSpace : UniformSpace α]

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
/-
**Cauchy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Cauchy (f : Filter α)
参数：f : Filter α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence.
-/
def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f ≤ 𝓤 α

/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
/-
**IsComplete** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsComplete (s : Set α)
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`).
-/
def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x
/-
**Filter.HasBasis.cauchy_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.cauchy_iff {ι} {p : ι -> Prop} {s : ι -> SetRel α α} (h : 
(𝓤 α).HasBasis p s) {f : Filter α} : Cauchy f ↔ NeBot f ∧ forall i, p i -> exist
s t in f, forall x in t, forall y in t, (x, y) in s i
参数：h : (𝓤 α).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.HasBasis.cauchy_iff {ι} {p : ι → Prop} {s : ι → SetRel α α} (h : (𝓤 α).HasBasis p s)
    {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ i, p i → ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, (x, y) ∈ s i :=
  and_congr Iff.rfl <|
    (f.basis_sets.prod_self.le_basis_iff h).trans <| by
      simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, id, forall_mem_comm]
/-
**cauchy_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchy_iff' {f : Filter α} : Cauchy f ↔ NeBot f ∧ forall s in 𝓤 α, exists 
t in f, forall x in t, forall y in t, (x, y) in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.cauchy_iff`：Filter.HasBasis.cauchy_iff {ι} {p : ι -> Pro
p} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s) {f : Filter α} : Cauchy f ↔ Ne
Bot f ∧ forall i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem cauchy_iff' {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, (x, y) ∈ s :=
  (𝓤 α).basis_sets.cauchy_iff
/-
**cauchy_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ forall s in 𝓤 α, exists t
 in f, t ×ˢ t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `cauchy_iff'`：cauchy_iff' {f : Filter α} : Cauchy f ↔ NeBot f ∧ forall s 
in 𝓤 α, exists t in f, forall x in t, forall y in t, (x, y) in s
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s :=
  cauchy_iff'.trans <| by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, forall_mem_comm]
/-
**cauchy_iff_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_iff_le {l : Filter α} [hl : l.NeBot] : Cauchy l ↔ l ×ˢ l <= 𝓤 α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cauchy_iff_le {l : Filter α} [hl : l.NeBot] :
    Cauchy l ↔ l ×ˢ l ≤ 𝓤 α := by
  simp only [Cauchy, hl, true_and]
/-
**Cauchy.ultrafilter_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Cauchy.ultrafilter_of {l : Filter α} (h : Cauchy l) : Cauchy (@Ultrafilter
.of _ l h.1 : Filter α)
参数：h : Cauchy l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Cauchy.ultrafilter_of {l : Filter α} (h : Cauchy l) :
    Cauchy (@Ultrafilter.of _ l h.1 : Filter α) := by
  have := h.1
  have := Ultrafilter.of_le l
  exact ⟨Ultrafilter.neBot _, (Filter.prod_mono this this).trans h.2⟩
/-
**cauchy_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchy_map_iff {l : Filter β} {f : β -> α} : Cauchy (l.map f) ↔ NeBot l ∧ 
Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cauchy.eq_1`：∀ {α : Type u} [uniformSpace : UniformSpace α] (f : Filter 
α), Cauchy f = (f.NeBot ∧ f ×ˢ f ≤ uniformity α)
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cauchy_map_iff {l : Filter β} {f : β → α} :
    Cauchy (l.map f) ↔ NeBot l ∧ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α) := by
  rw [Cauchy, map_neBot_iff, prod_map_map_eq, Tendsto]
/-
**cauchy_map_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchy_map_iff' {l : Filter β} [hl : NeBot l] {f : β -> α} : Cauchy (l.map
 f) ↔ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `cauchy_map_iff`：cauchy_map_iff {l : Filter β} {f : β -> α} : Cauchy (l.m
ap f) ↔ NeBot l ∧ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α)
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
-/
theorem cauchy_map_iff' {l : Filter β} [hl : NeBot l] {f : β → α} :
    Cauchy (l.map f) ↔ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α) :=
  cauchy_map_iff.trans <| and_iff_right hl
/-
**Cauchy.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f) (h_le : g <= 
f) : Cauchy g
参数：h_c : Cauchy f；h_le : g <= f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f) (h_le : g ≤ f) : Cauchy g :=
  ⟨hg, le_trans (Filter.prod_mono h_le h_le) h_c.right⟩
/-
**Cauchy.mono'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Cauchy.mono' {f g : Filter α} (h_c : Cauchy f) (_ : NeBot g) (h_le : g <= 
f) : Cauchy g
参数：h_c : Cauchy f；_ : NeBot g；h_le : g <= f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cauchy.mono`：Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f
) (h_le : g <= f) : Cauchy g
-/
theorem Cauchy.mono' {f g : Filter α} (h_c : Cauchy f) (_ : NeBot g) (h_le : g ≤ f) : Cauchy g :=
  h_c.mono h_le
/-
**cauchy_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchy_nhds {a : α} : Cauchy (𝓝 a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `nhds_le_uniformity`：nhds_le_uniformity (x : α) : 𝓝 (x, x) <= 𝓤 α
-/
theorem cauchy_nhds {a : α} : Cauchy (𝓝 a) :=
  ⟨nhds_neBot, nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)⟩
/-
**cauchy_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchy_pure {a : α} : Cauchy (pure a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cauchy.mono`：Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f
) (h_le : g <= f) : Cauchy g
· 使用定理 `cauchy_nhds`：cauchy_nhds {a : α} : Cauchy (𝓝 a)
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem cauchy_pure {a : α} : Cauchy (pure a) :=
  cauchy_nhds.mono (pure_le_nhds a)
/-
**Filter.Tendsto.cauchy_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.cauchy_map {l : Filter β} [NeBot l] {f : β -> α} {a : α} (h
 : Tendsto f l (𝓝 a)) : Cauchy (map f l)
参数：h : Tendsto f l (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cauchy.mono`：Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f
) (h_le : g <= f) : Cauchy g
· 使用定理 `cauchy_nhds`：cauchy_nhds {a : α} : Cauchy (𝓝 a)
-/
theorem Filter.Tendsto.cauchy_map {l : Filter β} [NeBot l] {f : β → α} {a : α}
    (h : Tendsto f l (𝓝 a)) : Cauchy (map f l) :=
  cauchy_nhds.mono h
/-
**Cauchy.mono_uniformSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Cauchy.mono_uniformSpace {u v : UniformSpace β} {F : Filter β} (huv : u <=
 v) (hF : Cauchy (uniformSpace
参数：huv : u <= v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Cauchy.mono_uniformSpace {u v : UniformSpace β} {F : Filter β} (huv : u ≤ v)
    (hF : Cauchy (uniformSpace := u) F) : Cauchy (uniformSpace := v) F :=
  ⟨hF.1, hF.2.trans huv⟩
/-
**cauchy_inf_uniformSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_inf_uniformSpace {u v : UniformSpace β} {F : Filter β} : Cauchy (un
iformSpace
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_uniformity`：inf_uniformity {u v : UniformSpace α} : 𝓤[u ⊓ v] = 𝓤[u] 
⊓ 𝓤[v]
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `and_and_left`：∀ {a b c : Prop}, a ∧ b ∧ c ↔ (a ∧ b) ∧ a ∧ c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cauchy_inf_uniformSpace {u v : UniformSpace β} {F : Filter β} :
    Cauchy (uniformSpace := u ⊓ v) F ↔
    Cauchy (uniformSpace := u) F ∧ Cauchy (uniformSpace := v) F := by
  unfold Cauchy
  rw [inf_uniformity (u := u), le_inf_iff, and_and_left]
/-
**cauchy_iInf_uniformSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_iInf_uniformSpace {ι : Sort*} [Nonempty ι] {u : ι -> UniformSpace β
} {l : Filter β} : Cauchy (uniformSpace
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `forall_const`：∀ {b : Prop} (α : Sort u_1) [i : Nonempty α], (∀ (a : α), 
b) ↔ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cauchy_iInf_uniformSpace {ι : Sort*} [Nonempty ι] {u : ι → UniformSpace β}
    {l : Filter β} :
    Cauchy (uniformSpace := ⨅ i, u i) l ↔ ∀ i, Cauchy (uniformSpace := u i) l := by
  unfold Cauchy
  rw [iInf_uniformity, le_iInf_iff, forall_and, forall_const]
/-
**cauchy_iInf_uniformSpace'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_iInf_uniformSpace' {ι : Sort*} {u : ι -> UniformSpace β} {l : Filte
r β} [l.NeBot] : Cauchy (uniformSpace
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cauchy_iff_le`：cauchy_iff_le {l : Filter α} [hl : l.NeBot] : Cauchy l ↔ 
l ×ˢ l <= 𝓤 α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cauchy_iInf_uniformSpace' {ι : Sort*} {u : ι → UniformSpace β}
    {l : Filter β} [l.NeBot] :
    Cauchy (uniformSpace := ⨅ i, u i) l ↔ ∀ i, Cauchy (uniformSpace := u i) l := by
  simp_rw [cauchy_iff_le (uniformSpace := _), iInf_uniformity, le_iInf_iff]
/-
**cauchy_comap_uniformSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_comap_uniformSpace {u : UniformSpace β} {α} {f : α -> β} {l : Filte
r α} : Cauchy (uniformSpace
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cauchy_comap_uniformSpace {u : UniformSpace β} {α} {f : α → β} {l : Filter α} :
    Cauchy (uniformSpace := comap f u) l ↔ Cauchy (map f l) := by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap]
  rfl
/-
**cauchy_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_prod_iff [UniformSpace β] {F : Filter (α × β)} : Cauchy F ↔ Cauchy 
(map Prod.fst F) ∧ Cauchy (map Prod.snd F)
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cauchy_prod_iff [UniformSpace β] {F : Filter (α × β)} :
    Cauchy F ↔ Cauchy (map Prod.fst F) ∧ Cauchy (map Prod.snd F) := by
  simp_rw +instances [instUniformSpaceProd, ← cauchy_comap_uniformSpace, ← cauchy_inf_uniformSpace]
/-
**Cauchy.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} (hf : Cauchy f)
 (hg : Cauchy g) : Cauchy (f ×ˢ g)
参数：hf : Cauchy f；hg : Cauchy g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_fst_prod`：map_fst_prod (f : Filter α) (g : Filter β) [NeBot g
] : map Prod.fst (f ×ˢ g) = f
· 使用定理 `Filter.map_snd_prod`：map_snd_prod (f : Filter α) (g : Filter β) [NeBot f
] : map Prod.snd (f ×ˢ g) = g
-/
theorem Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} (hf : Cauchy f) (hg : Cauchy g) :
    Cauchy (f ×ˢ g) := by
  have := hf.1; have := hg.1
  simpa [cauchy_prod_iff, hf.1] using ⟨hf, hg⟩

/-- The common part of the proofs of `le_nhds_of_cauchy_adhp` and
`SequentiallyComplete.le_nhds_of_seq_tendsto_nhds`: if for any entourage `s`
one can choose a set `t ∈ f` of diameter `s` such that it contains a point `y`
with `(x, y) ∈ s`, then `f` converges to `x`. -/
/-
**le_nhds_of_cauchy_adhp_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_nhds_of_cauchy_adhp_aux {f : Filter α} {x : α} (adhs : forall s in 𝓤 α,
 exists t in f, t ×ˢ t subseteq s ∧ exists y, (x, y) in s ∧ y in t) : f <= 𝓝 x
参数：adhs : forall s in 𝓤 α, exists t in f, t ×ˢ t subseteq s ∧ exists y, (x, y) i
n s ∧ y in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_uniformity_iff_right`：mem_nhds_uniformity_iff_right {x : α} {s 
: Set α} : s in 𝓝 x ↔ { p : α × α | p.1 = x -> p.2 in s } in 𝓤 α
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用引理 `SetRel.prodMk_mem_comp`：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c
) : a ~[R ○ S] c
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t

--- 原说明 ---
The common part of the proofs of `le_nhds_of_cauchy_adhp` and
`SequentiallyComplete.le_nhds_of_seq_tendsto_nhds`: if for any entourage `s`
one can choose a set `t ∈ f` of diameter `s` such that it contains a point `y`
with `(x, y) ∈ s`, then `f` converges to `x`.
-/
theorem le_nhds_of_cauchy_adhp_aux {f : Filter α} {x : α}
    (adhs : ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s ∧ ∃ y, (x, y) ∈ s ∧ y ∈ t) : f ≤ 𝓝 x := by
  -- Consider a neighborhood `s` of `x`
  intro s hs
  -- Take an entourage twice smaller than `s`
  rcases comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 hs) with ⟨U, U_mem, hU⟩
  -- Take a set `t ∈ f`, `t × t ⊆ U`, and a point `y ∈ t` such that `(x, y) ∈ U`
  rcases adhs U U_mem with ⟨t, t_mem, ht, y, hxy, hy⟩
  apply mem_of_superset t_mem
  -- Given a point `z ∈ t`, we have `(x, y) ∈ U` and `(y, z) ∈ t × t ⊆ U`, hence `z ∈ s`
  exact fun z hz => hU (SetRel.prodMk_mem_comp hxy (ht <| mk_mem_prod hy hz)) rfl

/-- If `x` is an adherent (cluster) point for a Cauchy filter `f`, then it is a limit point
for `f`. -/
/-
**le_nhds_of_cauchy_adhp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (hf : Cauchy f) (adhs : Clus
terPt x f) : f <= 𝓝 x
参数：hf : Cauchy f；adhs : ClusterPt x f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_nhds_of_cauchy_adhp_aux`：le_nhds_of_cauchy_adhp_aux {f : Filter α} {x
 : α} (adhs : forall s in 𝓤 α, exists t in f, t ×ˢ t subseteq s ∧ exists y, (x, 
y) in s ∧ y in t…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchy_iff`：cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ forall s in
 𝓤 α, exists t in f, t ×ˢ t subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.forall_mem_nonempty_iff_neBot`：forall_mem_nonempty_iff_neBot {f :
 Filter α} : (forall s : Set α, s in f -> s.Nonempty) ↔ NeBot f
· 使用定理 `Filter.inter_mem_inf`：inter_mem_inf {α : Type u} {f g : Filter α} {s t :
 Set α} (hs : s in f) (ht : t in g) : s inter t in f ⊓ g
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x

--- 原说明 ---
If `x` is an adherent (cluster) point for a Cauchy filter `f`, then it is a limi
t point
for `f`.
-/
theorem le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (hf : Cauchy f) (adhs : ClusterPt x f) :
    f ≤ 𝓝 x :=
  le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      obtain ⟨t, t_mem, ht⟩ : ∃ t ∈ f, t ×ˢ t ⊆ s := (cauchy_iff.1 hf).2 s hs
      use t, t_mem, ht
      exact forall_mem_nonempty_iff_neBot.2 adhs _ (inter_mem_inf (mem_nhds_left x hs) t_mem))
/-
**le_nhds_iff_adhp_of_cauchy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_nhds_iff_adhp_of_cauchy {f : Filter α} {x : α} (hf : Cauchy f) : f <= 𝓝
 x ↔ ClusterPt x f
参数：hf : Cauchy f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.of_le_nhds'`：ClusterPt.of_le_nhds' {f : Filter X} (H : f <= 𝓝 
x) (_hf : NeBot f) : ClusterPt x f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_nhds_of_cauchy_adhp`：le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (h
f : Cauchy f) (adhs : ClusterPt x f) : f <= 𝓝 x
-/
theorem le_nhds_iff_adhp_of_cauchy {f : Filter α} {x : α} (hf : Cauchy f) :
    f ≤ 𝓝 x ↔ ClusterPt x f :=
  ⟨fun h => ClusterPt.of_le_nhds' h hf.1, le_nhds_of_cauchy_adhp hf⟩
/-
**Cauchy.map** 是 Mathlib 中的一个定理，位于命名空间 `Cauchy`。
形式化陈述：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] [inst : Unifor
mSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuous m → Cauchy 
(Filter.map m f)
参数：Filter.map m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.map`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α}, f.NeBo
t → ∀ (m : α → β), (Filter.map m f).NeBot
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem Cauchy.map [UniformSpace β] {f : Filter α} {m : α → β} (hf : Cauchy f)
    (hm : UniformContinuous m) : Cauchy (map m f) :=
  ⟨hf.1.map _,
    calc
      map m f ×ˢ map m f = map (Prod.map m m) (f ×ˢ f) := Filter.prod_map_map_eq
      _ ≤ Filter.map (Prod.map m m) (𝓤 α) := map_mono hf.right
      _ ≤ 𝓤 β := hm⟩
/-
**Cauchy.comap** 是 Mathlib 中的一个定理，位于命名空间 `Cauchy`。
形式化陈述：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] [inst : Unifor
mSpace β] {f : Filter β} {m : α → β},   Cauchy f →     Filter.comap (fun p => (m
 p.1, m p.2)) (uniformity β) ≤ uniformity α →       ∀ [(Filter.comap m f).NeBot]
, Cauchy (Filter.comap m f)
参数：fun p => (m p.1, m p.2)；uniformity β；Filter.comap m f；Filter.comap m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.prod_comap_comap_eq`：prod_comap_comap_eq.{u, v, w, x} {α₁ : Type 
u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {
m₁ : β₁ -> α₁} {…
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem Cauchy.comap [UniformSpace β] {f : Filter β} {m : α → β} (hf : Cauchy f)
    (hm : comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α) [NeBot (comap m f)] :
    Cauchy (comap m f) :=
  ⟨‹_›,
    calc
      comap m f ×ˢ comap m f = comap (Prod.map m m) (f ×ˢ f) := prod_comap_comap_eq
      _ ≤ comap (Prod.map m m) (𝓤 β) := comap_mono hf.right
      _ ≤ 𝓤 α := hm⟩
/-
**Cauchy.comap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Cauchy.comap' [UniformSpace β] {f : Filter β} {m : α -> β} (hf : Cauchy f)
 (hm : Filter.comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) <= 𝓤 α) (_ : NeBot (
Filter.comap m f)) : Cauchy (Filter.comap m f)
参数：hf : Cauchy f；hm : Filter.comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) <= 𝓤 
α；_ : NeBot (Filter.comap m f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cauchy.comap`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α
] [inst : UniformSpace β] {f : Filter β} {m : α → β},   Cauchy f →     Filter.co
ma…
-/
theorem Cauchy.comap' [UniformSpace β] {f : Filter β} {m : α → β} (hf : Cauchy f)
    (hm : Filter.comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α)
    (_ : NeBot (Filter.comap m f)) : Cauchy (Filter.comap m f) :=
  hf.comap hm
/-
**Cauchy.map_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Cauchy.map_of_le [UniformSpace β] {f : Filter α} {m : α -> β} (hf : Cauchy
 f) {s : Set α} (hm : UniformContinuousOn m s) (hfs : f <= 𝓟 s) : Cauchy (map m 
f)
参数：hf : Cauchy f；hm : UniformContinuousOn m s；hfs : f <= 𝓟 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cauchy.comap'`：Cauchy.comap' [UniformSpace β] {f : Filter β} {m : α -> β
} (hf : Cauchy f) (hm : Filter.comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) <= 
𝓤 α…
· 使用定理 `Filter.comap_coe_neBot_of_le_principal`：comap_coe_neBot_of_le_principal 
{s : Set γ} {l : Filter γ} [h : NeBot l] (h' : l <= 𝓟 s) : NeBot (comap ((↑) : s
 -> γ) l)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.subtype_coe_map_comap`：subtype_coe_map_comap (s : Set α) (f : Fil
ter α) : map ((↑) : s -> α) (comap ((↑) : s -> α) f) = f ⊓ 𝓟 s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `Cauchy.map`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] 
[inst : UniformSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuo
…
· 使用定理 `UniformContinuousOn.restrict`：∀ {α : Type ua} {β : Type ub} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β} {s : Set α},   UniformContinuo
usOn f s → Uniform…
-/
lemma Cauchy.map_of_le [UniformSpace β] {f : Filter α} {m : α → β} (hf : Cauchy f) {s : Set α}
    (hm : UniformContinuousOn m s) (hfs : f ≤ 𝓟 s) :
    Cauchy (map m f) := by
  suffices Cauchy (comap (Subtype.val : s → α) f) by
    simpa [Set.domRestrict_def, ← Function.comp_def, ← map_map,
      subtype_coe_map_comap, inf_eq_left.mpr hfs] using this.map hm.restrict
  exact hf.comap' (fun _ x ↦ x) (comap_coe_neBot_of_le_principal (h := hf.1) hfs)

/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
/-
**CauchySeq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CauchySeq [Preorder β] (u : β -> α)
参数：u : β -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that 
a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a
 type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples.
-/
def CauchySeq [Preorder β] (u : β → α) :=
  Cauchy (atTop.map u)
/-
**CauchySeq.tendsto_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.tendsto_uniformity [Preorder β] {u : β -> α} (h : CauchySeq u) :
 Tendsto (Prod.map u u) atTop (𝓤 α)
参数：h : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.prod_map_map_eq'`：prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ 
: Type*} {β₂ : Type*} (f : α₁ -> α₂) (g : β₁ -> β₂) (F : Filter α₁) (G : Filter 
β₁) : map f F…
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem CauchySeq.tendsto_uniformity [Preorder β] {u : β → α} (h : CauchySeq u) :
    Tendsto (Prod.map u u) atTop (𝓤 α) := by
  simpa only [Tendsto, prod_map_map_eq', prod_atTop_atTop_eq] using h.right
/-
**CauchySeq.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.nonempty [Preorder β] {u : β -> α} (hu : CauchySeq u) : Nonempty
 β
参数：hu : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.nonempty_of_neBot`：nonempty_of_neBot (f : Filter α) [NeBot f] : N
onempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem CauchySeq.nonempty [Preorder β] {u : β → α} (hu : CauchySeq u) : Nonempty β :=
  @nonempty_of_neBot _ _ <| (map_neBot_iff _).1 hu.1
/-
**CauchySeq.mem_entourage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.mem_entourage {β : Type*} [SemilatticeSup β] {u : β -> α} (h : C
auchySeq u) {V : SetRel α α} (hV : V in 𝓤 α) : exists k₀, forall i j, k₀ <= i ->
 k₀ <= j -> (u i, u j) in V
参数：h : CauchySeq u；hV : V in 𝓤 α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauchySeq.nonempty`：CauchySeq.nonempty [Preorder β] {u : β -> α} (hu : C
auchySeq u) : Nonempty β
· 使用定理 `CauchySeq.tendsto_uniformity`：CauchySeq.tendsto_uniformity [Preorder β] 
{u : β -> α} (h : CauchySeq u) : Tendsto (Prod.map u u) atTop (𝓤 α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_left_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : S
ort u_4} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β}   {f :
 α → β}, la.HasBasis p…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
-/
theorem CauchySeq.mem_entourage {β : Type*} [SemilatticeSup β] {u : β → α} (h : CauchySeq u)
    {V : SetRel α α} (hV : V ∈ 𝓤 α) : ∃ k₀, ∀ i j, k₀ ≤ i → k₀ ≤ j → (u i, u j) ∈ V := by
  have := h.nonempty
  have := h.tendsto_uniformity; rw [← prod_atTop_atTop_eq] at this
  simpa [MapsTo] using atTop_basis.prod_self.tendsto_left_iff.1 this V hV
/-
**Filter.Tendsto.cauchySeq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.cauchySeq [SemilatticeSup β] [Nonempty β] {f : β -> α} {x} 
(hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
参数：hx : Tendsto f atTop (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.cauchy_map`：Filter.Tendsto.cauchy_map {l : Filter β} [NeB
ot l] {f : β -> α} {a : α} (h : Tendsto f l (𝓝 a)) : Cauchy (map f l)
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
-/
theorem Filter.Tendsto.cauchySeq [SemilatticeSup β] [Nonempty β] {f : β → α} {x}
    (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f :=
  hx.cauchy_map
/-
**cauchySeq_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_const [SemilatticeSup β] [Nonempty β] (x : α) : CauchySeq fun _ 
: β => x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem cauchySeq_const [SemilatticeSup β] [Nonempty β] (x : α) : CauchySeq fun _ : β => x :=
  tendsto_const_nhds.cauchySeq
/-
**cauchySeq_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSup β] {u : β -> α} : Cauch
ySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `cauchy_map_iff'`：cauchy_map_iff' {l : Filter β} [hl : NeBot l] {f : β ->
 α} : Cauchy (l.map f) ↔ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α
)
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `Prod.map_def`：map_def {f : α -> γ} {g : β -> δ} : Prod.map f g = fun p :
 α × β => (f p.1, g p.2)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α) :=
  cauchy_map_iff'.trans <| by simp only [prod_atTop_atTop_eq, Prod.map_def]
/-
**CauchySeq.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.comp_tendsto {γ} [Preorder β] [SemilatticeSup γ] [Nonempty γ] {f
 : β -> α} (hf : CauchySeq f) {g : γ -> β} (hg : Tendsto g atTop atTop) : Cauchy
Seq (f ∘ g)
参数：hf : CauchySeq f；hg : Tendsto g atTop atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.prod_le_prod`：prod_le_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} 
[NeBot f₁] [NeBot g₁] : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂ ↔ f₁ <= f₂ ∧ g₁ <= g₂
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem CauchySeq.comp_tendsto {γ} [Preorder β] [SemilatticeSup γ] [Nonempty γ] {f : β → α}
    (hf : CauchySeq f) {g : γ → β} (hg : Tendsto g atTop atTop) : CauchySeq (f ∘ g) :=
  ⟨inferInstance, le_trans (prod_le_prod.mpr ⟨Tendsto.comp le_rfl hg, Tendsto.comp le_rfl hg⟩) hf.2⟩
/-
**CauchySeq.comp_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.comp_injective [SemilatticeSup β] [NoMaxOrder β] [Nonempty β] {u
 : Nat -> α} (hu : CauchySeq u) {f : β -> Nat} (hf : Injective f) : CauchySeq (u
 ∘ f)
参数：hu : CauchySeq u；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauchySeq.comp_tendsto`：CauchySeq.comp_tendsto {γ} [Preorder β] [Semilat
ticeSup γ] [Nonempty γ] {f : β -> α} (hf : CauchySeq f) {g : γ -> β} (hg : Tends
to g atTop a…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Function.Injective.tendsto_cofinite`：Function.Injective.tendsto_cofinite
 {f : α -> β} (hf : Injective f) : Tendsto f cofinite cofinite
· 使用定理 `Filter.atTop_le_cofinite`：atTop_le_cofinite [Preorder α] [NoTopOrder α] 
: (atTop : Filter α) <= cofinite
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
-/
theorem CauchySeq.comp_injective [SemilatticeSup β] [NoMaxOrder β] [Nonempty β] {u : ℕ → α}
    (hu : CauchySeq u) {f : β → ℕ} (hf : Injective f) : CauchySeq (u ∘ f) :=
  hu.comp_tendsto <| Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite.mono_left atTop_le_cofinite
/-
**Function.Bijective.cauchySeq_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Bijective.cauchySeq_comp_iff {f : Nat -> Nat} (hf : Bijective f) 
(u : Nat -> α) : CauchySeq (u ∘ f) ↔ CauchySeq u
参数：hf : Bijective f；u : Nat -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Equiv.instCanLiftForallCoeBijective`：∀ {α : Sort u_1} {β : Sort u_4}, Ca
nLift (α → β) (α ≃ β) DFunLike.coe Function.Bijective
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `CauchySeq.comp_injective`：CauchySeq.comp_injective [SemilatticeSup β] [N
oMaxOrder β] [Nonempty β] {u : Nat -> α} (hu : CauchySeq u) {f : β -> Nat} (hf :
 Injective f) …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
theorem Function.Bijective.cauchySeq_comp_iff {f : ℕ → ℕ} (hf : Bijective f) (u : ℕ → α) :
    CauchySeq (u ∘ f) ↔ CauchySeq u := by
  refine ⟨fun H => ?_, fun H => H.comp_injective hf.injective⟩
  lift f to ℕ ≃ ℕ using hf
  simpa only [Function.comp_def, f.apply_symm_apply] using H.comp_injective f.symm.injective
/-
**CauchySeq.subseq_subseq_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.subseq_subseq_mem {V : Nat -> SetRel α α} (hV : forall n, V n in
 𝓤 α) {u : Nat -> α} (hu : CauchySeq u) {f g : Nat -> Nat} (hf : Tendsto f atTop
 atTop) (hg : Tendsto g atTop atTop) : exists φ : Nat -> Nat, StrictMono φ ∧ for
all n, ((u ∘ f ∘ φ) n, (u ∘ g ∘ φ) n) in V n
参数：hV : forall n, V n in 𝓤 α；hu : CauchySeq u；hf : Tendsto f atTop atTop；hg : Te
ndsto g atTop atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.subseq_mem`：∀ {α : Type u_3} {F : Filter α} {V : ℕ → Set 
α},   (∀ (n : ℕ), V n ∈ F) → ∀ {u : ℕ → α}, Filter.Tendsto u Filter.atTop F → ∃ 
φ, StrictMono φ…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cauchySeq_iff_tendsto`：cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSu
p β] {u : β -> α} : CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.prod_atTop`：∀ {α : Type u_3} {γ : Type u_5} [inst : Preor
der α] [inst_1 : Preorder γ] {f g : α → γ},   Filter.Tendsto f Filter.atTop Filt
er.atTop →     …
· 使用定理 `Filter.tendsto_atTop_diagonal`：tendsto_atTop_diagonal [Preorder α] : Ten
dsto (fun a : α => (a, a)) atTop atTop
-/
theorem CauchySeq.subseq_subseq_mem {V : ℕ → SetRel α α} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    (hu : CauchySeq u) {f g : ℕ → ℕ} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, ((u ∘ f ∘ φ) n, (u ∘ g ∘ φ) n) ∈ V n := by
  rw [cauchySeq_iff_tendsto] at hu
  exact ((hu.comp <| hf.prod_atTop hg).comp tendsto_atTop_diagonal).subseq_mem hV

-- todo: generalize this and other lemmas to a nonempty semilattice
/-
**cauchySeq_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_iff' {u : Nat -> α} : CauchySeq u ↔ forall V in 𝓤 α, forallᶠ k i
n atTop, k in Prod.map u u ⁻¹' V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_iff_tendsto`：cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSu
p β] {u : β -> α} : CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem cauchySeq_iff' {u : ℕ → α} :
    CauchySeq u ↔ ∀ V ∈ 𝓤 α, ∀ᶠ k in atTop, k ∈ Prod.map u u ⁻¹' V :=
  cauchySeq_iff_tendsto
/-
**cauchySeq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_iff {u : Nat -> α} : CauchySeq u ↔ forall V in 𝓤 α, exists N, fo
rall k >= N, forall l >= N, (u k, u l) in V
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cauchySeq_iff {u : ℕ → α} :
    CauchySeq u ↔ ∀ V ∈ 𝓤 α, ∃ N, ∀ k ≥ N, ∀ l ≥ N, (u k, u l) ∈ V := by
  simp only [cauchySeq_iff', Filter.eventually_atTop_prod_self', mem_preimage, Prod.map_apply]
/-
**CauchySeq.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.prodMap {γ δ} [UniformSpace β] [Preorder γ] [Preorder δ] {u : γ 
-> α} {v : δ -> β} (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq (Prod.map u
 v)
参数：hu : CauchySeq u；hv : CauchySeq v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.prod_map_map_eq'`：prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ 
: Type*} {β₂ : Type*} (f : α₁ -> α₂) (g : β₁ -> β₂) (F : Filter α₁) (G : Filter 
β₁) : map f F…
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `Cauchy.prod`：Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} 
(hf : Cauchy f) (hg : Cauchy g) : Cauchy (f ×ˢ g)
-/
theorem CauchySeq.prodMap {γ δ} [UniformSpace β] [Preorder γ] [Preorder δ] {u : γ → α} {v : δ → β}
    (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq (Prod.map u v) := by
  simpa only [CauchySeq, prod_map_map_eq', prod_atTop_atTop_eq] using hu.prod hv
/-
**CauchySeq.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.prodMk {γ} [UniformSpace β] [Preorder γ] {u : γ -> α} {v : γ -> 
β} (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq fun x => (u x, v x)
参数：hu : CauchySeq u；hv : CauchySeq v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cauchy.mono`：Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f
) (h_le : g <= f) : Cauchy g
· 使用定理 `Filter.NeBot.of_map`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {m :
 α → β}, (Filter.map m f).NeBot → f.NeBot
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Cauchy.prod`：Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} 
(hf : Cauchy f) (hg : Cauchy g) : Cauchy (f ×ˢ g)
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
-/
theorem CauchySeq.prodMk {γ} [UniformSpace β] [Preorder γ] {u : γ → α} {v : γ → β}
    (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq fun x => (u x, v x) :=
  haveI := hu.1.of_map
  (Cauchy.prod hu hv).mono (tendsto_map.prodMk tendsto_map)
/-
**CauchySeq.eventually_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.eventually_eventually [Preorder β] {u : β -> α} (hu : CauchySeq 
u) {V : SetRel α α} (hV : V in 𝓤 α) : forallᶠ k in atTop, forallᶠ l in atTop, (u
 k, u l) in V
参数：hu : CauchySeq u；hV : V in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_atTop_curry`：eventually_atTop_curry [Preorder α] [Preo
rder β] {p : α × β -> Prop} (hp : forallᶠ x : α × β in Filter.atTop, p x) : fora
llᶠ k in atTop, for…
· 使用定理 `CauchySeq.tendsto_uniformity`：CauchySeq.tendsto_uniformity [Preorder β] 
{u : β -> α} (h : CauchySeq u) : Tendsto (Prod.map u u) atTop (𝓤 α)
-/
theorem CauchySeq.eventually_eventually [Preorder β] {u : β → α} (hu : CauchySeq u)
    {V : SetRel α α} (hV : V ∈ 𝓤 α) : ∀ᶠ k in atTop, ∀ᶠ l in atTop, (u k, u l) ∈ V :=
  eventually_atTop_curry <| hu.tendsto_uniformity hV
/-
**UniformContinuous.comp_cauchySeq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.comp_cauchySeq {γ} [UniformSpace β] [Preorder γ] {f : α 
-> β} (hf : UniformContinuous f) {u : γ -> α} (hu : CauchySeq u) : CauchySeq (f 
∘ u)
参数：hf : UniformContinuous f；hu : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cauchy.map`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] 
[inst : UniformSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuo
…
-/
theorem UniformContinuous.comp_cauchySeq {γ} [UniformSpace β] [Preorder γ] {f : α → β}
    (hf : UniformContinuous f) {u : γ → α} (hu : CauchySeq u) : CauchySeq (f ∘ u) :=
  hu.map hf
/-
**CauchySeq.subseq_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.subseq_mem {V : Nat -> SetRel α α} (hV : forall n, V n in 𝓤 α) {
u : Nat -> α} (hu : CauchySeq u) : exists φ : Nat -> Nat, StrictMono φ ∧ forall 
n, (u <| φ (n + 1), u <| φ n) in V n
参数：hV : forall n, V n in 𝓤 α；hu : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cauchySeq_iff`：cauchySeq_iff {u : Nat -> α} : CauchySeq u ↔ forall V in 
𝓤 α, exists N, forall k >= N, forall l >= N, (u k, u l) in V
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.extraction_forall_of_eventually'`：extraction_forall_of_eventually
' {P : Nat -> Nat -> Prop} (h : forall n, exists N, forall k >= N, P n k) : exis
ts φ : Nat -> Nat, StrictMono…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
-/
theorem CauchySeq.subseq_mem {V : ℕ → SetRel α α} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    (hu : CauchySeq u) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, (u <| φ (n + 1), u <| φ n) ∈ V n := by
  have : ∀ n, ∃ N, ∀ k ≥ N, ∀ l ≥ k, (u l, u k) ∈ V n := fun n => by
    rw [cauchySeq_iff] at hu
    rcases hu _ (hV n) with ⟨N, H⟩
    exact ⟨N, fun k hk l hl => H _ (le_trans hk hl) _ hk⟩
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ∀ l ≥ φ n, (u l, u <| φ n) ∈ V n⟩ :=
    extraction_forall_of_eventually' this
  exact ⟨φ, φ_extr, fun n => hφ _ _ (φ_extr <| Nat.lt_add_one n).le⟩
/-
**Filter.Tendsto.subseq_mem_entourage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.subseq_mem_entourage {V : Nat -> SetRel α α} (hV : forall n
, V n in 𝓤 α) {u : Nat -> α} {a : α} (hu : Tendsto u atTop (𝓝 a)) : exists φ : N
at -> Nat, StrictMono φ ∧ (u (φ 0), a) in V 0 ∧ forall n, (u <| φ (n + 1), u <| 
φ n) in V (n + 1)
参数：hV : forall n, V n in 𝓤 α；hu : Tendsto u atTop (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
· 使用定理 `symm_le_uniformity`：symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) <= 𝓤
 _
· 使用定理 `CauchySeq.subseq_mem`：CauchySeq.subseq_mem {V : Nat -> SetRel α α} (hV :
 forall n, V n in 𝓤 α) {u : Nat -> α} (hu : CauchySeq u) : exists φ : Nat -> Nat
, StrictMo…
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_add_atTop_nat`：tendsto_add_atTop_nat (k : Nat) : Tendsto 
(fun a => a + k) atTop atTop
· 使用定理 `StrictMono.add_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [in
st_1 : Preorder α] [inst_2 : Preorder β] {f : β → α}   [AddRightStrictMono α], S
trictMono …
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
theorem Filter.Tendsto.subseq_mem_entourage {V : ℕ → SetRel α α} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    {a : α} (hu : Tendsto u atTop (𝓝 a)) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ (u (φ 0), a) ∈ V 0 ∧
      ∀ n, (u <| φ (n + 1), u <| φ n) ∈ V (n + 1) := by
  rcases mem_atTop_sets.1 (hu (ball_mem_nhds a (symm_le_uniformity <| hV 0))) with ⟨n, hn⟩
  rcases (hu.comp (tendsto_add_atTop_nat n)).cauchySeq.subseq_mem fun n => hV (n + 1) with
    ⟨φ, φ_mono, hφV⟩
  exact ⟨fun k => φ k + n, φ_mono.add_const _, hn _ le_add_self, hφV⟩

/-- If a Cauchy sequence has a convergent subsequence, then it converges. -/
/-
**tendsto_nhds_of_cauchySeq_of_subseq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_of_cauchySeq_of_subseq [Preorder β] {u : β -> α} (hu : Cauchy
Seq u) {ι : Type*} {f : ι -> β} {p : Filter ι} [NeBot p] (hf : Tendsto f p atTop
) {a : α} (ha : Tendsto (u ∘ f) p (𝓝 a)) : Tendsto u atTop (𝓝 a)
参数：hu : CauchySeq u；hf : Tendsto f p atTop；ha : Tendsto (u ∘ f) p (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_nhds_of_cauchy_adhp`：le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (h
f : Cauchy f) (adhs : ClusterPt x f) : f <= 𝓝 x
· 使用定理 `MapClusterPt.of_comp`：MapClusterPt.of_comp {φ : β -> α} {p : Filter β} (
h : Tendsto φ p F) (H : MapClusterPt x p (u ∘ φ)) : MapClusterPt x F u
· 使用定理 `Filter.Tendsto.mapClusterPt`：Filter.Tendsto.mapClusterPt [NeBot F] (h : 
Tendsto u F (𝓝 x)) : MapClusterPt x F u

--- 原说明 ---
If a Cauchy sequence has a convergent subsequence, then it converges.
-/
theorem tendsto_nhds_of_cauchySeq_of_subseq [Preorder β] {u : β → α} (hu : CauchySeq u)
    {ι : Type*} {f : ι → β} {p : Filter ι} [NeBot p] (hf : Tendsto f p atTop) {a : α}
    (ha : Tendsto (u ∘ f) p (𝓝 a)) : Tendsto u atTop (𝓝 a) :=
  le_nhds_of_cauchy_adhp hu (ha.mapClusterPt.of_comp hf)

/-- Any shift of a Cauchy sequence is also a Cauchy sequence. -/
/-
**cauchySeq_shift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_shift {u : Nat -> α} (k : Nat) : CauchySeq (fun n => u (n + k)) 
↔ CauchySeq u
参数：k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cauchySeq_iff`：cauchySeq_iff {u : Nat -> α} : CauchySeq u ↔ forall V in 
𝓤 α, exists N, forall k >= N, forall l >= N, (u k, u l) in V
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_sub_of_add_le`：∀ {a b c : ℕ}, a + b ≤ c → a ≤ c - b
· 使用定理 `CauchySeq.comp_tendsto`：CauchySeq.comp_tendsto {γ} [Preorder β] [Semilat
ticeSup γ] [Nonempty γ] {f : β -> α} (hf : CauchySeq f) {g : γ -> β} (hg : Tends
to g atTop a…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.tendsto_add_atTop_nat`：tendsto_add_atTop_nat (k : Nat) : Tendsto 
(fun a => a + k) atTop atTop

--- 原说明 ---
Any shift of a Cauchy sequence is also a Cauchy sequence.
-/
theorem cauchySeq_shift {u : ℕ → α} (k : ℕ) : CauchySeq (fun n ↦ u (n + k)) ↔ CauchySeq u := by
  constructor <;> intro h
  · rw [cauchySeq_iff] at h ⊢
    intro V mV
    obtain ⟨N, h⟩ := h V mV
    use N + k
    intro a ha b hb
    convert! h (a - k) (Nat.le_sub_of_add_le ha) (b - k) (Nat.le_sub_of_add_le hb) <;> lia
  · exact h.comp_tendsto (tendsto_add_atTop_nat k)
/-
**Filter.HasBasis.cauchySeq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.cauchySeq_iff {γ} [Nonempty β] [SemilatticeSup β] {u : β -
> α} {p : γ -> Prop} {s : γ -> SetRel α α} (h : (𝓤 α).HasBasis p s) : CauchySeq 
u ↔ forall i, p i -> exists N, forall m, N <= m -> forall n, N <= n -> (u m, u n
) in s i
参数：h : (𝓤 α).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cauchySeq_iff_tendsto`：cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSu
p β] {u : β -> α} : CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.HasBasis.cauchySeq_iff {γ} [Nonempty β] [SemilatticeSup β] {u : β → α} {p : γ → Prop}
    {s : γ → SetRel α α} (h : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ ∀ i, p i → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → (u m, u n) ∈ s i := by
  rw [cauchySeq_iff_tendsto, ← prod_atTop_atTop_eq]
  refine (atTop_basis.prod_self.tendsto_iff h).trans ?_
  simp only [true_and, Prod.forall, mem_prod_eq,
    mem_Ici, and_imp, Prod.map, @forall_comm (_ ≤ _) β]
/-
**Filter.HasBasis.cauchySeq_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.cauchySeq_iff' {γ} [Nonempty β] [SemilatticeSup β] {u : β 
-> α} {p : γ -> Prop} {s : γ -> SetRel α α} (H : (𝓤 α).HasBasis p s) : CauchySeq
 u ↔ forall i, p i -> exists N, forall n >= N, (u n, u N) in s i
参数：H : (𝓤 α).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.cauchySeq_iff`：Filter.HasBasis.cauchySeq_iff {γ} [Nonemp
ty β] [SemilatticeSup β] {u : β -> α} {p : γ -> Prop} {s : γ -> SetRel α α} (h :
 (𝓤 α).HasBasis p s…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `comp_symm_of_uniformity`：comp_symm_of_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : exists t in 𝓤 α, (forall {a b}, (a, b) in t -> (b, a) in t) ∧ t ○ t 
subseteq s
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
-/
theorem Filter.HasBasis.cauchySeq_iff' {γ} [Nonempty β] [SemilatticeSup β] {u : β → α}
    {p : γ → Prop} {s : γ → SetRel α α} (H : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ ∀ i, p i → ∃ N, ∀ n ≥ N, (u n, u N) ∈ s i := by
  refine H.cauchySeq_iff.trans ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · exact (h i hi).imp fun N hN n hn => hN n hn N le_rfl
  · rcases comp_symm_of_uniformity (H.mem_of_mem hi) with ⟨t, ht, ht', hts⟩
    rcases H.mem_iff.1 ht with ⟨j, hj, hjt⟩
    refine (h j hj).imp fun N hN m hm n hn => hts ⟨u N, hjt ?_, ht' <| hjt ?_⟩
    exacts [hN m hm, hN n hn]
/-
**cauchySeq_of_controlled** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_controlled [SemilatticeSup β] [Nonempty β] (U : β -> SetRel α
 α) (hU : forall s in 𝓤 α, exists n, U n subseteq s) {f : β -> α} (hf : forall ⦃
N m n : β⦄, N <= m -> N <= n -> (f m, f n) in U N) : CauchySeq f
参数：U : β -> SetRel α α；hU : forall s in 𝓤 α, exists n, U n subseteq s；hf : foral
l ⦃N m n : β⦄, N <= m -> N <= n -> (f m, f n) in U N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `cauchySeq_iff_tendsto`：cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSu
p β] {u : β -> α} : CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem cauchySeq_of_controlled [SemilatticeSup β] [Nonempty β] (U : β → SetRel α α)
    (hU : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s) {f : β → α}
    (hf : ∀ ⦃N m n : β⦄, N ≤ m → N ≤ n → (f m, f n) ∈ U N) : CauchySeq f :=
  cauchySeq_iff_tendsto.2
    (by
      intro s hs
      rw [mem_map, mem_atTop_sets]
      obtain ⟨N, hN⟩ := hU s hs
      refine ⟨(N, N), fun mn hmn => ?_⟩
      obtain ⟨m, n⟩ := mn
      exact hN (hf hmn.1 hmn.2))
/-
**isComplete_iff_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isComplete_iff_clusterPt {s : Set α} : IsComplete s ↔ forall l, Cauchy l -
> l <= 𝓟 s -> exists x in s, ClusterPt x l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `le_nhds_iff_adhp_of_cauchy`：le_nhds_iff_adhp_of_cauchy {f : Filter α} {x
 : α} (hf : Cauchy f) : f <= 𝓝 x ↔ ClusterPt x f
-/
theorem isComplete_iff_clusterPt {s : Set α} :
    IsComplete s ↔ ∀ l, Cauchy l → l ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x l :=
  forall₃_congr fun _ hl _ => exists_congr fun _ => and_congr_right fun _ =>
    le_nhds_iff_adhp_of_cauchy hl
/-
**isComplete_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isComplete_iff_ultrafilter {s : Set α} : IsComplete s ↔ forall l : Ultrafi
lter α, Cauchy (l : Filter α) -> ↑l <= 𝓟 s -> exists x in s, ↑l <= 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isComplete_iff_clusterPt`：isComplete_iff_clusterPt {s : Set α} : IsCompl
ete s ↔ forall l, Cauchy l -> l <= 𝓟 s -> exists x in s, ClusterPt x l
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Cauchy.ultrafilter_of`：Cauchy.ultrafilter_of {l : Filter α} (h : Cauchy 
l) : Cauchy (@Ultrafilter.of _ l h.1 : Filter α)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `ClusterPt.of_le_nhds`：ClusterPt.of_le_nhds {f : Filter X} (H : f <= 𝓝 x)
 [NeBot f] : ClusterPt x f
-/
theorem isComplete_iff_ultrafilter {s : Set α} :
    IsComplete s ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → ↑l ≤ 𝓟 s → ∃ x ∈ s, ↑l ≤ 𝓝 x := by
  refine ⟨fun h l => h l, fun H => isComplete_iff_clusterPt.2 fun l hl hls => ?_⟩
  have := hl.1
  rcases H (Ultrafilter.of l) hl.ultrafilter_of ((Ultrafilter.of_le l).trans hls) with ⟨x, hxs, hxl⟩
  exact ⟨x, hxs, (ClusterPt.of_le_nhds hxl).mono (Ultrafilter.of_le l)⟩
/-
**isComplete_iff_ultrafilter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isComplete_iff_ultrafilter' {s : Set α} : IsComplete s ↔ forall l : Ultraf
ilter α, Cauchy (l : Filter α) -> s in l -> exists x in s, ↑l <= 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isComplete_iff_ultrafilter`：isComplete_iff_ultrafilter {s : Set α} : IsC
omplete s ↔ forall l : Ultrafilter α, Cauchy (l : Filter α) -> ↑l <= 𝓟 s -> exis
ts x in s, ↑l <=…
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
theorem isComplete_iff_ultrafilter' {s : Set α} :
    IsComplete s ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → s ∈ l → ∃ x ∈ s, ↑l ≤ 𝓝 x :=
  isComplete_iff_ultrafilter.trans <| by simp only [le_principal_iff, Ultrafilter.mem_coe]
/-
**IsComplete.union** 是 Mathlib 中的一个定理，位于命名空间 `IsComplete`。
形式化陈述：∀ {α : Type u} [uniformSpace : UniformSpace α] {s t : Set α}, IsComplete s
 → IsComplete t → IsComplete (s ∪ t)
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem IsComplete.union {s t : Set α} (hs : IsComplete s) (ht : IsComplete t) :
    IsComplete (s ∪ t) := by
  simp only [isComplete_iff_ultrafilter', Ultrafilter.union_mem_iff, or_imp] at *
  exact fun l hl =>
    ⟨fun hsl => (hs l hl hsl).imp fun x hx => ⟨Or.inl hx.1, hx.2⟩, fun htl =>
      (ht l hl htl).imp fun x hx => ⟨Or.inr hx.1, hx.2⟩⟩
/-
**isComplete_iUnion_separated** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isComplete_iUnion_separated {ι : Sort*} {s : ι -> Set α} (hs : forall i, I
sComplete (s i)) {U : SetRel α α} (hU : U in 𝓤 α) (hd : forall (i j : ι), forall
 x in s i, forall y in s j, (x, y) in U -> i = j) : IsComplete (⋃ i, s i)
参数：hs : forall i, IsComplete (s i)；hU : U in 𝓤 α；hd : forall (i j : ι), forall x
 in s i, forall y in s j, (x, y) in U -> i = j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchy_iff`：cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ forall s in
 𝓤 α, exists t in f, t ×ˢ t subseteq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem isComplete_iUnion_separated {ι : Sort*} {s : ι → Set α} (hs : ∀ i, IsComplete (s i))
    {U : SetRel α α} (hU : U ∈ 𝓤 α) (hd : ∀ (i j : ι), ∀ x ∈ s i, ∀ y ∈ s j, (x, y) ∈ U → i = j) :
    IsComplete (⋃ i, s i) := by
  set S := ⋃ i, s i
  intro l hl hls
  rw [le_principal_iff] at hls
  obtain ⟨hl_ne, hl'⟩ := cauchy_iff.1 hl
  obtain ⟨t, htS, htl, htU⟩ : ∃ t, t ⊆ S ∧ t ∈ l ∧ t ×ˢ t ⊆ U := by
    rcases hl' U hU with ⟨t, htl, htU⟩
    refine ⟨t ∩ S, inter_subset_right, inter_mem htl hls, Subset.trans ?_ htU⟩
    gcongr <;> apply inter_subset_left
  obtain ⟨i, hi⟩ : ∃ i, t ⊆ s i := by
    rcases Filter.nonempty_of_mem htl with ⟨x, hx⟩
    rcases mem_iUnion.1 (htS hx) with ⟨i, hi⟩
    refine ⟨i, fun y hy => ?_⟩
    rcases mem_iUnion.1 (htS hy) with ⟨j, hj⟩
    rwa [hd i j x hi y hj (htU <| mk_mem_prod hx hy)]
  rcases hs i l hl (le_principal_iff.2 <| mem_of_superset htl hi) with ⟨x, hxs, hlx⟩
  exact ⟨x, mem_iUnion.2 ⟨i, hxs⟩, hlx⟩

/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
@[wikidata Q848569]
/-
**CompleteSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [UniformSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges.
-/
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  /-- In a complete uniform space, every Cauchy filter converges. -/
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x
/-
**isComplete_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isComplete_univ {α : Type u} [UniformSpace α] [CompleteSpace α] : IsComple
te (univ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem isComplete_univ {α : Type u} [UniformSpace α] [CompleteSpace α] :
    IsComplete (univ : Set α) := fun f hf _ => by
  rcases CompleteSpace.complete hf with ⟨x, hx⟩
  exact ⟨x, mem_univ x, hx⟩

@[deprecated (since := "2026-07-27")] alias complete_univ := isComplete_univ
/-
**CompleteSpace.prod** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CompleteSpace.prod [UniformSpace β] [CompleteSpace α] [CompleteSpace β] : 
CompleteSpace (α × β) where complete hf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `Cauchy.map`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] 
[inst : UniformSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuo
…
· 使用定理 `uniformContinuous_fst`：uniformContinuous_fst [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.1
· 使用定理 `uniformContinuous_snd`：uniformContinuous_snd [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.le_prod`：le_prod {f : Filter (α × β)} {g : Filter α} {g' : Filter
 β} : (f <= g ×ˢ g') ↔ Tendsto Prod.fst f g ∧ Tendsto Prod.snd f g'
-/
instance CompleteSpace.prod [UniformSpace β] [CompleteSpace α] [CompleteSpace β] :
    CompleteSpace (α × β) where
  complete hf :=
    let ⟨x1, hx1⟩ := CompleteSpace.complete <| hf.map uniformContinuous_fst
    let ⟨x2, hx2⟩ := CompleteSpace.complete <| hf.map uniformContinuous_snd
    ⟨(x1, x2), by rw [nhds_prod_eq, le_prod]; constructor <;> assumption⟩
/-
**CompleteSpace.fst_of_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteSpace.fst_of_prod [UniformSpace β] [CompleteSpace (α × β)] [h : No
nempty β] : CompleteSpace α where complete hf
参数：α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `Cauchy.prod`：Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} 
(hf : Cauchy f) (hg : Cauchy g) : Cauchy (f ×ˢ g)
· 使用定理 `cauchy_pure`：cauchy_pure {a : α} : Cauchy (pure a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_fst_prod`：map_fst_prod (f : Filter α) (g : Filter β) [NeBot g
] : map Prod.fst (f ×ˢ g) = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
lemma CompleteSpace.fst_of_prod [UniformSpace β] [CompleteSpace (α × β)] [h : Nonempty β] :
    CompleteSpace α where
  complete hf :=
    let ⟨y⟩ := h
    let ⟨(a, b), hab⟩ := CompleteSpace.complete <| hf.prod <| cauchy_pure (a := y)
    ⟨a, by simpa only [map_fst_prod, nhds_prod_eq] using map_mono (m := Prod.fst) hab⟩
/-
**CompleteSpace.snd_of_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteSpace.snd_of_prod [UniformSpace β] [CompleteSpace (α × β)] [h : No
nempty α] : CompleteSpace β where complete hf
参数：α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `Cauchy.prod`：Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} 
(hf : Cauchy f) (hg : Cauchy g) : Cauchy (f ×ˢ g)
· 使用定理 `cauchy_pure`：cauchy_pure {a : α} : Cauchy (pure a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_snd_prod`：map_snd_prod (f : Filter α) (g : Filter β) [NeBot f
] : map Prod.snd (f ×ˢ g) = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
lemma CompleteSpace.snd_of_prod [UniformSpace β] [CompleteSpace (α × β)] [h : Nonempty α] :
    CompleteSpace β where
  complete hf :=
    let ⟨x⟩ := h
    let ⟨(a, b), hab⟩ := CompleteSpace.complete <| (cauchy_pure (a := x)).prod hf
    ⟨b, by simpa only [map_snd_prod, nhds_prod_eq] using map_mono (m := Prod.snd) hab⟩
/-
**completeSpace_prod_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：completeSpace_prod_of_nonempty [UniformSpace β] [Nonempty α] [Nonempty β] 
: CompleteSpace (α × β) ↔ CompleteSpace α ∧ CompleteSpace β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CompleteSpace.fst_of_prod`：CompleteSpace.fst_of_prod [UniformSpace β] [C
ompleteSpace (α × β)] [h : Nonempty β] : CompleteSpace α where complete hf
· 使用引理 `CompleteSpace.snd_of_prod`：CompleteSpace.snd_of_prod [UniformSpace β] [C
ompleteSpace (α × β)] [h : Nonempty α] : CompleteSpace β where complete hf
-/
lemma completeSpace_prod_of_nonempty [UniformSpace β] [Nonempty α] [Nonempty β] :
    CompleteSpace (α × β) ↔ CompleteSpace α ∧ CompleteSpace β :=
  ⟨fun _ ↦ ⟨.fst_of_prod (β := β), .snd_of_prod (α := α)⟩, fun ⟨_, _⟩ ↦ .prod⟩

@[to_additive]
/-
**CompleteSpace.mulOpposite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CompleteSpace.mulOpposite [CompleteSpace α] : CompleteSpace αᵐᵒᵖ where com
plete hf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `Cauchy.map`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] 
[inst : UniformSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuo
…
· 使用定理 `MulOpposite.uniformContinuous_unop`：uniformContinuous_unop [UniformSpace
 α] : UniformContinuous (unop : αᵐᵒᵖ -> α)
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `MulOpposite.comap_unop_nhds`：comap_unop_nhds (x : M) : comap (unop : Mᵐᵒ
ᵖ -> M) (𝓝 x) = 𝓝 (op x)
-/
instance CompleteSpace.mulOpposite [CompleteSpace α] : CompleteSpace αᵐᵒᵖ where
  complete hf :=
    MulOpposite.op_surjective.exists.mpr <|
      let ⟨x, hx⟩ := CompleteSpace.complete (hf.map MulOpposite.uniformContinuous_unop)
      ⟨x, (map_le_iff_le_comap.mp hx).trans_eq <| MulOpposite.comap_unop_nhds _⟩

/-- If `univ` is complete, the space is a complete space -/
/-
**completeSpace_of_isComplete_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completeSpace_of_isComplete_univ (h : IsComplete (univ : Set α)) : Complet
eSpace α
参数：h : IsComplete (univ : Set α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤

--- 原说明 ---
If `univ` is complete, the space is a complete space
-/
theorem completeSpace_of_isComplete_univ (h : IsComplete (univ : Set α)) : CompleteSpace α :=
  ⟨fun hf => let ⟨x, _, hx⟩ := h _ hf ((@principal_univ α).symm ▸ le_top); ⟨x, hx⟩⟩
/-
**completeSpace_iff_isComplete_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completeSpace_iff_isComplete_univ : CompleteSpace α ↔ IsComplete (univ : S
et α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isComplete_univ`：isComplete_univ {α : Type u} [UniformSpace α] [Complete
Space α] : IsComplete (univ : Set α)
· 使用定理 `completeSpace_of_isComplete_univ`：completeSpace_of_isComplete_univ (h : 
IsComplete (univ : Set α)) : CompleteSpace α
-/
theorem completeSpace_iff_isComplete_univ : CompleteSpace α ↔ IsComplete (univ : Set α) :=
  ⟨@isComplete_univ α _, completeSpace_of_isComplete_univ⟩
/-
**completeSpace_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completeSpace_iff_ultrafilter : CompleteSpace α ↔ forall l : Ultrafilter α
, Cauchy (l : Filter α) -> exists x : α, ↑l <= 𝓝 x
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
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem completeSpace_iff_ultrafilter :
    CompleteSpace α ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → ∃ x : α, ↑l ≤ 𝓝 x := by
  simp [completeSpace_iff_isComplete_univ, isComplete_iff_ultrafilter]
/-
**cauchy_iff_exists_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchy_iff_exists_le_nhds [CompleteSpace α] {l : Filter α} [NeBot l] : Cau
chy l ↔ exists x, l <= 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `Cauchy.mono`：Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f
) (h_le : g <= f) : Cauchy g
· 使用定理 `cauchy_nhds`：cauchy_nhds {a : α} : Cauchy (𝓝 a)
-/
theorem cauchy_iff_exists_le_nhds [CompleteSpace α] {l : Filter α} [NeBot l] :
    Cauchy l ↔ ∃ x, l ≤ 𝓝 x :=
  ⟨CompleteSpace.complete, fun ⟨_, hx⟩ => cauchy_nhds.mono hx⟩
/-
**cauchy_map_iff_exists_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchy_map_iff_exists_tendsto [CompleteSpace α] {l : Filter β} {f : β -> α
} [NeBot l] : Cauchy (l.map f) ↔ exists x, Tendsto f l (𝓝 x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchy_iff_exists_le_nhds`：cauchy_iff_exists_le_nhds [CompleteSpace α] {
l : Filter α} [NeBot l] : Cauchy l ↔ exists x, l <= 𝓝 x
-/
theorem cauchy_map_iff_exists_tendsto [CompleteSpace α] {l : Filter β} {f : β → α} [NeBot l] :
    Cauchy (l.map f) ↔ ∃ x, Tendsto f l (𝓝 x) :=
  cauchy_iff_exists_le_nhds

/-- A Cauchy sequence in a complete space converges -/
/-
**cauchySeq_tendsto_of_complete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_tendsto_of_complete [Preorder β] [CompleteSpace α] {u : β -> α} 
(H : CauchySeq u) : exists x, Tendsto u atTop (𝓝 x)
参数：H : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x

--- 原说明 ---
A Cauchy sequence in a complete space converges
-/
theorem cauchySeq_tendsto_of_complete [Preorder β] [CompleteSpace α] {u : β → α}
    (H : CauchySeq u) : ∃ x, Tendsto u atTop (𝓝 x) :=
  CompleteSpace.complete H

/-- If `K` is a complete subset, then any Cauchy sequence in `K` converges to a point in `K` -/
/-
**cauchySeq_tendsto_of_isComplete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_tendsto_of_isComplete [Preorder β] {K : Set α} (h₁ : IsComplete 
K) {u : β -> α} (h₂ : forall n, u n in K) (h₃ : CauchySeq u) : exists v in K, Te
ndsto u atTop (𝓝 v)
参数：h₁ : IsComplete K；h₂ : forall n, u n in K；h₃ : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_map_iff_exists_image`：mem_map_iff_exists_image : t in map m f
 ↔ exists s in f, m '' s subseteq t
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s

--- 原说明 ---
If `K` is a complete subset, then any Cauchy sequence in `K` converges to a poin
t in `K`
-/
theorem cauchySeq_tendsto_of_isComplete [Preorder β] {K : Set α} (h₁ : IsComplete K)
    {u : β → α} (h₂ : ∀ n, u n ∈ K) (h₃ : CauchySeq u) : ∃ v ∈ K, Tendsto u atTop (𝓝 v) :=
  h₁ _ h₃ <| le_principal_iff.2 <| mem_map_iff_exists_image.2
    ⟨univ, univ_mem, by rwa [image_univ, range_subset_iff]⟩
/-
**Cauchy.le_nhds_lim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Cauchy.le_nhds_lim [CompleteSpace α] {f : Filter α} (hf : Cauchy f) : have
I
参数：hf : Cauchy f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_nhds_lim`：le_nhds_lim {f : Filter X} (h : exists x, f <= 𝓝 x) : f <= 
𝓝 (@lim _ _ h.nonempty f)
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
-/
theorem Cauchy.le_nhds_lim [CompleteSpace α] {f : Filter α} (hf : Cauchy f) :
    haveI := hf.1.nonempty; f ≤ 𝓝 (lim f) :=
  _root_.le_nhds_lim (CompleteSpace.complete hf)
/-
**CauchySeq.tendsto_limUnder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.tendsto_limUnder [Preorder β] [CompleteSpace α] {u : β -> α} (h 
: CauchySeq u) : haveI
参数：h : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cauchy.le_nhds_lim`：Cauchy.le_nhds_lim [CompleteSpace α] {f : Filter α} 
(hf : Cauchy f) : haveI
-/
theorem CauchySeq.tendsto_limUnder [Preorder β] [CompleteSpace α] {u : β → α} (h : CauchySeq u) :
    haveI := h.1.nonempty; Tendsto u atTop (𝓝 <| limUnder atTop u) :=
  h.le_nhds_lim
/-
**IsClosed.isComplete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.isComplete [CompleteSpace α] {s : Set α} (h : IsClosed s) : IsCom
plete s
参数：h : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_iff_clusterPt`：isClosed_iff_clusterPt : IsClosed s ↔ forall a, 
ClusterPt a (𝓟 s) -> a in s
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
-/
theorem IsClosed.isComplete [CompleteSpace α] {s : Set α} (h : IsClosed s) : IsComplete s :=
  fun _ cf fs =>
  let ⟨x, hx⟩ := CompleteSpace.complete cf
  ⟨x, isClosed_iff_clusterPt.mp h x (cf.left.mono (le_inf hx fs)), hx⟩

namespace DiscreteUniformity

variable [DiscreteUniformity α]

/-- A Cauchy filter in a discrete uniform space is contained in the principal filter
of a point. -/
/-
**DiscreteUniformity.eq_pure_of_cauchy** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteUnifor
mity`。
形式化陈述：eq_pure_of_cauchy {f : Filter α} (hf : Cauchy f) : exists x : α, f = pure 
x
参数：hf : Cauchy f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DiscreteUniformity.eq_principal_setRelId`：eq_principal_setRelId : unifor
mity X = 𝓟 SetRel.id
· 使用引理 `SetRel.exists_eq_singleton_of_prod_subset_id`：exists_eq_singleton_of_pro
d_subset_id {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ×ˢ t subs
eteq SetRel.id) : exists x, s = {x…
· 使用定理 `Filter.NeBot.nonempty_of_mem`：∀ {α : Type u} {f : Filter α}, f.NeBot → ∀
 {s : Set α}, s ∈ f → s.Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.NeBot.le_pure_iff`：∀ {α : Type u} {f : Filter α} {a : α}, f.NeBot
 → (f ≤ pure a ↔ f = pure a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_pure_iff`：le_pure_iff {f : Filter α} {a : α} : f <= pure a ↔ {
a} in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A Cauchy filter in a discrete uniform space is contained in the principal filter
of a point.
-/
theorem eq_pure_of_cauchy {f : Filter α} (hf : Cauchy f) : ∃ x : α, f = pure x := by
  rcases hf with ⟨f_ne_bot, f_le⟩
  simp only [DiscreteUniformity.eq_principal_setRelId, le_principal_iff, mem_prod_iff] at f_le
  obtain ⟨S, hS, T, hT, H⟩ := f_le
  obtain ⟨x, rfl, _, _, _⟩ := SetRel.exists_eq_singleton_of_prod_subset_id
    (f_ne_bot.nonempty_of_mem hS) (f_ne_bot.nonempty_of_mem hT) H
  exact ⟨x, f_ne_bot.le_pure_iff.mp <| le_pure_iff.mpr hS⟩

/-- The discrete uniformity makes a space complete. -/
/-
**DiscreteUniformity.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteUniformity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete uniformity makes a space complete.
-/
instance : CompleteSpace α where
  complete {f} hf := by
    obtain ⟨x, rfl⟩ := eq_pure_of_cauchy hf
    exact ⟨x, pure_le_nhds x⟩

variable {X}

/-- A constant to which a Cauchy filter in a discrete uniform space converges. -/
/-
**DiscreteUniformity.cauchyConst** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteUniformity`。
形式化陈述：cauchyConst {f : Filter α} (hf : Cauchy f) : α
参数：hf : Cauchy f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteUniformity.eq_pure_of_cauchy`：eq_pure_of_cauchy {f : Filter α} (
hf : Cauchy f) : exists x : α, f = pure x

--- 原说明 ---
A constant to which a Cauchy filter in a discrete uniform space converges.
-/
noncomputable def cauchyConst {f : Filter α} (hf : Cauchy f) : α :=
  (eq_pure_of_cauchy hf).choose
/-
**DiscreteUniformity.eq_pure_cauchyConst** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteUnif
ormity`。
形式化陈述：eq_pure_cauchyConst {f : Filter α} (hf : Cauchy f) : f = pure (cauchyConst
 hf)
参数：hf : Cauchy f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `DiscreteUniformity.eq_pure_of_cauchy`：eq_pure_of_cauchy {f : Filter α} (
hf : Cauchy f) : exists x : α, f = pure x
-/
theorem eq_pure_cauchyConst {f : Filter α} (hf : Cauchy f) : f = pure (cauchyConst hf) :=
  (eq_pure_of_cauchy hf).choose_spec

end DiscreteUniformity

/-- A set `s` is totally bounded if for every entourage `d` there is a finite
  set of points `t` such that every element of `s` is `d`-near to some element of `t`. -/
/-
**TotallyBounded** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TotallyBounded (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is totally bounded if for every entourage `d` there is a finite
  set of points `t` such that every element of `s` is `d`-near to some element o
f `t`.
-/
def TotallyBounded (s : Set α) : Prop :=
  ∀ d ∈ 𝓤 α, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d }

/-- A filter `f` is totally bounded if for every entourage `d`, the `d`-neighborhood of some finite
set is in `f`. -/
/-
**Filter.TotallyBounded** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u} → [uniformSpace : UniformSpace α] → Filter α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filter `f` is totally bounded if for every entourage `d`, the `d`-neighborhood
 of some finite
set is in `f`.
-/
protected def Filter.TotallyBounded (f : Filter α) :=
  ∀ d : SetRel α α, d ∈ 𝓤 α → ∃ t : Set α, t.Finite ∧ d.preimage t ∈ f
/-
**Filter.totallyBounded_principal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.totallyBounded_principal_iff {s : Set α} : (𝓟 s).TotallyBounded ↔ T
otallyBounded s
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SetRel.preimage_eq_biUnion`：preimage_eq_biUnion : R.preimage t = ⋃ y in 
t, {x | x ~[R] y}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.totallyBounded_principal_iff {s : Set α} :
    (𝓟 s).TotallyBounded ↔ TotallyBounded s := by
  simp only [Filter.TotallyBounded, mem_principal, SetRel.preimage_eq_biUnion, TotallyBounded]
/-
**Filter.TotallyBounded.exists_subset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.TotallyBounded.exists_subset_of_mem {f : Filter α} (hf : f.TotallyB
ounded) {s : Set α} (hs : s in f) {U : SetRel α α} (hU : U in 𝓤 α) : exists t su
bseteq s, Set.Finite t ∧ U.preimage t in f
参数：hf : f.TotallyBounded；hs : s in f；hU : U in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_symm_of_uniformity`：comp_symm_of_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : exists t in 𝓤 α, (forall {a b}, (a, b) in t -> (b, a) in t) ∧ t ○ t 
subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Filter.TotallyBounded.exists_subset_of_mem {f : Filter α} (hf : f.TotallyBounded)
    {s : Set α} (hs : s ∈ f) {U : SetRel α α} (hU : U ∈ 𝓤 α) :
    ∃ t ⊆ s, Set.Finite t ∧ U.preimage t ∈ f := by
  rcases comp_symm_of_uniformity hU with ⟨r, hr, rs, rU⟩
  rcases hf r hr with ⟨k, fk, ks⟩
  let u := k ∩ { y | ∃ x ∈ s, (x, y) ∈ r }
  choose g hgs hgr using fun x : u => x.coe_prop.2
  refine ⟨range g, ?_, ?_, ?_⟩
  · exact range_subset_iff.2 hgs
  · have : Fintype u := (fk.inter_of_left _).fintype
    exact finite_range g
  · filter_upwards [hs, ks] with x xs ⟨y, hy, xy⟩
    simp_rw [SetRel.preimage, exists_range_iff]
    set z : ↥u := ⟨y, hy, ⟨x, xs, xy⟩⟩
    exact ⟨z, rU ⟨y, xy, rs (hgr z)⟩⟩
/-
**TotallyBounded.exists_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TotallyBounded.exists_subset {s : Set α} (hs : TotallyBounded s) {U : SetR
el α α} (hU : U in 𝓤 α) : exists t, t subseteq s ∧ Set.Finite t ∧ s subseteq ⋃ y
 in t, { x | (x, y) in U }
参数：hs : TotallyBounded s；hU : U in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.TotallyBounded.exists_subset_of_mem`：Filter.TotallyBounded.exists
_subset_of_mem {f : Filter α} (hf : f.TotallyBounded) {s : Set α} (hs : s in f) 
{U : SetRel α α} (hU : U in 𝓤 α)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.totallyBounded_principal_iff`：Filter.totallyBounded_principal_iff
 {s : Set α} : (𝓟 s).TotallyBounded ↔ TotallyBounded s
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
-/
theorem TotallyBounded.exists_subset {s : Set α} (hs : TotallyBounded s) {U : SetRel α α}
    (hU : U ∈ 𝓤 α) : ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ U } := by
  rw [← Filter.totallyBounded_principal_iff] at hs
  simp_rw [← SetRel.preimage_eq_biUnion]
  exact hs.exists_subset_of_mem (Filter.mem_principal_self s) hU
/-
**totallyBounded_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：totallyBounded_iff_subset {s : Set α} : TotallyBounded s ↔ forall d in 𝓤 α
, exists t, t subseteq s ∧ Set.Finite t ∧ s subseteq ⋃ y in t, { x | (x, y) in d
 }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.exists_subset`：TotallyBounded.exists_subset {s : Set α} (
hs : TotallyBounded s) {U : SetRel α α} (hU : U in 𝓤 α) : exists t, t subseteq s
 ∧ Set.Finite t ∧ …
-/
theorem totallyBounded_iff_subset {s : Set α} :
    TotallyBounded s ↔
      ∀ d ∈ 𝓤 α, ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d } :=
  ⟨fun H _ hd ↦ H.exists_subset hd, fun H d hd ↦ let ⟨t, _, ht⟩ := H d hd; ⟨t, ht⟩⟩
/-
**Filter.HasBasis.totallyBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.totallyBounded_iff {ι} {p : ι -> Prop} {U : ι -> SetRel α 
α} (H : (𝓤 α).HasBasis p U) {s : Set α} : TotallyBounded s ↔ forall i, p i -> ex
ists t : Set α, Set.Finite t ∧ s subseteq ⋃ y in t, { x | (x, y) in U i }
参数：H : (𝓤 α).HasBasis p U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
-/
theorem Filter.HasBasis.totallyBounded_iff {ι} {p : ι → Prop} {U : ι → SetRel α α}
    (H : (𝓤 α).HasBasis p U) {s : Set α} :
    TotallyBounded s ↔ ∀ i, p i → ∃ t : Set α, Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ U i } :=
  H.forall_iff fun _ _ hUV h =>
    h.imp fun _ ht => ⟨ht.1, ht.2.trans <| iUnion₂_mono fun _ _ _ hy => hUV hy⟩
/-
**Filter.HasBasis.filter_totallyBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.filter_totallyBounded_iff {ι} {p : ι -> Prop} {U : ι -> Se
tRel α α} (H : (𝓤 α).HasBasis p U) {f : Filter α} : f.TotallyBounded ↔ forall i,
 p i -> exists t : Set α, Set.Finite t ∧ (U i).preimage t in f
参数：H : (𝓤 α).HasBasis p U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SetRel.preimage_subset_preimage_left`：∀ {α : Type u_1} {β : Type u_2} {R
₁ R₂ : SetRel α β} {t : Set β}, R₁ ⊆ R₂ → R₁.preimage t ⊆ R₂.preimage t
-/
theorem Filter.HasBasis.filter_totallyBounded_iff {ι} {p : ι → Prop} {U : ι → SetRel α α}
    (H : (𝓤 α).HasBasis p U) {f : Filter α} :
    f.TotallyBounded ↔ ∀ i, p i → ∃ t : Set α, Set.Finite t ∧ (U i).preimage t ∈ f :=
  H.forall_iff fun _ _ _ h =>
    h.imp fun _ ht => ⟨ht.1, f.mem_of_superset ht.2 <| by gcongr⟩
/-
**totallyBounded_of_forall_isSymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：totallyBounded_of_forall_isSymm {s : Set α} (h : forall V in 𝓤 α, SetRel.I
sSymm V -> exists t : Set α, Set.Finite t ∧ s subseteq ⋃ y in t, ball y V) : Tot
allyBounded s
参数：h : forall V in 𝓤 α, SetRel.IsSymm V -> exists t : Set α, Set.Finite t ∧ s su
bseteq ⋃ y in t, ball y V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.totallyBounded_iff`：Filter.HasBasis.totallyBounded_iff {
ι} {p : ι -> Prop} {U : ι -> SetRel α α} (H : (𝓤 α).HasBasis p U) {s : Set α} : 
TotallyBounded s ↔ foral…
· 使用定理 `UniformSpace.hasBasis_symmetric`：UniformSpace.hasBasis_symmetric : (𝓤 α)
.HasBasis (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) id
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `UniformSpace.ball_eq_of_symmetry`：ball_eq_of_symmetry {V : SetRel β β} [
V.IsSymm] {x} : ball x V = { y | (y, x) in V }
-/
theorem totallyBounded_of_forall_isSymm {s : Set α}
    (h : ∀ V ∈ 𝓤 α, SetRel.IsSymm V → ∃ t : Set α, Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y V) :
    TotallyBounded s :=
  UniformSpace.hasBasis_symmetric.totallyBounded_iff.2 fun V ⟨_, _⟩ => by
    simpa only [ball_eq_of_symmetry] using! h V ‹_› ‹_›
/-
**TotallyBounded.subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ subseteq s₂) (h : TotallyBo
unded s₂) : TotallyBounded s₁
参数：hs : s₁ subseteq s₂；h : TotallyBounded s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
theorem TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ ⊆ s₂) (h : TotallyBounded s₂) :
    TotallyBounded s₁ := fun d hd =>
  let ⟨t, ht₁, ht₂⟩ := h d hd
  ⟨t, ht₁, Subset.trans hs ht₂⟩
/-
**Filter.TotallyBounded.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.TotallyBounded.mono {f g : Filter α} (h : f <= g) (hg : g.TotallyBo
unded) : f.TotallyBounded
参数：h : f <= g；hg : g.TotallyBounded。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
-/
theorem Filter.TotallyBounded.mono {f g : Filter α} (h : f ≤ g) (hg : g.TotallyBounded) :
    f.TotallyBounded :=
  fun U hU => (hg U hU).imp fun _ => And.imp_right (@h _)
/-
**Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt {f : Filter α} (h
 : f.TotallyBounded) : TotallyBounded {x | ClusterPt x f}
参数：h : f.TotallyBounded。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.totallyBounded_iff`：Filter.HasBasis.totallyBounded_iff {
ι} {p : ι -> Prop} {U : ι -> SetRel α α} (H : (𝓤 α).HasBasis p U) {s : Set α} : 
TotallyBounded s ↔ foral…
· 使用定理 `uniformity_hasBasis_closed`：uniformity_hasBasis_closed : HasBasis (𝓤 α) 
(fun V : SetRel α α => V in 𝓤 α ∧ IsClosed V) id
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SetRel.preimage_eq_biUnion`：preimage_eq_biUnion : R.preimage t = ⋃ y in 
t, {x | x ~[R] y}
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用引理 `IsClosed.relPreimage_of_finite`：IsClosed.relPreimage_of_finite [Topologi
calSpace α] [TopologicalSpace β] {s : SetRel α β} (hs : IsClosed s) {t : Set β} 
(ht : t.Finite) : Is…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ClusterPt.mem_closure_of_mem`：∀ {X : Type u} [inst : TopologicalSpace X]
 {x : X} {F : Filter X}, ClusterPt x F → ∀ s ∈ F, x ∈ closure s
-/
theorem Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt {f : Filter α}
    (h : f.TotallyBounded) :
    TotallyBounded {x | ClusterPt x f} := by
  refine uniformity_hasBasis_closed.totallyBounded_iff.2 fun V hV => ?_
  obtain ⟨t, htf, hst⟩ := h V hV.1
  refine ⟨t, htf, fun x hx => ?_⟩
  rw [← SetRel.preimage_eq_biUnion, id, ← (hV.2.relPreimage_of_finite htf).closure_eq]
  exact hx.mem_closure_of_mem _ hst

@[deprecated (since := "2026-07-09")]
alias Filter.TotallyBounded.totallyBounded_setOf_clusterPt :=
  Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt

/-- The closure of a totally bounded set is totally bounded. -/
/-
**TotallyBounded.closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TotallyBounded.closure {s : Set α} (h : TotallyBounded s) : TotallyBounded
 (closure s)
参数：h : TotallyBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_eq_cluster_pts`：closure_eq_cluster_pts : closure s = { a | Clust
erPt a (𝓟 s) }
· 使用定理 `Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt`：Filter.Totally
Bounded.totallyBounded_setOfPred_clusterPt {f : Filter α} (h : f.TotallyBounded)
 : TotallyBounded {x | ClusterPt x f}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.totallyBounded_principal_iff`：Filter.totallyBounded_principal_iff
 {s : Set α} : (𝓟 s).TotallyBounded ↔ TotallyBounded s

--- 原说明 ---
The closure of a totally bounded set is totally bounded.
-/
theorem TotallyBounded.closure {s : Set α} (h : TotallyBounded s) : TotallyBounded (closure s) := by
  rw [closure_eq_cluster_pts]
  exact (Filter.totallyBounded_principal_iff.mpr h).totallyBounded_setOfPred_clusterPt

@[simp]
/-
**totallyBounded_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_closure {s : Set α} : TotallyBounded (closure s) ↔ TotallyB
ounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.subset`：TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) (h : TotallyBounded s₂) : TotallyBounded s₁
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `TotallyBounded.closure`：TotallyBounded.closure {s : Set α} (h : TotallyB
ounded s) : TotallyBounded (closure s)
-/
lemma totallyBounded_closure {s : Set α} : TotallyBounded (closure s) ↔ TotallyBounded s :=
  ⟨fun h ↦ h.subset subset_closure, TotallyBounded.closure⟩

@[simp]
/-
**Filter.totallyBounded_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.totallyBounded_iSup {ι : Sort*} [Finite ι] {f : ι -> Filter α} : (⨆
 i, f i).TotallyBounded ↔ forall i, (f i).TotallyBounded
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.TotallyBounded.mono`：Filter.TotallyBounded.mono {f g : Filter α} 
(h : f <= g) (hg : g.TotallyBounded) : f.TotallyBounded
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.finite_iUnion`：finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall
 i, (f i).Finite) : (⋃ i, f i).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SetRel.preimage_iUnion`：preimage_iUnion (t : ι -> Set β) : preimage R (⋃
 i, t i) = ⋃ i, preimage R (t i)
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma Filter.totallyBounded_iSup {ι : Sort*} [Finite ι] {f : ι → Filter α} :
    (⨆ i, f i).TotallyBounded ↔ ∀ i, (f i).TotallyBounded := by
  refine ⟨fun h i ↦ h.mono (le_iSup _ _), fun h U hU ↦ ?_⟩
  choose t htf ht using (h · U hU)
  refine ⟨⋃ i, t i, finite_iUnion htf, ?_⟩
  simp_rw [U.preimage_iUnion, ← le_principal_iff, ← iSup_principal] at ht ⊢
  gcongr; apply ht
/-
**Filter.totallyBounded_biSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.totallyBounded_biSup {ι : Type*} {I : Set ι} (hI : I.Finite) {f : ι
 -> Filter α} : (⨆ i in I, f i).TotallyBounded ↔ forall i in I, (f i).TotallyBou
nded
参数：hI : I.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用引理 `Filter.totallyBounded_iSup`：Filter.totallyBounded_iSup {ι : Sort*} [Fini
te ι] {f : ι -> Filter α} : (⨆ i, f i).TotallyBounded ↔ forall i, (f i).TotallyB
ounded
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Filter.totallyBounded_biSup {ι : Type*} {I : Set ι} (hI : I.Finite) {f : ι → Filter α} :
    (⨆ i ∈ I, f i).TotallyBounded ↔ ∀ i ∈ I, (f i).TotallyBounded := by
  have := hI.to_subtype
  rw [iSup_subtype', totallyBounded_iSup, Subtype.forall]
/-
**totallyBounded_sSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_sSup {S : Set (Filter α)} (hS : S.Finite) : (sSup S).Totall
yBounded ↔ forall f in S, f.TotallyBounded
参数：Filter α；hS : S.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用引理 `Filter.totallyBounded_biSup`：Filter.totallyBounded_biSup {ι : Type*} {I 
: Set ι} (hI : I.Finite) {f : ι -> Filter α} : (⨆ i in I, f i).TotallyBounded ↔ 
forall i in I, (f…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma totallyBounded_sSup {S : Set (Filter α)} (hS : S.Finite) :
    (sSup S).TotallyBounded ↔ ∀ f ∈ S, f.TotallyBounded := by
  rw [sSup_eq_iSup, totallyBounded_biSup hS]

/-- A finite indexed union is totally bounded
if and only if each set of the family is totally bounded. -/
@[simp]
/-
**totallyBounded_iUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_iUnion {ι : Sort*} [Finite ι] {s : ι -> Set α} : TotallyBou
nded (⋃ i, s i) ↔ forall i, TotallyBounded (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A finite indexed union is totally bounded
if and only if each set of the family is totally bounded.
-/
lemma totallyBounded_iUnion {ι : Sort*} [Finite ι] {s : ι → Set α} :
    TotallyBounded (⋃ i, s i) ↔ ∀ i, TotallyBounded (s i) := by
  simp_rw [← Filter.totallyBounded_principal_iff, ← Filter.iSup_principal,
    Filter.totallyBounded_iSup]

/-- A union indexed by a finite set is totally bounded
if and only if each set of the family is totally bounded. -/
/-
**totallyBounded_biUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> S
et α} : TotallyBounded (⋃ i in I, s i) ↔ forall i in I, TotallyBounded (s i)
参数：hI : I.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用引理 `totallyBounded_iUnion`：totallyBounded_iUnion {ι : Sort*} [Finite ι] {s :
 ι -> Set α} : TotallyBounded (⋃ i, s i) ↔ forall i, TotallyBounded (s i)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A union indexed by a finite set is totally bounded
if and only if each set of the family is totally bounded.
-/
lemma totallyBounded_biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set α} :
    TotallyBounded (⋃ i ∈ I, s i) ↔ ∀ i ∈ I, TotallyBounded (s i) := by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion, totallyBounded_iUnion, Subtype.forall]

/-- A union of a finite family of sets is totally bounded
if and only if each set of the family is totally bounded. -/
/-
**totallyBounded_sUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_sUnion {S : Set (Set α)} (hS : S.Finite) : TotallyBounded (
⋃₀ S) ↔ forall s in S, TotallyBounded s
参数：Set α；hS : S.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用引理 `totallyBounded_biUnion`：totallyBounded_biUnion {ι : Type*} {I : Set ι} (
hI : I.Finite) {s : ι -> Set α} : TotallyBounded (⋃ i in I, s i) ↔ forall i in I
, TotallyBou…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A union of a finite family of sets is totally bounded
if and only if each set of the family is totally bounded.
-/
lemma totallyBounded_sUnion {S : Set (Set α)} (hS : S.Finite) :
    TotallyBounded (⋃₀ S) ↔ ∀ s ∈ S, TotallyBounded s := by
  rw [sUnion_eq_biUnion, totallyBounded_biUnion hS]

/-- A finite set is totally bounded. -/
/-
**Set.Finite.totallyBounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Finite.totallyBounded {s : Set α} (hs : s.Finite) : TotallyBounded s
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s

--- 原说明 ---
A finite set is totally bounded.
-/
lemma Set.Finite.totallyBounded {s : Set α} (hs : s.Finite) : TotallyBounded s := fun _U hU ↦
  ⟨s, hs, fun _x hx ↦ mem_biUnion hx <| refl_mem_uniformity hU⟩

/-- A subsingleton is totally bounded. -/
/-
**Set.Subsingleton.totallyBounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.totallyBounded {s : Set α} (hs : s.Subsingleton) : Totall
yBounded s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Finite.totallyBounded`：Set.Finite.totallyBounded {s : Set α} (hs : s
.Finite) : TotallyBounded s
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite

--- 原说明 ---
A subsingleton is totally bounded.
-/
lemma Set.Subsingleton.totallyBounded {s : Set α} (hs : s.Subsingleton) :
    TotallyBounded s :=
  hs.finite.totallyBounded

@[simp]
/-
**totallyBounded_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_singleton (a : α) : TotallyBounded {a}
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Finite.totallyBounded`：Set.Finite.totallyBounded {s : Set α} (hs : s
.Finite) : TotallyBounded s
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
lemma totallyBounded_singleton (a : α) : TotallyBounded {a} := (finite_singleton a).totallyBounded

@[simp]
/-
**totallyBounded_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：totallyBounded_empty : TotallyBounded (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Finite.totallyBounded`：Set.Finite.totallyBounded {s : Set α} (hs : s
.Finite) : TotallyBounded s
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
-/
theorem totallyBounded_empty : TotallyBounded (∅ : Set α) := finite_empty.totallyBounded

@[simp]
/-
**Filter.totallyBounded_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.totallyBounded_bot : (⊥ : Filter α).TotallyBounded
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `Filter.totallyBounded_principal_iff`：Filter.totallyBounded_principal_iff
 {s : Set α} : (𝓟 s).TotallyBounded ↔ TotallyBounded s
· 使用定理 `totallyBounded_empty`：totallyBounded_empty : TotallyBounded (∅ : Set α)
-/
theorem Filter.totallyBounded_bot : (⊥ : Filter α).TotallyBounded := by
  rw [← principal_empty, totallyBounded_principal_iff]
  exact totallyBounded_empty

/-- The union of two sets is totally bounded
if and only if each of the two sets is totally bounded. -/
@[simp]
/-
**totallyBounded_union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_union {s t : Set α} : TotallyBounded (s union t) ↔ TotallyB
ounded s ∧ TotallyBounded t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用引理 `totallyBounded_iUnion`：totallyBounded_iUnion {ι : Sort*} [Finite ι] {s :
 ι -> Set α} : TotallyBounded (⋃ i, s i) ↔ forall i, TotallyBounded (s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The union of two sets is totally bounded
if and only if each of the two sets is totally bounded.
-/
lemma totallyBounded_union {s t : Set α} :
    TotallyBounded (s ∪ t) ↔ TotallyBounded s ∧ TotallyBounded t := by
  rw [union_eq_iUnion, totallyBounded_iUnion]
  simp [and_comm]

/-- The union of two totally bounded sets is totally bounded. -/
/-
**TotallyBounded.union** 是 Mathlib 中的一个定理，位于命名空间 `TotallyBounded`。
形式化陈述：∀ {α : Type u} [uniformSpace : UniformSpace α] {s t : Set α},   TotallyBou
nded s → TotallyBounded t → TotallyBounded (s ∪ t)
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `totallyBounded_union`：totallyBounded_union {s t : Set α} : TotallyBounde
d (s union t) ↔ TotallyBounded s ∧ TotallyBounded t

--- 原说明 ---
The union of two totally bounded sets is totally bounded.
-/
protected lemma TotallyBounded.union {s t : Set α} (hs : TotallyBounded s) (ht : TotallyBounded t) :
    TotallyBounded (s ∪ t) :=
  totallyBounded_union.2 ⟨hs, ht⟩

@[simp]
/-
**totallyBounded_insert** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_insert (a : α) {s : Set α} : TotallyBounded (insert a s) ↔ 
TotallyBounded s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma totallyBounded_insert (a : α) {s : Set α} :
    TotallyBounded (insert a s) ↔ TotallyBounded s := by
  simp_rw [← singleton_union, totallyBounded_union, totallyBounded_singleton, true_and]

protected alias ⟨_, TotallyBounded.insert⟩ := totallyBounded_insert

@[simp]
/-
**Filter.totallyBounded_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.totallyBounded_sup {f g : Filter α} : (f ⊔ g).TotallyBounded ↔ f.To
tallyBounded ∧ g.TotallyBounded
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_eq_iSup`：sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y
· 使用引理 `Filter.totallyBounded_iSup`：Filter.totallyBounded_iSup {ι : Sort*} [Fini
te ι] {f : ι -> Filter α} : (⨆ i, f i).TotallyBounded ↔ forall i, (f i).TotallyB
ounded
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Filter.totallyBounded_sup {f g : Filter α} :
    (f ⊔ g).TotallyBounded ↔ f.TotallyBounded ∧ g.TotallyBounded := by
  rw [sup_eq_iSup, totallyBounded_iSup]
  simp [and_comm]
/-
**Filter.TotallyBounded.sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.TotallyBounded.sup {f g : Filter α} (hf : f.TotallyBounded) (hg : g
.TotallyBounded) : (f ⊔ g).TotallyBounded
参数：hf : f.TotallyBounded；hg : g.TotallyBounded。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.totallyBounded_sup`：Filter.totallyBounded_sup {f g : Filter α} : 
(f ⊔ g).TotallyBounded ↔ f.TotallyBounded ∧ g.TotallyBounded
-/
lemma Filter.TotallyBounded.sup {f g : Filter α} (hf : f.TotallyBounded) (hg : g.TotallyBounded) :
    (f ⊔ g).TotallyBounded :=
  totallyBounded_sup.2 ⟨hf, hg⟩
/-
**Filter.TotallyBounded.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.TotallyBounded.map [UniformSpace β] {f : α -> β} {g : Filter α} (hg
 : g.TotallyBounded) (hf : UniformContinuous f) : (g.map f).TotallyBounded
参数：hg : g.TotallyBounded；hf : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem Filter.TotallyBounded.map [UniformSpace β] {f : α → β} {g : Filter α}
    (hg : g.TotallyBounded) (hf : UniformContinuous f) : (g.map f).TotallyBounded := fun t ht =>
  let ⟨c, hfc, hct⟩ := hg _ (hf ht)
  ⟨f '' c, hfc.image f, by simpa [SetRel.preimage]⟩

/-- The image of a totally bounded set under a uniformly continuous map is totally bounded. -/
/-
**TotallyBounded.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TotallyBounded.image [UniformSpace β] {f : α -> β} {s : Set α} (hs : Total
lyBounded s) (hf : UniformContinuous f) : TotallyBounded (f '' s)
参数：hs : TotallyBounded s；hf : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.TotallyBounded.map`：Filter.TotallyBounded.map [UniformSpace β] {f
 : α -> β} {g : Filter α} (hg : g.TotallyBounded) (hf : UniformContinuous f) : (
g.map f).Totall…

--- 原说明 ---
The image of a totally bounded set under a uniformly continuous map is totally b
ounded.
-/
theorem TotallyBounded.image [UniformSpace β] {f : α → β} {s : Set α} (hs : TotallyBounded s)
    (hf : UniformContinuous f) : TotallyBounded (f '' s) := by
  simp only [← Filter.totallyBounded_principal_iff, ← Filter.map_principal] at hs ⊢
  exact hs.map hf
/-
**Ultrafilter.cauchy_of_totallyBounded'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ultrafilter.cauchy_of_totallyBounded' (f : Ultrafilter α) (hf : f.TotallyB
ounded) : Cauchy (f : Filter α)
参数：f : Ultrafilter α；hf : f.TotallyBounded。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.neBot'`：∀ {α : Type u_2} (self : Ultrafilter α), (↑self).NeB
ot
· 使用定理 `comp_symm_of_uniformity`：comp_symm_of_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : exists t in 𝓤 α, (forall {a b}, (a, b) in t -> (b, a) in t) ∧ t ○ t 
subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Ultrafilter.eventually_exists_mem_iff`：eventually_exists_mem_iff {is : S
et β} {P : β -> α -> Prop} (his : is.Finite) : (forallᶠ i in f, exists a in is, 
P a i) ↔ exists a in is, fo…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
theorem Ultrafilter.cauchy_of_totallyBounded' (f : Ultrafilter α) (hf : f.TotallyBounded) :
    Cauchy (f : Filter α) :=
  ⟨f.neBot', fun _ ht =>
    let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht
    let ⟨i, hi, ht'_f⟩ := hf t' ht'₁
    have : ∃ y ∈ i, { x | (x, y) ∈ t' } ∈ f := (Ultrafilter.eventually_exists_mem_iff hi).1 ht'_f
    let ⟨y, _, hif⟩ := this
    have : {x | (x, y) ∈ t'} ×ˢ {x | (x, y) ∈ t'} ⊆ t' ○ t' :=
      fun ⟨_, _⟩ ⟨(h₁ : (_, y) ∈ t'), (h₂ : (_, y) ∈ t')⟩ => ⟨y, h₁, ht'_symm h₂⟩
    mem_of_superset (prod_mem_prod hif hif) (Subset.trans this ht'_t)⟩
/-
**Ultrafilter.cauchy_of_totallyBounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ultrafilter.cauchy_of_totallyBounded {s : Set α} (f : Ultrafilter α) (hs :
 TotallyBounded s) (h : ↑f <= 𝓟 s) : Cauchy (f : Filter α)
参数：f : Ultrafilter α；hs : TotallyBounded s；h : ↑f <= 𝓟 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.cauchy_of_totallyBounded'`：Ultrafilter.cauchy_of_totallyBoun
ded' (f : Ultrafilter α) (hf : f.TotallyBounded) : Cauchy (f : Filter α)
· 使用定理 `Filter.TotallyBounded.mono`：Filter.TotallyBounded.mono {f g : Filter α} 
(h : f <= g) (hg : g.TotallyBounded) : f.TotallyBounded
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.totallyBounded_principal_iff`：Filter.totallyBounded_principal_iff
 {s : Set α} : (𝓟 s).TotallyBounded ↔ TotallyBounded s
-/
theorem Ultrafilter.cauchy_of_totallyBounded {s : Set α} (f : Ultrafilter α) (hs : TotallyBounded s)
    (h : ↑f ≤ 𝓟 s) : Cauchy (f : Filter α) :=
  f.cauchy_of_totallyBounded' <| (Filter.totallyBounded_principal_iff.mpr hs).mono h
/-
**Filter.totallyBounded_iff_filter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} [uniformSpace : UniformSpace α] {g : Filter α},   g.Totally
Bounded ↔ ∀ (f : Filter α), f.NeBot → f ≤ g → ∃ c ≤ f, Cauchy c
参数：f : Filter α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
· 使用定理 `Ultrafilter.cauchy_of_totallyBounded'`：Ultrafilter.cauchy_of_totallyBoun
ded' (f : Ultrafilter α) (hf : f.TotallyBounded) : Cauchy (f : Filter α)
· 使用定理 `Filter.TotallyBounded.mono`：Filter.TotallyBounded.mono {f g : Filter α} 
(h : f <= g) (hg : g.TotallyBounded) : f.TotallyBounded
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.principal_mono._gcongr_1`：∀ {α : Type u} {s t : Set α}, s ⊆ t → F
ilter.principal s ≤ Filter.principal t
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
· 使用定理 `SetRel.preimage_subset_preimage`：∀ {α : Type u_1} {β : Type u_2} {R : Se
tRel α β} {t₁ t₂ : Set β}, t₁ ⊆ t₂ → R.preimage t₁ ⊆ R.preimage t₂
· 使用定理 `Finset.coe_subset._gcongr_2`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s
₂ → ↑s₁ ⊆ ↑s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.iInf_neBot_iff_of_directed'`：iInf_neBot_iff_of_directed' {f : ι -
> Filter α} [Nonempty ι] (hd : Directed (· >= ·) f) : NeBot (iInf f) ↔ forall i,
 NeBot (f i)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Antitone.directed_ge`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α
] [IsDirectedOrder α] [inst_2 : Preorder β] {f : α → β},   Antitone f → Directed
 (fun x1 x…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.notMem_iff_inf_principal_compl`：notMem_iff_inf_principal_compl {f
 : Filter α} {s : Set α} : s ∉ f ↔ NeBot (f ⊓ 𝓟 sᶜ)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `SetRel.preimage_empty_right`：∀ {α : Type u_1} {β : Type u_2} {R : SetRel
 α β}, R.preimage ∅ = ∅
（共 41 条，此处仅展示前 30 条）
-/
protected theorem Filter.totallyBounded_iff_filter {g : Filter α} :
    g.TotallyBounded ↔ ∀ f, NeBot f → f ≤ g → ∃ c ≤ f, Cauchy c := by
  constructor
  · exact fun H f hf hfs => ⟨Ultrafilter.of f, Ultrafilter.of_le f,
      (Ultrafilter.of f).cauchy_of_totallyBounded' (H.mono ((Ultrafilter.of_le f).trans hfs))⟩
  · intro H d hd
    contrapose! H with hd_cover
    set f := ⨅ t : Finset α, g ⊓ 𝓟 (d.preimage t)ᶜ
    have hb : Antitone fun t : Finset α ↦ g ⊓ 𝓟 (d.preimage t)ᶜ :=
      fun s t (h : s ⊆ t) => by beta_reduce; gcongr
    have : Filter.NeBot f :=
      (Filter.iInf_neBot_iff_of_directed' <| hb.directed_ge).mpr fun t =>
        Filter.notMem_iff_inf_principal_compl.mp <| hd_cover t t.finite_toSet
    have : f ≤ g := iInf_le_of_le ∅ (by simp)
    refine ⟨f, ‹_›, ‹_›, fun c hcf hc => ?_⟩
    rcases mem_prod_same_iff.1 (hc.2 hd) with ⟨m, hm, hmd⟩
    rcases hc.1.nonempty_of_mem hm with ⟨y, hym⟩
    have : {x | (x, y) ∈ d}ᶜ ∈ c := by
      simpa [SetRel.preimage] using hcf.trans <| (iInf_le _ {y}).trans inf_le_right
    rcases hc.1.nonempty_of_mem (inter_mem hm this) with ⟨z, hzm, hyz⟩
    exact hyz (hmd ⟨hzm, hym⟩)
/-
**Filter.totallyBounded_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} [uniformSpace : UniformSpace α] {g : Filter α},   g.Totally
Bounded ↔ ∀ (f : Ultrafilter α), ↑f ≤ g → Cauchy ↑f
参数：f : Ultrafilter α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.cauchy_of_totallyBounded'`：Ultrafilter.cauchy_of_totallyBoun
ded' (f : Ultrafilter α) (hf : f.TotallyBounded) : Cauchy (f : Filter α)
· 使用定理 `Filter.TotallyBounded.mono`：Filter.TotallyBounded.mono {f g : Filter α} 
(h : f <= g) (hg : g.TotallyBounded) : f.TotallyBounded
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.totallyBounded_iff_filter`：∀ {α : Type u} [uniformSpace : Uniform
Space α] {g : Filter α},   g.TotallyBounded ↔ ∀ (f : Filter α), f.NeBot → f ≤ g 
→ ∃ c ≤ f, Cauchy c
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
protected theorem Filter.totallyBounded_iff_ultrafilter {g : Filter α} :
    g.TotallyBounded ↔ ∀ f : Ultrafilter α, ↑f ≤ g → Cauchy (f : Filter α) := by
  refine ⟨fun hg f hf => f.cauchy_of_totallyBounded' <| hg.mono hf,
    fun H => g.totallyBounded_iff_filter.2 ?_⟩
  intro f hf hfs
  exact ⟨Ultrafilter.of f, Ultrafilter.of_le f, H _ ((Ultrafilter.of_le f).trans hfs)⟩
/-
**totallyBounded_iff_filter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：totallyBounded_iff_filter {s : Set α} : TotallyBounded s ↔ forall f, NeBot
 f -> f <= 𝓟 s -> exists c <= f, Cauchy c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.totallyBounded_principal_iff`：Filter.totallyBounded_principal_iff
 {s : Set α} : (𝓟 s).TotallyBounded ↔ TotallyBounded s
· 使用定理 `Filter.totallyBounded_iff_filter`：∀ {α : Type u} [uniformSpace : Uniform
Space α] {g : Filter α},   g.TotallyBounded ↔ ∀ (f : Filter α), f.NeBot → f ≤ g 
→ ∃ c ≤ f, Cauchy c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem totallyBounded_iff_filter {s : Set α} :
    TotallyBounded s ↔ ∀ f, NeBot f → f ≤ 𝓟 s → ∃ c ≤ f, Cauchy c := by
  rw [← Filter.totallyBounded_principal_iff, Filter.totallyBounded_iff_filter]
/-
**totallyBounded_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：totallyBounded_iff_ultrafilter {s : Set α} : TotallyBounded s ↔ forall f :
 Ultrafilter α, ↑f <= 𝓟 s -> Cauchy (f : Filter α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.totallyBounded_principal_iff`：Filter.totallyBounded_principal_iff
 {s : Set α} : (𝓟 s).TotallyBounded ↔ TotallyBounded s
· 使用定理 `Filter.totallyBounded_iff_ultrafilter`：∀ {α : Type u} [uniformSpace : Un
iformSpace α] {g : Filter α},   g.TotallyBounded ↔ ∀ (f : Ultrafilter α), ↑f ≤ g
 → Cauchy ↑f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem totallyBounded_iff_ultrafilter {s : Set α} :
    TotallyBounded s ↔ ∀ f : Ultrafilter α, ↑f ≤ 𝓟 s → Cauchy (f : Filter α) := by
  rw [← Filter.totallyBounded_principal_iff, Filter.totallyBounded_iff_ultrafilter]
/-
**isCompact_iff_totallyBounded_isComplete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_iff_totallyBounded_isComplete {s : Set α} : IsCompact s ↔ Totall
yBounded s ∧ IsComplete s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `totallyBounded_iff_ultrafilter`：totallyBounded_iff_ultrafilter {s : Set 
α} : TotallyBounded s ↔ forall f : Ultrafilter α, ↑f <= 𝓟 s -> Cauchy (f : Filte
r α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_ultrafilter_le_nhds`：isCompact_iff_ultrafilter_le_nhds : I
sCompact s ↔ forall f : Ultrafilter X, ↑f <= 𝓟 s -> exists x in s, ↑f <= 𝓝 x
· 使用定理 `Cauchy.mono`：Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f
) (h_le : g <= f) : Cauchy g
· 使用定理 `cauchy_nhds`：cauchy_nhds {a : α} : Cauchy (𝓝 a)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_nhds_of_cauchy_adhp`：le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (h
f : Cauchy f) (adhs : ClusterPt x f) : f <= 𝓝 x
-/
theorem isCompact_iff_totallyBounded_isComplete {s : Set α} :
    IsCompact s ↔ TotallyBounded s ∧ IsComplete s :=
  ⟨fun hs =>
    ⟨totallyBounded_iff_ultrafilter.2 fun f hf =>
        let ⟨_, _, fx⟩ := isCompact_iff_ultrafilter_le_nhds.1 hs f hf
        cauchy_nhds.mono fx,
      fun f fc fs =>
      let ⟨a, as, fa⟩ := @hs f fc.1 fs
      ⟨a, as, le_nhds_of_cauchy_adhp fc fa⟩⟩,
    fun ⟨ht, hc⟩ =>
    isCompact_iff_ultrafilter_le_nhds.2 fun f hf =>
      hc _ (totallyBounded_iff_ultrafilter.1 ht f hf) hf⟩
/-
**IsCompact.totallyBounded** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：∀ {α : Type u} [uniformSpace : UniformSpace α] {s : Set α}, IsCompact s → 
TotallyBounded s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_totallyBounded_isComplete`：isCompact_iff_totallyBounded_is
Complete {s : Set α} : IsCompact s ↔ TotallyBounded s ∧ IsComplete s
-/
protected theorem IsCompact.totallyBounded {s : Set α} (h : IsCompact s) : TotallyBounded s :=
  (isCompact_iff_totallyBounded_isComplete.1 h).1
/-
**IsCompact.isComplete** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：∀ {α : Type u} [uniformSpace : UniformSpace α] {s : Set α}, IsCompact s → 
IsComplete s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_totallyBounded_isComplete`：isCompact_iff_totallyBounded_is
Complete {s : Set α} : IsCompact s ↔ TotallyBounded s ∧ IsComplete s
-/
protected theorem IsCompact.isComplete {s : Set α} (h : IsCompact s) : IsComplete s :=
  (isCompact_iff_totallyBounded_isComplete.1 h).2

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) complete_of_compact {α : Type u} [UniformSpace α] [CompactSpace α] :
    CompleteSpace α :=
  ⟨fun hf => by simpa using (isCompact_iff_totallyBounded_isComplete.1 isCompact_univ).2 _ hf⟩
/-
**TotallyBounded.isCompact_of_isComplete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TotallyBounded.isCompact_of_isComplete {s : Set α} (ht : TotallyBounded s)
 (hc : IsComplete s) : IsCompact s
参数：ht : TotallyBounded s；hc : IsComplete s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_totallyBounded_isComplete`：isCompact_iff_totallyBounded_is
Complete {s : Set α} : IsCompact s ↔ TotallyBounded s ∧ IsComplete s
-/
theorem TotallyBounded.isCompact_of_isComplete {s : Set α} (ht : TotallyBounded s)
    (hc : IsComplete s) : IsCompact s := isCompact_iff_totallyBounded_isComplete.mpr ⟨ht, hc⟩
/-
**TotallyBounded.isCompact_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TotallyBounded.isCompact_of_isClosed [CompleteSpace α] {s : Set α} (ht : T
otallyBounded s) (hc : IsClosed s) : IsCompact s
参数：ht : TotallyBounded s；hc : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.isCompact_of_isComplete`：TotallyBounded.isCompact_of_isCo
mplete {s : Set α} (ht : TotallyBounded s) (hc : IsComplete s) : IsCompact s
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
-/
theorem TotallyBounded.isCompact_of_isClosed [CompleteSpace α] {s : Set α} (ht : TotallyBounded s)
    (hc : IsClosed s) : IsCompact s := ht.isCompact_of_isComplete hc.isComplete
/-
**Filter.TotallyBounded.isCompact_setOfPred_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Filter.TotallyBounded.isCompact_setOfPred_clusterPt [CompleteSpace α] {f :
 Filter α} (hf : f.TotallyBounded) : IsCompact {x | ClusterPt x f}
参数：hf : f.TotallyBounded。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.isCompact_of_isClosed`：TotallyBounded.isCompact_of_isClos
ed [CompleteSpace α] {s : Set α} (ht : TotallyBounded s) (hc : IsClosed s) : IsC
ompact s
· 使用定理 `Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt`：Filter.Totally
Bounded.totallyBounded_setOfPred_clusterPt {f : Filter α} (h : f.TotallyBounded)
 : TotallyBounded {x | ClusterPt x f}
· 使用定理 `isClosed_setOfPred_clusterPt`：isClosed_setOfPred_clusterPt {f : Filter X
} : IsClosed { x | ClusterPt x f }
-/
theorem Filter.TotallyBounded.isCompact_setOfPred_clusterPt
    [CompleteSpace α] {f : Filter α} (hf : f.TotallyBounded) : IsCompact {x | ClusterPt x f} :=
  hf.totallyBounded_setOfPred_clusterPt.isCompact_of_isClosed isClosed_setOfPred_clusterPt

@[deprecated (since := "2026-07-09")]
alias Filter.TotallyBounded.isCompact_setOf_clusterPt :=
  Filter.TotallyBounded.isCompact_setOfPred_clusterPt
/-
**Filter.TotallyBounded.exists_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.TotallyBounded.exists_clusterPt [CompleteSpace α] {f : Filter α} [f
.NeBot] (hf : f.TotallyBounded) : exists x, ClusterPt x f
参数：hf : f.TotallyBounded。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
· 使用定理 `Ultrafilter.cauchy_of_totallyBounded'`：Ultrafilter.cauchy_of_totallyBoun
ded' (f : Ultrafilter α) (hf : f.TotallyBounded) : Cauchy (f : Filter α)
· 使用定理 `Filter.TotallyBounded.mono`：Filter.TotallyBounded.mono {f g : Filter α} 
(h : f <= g) (hg : g.TotallyBounded) : f.TotallyBounded
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_nhds_iff_adhp_of_cauchy`：le_nhds_iff_adhp_of_cauchy {f : Filter α} {x
 : α} (hf : Cauchy f) : f <= 𝓝 x ↔ ClusterPt x f
-/
theorem Filter.TotallyBounded.exists_clusterPt
    [CompleteSpace α] {f : Filter α} [f.NeBot] (hf : f.TotallyBounded) : ∃ x, ClusterPt x f := by
  let m := Ultrafilter.of f
  have hmf : m ≤ f := Ultrafilter.of_le f
  have hm := m.cauchy_of_totallyBounded' (hf.mono hmf)
  obtain ⟨x, hx⟩ := CompleteSpace.complete hm
  rw [le_nhds_iff_adhp_of_cauchy hm] at hx
  exact ⟨x, hx.mono hmf⟩

/-- Every Cauchy sequence over `ℕ` is totally bounded. -/
/-
**CauchySeq.totallyBounded_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CauchySeq.totallyBounded_range {s : Nat -> α} (hs : CauchySeq s) : Totally
Bounded (range s)
参数：hs : CauchySeq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchySeq_iff`：cauchySeq_iff {u : Nat -> α} : CauchySeq u ↔ forall V in 
𝓤 α, exists N, forall k >= N, forall l >= N, (u k, u l) in V
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Set.biUnion_image`：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y
)
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Every Cauchy sequence over `ℕ` is totally bounded.
-/
theorem CauchySeq.totallyBounded_range {s : ℕ → α} (hs : CauchySeq s) :
    TotallyBounded (range s) := by
  intro a ha
  obtain ⟨n, hn⟩ := cauchySeq_iff.1 hs a ha
  refine ⟨s '' { k | k ≤ n }, (finite_le_nat _).image _, ?_⟩
  rw [range_subset_iff, biUnion_image]
  intro m
  rw [mem_iUnion₂]
  rcases le_total m n with hm | hm
  exacts [⟨m, hm, refl_mem_uniformity ha⟩, ⟨n, le_refl n, hn m hm n le_rfl⟩]

/-- Given a family of points `xs n`, a family of entourages `V n` of the diagonal and a family of
natural numbers `u n`, the intersection over `n` of the `V n`-neighborhood of `xs 1, ..., xs (u n)`.
Designed to be relatively compact when `V n` tends to the diagonal. -/
/-
**interUnionBalls** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：interUnionBalls (xs : Nat -> α) (u : Nat -> Nat) (V : Nat -> SetRel α α) :
 Set α
参数：xs : Nat -> α；u : Nat -> Nat；V : Nat -> SetRel α α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of points `xs n`, a family of entourages `V n` of the diagonal an
d a family of
natural numbers `u n`, the intersection over `n` of the `V n`-neighborhood of `x
s 1, ..., xs (u n)`.
Designed to be relatively compact when `V n` tends to the diagonal.
-/
def interUnionBalls (xs : ℕ → α) (u : ℕ → ℕ) (V : ℕ → SetRel α α) : Set α :=
  ⋂ n, ⋃ m ≤ u n, UniformSpace.ball (xs m) (Prod.swap ⁻¹' V n)
/-
**totallyBounded_interUnionBalls** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_interUnionBalls {p : Nat -> Prop} {U : Nat -> SetRel α α} (
H : (uniformity α).HasBasis p U) (xs : Nat -> α) (u : Nat -> Nat) : TotallyBound
ed (interUnionBalls xs u U)
参数：H : (uniformity α).HasBasis p U；xs : Nat -> α；u : Nat -> Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.totallyBounded_iff`：Filter.HasBasis.totallyBounded_iff {
ι} {p : ι -> Prop} {U : ι -> SetRel α α} (H : (𝓤 α).HasBasis p U) {s : Set α} : 
TotallyBounded s ↔ foral…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_and'`：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
-/
lemma totallyBounded_interUnionBalls {p : ℕ → Prop} {U : ℕ → SetRel α α}
    (H : (uniformity α).HasBasis p U) (xs : ℕ → α) (u : ℕ → ℕ) :
    TotallyBounded (interUnionBalls xs u U) := by
  rw [Filter.HasBasis.totallyBounded_iff H]
  intro i _
  have h_subset : interUnionBalls xs u U
      ⊆ ⋃ m ≤ u i, UniformSpace.ball (xs m) (Prod.swap ⁻¹' U i) :=
    fun x hx ↦ Set.mem_iInter.1 hx i
  classical
  refine ⟨Finset.image xs (Finset.range (u i + 1)), Finset.finite_toSet _, fun x hx ↦ ?_⟩
  simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio, iUnion_exists, biUnion_and',
    iUnion_iUnion_eq_right, Nat.lt_succ_iff]
  exact h_subset hx

/-- The construction `interUnionBalls` is used to have a relatively compact set. -/
/-
**isCompact_closure_interUnionBalls** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_closure_interUnionBalls {p : Nat -> Prop} {U : Nat -> SetRel α α
} (H : (uniformity α).HasBasis p U) [CompleteSpace α] (xs : Nat -> α) (u : Nat -
> Nat) : IsCompact (closure (interUnionBalls xs u U))
参数：H : (uniformity α).HasBasis p U；xs : Nat -> α；u : Nat -> Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompact_iff_totallyBounded_isComplete`：isCompact_iff_totallyBounded_is
Complete {s : Set α} : IsCompact s ↔ TotallyBounded s ∧ IsComplete s
· 使用定理 `TotallyBounded.closure`：TotallyBounded.closure {s : Set α} (h : TotallyB
ounded s) : TotallyBounded (closure s)
· 使用引理 `totallyBounded_interUnionBalls`：totallyBounded_interUnionBalls {p : Nat 
-> Prop} {U : Nat -> SetRel α α} (H : (uniformity α).HasBasis p U) (xs : Nat -> 
α) (u : Nat -> Nat) …
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
The construction `interUnionBalls` is used to have a relatively compact set.
-/
theorem isCompact_closure_interUnionBalls {p : ℕ → Prop} {U : ℕ → SetRel α α}
    (H : (uniformity α).HasBasis p U) [CompleteSpace α] (xs : ℕ → α) (u : ℕ → ℕ) :
    IsCompact (closure (interUnionBalls xs u U)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
  exact totallyBounded_interUnionBalls H xs u

/-!
### Sequentially complete space

In this section we prove that a uniform space is complete provided that it is sequentially complete
(i.e., any Cauchy sequence converges) and its uniformity filter admits a countable generating set.
In particular, this applies to (e)metric spaces, see the files
`Mathlib/Topology/EMetricSpace/Basic.lean` and `Mathlib/Topology/MetricSpace/Basic.lean`.

More precisely, we assume that there is a sequence of entourages `U_n` such that any other
entourage includes one of `U_n`. Then any Cauchy filter `f` generates a decreasing sequence of
sets `s_n ∈ f` such that `s_n × s_n ⊆ U_n`. Choose a sequence `x_n∈s_n`. It is easy to show
that this is a Cauchy sequence. If this sequence converges to some `a`, then `f ≤ 𝓝 a`. -/


namespace SequentiallyComplete

variable {f : Filter α} (hf : Cauchy f) {U : ℕ → SetRel α α} (U_mem : ∀ n, U n ∈ 𝓤 α)

open Set Finset

noncomputable section

/-- An auxiliary sequence of sets approximating a Cauchy filter. -/
/-
**SequentiallyComplete.setSeqAux** 是 Mathlib 中的一个定义，位于命名空间 `SequentiallyComplete
`。
形式化陈述：setSeqAux (n : Nat) : { s : Set α // s in f ∧ s ×ˢ s subseteq U n }
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary sequence of sets approximating a Cauchy filter.
-/
def setSeqAux (n : ℕ) : { s : Set α // s ∈ f ∧ s ×ˢ s ⊆ U n } :=
  Classical.indefiniteDescription _ <| (cauchy_iff.1 hf).2 (U n) (U_mem n)

/-- Given a Cauchy filter `f` and a sequence `U` of entourages, `set_seq` provides
an antitone sequence of sets `s n ∈ f` such that `s n ×ˢ s n ⊆ U`. -/
/-
**SequentiallyComplete.setSeq** 是 Mathlib 中的一个定义，位于命名空间 `SequentiallyComplete`。
形式化陈述：setSeq (n : Nat) : Set α
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Cauchy filter `f` and a sequence `U` of entourages, `set_seq` provides
an antitone sequence of sets `s n ∈ f` such that `s n ×ˢ s n ⊆ U`.
-/
def setSeq (n : ℕ) : Set α :=
  ⋂ m ∈ Set.Iic n, (setSeqAux hf U_mem m).val
/-
**SequentiallyComplete.setSeq_mem** 是 Mathlib 中的一个定理，位于命名空间 `SequentiallyComplet
e`。
形式化陈述：setSeq_mem (n : Nat) : setSeq hf U_mem n in f
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem setSeq_mem (n : ℕ) : setSeq hf U_mem n ∈ f :=
  (biInter_mem (finite_le_nat n)).2 fun m _ => (setSeqAux hf U_mem m).2.1
/-
**SequentiallyComplete.setSeq_mono** 是 Mathlib 中的一个定理，位于命名空间 `SequentiallyComple
te`。
形式化陈述：setSeq_mono ⦃m n : Nat⦄ (h : m <= n) : setSeq hf U_mem n subseteq setSeq h
f U_mem m
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biInter_subset_biInter_left`：biInter_subset_biInter_left {s s' : Set
 α} {t : α -> Set β} (h : s' subseteq s) : ⋂ x in s, t x subseteq ⋂ x in s', t x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
-/
theorem setSeq_mono ⦃m n : ℕ⦄ (h : m ≤ n) : setSeq hf U_mem n ⊆ setSeq hf U_mem m :=
  biInter_subset_biInter_left <| Iic_subset_Iic.2 h
/-
**SequentiallyComplete.setSeq_sub_aux** 是 Mathlib 中的一个定理，位于命名空间 `SequentiallyCom
plete`。
形式化陈述：setSeq_sub_aux (n : Nat) : setSeq hf U_mem n subseteq setSeqAux hf U_mem n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
-/
theorem setSeq_sub_aux (n : ℕ) : setSeq hf U_mem n ⊆ setSeqAux hf U_mem n :=
  biInter_subset_of_mem self_mem_Iic
/-
**SequentiallyComplete.setSeq_prod_subset** 是 Mathlib 中的一个定理，位于命名空间 `Sequentiall
yComplete`。
形式化陈述：setSeq_prod_subset {N m n} (hm : N <= m) (hn : N <= n) : setSeq hf U_mem m
 ×ˢ setSeq hf U_mem n subseteq U N
参数：hm : N <= m；hn : N <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SequentiallyComplete.setSeq_sub_aux`：setSeq_sub_aux (n : Nat) : setSeq h
f U_mem n subseteq setSeqAux hf U_mem n
· 使用定理 `SequentiallyComplete.setSeq_mono`：setSeq_mono ⦃m n : Nat⦄ (h : m <= n) :
 setSeq hf U_mem n subseteq setSeq hf U_mem m
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem setSeq_prod_subset {N m n} (hm : N ≤ m) (hn : N ≤ n) :
    setSeq hf U_mem m ×ˢ setSeq hf U_mem n ⊆ U N := fun p hp => by
  refine (setSeqAux hf U_mem N).2.2 ⟨?_, ?_⟩ <;> apply setSeq_sub_aux
  · exact setSeq_mono hf U_mem hm hp.1
  · exact setSeq_mono hf U_mem hn hp.2

/-- A sequence of points such that `seq n ∈ setSeq n`. Here `setSeq` is an antitone
sequence of sets `setSeq n ∈ f` with diameters controlled by a given sequence
of entourages. -/
/-
**SequentiallyComplete.seq** 是 Mathlib 中的一个定义，位于命名空间 `SequentiallyComplete`。
形式化陈述：seq (n : Nat) : α
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of points such that `seq n ∈ setSeq n`. Here `setSeq` is an antitone
sequence of sets `setSeq n ∈ f` with diameters controlled by a given sequence
of entourages.
-/
def seq (n : ℕ) : α :=
  (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose
/-
**SequentiallyComplete.seq_mem** 是 Mathlib 中的一个定理，位于命名空间 `SequentiallyComplete`。
形式化陈述：seq_mem (n : Nat) : seq hf U_mem n in setSeq hf U_mem n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Filter.NeBot.nonempty_of_mem`：∀ {α : Type u} {f : Filter α}, f.NeBot → ∀
 {s : Set α}, s ∈ f → s.Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SequentiallyComplete.setSeq_mem`：setSeq_mem (n : Nat) : setSeq hf U_mem 
n in f
-/
theorem seq_mem (n : ℕ) : seq hf U_mem n ∈ setSeq hf U_mem n :=
  (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose_spec
/-
**SequentiallyComplete.seq_pair_mem** 是 Mathlib 中的一个定理，位于命名空间 `SequentiallyCompl
ete`。
形式化陈述：seq_pair_mem ⦃N m n : Nat⦄ (hm : N <= m) (hn : N <= n) : (seq hf U_mem m, 
seq hf U_mem n) in U N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SequentiallyComplete.setSeq_prod_subset`：setSeq_prod_subset {N m n} (hm 
: N <= m) (hn : N <= n) : setSeq hf U_mem m ×ˢ setSeq hf U_mem n subseteq U N
· 使用定理 `SequentiallyComplete.seq_mem`：seq_mem (n : Nat) : seq hf U_mem n in setS
eq hf U_mem n
-/
theorem seq_pair_mem ⦃N m n : ℕ⦄ (hm : N ≤ m) (hn : N ≤ n) :
    (seq hf U_mem m, seq hf U_mem n) ∈ U N :=
  setSeq_prod_subset hf U_mem hm hn ⟨seq_mem hf U_mem m, seq_mem hf U_mem n⟩
/-
**SequentiallyComplete.seq_is_cauchySeq** 是 Mathlib 中的一个定理，位于命名空间 `SequentiallyC
omplete`。
形式化陈述：seq_is_cauchySeq (U_le : forall s in 𝓤 α, exists n, U n subseteq s) : Cauc
hySeq seq hf U_mem
参数：U_le : forall s in 𝓤 α, exists n, U n subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_of_controlled`：cauchySeq_of_controlled [SemilatticeSup β] [Non
empty β] (U : β -> SetRel α α) (hU : forall s in 𝓤 α, exists n, U n subseteq s) 
{f : β -> α} …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SequentiallyComplete.seq_pair_mem`：seq_pair_mem ⦃N m n : Nat⦄ (hm : N <=
 m) (hn : N <= n) : (seq hf U_mem m, seq hf U_mem n) in U N
-/
theorem seq_is_cauchySeq (U_le : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s) : CauchySeq <| seq hf U_mem :=
  cauchySeq_of_controlled U U_le <| seq_pair_mem hf U_mem

/-- If the sequence `SequentiallyComplete.seq` converges to `a`, then `f ≤ 𝓝 a`. -/
/-
**SequentiallyComplete.le_nhds_of_seq_tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Se
quentiallyComplete`。
形式化陈述：le_nhds_of_seq_tendsto_nhds (U_le : forall s in 𝓤 α, exists n, U n subsete
q s) ⦃a : α⦄ (ha : Tendsto (seq hf U_mem) atTop (𝓝 a)) : f <= 𝓝 a
参数：U_le : forall s in 𝓤 α, exists n, U n subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_nhds_of_cauchy_adhp_aux`：le_nhds_of_cauchy_adhp_aux {f : Filter α} {x
 : α} (adhs : forall s in 𝓤 α, exists t in f, t ×ˢ t subseteq s ∧ exists y, (x, 
y) in s ∧ y in t…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_atTop'`：tendsto_atTop' : Tendsto f atTop l ↔ forall s in 
l, exists a, forall b, a <= b -> f b in s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x
· 使用定理 `SequentiallyComplete.setSeq_mem`：setSeq_mem (n : Nat) : setSeq hf U_mem 
n in f
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `SequentiallyComplete.setSeq_prod_subset`：setSeq_prod_subset {N m n} (hm 
: N <= m) (hn : N <= n) : setSeq hf U_mem m ×ˢ setSeq hf U_mem n subseteq U N
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `SequentiallyComplete.seq_mem`：seq_mem (n : Nat) : seq hf U_mem n in setS
eq hf U_mem n

--- 原说明 ---
If the sequence `SequentiallyComplete.seq` converges to `a`, then `f ≤ 𝓝 a`.
-/
theorem le_nhds_of_seq_tendsto_nhds (U_le : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s)
    ⦃a : α⦄ (ha : Tendsto (seq hf U_mem) atTop (𝓝 a)) : f ≤ 𝓝 a :=
  le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      rcases U_le s hs with ⟨m, hm⟩
      rcases tendsto_atTop'.1 ha _ (mem_nhds_left a (U_mem m)) with ⟨n, hn⟩
      refine
        ⟨setSeq hf U_mem (max m n), setSeq_mem hf U_mem _, ?_, seq hf U_mem (max m n), ?_,
          seq_mem hf U_mem _⟩
      · have := le_max_left m n
        exact Set.Subset.trans (setSeq_prod_subset hf U_mem this this) hm
      · exact hm (hn _ <| le_max_right m n))

end

end SequentiallyComplete

namespace UniformSpace

open SequentiallyComplete

variable [IsCountablyGenerated (𝓤 α)]

/-- A uniform space is complete provided that (a) its uniformity filter has a countable basis;
(b) any sequence satisfying a "controlled" version of the Cauchy condition converges. -/
/-
**UniformSpace.complete_of_convergent_controlled_sequences** 是 Mathlib 中的一个定理，位于
命名空间 `UniformSpace`。
形式化陈述：complete_of_convergent_controlled_sequences (U : Nat -> SetRel α α) (U_mem
 : forall n, U n in 𝓤 α) (HU : forall u : Nat -> α, (forall N m n, N <= m -> N <
= n -> (u m, u n) in U N) -> exists a, Tendsto u atTop (𝓝 a)) : CompleteSpace α
参数：U : Nat -> SetRel α α；U_mem : forall n, U n in 𝓤 α；HU : forall u : Nat -> α, 
(forall N m n, N <= m -> N <= n -> (u m, u n) in U N) -> exists a, Tendsto u atT
op (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_antitone_seq`：exists_antitone_seq (f : Filter α) [f.IsCoun
tablyGenerated] : exists x : Nat -> Set α, Antitone x ∧ forall {s}, s in f ↔ exi
sts i, x i subse…
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `SequentiallyComplete.le_nhds_of_seq_tendsto_nhds`：le_nhds_of_seq_tendsto
_nhds (U_le : forall s in 𝓤 α, exists n, U n subseteq s) ⦃a : α⦄ (ha : Tendsto (
seq hf U_mem) atTop (𝓝 a)) : f <= 𝓝 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `SequentiallyComplete.seq_pair_mem`：seq_pair_mem ⦃N m n : Nat⦄ (hm : N <=
 m) (hn : N <= n) : (seq hf U_mem m, seq hf U_mem n) in U N

--- 原说明 ---
A uniform space is complete provided that (a) its uniformity filter has a counta
ble basis;
(b) any sequence satisfying a "controlled" version of the Cauchy condition conve
rges.
-/
theorem complete_of_convergent_controlled_sequences (U : ℕ → SetRel α α) (U_mem : ∀ n, U n ∈ 𝓤 α)
    (HU : ∀ u : ℕ → α, (∀ N m n, N ≤ m → N ≤ n → (u m, u n) ∈ U N) → ∃ a, Tendsto u atTop (𝓝 a)) :
    CompleteSpace α := by
  obtain ⟨U', -, hU'⟩ := (𝓤 α).exists_antitone_seq
  have Hmem : ∀ n, U n ∩ U' n ∈ 𝓤 α := fun n => inter_mem (U_mem n) (hU'.2 ⟨n, Subset.refl _⟩)
  refine ⟨fun hf => (HU (seq hf Hmem) fun N m n hm hn => ?_).imp <|
    le_nhds_of_seq_tendsto_nhds _ _ fun s hs => ?_⟩
  · exact inter_subset_left (seq_pair_mem hf Hmem hm hn)
  · rcases hU'.1 hs with ⟨N, hN⟩
    exact ⟨N, Subset.trans inter_subset_right hN⟩

/-- A sequentially complete uniform space with a countable basis of the uniformity filter is
complete. -/
/-
**UniformSpace.complete_of_cauchySeq_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `UniformS
pace`。
形式化陈述：complete_of_cauchySeq_tendsto (H' : forall u : Nat -> α, CauchySeq u -> ex
ists a, Tendsto u atTop (𝓝 a)) : CompleteSpace α
参数：H' : forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_antitone_seq`：exists_antitone_seq (f : Filter α) [f.IsCoun
tablyGenerated] : exists x : Nat -> Set α, Antitone x ∧ forall {s}, s in f ↔ exi
sts i, x i subse…
· 使用定理 `UniformSpace.complete_of_convergent_controlled_sequences`：complete_of_co
nvergent_controlled_sequences (U : Nat -> SetRel α α) (U_mem : forall n, U n in 
𝓤 α) (HU : forall u : Nat -> α, (forall N m n,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `cauchySeq_of_controlled`：cauchySeq_of_controlled [SemilatticeSup β] [Non
empty β] (U : β -> SetRel α α) (hU : forall s in 𝓤 α, exists n, U n subseteq s) 
{f : β -> α} …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
A sequentially complete uniform space with a countable basis of the uniformity f
ilter is
complete.
-/
theorem complete_of_cauchySeq_tendsto (H' : ∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) :
    CompleteSpace α :=
  let ⟨U', _, hU'⟩ := (𝓤 α).exists_antitone_seq
  complete_of_convergent_controlled_sequences U' (fun n => hU'.2 ⟨n, Subset.refl _⟩) fun u hu =>
    H' u <| cauchySeq_of_controlled U' (fun _ hs => hU'.1 hs) hu

variable (α)

-- TODO: move to `Topology.UniformSpace.Basic`
/-
**UniformSpace.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) firstCountableTopology : FirstCountableTopology α :=
  ⟨fun a => by rw [nhds_eq_comap_uniformity]; infer_instance⟩

/-- A separable uniform space with countably generated uniformity filter is second countable:
one obtains a countable basis by taking the balls centered at points in a dense subset,
and with rational "radii" from a countable open symmetric antitone basis of `𝓤 α`. -/
/-
**UniformSpace.secondCountable_of_separable** 是 Mathlib 中的一个实例，位于命名空间 `UniformSp
ace`。
形式化陈述：secondCountable_of_separable [SeparableSpace α] : SecondCountableTopology 
α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.exists_countable_dense`：exists_countable_dense [Separab
leSpace α] : exists s : Set α, s.Countable ∧ Dense s
· 使用定理 `Filter.HasBasis.exists_antitone_subbasis`：∀ {α : Type u_1} {ι' : Sort u_
5} {f : Filter α} [h : f.IsCountablyGenerated] {p : ι' → Prop} {s : ι' → Set α},
   f.HasBasis p s → ∃ x, (∀ (i…
· 使用定理 `uniformity_hasBasis_open_symmetric`：uniformity_hasBasis_open_symmetric :
 HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α ∧ IsOpen V ∧ SetRel.IsSymm V) id
· 使用定理 `Set.Countable.biUnion`：∀ {α : Type u} {β : Type v} {s : Set α} {t : (a :
 α) → a ∈ s → Set β},   s.Countable → (∀ (a : α) (ha : a ∈ s), (t a ha).Countabl
e) → (⋃ a, …
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `TopologicalSpace.IsTopologicalBasis.eq_generateFrom`：∀ {α : Type u} [t :
 TopologicalSpace α] {s : Set (Set α)},   TopologicalSpace.IsTopologicalBasis s 
→ t = TopologicalSpace.generateFrom s
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `UniformSpace.isOpen_ball`：isOpen_ball (x : α) {V : SetRel α α} (hV : IsO
pen V) : IsOpen (ball x V)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniformSpace.mem_nhds_iff`：UniformSpace.mem_nhds_iff {x : α} {s : Set α}
 : s in 𝓝 x ↔ exists V in 𝓤 α, ball x V subseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `comp_symm_of_uniformity`：comp_symm_of_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : exists t in 𝓤 α, (forall {a b}, (a, b) in t -> (b, a) in t) ∧ t ○ t 
subseteq s
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `Dense.inter_open_nonempty`：∀ {X : Type u} [inst : TopologicalSpace X] {s
 : Set X},   Dense s → ∀ (U : Set X), IsOpen U → U.Nonempty → (U ∩ s).Nonempty
· 使用引理 `UniformSpace.mem_ball_self`：mem_ball_self (x : α) {V : SetRel α α} : V i
n 𝓤 α -> x in ball x V
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
· 使用定理 `UniformSpace.ball_subset_of_comp_subset`：ball_subset_of_comp_subset {V W
 : Set (β × β)} {x y} (h : x in ball y W) (h' : W ○ W subseteq V) : ball x W sub
seteq ball y V

--- 原说明 ---
A separable uniform space with countably generated uniformity filter is second c
ountable:
one obtains a countable basis by taking the balls centered at points in a dense 
subset,
and with rational "radii" from a countable open symmetric antitone basis of `𝓤 α
`.
-/
instance secondCountable_of_separable [SeparableSpace α] : SecondCountableTopology α := by
  rcases exists_countable_dense α with ⟨s, hsc, hsd⟩
  obtain
    ⟨t : ℕ → SetRel α α, hto : ∀ i : ℕ, t i ∈ (𝓤 α).sets ∧ IsOpen (t i) ∧ (t i).IsSymm,
      h_basis : (𝓤 α).HasAntitoneBasis t⟩ :=
    (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
  choose ht_mem hto hts using hto
  refine ⟨⟨⋃ x ∈ s, range fun k => ball x (t k), hsc.biUnion fun x _ => countable_range _, ?_⟩⟩
  refine (isTopologicalBasis_of_isOpen_of_nhds ?_ ?_).eq_generateFrom
  · simp only [mem_iUnion₂, mem_range]
    rintro _ ⟨x, _, k, rfl⟩
    exact isOpen_ball x (hto k)
  · intro x V hxV hVo
    simp only [mem_iUnion₂, mem_range, exists_prop]
    rcases UniformSpace.mem_nhds_iff.1 (IsOpen.mem_nhds hVo hxV) with ⟨U, hU, hUV⟩
    rcases comp_symm_of_uniformity hU with ⟨U', hU', _, hUU'⟩
    rcases h_basis.toHasBasis.mem_iff.1 hU' with ⟨k, -, hk⟩
    rcases hsd.inter_open_nonempty (ball x <| t k) (isOpen_ball x (hto k))
        ⟨x, UniformSpace.mem_ball_self _ (ht_mem k)⟩ with
      ⟨y, hxy, hys⟩
    refine ⟨_, ⟨y, hys, k, rfl⟩, (t k).symm hxy, fun z hz => ?_⟩
    exact hUV (ball_subset_of_comp_subset (hk hxy) hUU' (hk hz))

variable {α}
/-
**UniformSpace.subset_countable_closure_of_almost_dense_set** 是 Mathlib 中的一个定理，位
于命名空间 `UniformSpace`。
形式化陈述：subset_countable_closure_of_almost_dense_set (s : Set α) (hs : forall U in
 𝓤 α, exists t : Set α, t.Countable ∧ s subseteq ⋃ x in t, ball x U) : exists t,
 t subseteq s ∧ t.Countable ∧ s subseteq closure t
参数：s : Set α；hs : forall U in 𝓤 α, exists t : Set α, t.Countable ∧ s subseteq ⋃ 
x in t, ball x U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.has_seq_basis`：UniformSpace.has_seq_basis [IsCountablyGener
ated <| 𝓤 α] : exists V : Nat -> SetRel α α, HasAntitoneBasis (𝓤 α) V ∧ forall n
, SetRel.IsSymm …
· 使用定理 `Filter.HasAntitoneBasis.mem`：∀ {α : Type u_1} {ι : Type u_4} [inst : Pre
order ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → ∀ (i : ι), s i
 ∈ l
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.mem_closure_iff_ball`：UniformSpace.mem_closure_iff_ball {s 
: Set α} {x} : x in closure s ↔ forall {V}, V in 𝓤 α -> (ball x V inter s).Nonem
pty
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasAntitoneBasis.mem_iff`：∀ {α : Type u_1} {ι : Type u_4} [inst :
 Preorder ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → ∀ {t : Set
 α}, t ∈ l ↔ ∃ i, s i…
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SetRel.comp_subset_comp`：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ 
subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂
· 使用定理 `UniformSpace.mem_ball_comp`：mem_ball_comp {V W : Set (β × β)} {x y z} (h
 : y in ball x V) (h' : z in ball y W) : z in ball x (V ○ W)
· 使用定理 `UniformSpace.mem_ball_symmetry`：mem_ball_symmetry {V : SetRel β β} [V.Is
Symm] {x y} : x in ball y V ↔ y in ball x V
· 使用定理 `Set.mem_iUnion₂_of_mem`：mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} {i : ι} (j : κ i) (ha : a in s i j) : a in ⋃ (i) (j), s i j
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem subset_countable_closure_of_almost_dense_set (s : Set α)
    (hs : ∀ U ∈ 𝓤 α, ∃ t : Set α, t.Countable ∧ s ⊆ ⋃ x ∈ t, ball x U) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ s ⊆ closure t := by
  obtain ⟨B, hB, _⟩ := has_seq_basis α
  replace hs (n : ℕ) := hs (B n) (hB.mem n)
  choose t tC ht using hs
  have := fun n => (tC n).to_subtype
  choose o hox hos using fun (n : ℕ) (x : t n) (hx : (ball x.1 (B n) ∩ s).Nonempty) => hx
  refine ⟨⋃ (n) (x), range (o n x), iUnion₂_subset fun _ _ => range_subset_iff.2 (hos _ _),
    countable_iUnion fun _ => countable_iUnion fun _ => countable_range _, fun x hx => ?_⟩
  rw [mem_closure_iff_ball]
  intro U hU
  obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
  obtain ⟨n, hn⟩ := hB.mem_iff.1 hV
  specialize ht n hx
  rw [mem_iUnion₂] at ht
  obtain ⟨y, hy, hyx⟩ := ht
  refine ⟨o n ⟨y, hy⟩ ⟨x, hyx, hx⟩, ?_, ?_⟩
  · apply ball_mono ((SetRel.comp_subset_comp hn hn).trans hVU)
    exact mem_ball_comp (mem_ball_symmetry.2 hyx) (hox n ⟨y, hy⟩ ⟨x, hyx, hx⟩)
  · exact mem_iUnion₂_of_mem ⟨y, hy⟩ (mem_range_self ⟨x, hyx, hx⟩)
/-
**UniformSpace.secondCountable_of_almost_dense_set** 是 Mathlib 中的一个定理，位于命名空间 `Un
iformSpace`。
形式化陈述：secondCountable_of_almost_dense_set (hs : forall U in 𝓤 α, exists t : Set 
α, t.Countable ∧ ⋃ x in t, ball x U = univ) : SecondCountableTopology α
参数：hs : forall U in 𝓤 α, exists t : Set α, t.Countable ∧ ⋃ x in t, ball x U = un
iv。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UniformSpace.subset_countable_closure_of_almost_dense_set`：subset_counta
ble_closure_of_almost_dense_set (s : Set α) (hs : forall U in 𝓤 α, exists t : Se
t α, t.Countable ∧ s subseteq ⋃ x in t, ball x …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem secondCountable_of_almost_dense_set
    (hs : ∀ U ∈ 𝓤 α, ∃ t : Set α, t.Countable ∧ ⋃ x ∈ t, ball x U = univ) :
    SecondCountableTopology α := by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : ∀ U ∈ 𝓤 α, ∃ t : Set α, Set.Countable t ∧ univ ⊆ ⋃ x ∈ t, ball x U := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this with ⟨t, -, htc, ht⟩
  exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩

/-- A totally bounded set is separable in countably generated uniform spaces. This can be obtained
from the more general `UniformSpace.subset_countable_closure_of_almost_dense_set`. -/
/-
**UniformSpace._root_.TotallyBounded.isSeparable** 是 Mathlib 中的一个引理，位于命名空间 `Unif
ormSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A totally bounded set is separable in countably generated uniform spaces. This c
an be obtained
from the more general `UniformSpace.subset_countable_closure_of_almost_dense_set
`.
-/
lemma _root_.TotallyBounded.isSeparable {s : Set α} (h : TotallyBounded s) :
    TopologicalSpace.IsSeparable s := by
  obtain ⟨t, -, htc, hts⟩ := subset_countable_closure_of_almost_dense_set s fun U hU => by
    obtain ⟨t, ht, hst⟩ := h (SetRel.inv U)
      (mem_of_superset (symmetrize_mem_uniformity hU) SetRel.symmetrize_subset_inv)
    exact ⟨t, ht.countable, hst⟩
  exact ⟨t, htc, hts⟩

end UniformSpace

