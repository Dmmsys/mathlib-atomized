/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Constructions

/-!
# Neighborhoods relative to a subset

This file develops API on the relative versions `nhdsWithin` and `nhdsSetWithin` of `nhds` and
`nhdsSet`, which are defined in previous definition files.

Their basic properties studied in this file include the relationship between neighborhood filters
relative to a set and neighborhood filters in the corresponding subtype, and are in later files used
to develop relative versions `ContinuousOn` and `ContinuousWithinAt` of `Continuous` and
`ContinuousAt`.

## Notation

* `𝓝 x`: the filter of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhdsWithin x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝ˢ[t] s`: the filter `nhdsSetWithin s t` of neighborhoods of a set `s` within a set `t`.

-/

public section

open Set Filter Function Topology

variable {α β γ δ : Type*} [TopologicalSpace α]

/-!
## Properties of the neighborhood-within filter
-/

@[simp]
/-
**nhds_bind_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_bind_nhdsWithin {a : α} {s : Set α} : ((𝓝 a).bind fun x => 𝓝[s] x) = 
𝓝[s] a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.bind_inf_principal`：bind_inf_principal {f : Filter α} {g : α -> F
ilter β} {s : Set β} : (f.bind fun x => g x ⊓ 𝓟 s) = f.bind g ⊓ 𝓟 s
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `nhds_bind_nhds`：nhds_bind_nhds : (𝓝 x).bind 𝓝 = 𝓝 x

--- 原说明 ---
## Properties of the neighborhood-within filter
-/
theorem nhds_bind_nhdsWithin {a : α} {s : Set α} : ((𝓝 a).bind fun x => 𝓝[s] x) = 𝓝[s] a :=
  bind_inf_principal.trans <| congr_arg₂ _ nhds_bind_nhds rfl

@[simp]
/-
**eventually_nhds_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhds_nhdsWithin {a : α} {s : Set α} {p : α -> Prop} : (forallᶠ 
y in 𝓝 a, forallᶠ x in 𝓝[s] y, p x) ↔ forallᶠ x in 𝓝[s] a, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.ext_iff`：∀ {α : Type u_1} {f g : Filter α}, f = g ↔ ∀ (s : Set α)
, s ∈ f ↔ s ∈ g
· 使用定理 `nhds_bind_nhdsWithin`：nhds_bind_nhdsWithin {a : α} {s : Set α} : ((𝓝 a).
bind fun x => 𝓝[s] x) = 𝓝[s] a
-/
theorem eventually_nhds_nhdsWithin {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝[s] y, p x) ↔ ∀ᶠ x in 𝓝[s] a, p x :=
  Filter.ext_iff.1 nhds_bind_nhdsWithin { x | p x }
/-
**eventually_nhdsWithin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhdsWithin_iff {a : α} {s : Set α} {p : α -> Prop} : (forallᶠ x
 in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
-/
theorem eventually_nhdsWithin_iff {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ x in 𝓝[s] a, p x) ↔ ∀ᶠ x in 𝓝 a, x ∈ s → p x :=
  eventually_inf_principal
/-
**frequently_nhdsWithin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frequently_nhdsWithin_iff {z : α} {s : Set α} {p : α -> Prop} : (existsᶠ x
 in 𝓝[s] z, p x) ↔ existsᶠ x in 𝓝 z, p x ∧ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.frequently_inf_principal`：frequently_inf_principal {f : Filter α}
 {s : Set α} {p : α -> Prop} : (existsᶠ x in f ⊓ 𝓟 s, p x) ↔ existsᶠ x in f, x i
n s ∧ p x
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
theorem frequently_nhdsWithin_iff {z : α} {s : Set α} {p : α → Prop} :
    (∃ᶠ x in 𝓝[s] z, p x) ↔ ∃ᶠ x in 𝓝 z, p x ∧ x ∈ s :=
  frequently_inf_principal.trans <| by simp only [and_comm]
/-
**mem_closure_ne_iff_frequently_within** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_ne_iff_frequently_within {z : α} {s : Set α} : z in closure (s
 \ {z}) ↔ existsᶠ x in 𝓝[!=] z, x in s
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closure_ne_iff_frequently_within {z : α} {s : Set α} :
    z ∈ closure (s \ {z}) ↔ ∃ᶠ x in 𝓝[≠] z, x ∈ s := by
  simp [mem_closure_iff_frequently, frequently_nhdsWithin_iff]

@[simp]
/-
**eventually_eventually_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_eventually_nhdsWithin {a : α} {s : Set α} {p : α -> Prop} : (fo
rallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝[s] y, p x) ↔ forallᶠ x in 𝓝[s] a, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhds_nhdsWithin`：eventually_nhds_nhdsWithin {a : α} {s : Set 
α} {p : α -> Prop} : (forallᶠ y in 𝓝 a, forallᶠ x in 𝓝[s] y, p x) ↔ forallᶠ x in
 𝓝[s] a, p x
-/
theorem eventually_eventually_nhdsWithin {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ y in 𝓝[s] a, ∀ᶠ x in 𝓝[s] y, p x) ↔ ∀ᶠ x in 𝓝[s] a, p x := by
  refine ⟨fun h => ?_, fun h => (eventually_nhds_nhdsWithin.2 h).filter_mono inf_le_left⟩
  simp only [eventually_nhdsWithin_iff] at h ⊢
  exact h.mono fun x hx hxs => (hx hxs).self_of_nhds hxs

@[simp]
/-
**eventually_mem_nhdsWithin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_mem_nhdsWithin_iff {x : α} {s t : Set α} : (forallᶠ x' in 𝓝[s] 
x, t in 𝓝[s] x') ↔ t in 𝓝[s] x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_eventually_nhdsWithin`：eventually_eventually_nhdsWithin {a : 
α} {s : Set α} {p : α -> Prop} : (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝[s] y, p x)
 ↔ forallᶠ x in 𝓝[s] a…
-/
theorem eventually_mem_nhdsWithin_iff {x : α} {s t : Set α} :
    (∀ᶠ x' in 𝓝[s] x, t ∈ 𝓝[s] x') ↔ t ∈ 𝓝[s] x :=
  eventually_eventually_nhdsWithin
/-
**nhdsWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_eq (a : α) (s : Set α) : 𝓝[s] a = ⨅ t in { t : Set α | a in t ∧
 IsOpen t }, 𝓟 (t inter s)
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
-/
theorem nhdsWithin_eq (a : α) (s : Set α) :
    𝓝[s] a = ⨅ t ∈ { t : Set α | a ∈ t ∧ IsOpen t }, 𝓟 (t ∩ s) :=
  ((nhds_basis_opens a).inf_principal s).eq_biInf
/-
**nhdsWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), nhdsWithin a Set.uni
v = nhds a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
-/
@[simp] lemma nhdsWithin_univ (a : α) : 𝓝[Set.univ] a = 𝓝 a := by
  rw [nhdsWithin, principal_univ, inf_top_eq]
/-
**nhdsWithin_hasBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s : ι -> Set α} {a : α} (
h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p fun i => s i inter t
参数：h : (𝓝 a).HasBasis p s；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
-/
theorem nhdsWithin_hasBasis {ι : Sort*} {p : ι → Prop} {s : ι → Set α} {a : α}
    (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p fun i => s i ∩ t :=
  h.inf_principal t
/-
**nhdsWithin_basis_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_basis_open (a : α) (t : Set α) : (𝓝[t] a).HasBasis (fun u => a 
in u ∧ IsOpen u) fun u => u inter t
参数：a : α；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
-/
theorem nhdsWithin_basis_open (a : α) (t : Set α) :
    (𝓝[t] a).HasBasis (fun u => a ∈ u ∧ IsOpen u) fun u => u ∩ t :=
  nhdsWithin_hasBasis (nhds_basis_opens a) t
/-
**mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u, I
sOpen u ∧ a in u ∧ u inter s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhdsWithin_basis_open`：nhdsWithin_basis_open (a : α) (t : Set α) : (𝓝[t]
 a).HasBasis (fun u => a in u ∧ IsOpen u) fun u => u inter t
-/
theorem mem_nhdsWithin {t : Set α} {a : α} {s : Set α} :
    t ∈ 𝓝[s] a ↔ ∃ u, IsOpen u ∧ a ∈ u ∧ u ∩ s ⊆ t := by
  simpa only [and_assoc, and_left_comm] using (nhdsWithin_basis_open a s).mem_iff
/-
**mem_nhdsWithin_iff_exists_mem_nhds_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsWithin_iff_exists_mem_nhds_inter {t : Set α} {a : α} {s : Set α} :
 t in 𝓝[s] a ↔ exists u in 𝓝 a, u inter s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem mem_nhdsWithin_iff_exists_mem_nhds_inter {t : Set α} {a : α} {s : Set α} :
    t ∈ 𝓝[s] a ↔ ∃ u ∈ 𝓝 a, u ∩ s ⊆ t :=
  (nhdsWithin_hasBasis (𝓝 a).basis_sets s).mem_iff
/-
**sdiff_mem_nhdsWithin_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_mem_nhdsWithin_compl {x : α} {s : Set α} (hs : s in 𝓝 x) (t : Set α)
 : s \ t in 𝓝[tᶜ] x
参数：hs : s in 𝓝 x；t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.sdiff_mem_inf_principal_compl`：sdiff_mem_inf_principal_compl {f :
 Filter α} {s : Set α} (hs : s in f) (t : Set α) : s \ t in f ⊓ 𝓟 tᶜ
-/
theorem sdiff_mem_nhdsWithin_compl {x : α} {s : Set α} (hs : s ∈ 𝓝 x) (t : Set α) :
    s \ t ∈ 𝓝[tᶜ] x :=
  sdiff_mem_inf_principal_compl hs t

@[deprecated (since := "2026-06-03")] alias diff_mem_nhdsWithin_compl := sdiff_mem_nhdsWithin_compl
/-
**sdiff_mem_nhdsWithin_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_mem_nhdsWithin_sdiff {x : α} {s t : Set α} (hs : s in 𝓝[t] x) (t' : 
Set α) : s \ t' in 𝓝[t \ t'] x
参数：hs : s in 𝓝[t] x；t' : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Filter.inter_mem_inf`：inter_mem_inf {α : Type u} {f g : Filter α} {s t :
 Set α} (hs : s in f) (ht : t in g) : s inter t in f ⊓ g
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
-/
theorem sdiff_mem_nhdsWithin_sdiff {x : α} {s t : Set α} (hs : s ∈ 𝓝[t] x) (t' : Set α) :
    s \ t' ∈ 𝓝[t \ t'] x := by
  rw [nhdsWithin, sdiff_eq, sdiff_eq, ← inf_principal, ← inf_assoc]
  exact inter_mem_inf hs (mem_principal_self _)

@[deprecated (since := "2026-06-03")] alias diff_mem_nhdsWithin_diff := sdiff_mem_nhdsWithin_sdiff
/-
**nhds_of_nhdsWithin_of_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_of_nhdsWithin_of_nhds {s t : Set α} {a : α} (h1 : s in 𝓝 a) (h2 : t i
n 𝓝[s] a) : t in 𝓝 a
参数：h1 : s in 𝓝 a；h2 : t in 𝓝[s] a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
· 使用定理 `Filter.inter_sets`：∀ {α : Type u_1} (self : Filter α) {x y : Set α}, x ∈
 self.sets → y ∈ self.sets → x ∩ y ∈ self.sets
-/
theorem nhds_of_nhdsWithin_of_nhds {s t : Set α} {a : α} (h1 : s ∈ 𝓝 a) (h2 : t ∈ 𝓝[s] a) :
    t ∈ 𝓝 a := by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h2 with ⟨_, Hw, hw⟩
  exact (𝓝 a).sets_of_superset ((𝓝 a).inter_sets Hw h1) hw
/-
**mem_nhdsWithin_iff_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsWithin_iff_eventually {s t : Set α} {x : α} : t in 𝓝[s] x ↔ forall
ᶠ y in 𝓝 x, y in s -> y in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
-/
theorem mem_nhdsWithin_iff_eventually {s t : Set α} {x : α} :
    t ∈ 𝓝[s] x ↔ ∀ᶠ y in 𝓝 x, y ∈ s → y ∈ t :=
  eventually_inf_principal
/-
**mem_nhdsWithin_iff_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsWithin_iff_eventuallyEq {s t : Set α} {x : α} : t in 𝓝[s] x ↔ s =ᶠ
[𝓝 x] (s inter t : Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhdsWithin_iff_eventuallyEq {s t : Set α} {x : α} :
    t ∈ 𝓝[s] x ↔ s =ᶠ[𝓝 x] (s ∩ t : Set α) := by
  simp_rw [mem_nhdsWithin_iff_eventually, eventuallyEq_set, mem_inter_iff, iff_self_and]

set_option backward.isDefEq.respectTransparency false in
/-
**mem_nhdsWithin_inter_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nhdsWithin_inter_self {s t : Set α} {x : α} : t in 𝓝[s inter t] x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsWithin_iff_eventuallyEq`：mem_nhdsWithin_iff_eventuallyEq {s t : 
Set α} {x : α} : t in 𝓝[s] x ↔ s =ᶠ[𝓝 x] (s inter t : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
lemma mem_nhdsWithin_inter_self {s t : Set α} {x : α} : t ∈ 𝓝[s ∩ t] x :=
  mem_nhdsWithin_iff_eventuallyEq.mpr <| by simp [inter_assoc]

set_option backward.isDefEq.respectTransparency false in
/-
**mem_nhdsWithin_self_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nhdsWithin_self_inter {s t : Set α} {x : α} : s in 𝓝[s inter t] x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsWithin_iff_eventuallyEq`：mem_nhdsWithin_iff_eventuallyEq {s t : 
Set α} {x : α} : t in 𝓝[s] x ↔ s =ᶠ[𝓝 x] (s inter t : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
lemma mem_nhdsWithin_self_inter {s t : Set α} {x : α} : s ∈ 𝓝[s ∩ t] x :=
  mem_nhdsWithin_iff_eventuallyEq.mpr <| by simp [inter_comm s t, inter_assoc]
/-
**nhdsWithin_eq_iff_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_eq_iff_eventuallyEq {s t : Set α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s
 =ᶠ[𝓝 x] t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.set_eventuallyEq_iff_inf_principal`：set_eventuallyEq_iff_inf_prin
cipal {s t : Set α} {l : Filter α} : s =ᶠ[l] t ↔ l ⊓ 𝓟 s = l ⊓ 𝓟 t
-/
theorem nhdsWithin_eq_iff_eventuallyEq {s t : Set α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t :=
  set_eventuallyEq_iff_inf_principal.symm
/-
**nhdsWithin_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝[t] x ↔ t in 𝓝[s] x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.set_eventuallyLE_iff_inf_principal_le`：set_eventuallyLE_iff_inf_p
rincipal_le {s t : Set α} {l : Filter α} : s <=ᶠ[l] t ↔ l ⊓ 𝓟 s <= l ⊓ 𝓟 t
· 使用定理 `Filter.set_eventuallyLE_iff_mem_inf_principal`：set_eventuallyLE_iff_mem_
inf_principal {s t : Set α} {l : Filter α} : s <=ᶠ[l] t ↔ t in l ⊓ 𝓟 s
-/
theorem nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x ≤ 𝓝[t] x ↔ t ∈ 𝓝[s] x :=
  set_eventuallyLE_iff_inf_principal_le.symm.trans set_eventuallyLE_iff_mem_inf_principal
/-
**preimage_nhdsWithin_coinduced'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_nhdsWithin_coinduced' {X : α -> β} {s : Set β} {t : Set α} {a : α
} (h : a in t) (hs : s in @nhds β (.coinduced (fun x : t => X x) inferInstance) 
(X a)) : X ⁻¹' s in 𝓝[t] a
参数：h : a in t；hs : s in @nhds β (.coinduced (fun x : t => X x) inferInstance) (X
 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `preimage_nhds_coinduced`：preimage_nhds_coinduced [TopologicalSpace α] {π
 : α -> β} {s : Set β} {a : α} (hs : s in @nhds β (TopologicalSpace.coinduced π 
‹_›) (π a)) :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_nhds_subtype_val`：map_nhds_subtype_val {s : Set X} (x : s) : map ((↑
) : s -> X) (𝓝 x) = 𝓝[s] ↑x
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
-/
theorem preimage_nhdsWithin_coinduced' {X : α → β} {s : Set β} {t : Set α} {a : α} (h : a ∈ t)
    (hs : s ∈ @nhds β (.coinduced (fun x : t => X x) inferInstance) (X a)) :
    X ⁻¹' s ∈ 𝓝[t] a := by
  lift a to t using h
  replace hs : (fun x : t => X x) ⁻¹' s ∈ 𝓝 a := preimage_nhds_coinduced hs
  rwa [← map_nhds_subtype_val, mem_map]
/-
**mem_nhdsWithin_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a : α} (h : s in 𝓝 a) : s in 𝓝[t
] a
参数：h : s in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_inf_of_left`：mem_inf_of_left {f g : Filter α} {s : Set α} (h 
: s in f) : s in f ⊓ g
-/
theorem mem_nhdsWithin_of_mem_nhds {s t : Set α} {a : α} (h : s ∈ 𝓝 a) : s ∈ 𝓝[t] a :=
  mem_inf_of_left h
/-
**self_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s] a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
-/
theorem self_mem_nhdsWithin {a : α} {s : Set α} : s ∈ 𝓝[s] a :=
  mem_inf_of_right (mem_principal_self s)
/-
**eventually_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_mem_nhdsWithin {a : α} {s : Set α} : forallᶠ x in 𝓝[s] a, x in 
s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem eventually_mem_nhdsWithin {a : α} {s : Set α} : ∀ᶠ x in 𝓝[s] a, x ∈ s :=
  self_mem_nhdsWithin
/-
**inter_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : α} (h : t in 𝓝 a) : s in
ter t in 𝓝[s] a
参数：s : Set α；h : t in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.mem_inf_of_left`：mem_inf_of_left {f g : Filter α} {s : Set α} (h 
: s in f) : s in f ⊓ g
-/
theorem inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : α} (h : t ∈ 𝓝 a) : s ∩ t ∈ 𝓝[s] a :=
  inter_mem self_mem_nhdsWithin (mem_inf_of_left h)
/-
**pure_le_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s) : pure a <= 𝓝[s] a
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem pure_le_nhdsWithin {a : α} {s : Set α} (ha : a ∈ s) : pure a ≤ 𝓝[s] a :=
  le_inf (pure_le_nhds a) (le_principal_iff.2 ha)
/-
**mem_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha : a in s) (ht : t in 𝓝[s] 
a) : a in t
参数：ha : a in s；ht : t in 𝓝[s] a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
-/
theorem mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha : a ∈ s) (ht : t ∈ 𝓝[s] a) : a ∈ t :=
  pure_le_nhdsWithin ha ht
/-
**Filter.Eventually.self_of_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.self_of_nhdsWithin {p : α -> Prop} {s : Set α} {x : α} (
h : forallᶠ y in 𝓝[s] x, p y) (hx : x in s) : p x
参数：h : forallᶠ y in 𝓝[s] x, p y；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
-/
theorem Filter.Eventually.self_of_nhdsWithin {p : α → Prop} {s : Set α} {x : α}
    (h : ∀ᶠ y in 𝓝[s] x, p y) (hx : x ∈ s) : p x :=
  mem_of_mem_nhdsWithin hx h
/-
**tendsto_const_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_nhdsWithin {l : Filter β} {s : Set α} {a : α} (ha : a in s) 
: Tendsto (fun _ : β => a) l (𝓝[s] a)
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.tendsto_const_pure`：tendsto_const_pure {a : Filter α} {b : β} : T
endsto (fun _ => b) a (pure b)
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
-/
theorem tendsto_const_nhdsWithin {l : Filter β} {s : Set α} {a : α} (ha : a ∈ s) :
    Tendsto (fun _ : β => a) l (𝓝[s] a) :=
  tendsto_const_pure.mono_right <| pure_le_nhdsWithin ha
/-
**nhdsWithin_restrict''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_restrict'' {a : α} (s : Set α) {t : Set α} (h : t in 𝓝[s] a) : 
𝓝[s] a = 𝓝[s inter t] a
参数：s : Set α；h : t in 𝓝[s] a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem nhdsWithin_restrict'' {a : α} (s : Set α) {t : Set α} (h : t ∈ 𝓝[s] a) :
    𝓝[s] a = 𝓝[s ∩ t] a :=
  le_antisymm (le_inf inf_le_left (le_principal_iff.mpr (inter_mem self_mem_nhdsWithin h)))
    (inf_le_inf_left _ (principal_mono.mpr Set.inter_subset_left))
/-
**nhdsWithin_restrict'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_restrict' {a : α} (s : Set α) {t : Set α} (h : t in 𝓝 a) : 𝓝[s]
 a = 𝓝[s inter t] a
参数：s : Set α；h : t in 𝓝 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_restrict''`：nhdsWithin_restrict'' {a : α} (s : Set α) {t : Se
t α} (h : t in 𝓝[s] a) : 𝓝[s] a = 𝓝[s inter t] a
· 使用定理 `Filter.mem_inf_of_left`：mem_inf_of_left {f g : Filter α} {s : Set α} (h 
: s in f) : s in f ⊓ g
-/
theorem nhdsWithin_restrict' {a : α} (s : Set α) {t : Set α} (h : t ∈ 𝓝 a) : 𝓝[s] a = 𝓝[s ∩ t] a :=
  nhdsWithin_restrict'' s <| mem_inf_of_left h
/-
**nhdsWithin_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_restrict {a : α} (s : Set α) {t : Set α} (h₀ : a in t) (h₁ : Is
Open t) : 𝓝[s] a = 𝓝[s inter t] a
参数：s : Set α；h₀ : a in t；h₁ : IsOpen t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_restrict'`：nhdsWithin_restrict' {a : α} (s : Set α) {t : Set 
α} (h : t in 𝓝 a) : 𝓝[s] a = 𝓝[s inter t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem nhdsWithin_restrict {a : α} (s : Set α) {t : Set α} (h₀ : a ∈ t) (h₁ : IsOpen t) :
    𝓝[s] a = 𝓝[s ∩ t] a :=
  nhdsWithin_restrict' s (IsOpen.mem_nhds h₁ h₀)
/-
**nhdsWithin_le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s in 𝓝[t] a) : 𝓝[t] a <= 𝓝
[s] a
参数：h : s in 𝓝[t] a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_le_iff`：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝
[t] x ↔ t in 𝓝[s] x
-/
theorem nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s ∈ 𝓝[t] a) : 𝓝[t] a ≤ 𝓝[s] a :=
  nhdsWithin_le_iff.mpr h
/-
**nhdsWithin_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝 a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `nhdsWithin_le_of_mem`：nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s 
in 𝓝[t] a) : 𝓝[t] a <= 𝓝[s] a
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a ≤ 𝓝 a := by
  rw [← nhdsWithin_univ]
  apply nhdsWithin_le_of_mem
  exact univ_mem
/-
**nhdsWithin_eq_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_eq_nhdsWithin' {a : α} {s t u : Set α} (hs : s in 𝓝 a) (h₂ : t 
inter s = u inter s) : 𝓝[t] a = 𝓝[u] a
参数：hs : s in 𝓝 a；h₂ : t inter s = u inter s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_restrict'`：nhdsWithin_restrict' {a : α} (s : Set α) {t : Set 
α} (h : t in 𝓝 a) : 𝓝[s] a = 𝓝[s inter t] a
-/
theorem nhdsWithin_eq_nhdsWithin' {a : α} {s t u : Set α} (hs : s ∈ 𝓝 a) (h₂ : t ∩ s = u ∩ s) :
    𝓝[t] a = 𝓝[u] a := by rw [nhdsWithin_restrict' t hs, nhdsWithin_restrict' u hs, h₂]
/-
**nhdsWithin_eq_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_eq_nhdsWithin {a : α} {s t u : Set α} (h₀ : a in s) (h₁ : IsOpe
n s) (h₂ : t inter s = u inter s) : 𝓝[t] a = 𝓝[u] a
参数：h₀ : a in s；h₁ : IsOpen s；h₂ : t inter s = u inter s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_restrict`：nhdsWithin_restrict {a : α} (s : Set α) {t : Set α}
 (h₀ : a in t) (h₁ : IsOpen t) : 𝓝[s] a = 𝓝[s inter t] a
-/
theorem nhdsWithin_eq_nhdsWithin {a : α} {s t u : Set α} (h₀ : a ∈ s) (h₁ : IsOpen s)
    (h₂ : t ∩ s = u ∩ s) : 𝓝[t] a = 𝓝[u] a := by
  rw [nhdsWithin_restrict t h₀ h₁, nhdsWithin_restrict u h₀ h₁, h₂]
/-
**nhdsWithin_eq_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {a : α} {s : Set α}, nhdsWith
in a s = nhds a ↔ s ∈ nhds a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
@[simp] theorem nhdsWithin_eq_nhds {a : α} {s : Set α} : 𝓝[s] a = 𝓝 a ↔ s ∈ 𝓝 a :=
  inf_eq_left.trans le_principal_iff
/-
**IsOpen.nhdsWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOpen s) (ha : a in s) : 𝓝[
s] a = 𝓝 a
参数：h : IsOpen s；ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_eq_nhds`：∀ {α : Type u_1} [inst : TopologicalSpace α] {a : α}
 {s : Set α}, nhdsWithin a s = nhds a ↔ s ∈ nhds a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOpen s) (ha : a ∈ s) : 𝓝[s] a = 𝓝 a :=
  nhdsWithin_eq_nhds.2 <| h.mem_nhds ha
/-
**preimage_nhds_within_coinduced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_nhds_within_coinduced {X : α -> β} {s : Set β} {t : Set α} {a : α
} (h : a in t) (ht : IsOpen t) (hs : s in @nhds β (.coinduced (fun x : t => X x)
 inferInstance) (X a)) : X ⁻¹' s in 𝓝 a
参数：h : a in t；ht : IsOpen t；hs : s in @nhds β (.coinduced (fun x : t => X x) inf
erInstance) (X a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用定理 `preimage_nhdsWithin_coinduced'`：preimage_nhdsWithin_coinduced' {X : α ->
 β} {s : Set β} {t : Set α} {a : α} (h : a in t) (hs : s in @nhds β (.coinduced 
(fun x : t => X x) i…
-/
theorem preimage_nhds_within_coinduced {X : α → β} {s : Set β} {t : Set α} {a : α} (h : a ∈ t)
    (ht : IsOpen t)
    (hs : s ∈ @nhds β (.coinduced (fun x : t => X x) inferInstance) (X a)) :
    X ⁻¹' s ∈ 𝓝 a := by
  rw [← ht.nhdsWithin_eq h]
  exact preimage_nhdsWithin_coinduced' h hs

@[simp]
/-
**nhdsWithin_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
-/
theorem nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥ := by rw [nhdsWithin, principal_empty, inf_bot_eq]
/-
**nhdsWithin_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] a = 𝓝[s] a ⊔ 𝓝[t] a
参数：a : α；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `Filter.sup_principal`：sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s uni
on t)
-/
theorem nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s ∪ t] a = 𝓝[s] a ⊔ 𝓝[t] a := by
  delta nhdsWithin
  rw [← inf_sup_left, sup_principal]
/-
**nhds_eq_nhdsWithin_sup_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_eq_nhdsWithin_sup_nhdsWithin (b : α) {I₁ I₂ : Set α} (hI : Set.univ =
 I₁ union I₂) : nhds b = nhdsWithin b I₁ ⊔ nhdsWithin b I₂
参数：b : α；hI : Set.univ = I₁ union I₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
-/
theorem nhds_eq_nhdsWithin_sup_nhdsWithin (b : α) {I₁ I₂ : Set α} (hI : Set.univ = I₁ ∪ I₂) :
    nhds b = nhdsWithin b I₁ ⊔ nhdsWithin b I₂ := by
  rw [← nhdsWithin_univ b, hI, nhdsWithin_union]
/-
**inter_mem_nhdsWithin_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inter_mem_nhdsWithin_inter {a b c d : Set α} {x : α} (h : a in 𝓝[b] x) (h'
 : c in 𝓝[d] x) : a inter c in 𝓝[b inter d] x
参数：h : a in 𝓝[b] x；h' : c in 𝓝[d] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma inter_mem_nhdsWithin_inter {a b c d : Set α} {x : α} (h : a ∈ 𝓝[b] x) (h' : c ∈ 𝓝[d] x) :
    a ∩ c ∈ 𝓝[b ∩ d] x :=
  inter_mem (nhdsWithin_mono _ inter_subset_left h) (nhdsWithin_mono _ inter_subset_right h')

/-- If `L` and `R` are neighborhoods of `b` within sets whose union is `Set.univ`, then
`L ∪ R` is a neighborhood of `b`. -/
/-
**union_mem_nhds_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：union_mem_nhds_of_mem_nhdsWithin {b : α} {I₁ I₂ : Set α} (h : Set.univ = I
₁ union I₂) {L : Set α} (hL : L in nhdsWithin b I₁) {R : Set α} (hR : R in nhdsW
ithin b I₂) : L union R in nhds b
参数：h : Set.univ = I₁ union I₂；hL : L in nhdsWithin b I₁；hR : R in nhdsWithin b I
₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If `L` and `R` are neighborhoods of `b` within sets whose union is `Set.univ`, t
hen
`L ∪ R` is a neighborhood of `b`.
-/
theorem union_mem_nhds_of_mem_nhdsWithin {b : α}
    {I₁ I₂ : Set α} (h : Set.univ = I₁ ∪ I₂)
    {L : Set α} (hL : L ∈ nhdsWithin b I₁)
    {R : Set α} (hR : R ∈ nhdsWithin b I₂) : L ∪ R ∈ nhds b := by
  rw [← nhdsWithin_univ b, h, nhdsWithin_union]
  exact ⟨mem_of_superset hL (by simp), mem_of_superset hR (by simp)⟩


/-- Writing a punctured neighborhood filter as a sup of left and right filters. -/
/-
**punctured_nhds_eq_nhdsWithin_sup_nhdsWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：punctured_nhds_eq_nhdsWithin_sup_nhdsWithin [LinearOrder α] {x : α} : 𝓝[!=
] x = 𝓝[<] x ⊔ 𝓝[>] x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_Ioi`：Iio_union_Ioi : Iio a union Ioi a = {a}ᶜ
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a

--- 原说明 ---
Writing a punctured neighborhood filter as a sup of left and right filters.
-/
lemma punctured_nhds_eq_nhdsWithin_sup_nhdsWithin [LinearOrder α] {x : α} :
    𝓝[≠] x = 𝓝[<] x ⊔ 𝓝[>] x := by
  rw [← Iio_union_Ioi, nhdsWithin_union]


/-- Obtain a "predictably-sided" neighborhood of `b` from two one-sided neighborhoods. -/
/-
**nhds_of_Ici_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_of_Ici_Iic [LinearOrder α] {b : α} {L : Set α} (hL : L in 𝓝[<=] b) {R
 : Set α} (hR : R in 𝓝[>=] b) : L inter Iic b union R inter Ici b in 𝓝 b
参数：hL : L in 𝓝[<=] b；hR : R in 𝓝[>=] b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `union_mem_nhds_of_mem_nhdsWithin`：union_mem_nhds_of_mem_nhdsWithin {b : 
α} {I₁ I₂ : Set α} (h : Set.univ = I₁ union I₂) {L : Set α} (hL : L in nhdsWithi
n b I₁) {R : Set α} (h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iic_union_Ici`：Iic_union_Ici : Iic a union Ici a = univ
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a

--- 原说明 ---
Obtain a "predictably-sided" neighborhood of `b` from two one-sided neighborhood
s.
-/
theorem nhds_of_Ici_Iic [LinearOrder α] {b : α}
    {L : Set α} (hL : L ∈ 𝓝[≤] b)
    {R : Set α} (hR : R ∈ 𝓝[≥] b) : L ∩ Iic b ∪ R ∩ Ici b ∈ 𝓝 b :=
  union_mem_nhds_of_mem_nhdsWithin Iic_union_Ici.symm
    (inter_mem hL self_mem_nhdsWithin) (inter_mem hR self_mem_nhdsWithin)
/-
**nhdsWithin_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_biUnion {ι} {I : Set ι} (hI : I.Finite) (s : ι -> Set α) (a : α
) : 𝓝[⋃ i in I, s i] a = ⨆ i in I, 𝓝[s i] a
参数：hI : I.Finite；s : ι -> Set α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.biUnion_insert`：biUnion_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `iSup_insert`：iSup_insert {f : β -> α} {s : Set β} {b : β} : ⨆ x in inser
t b s, f x = f b ⊔ ⨆ x in s, f x
-/
theorem nhdsWithin_biUnion {ι} {I : Set ι} (hI : I.Finite) (s : ι → Set α) (a : α) :
    𝓝[⋃ i ∈ I, s i] a = ⨆ i ∈ I, 𝓝[s i] a := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hT => simp only [hT, nhdsWithin_union, iSup_insert, biUnion_insert]
/-
**nhdsWithin_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_sUnion {S : Set (Set α)} (hS : S.Finite) (a : α) : 𝓝[⋃₀ S] a = 
⨆ s in S, 𝓝[s] a
参数：Set α；hS : S.Finite；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `nhdsWithin_biUnion`：nhdsWithin_biUnion {ι} {I : Set ι} (hI : I.Finite) (
s : ι -> Set α) (a : α) : 𝓝[⋃ i in I, s i] a = ⨆ i in I, 𝓝[s i] a
-/
theorem nhdsWithin_sUnion {S : Set (Set α)} (hS : S.Finite) (a : α) :
    𝓝[⋃₀ S] a = ⨆ s ∈ S, 𝓝[s] a := by
  rw [sUnion_eq_biUnion, nhdsWithin_biUnion hS]
/-
**nhdsWithin_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_iUnion {ι} [Finite ι] (s : ι -> Set α) (a : α) : 𝓝[⋃ i, s i] a 
= ⨆ i, 𝓝[s i] a
参数：s : ι -> Set α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `nhdsWithin_sUnion`：nhdsWithin_sUnion {S : Set (Set α)} (hS : S.Finite) (
a : α) : 𝓝[⋃₀ S] a = ⨆ s in S, 𝓝[s] a
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
theorem nhdsWithin_iUnion {ι} [Finite ι] (s : ι → Set α) (a : α) :
    𝓝[⋃ i, s i] a = ⨆ i, 𝓝[s i] a := by
  rw [← sUnion_range, nhdsWithin_sUnion (finite_range s), iSup_range]
/-
**nhdsWithin_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_inter (a : α) (s t : Set α) : 𝓝[s inter t] a = 𝓝[s] a ⊓ 𝓝[t] a
参数：a : α；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_left_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓
 (b ⊓ c) = b ⊓ (a ⊓ c)
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
theorem nhdsWithin_inter (a : α) (s t : Set α) : 𝓝[s ∩ t] a = 𝓝[s] a ⊓ 𝓝[t] a := by
  delta nhdsWithin
  rw [inf_left_comm, inf_assoc, inf_principal, ← inf_assoc, inf_idem]
/-
**nhdsWithin_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_inter' (a : α) (s t : Set α) : 𝓝[s inter t] a = 𝓝[s] a ⊓ 𝓟 t
参数：a : α；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
-/
theorem nhdsWithin_inter' (a : α) (s t : Set α) : 𝓝[s ∩ t] a = 𝓝[s] a ⊓ 𝓟 t := by
  delta nhdsWithin
  rw [← inf_principal, inf_assoc]
/-
**nhdsWithin_inter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (h : s in 𝓝[t] a) : 𝓝[s inte
r t] a = 𝓝[t] a
参数：h : s in 𝓝[t] a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_inter`：nhdsWithin_inter (a : α) (s t : Set α) : 𝓝[s inter t] 
a = 𝓝[s] a ⊓ 𝓝[t] a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `nhdsWithin_le_of_mem`：nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s 
in 𝓝[t] a) : 𝓝[t] a <= 𝓝[s] a
-/
theorem nhdsWithin_inter_of_mem {a : α} {s t : Set α} (h : s ∈ 𝓝[t] a) : 𝓝[s ∩ t] a = 𝓝[t] a := by
  rw [nhdsWithin_inter, inf_eq_right]
  exact nhdsWithin_le_of_mem h
/-
**nhdsWithin_inter_of_mem'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_inter_of_mem' {a : α} {s t : Set α} (h : t in 𝓝[s] a) : 𝓝[s int
er t] a = 𝓝[s] a
参数：h : t in 𝓝[s] a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
-/
theorem nhdsWithin_inter_of_mem' {a : α} {s t : Set α} (h : t ∈ 𝓝[s] a) : 𝓝[s ∩ t] a = 𝓝[s] a := by
  rw [inter_comm, nhdsWithin_inter_of_mem h]

@[simp]
/-
**nhdsWithin_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a := by
  rw [nhdsWithin, principal_singleton, inf_eq_right.2 (pure_le_nhds a)]

@[simp]
/-
**nhdsWithin_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s] a = pure a ⊔ 𝓝[s] a
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `nhdsWithin_singleton`：nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a
-/
theorem nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s] a = pure a ⊔ 𝓝[s] a := by
  rw [← singleton_union, nhdsWithin_union, nhdsWithin_singleton]
/-
**mem_nhdsWithin_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsWithin_insert {a : α} {s t : Set α} : t in 𝓝[insert a s] a ↔ a in 
t ∧ t in 𝓝[s] a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_insert`：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s]
 a = pure a ⊔ 𝓝[s] a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhdsWithin_insert {a : α} {s t : Set α} : t ∈ 𝓝[insert a s] a ↔ a ∈ t ∧ t ∈ 𝓝[s] a := by
  simp
/-
**insert_mem_nhdsWithin_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：insert_mem_nhdsWithin_insert {a : α} {s t : Set α} (h : t in 𝓝[s] a) : ins
ert a t in 𝓝[insert a s] a
参数：h : t in 𝓝[s] a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_insert`：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s]
 a = pure a ⊔ 𝓝[s] a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem insert_mem_nhdsWithin_insert {a : α} {s t : Set α} (h : t ∈ 𝓝[s] a) :
    insert a t ∈ 𝓝[insert a s] a := by simp [mem_of_superset h]
/-
**insert_mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：insert_mem_nhds_iff {a : α} {s : Set α} : insert a s in 𝓝 a ↔ s in 𝓝[!=] a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem insert_mem_nhds_iff {a : α} {s : Set α} : insert a s ∈ 𝓝 a ↔ s ∈ 𝓝[≠] a := by
  simp only [nhdsWithin, mem_inf_principal, mem_compl_iff, mem_singleton_iff, or_iff_not_imp_left,
    insert_def]

@[simp]
/-
**nhdsNE_sup_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsNE_sup_pure (a : α) : 𝓝[!=] a ⊔ pure a = 𝓝 a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_singleton`：nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
-/
theorem nhdsNE_sup_pure (a : α) : 𝓝[≠] a ⊔ pure a = 𝓝 a := by
  rw [← nhdsWithin_singleton, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ]

@[simp]
/-
**pure_sup_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pure_sup_nhdsNE (a : α) : pure a ⊔ 𝓝[!=] a = 𝓝 a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `nhdsNE_sup_pure`：nhdsNE_sup_pure (a : α) : 𝓝[!=] a ⊔ pure a = 𝓝 a
-/
theorem pure_sup_nhdsNE (a : α) : pure a ⊔ 𝓝[≠] a = 𝓝 a := by rw [← sup_comm, nhdsNE_sup_pure]
/-
**continuousAt_iff_punctured_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuousAt_iff_punctured_nhds [TopologicalSpace β] {f : α -> β} {a : α} 
: ContinuousAt f a ↔ Tendsto f (𝓝[!=] a) (𝓝 (f a))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pure_sup_nhdsNE`：pure_sup_nhdsNE (a : α) : pure a ⊔ 𝓝[!=] a = 𝓝 a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma continuousAt_iff_punctured_nhds [TopologicalSpace β] {f : α → β} {a : α} :
    ContinuousAt f a ↔ Tendsto f (𝓝[≠] a) (𝓝 (f a)) := by
  simp [ContinuousAt, -pure_sup_nhdsNE, ← pure_sup_nhdsNE a, tendsto_pure_nhds]
/-
**nhdsWithin_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_prod [TopologicalSpace β] {s u : Set α} {t v : Set β} {a : α} {
b : β} (hu : u in 𝓝[s] a) (hv : v in 𝓝[t] b) : u ×ˢ v in 𝓝[s ×ˢ t] (a, b)
参数：hu : u in 𝓝[s] a；hv : v in 𝓝[t] b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_prod_eq`：nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : 
Set Y) : 𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
-/
theorem nhdsWithin_prod [TopologicalSpace β]
    {s u : Set α} {t v : Set β} {a : α} {b : β} (hu : u ∈ 𝓝[s] a) (hv : v ∈ 𝓝[t] b) :
    u ×ˢ v ∈ 𝓝[s ×ˢ t] (a, b) := by
  rw [nhdsWithin_prod_eq]
  exact prod_mem_prod hu hv
/-
**Filter.EventuallyEq.mem_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.mem_interior {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t)
 (h : x in interior s) : x in interior t
参数：hst : s =ᶠ[𝓝 x] t；h : x in interior s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
-/
lemma Filter.EventuallyEq.mem_interior {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t)
    (h : x ∈ interior s) : x ∈ interior t := by
  rw [← nhdsWithin_eq_iff_eventuallyEq] at hst
  simpa [mem_interior_iff_mem_nhds, ← nhdsWithin_eq_nhds, hst] using h
/-
**Filter.EventuallyEq.mem_interior_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.mem_interior_iff {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x
] t) : x in interior s ↔ x in interior t
参数：hst : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyEq.mem_interior`：Filter.EventuallyEq.mem_interior {x : 
α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t) (h : x in interior s) : x in interior t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
lemma Filter.EventuallyEq.mem_interior_iff {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t) :
    x ∈ interior s ↔ x ∈ interior t :=
  ⟨fun h ↦ hst.mem_interior h, fun h ↦ hst.symm.mem_interior h⟩

section Pi

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-
**nhdsWithin_pi_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_pi_eq' {I : Set ι} (hI : I.Finite) (s : forall i, Set (X i)) (x
 : forall i, X i) : 𝓝[pi I s] x = ⨅ i, comap (fun x => x i) (𝓝 (x i) ⊓ ⨅ (_ : i 
in I), 𝓟 (s i))
参数：hI : I.Finite；s : forall i, Set (X i)；x : forall i, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.iInf_principal_finite`：iInf_principal_finite {ι : Type w} {s : Se
t ι} (hs : s.Finite) (f : ι -> Set α) : ⨅ i in s, 𝓟 (f i) = 𝓟 (⋂ i in s, f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsWithin_pi_eq' {I : Set ι} (hI : I.Finite) (s : ∀ i, Set (X i)) (x : ∀ i, X i) :
    𝓝[pi I s] x = ⨅ i, comap (fun x => x i) (𝓝 (x i) ⊓ ⨅ (_ : i ∈ I), 𝓟 (s i)) := by
  simp only [nhdsWithin, nhds_pi, Filter.pi, comap_inf, comap_iInf, pi_def, comap_principal, ←
    iInf_principal_finite hI, ← iInf_inf_eq]
/-
**nhdsWithin_pi_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_pi_eq {I : Set ι} (hI : I.Finite) (s : forall i, Set (X i)) (x 
: forall i, X i) : 𝓝[pi I s] x = (⨅ i in I, comap (fun x => x i) (𝓝[s i] x i)) ⊓
 ⨅ (i) (_ : i ∉ I), comap (fun x => x i) (𝓝 (x i))
参数：hI : I.Finite；s : forall i, Set (X i)；x : forall i, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.iInf_principal_finite`：iInf_principal_finite {ι : Type w} {s : Se
t ι} (hs : s.Finite) (f : ι -> Set α) : ⨅ i in s, 𝓟 (f i) = 𝓟 (⋂ i in s, f i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `iInf_split`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] (
f : β → α) (p : β → Prop),   ⨅ i, f i = (⨅ i, ⨅ (_ : p i), f i) ⊓ ⨅ i, ⨅ (_ : ¬p
…
· 使用定理 `inf_right_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a 
⊓ b ⊓ c = a ⊓ c ⊓ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iInf_inf_eq`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f g : ι → α}, ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ ⨅ x, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsWithin_pi_eq {I : Set ι} (hI : I.Finite) (s : ∀ i, Set (X i)) (x : ∀ i, X i) :
    𝓝[pi I s] x =
      (⨅ i ∈ I, comap (fun x => x i) (𝓝[s i] x i)) ⊓
        ⨅ (i) (_ : i ∉ I), comap (fun x => x i) (𝓝 (x i)) := by
  simp only [nhdsWithin, nhds_pi, Filter.pi, pi_def, ← iInf_principal_finite hI, comap_inf,
    comap_principal]
  rw [iInf_split _ fun i => i ∈ I, inf_right_comm]
  simp only [iInf_inf_eq]
/-
**nhdsWithin_pi_univ_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_pi_univ_eq [Finite ι] (s : forall i, Set (X i)) (x : forall i, 
X i) : 𝓝[pi univ s] x = ⨅ i, comap (fun x => x i) (𝓝[s i] x i)
参数：s : forall i, Set (X i)；x : forall i, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `nhdsWithin_pi_eq`：nhdsWithin_pi_eq {I : Set ι} (hI : I.Finite) (s : fora
ll i, Set (X i)) (x : forall i, X i) : 𝓝[pi I s] x = (⨅ i in I, comap (fun x => 
x i) (…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
theorem nhdsWithin_pi_univ_eq [Finite ι] (s : ∀ i, Set (X i)) (x : ∀ i, X i) :
    𝓝[pi univ s] x = ⨅ i, comap (fun x => x i) (𝓝[s i] x i) := by
  simpa [nhdsWithin] using nhdsWithin_pi_eq finite_univ s x
/-
**nhdsWithin_pi_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_pi_eq_bot {I : Set ι} {s : forall i, Set (X i)} {x : forall i, 
X i} : 𝓝[pi I s] x = ⊥ ↔ exists i in I, 𝓝[s i] x i = ⊥
参数：X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nhdsWithin_pi_eq_bot {I : Set ι} {s : ∀ i, Set (X i)} {x : ∀ i, X i} :
    𝓝[pi I s] x = ⊥ ↔ ∃ i ∈ I, 𝓝[s i] x i = ⊥ := by
  simp only [nhdsWithin, nhds_pi, pi_inf_principal_pi_eq_bot]
/-
**nhdsWithin_pi_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_pi_neBot {I : Set ι} {s : forall i, Set (X i)} {x : forall i, X
 i} : (𝓝[pi I s] x).NeBot ↔ forall i in I, (𝓝[s i] x i).NeBot
参数：X i。
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
theorem nhdsWithin_pi_neBot {I : Set ι} {s : ∀ i, Set (X i)} {x : ∀ i, X i} :
    (𝓝[pi I s] x).NeBot ↔ ∀ i ∈ I, (𝓝[s i] x i).NeBot := by
  simp [neBot_iff, nhdsWithin_pi_eq_bot]
/-
**instNeBotNhdsWithinUnivPi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instNeBotNhdsWithinUnivPi {s : forall i, Set (X i)} {x : forall i, X i} [f
orall i, (𝓝[s i] x i).NeBot] : (𝓝[pi univ s] x).NeBot
参数：X i；𝓝[s i] x i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
instance instNeBotNhdsWithinUnivPi {s : ∀ i, Set (X i)} {x : ∀ i, X i}
    [∀ i, (𝓝[s i] x i).NeBot] : (𝓝[pi univ s] x).NeBot := by
  simpa [nhdsWithin_pi_neBot]
/-
**Pi.instNeBotNhdsWithinIio** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instNeBotNhdsWithinIio [Nonempty ι] [forall i, Preorder (X i)] {x : for
all i, X i} [forall i, (𝓝[<] x i).NeBot] : (𝓝[<] x).NeBot
参数：X i；𝓝[<] x i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `lt_of_strongLT`：lt_of_strongLT [Nonempty ι] (h : a ≺ b) : a < b
· 使用定理 `trivial`：True
-/
instance Pi.instNeBotNhdsWithinIio [Nonempty ι] [∀ i, Preorder (X i)] {x : ∀ i, X i}
    [∀ i, (𝓝[<] x i).NeBot] : (𝓝[<] x).NeBot :=
  have : (𝓝[pi univ fun i ↦ Iio (x i)] x).NeBot := inferInstance
  this.mono <| nhdsWithin_mono _ fun _y hy ↦ lt_of_strongLT fun i ↦ hy i trivial
/-
**Pi.instNeBotNhdsWithinIoi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instNeBotNhdsWithinIoi [Nonempty ι] [forall i, Preorder (X i)] {x : for
all i, X i} [forall i, (𝓝[>] x i).NeBot] : (𝓝[>] x).NeBot
参数：X i；𝓝[>] x i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instNeBotNhdsWithinIoi [Nonempty ι] [∀ i, Preorder (X i)] {x : ∀ i, X i}
    [∀ i, (𝓝[>] x i).NeBot] : (𝓝[>] x).NeBot :=
  Pi.instNeBotNhdsWithinIio (X := fun i ↦ (X i)ᵒᵈ) (x := fun i ↦ OrderDual.toDual (x i))

end Pi

/-
**Filter.Tendsto.piecewise_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.piecewise_nhdsWithin {f g : α -> β} {t : Set α} [forall x, 
Decidable (x in t)] {a : α} {s : Set α} {l : Filter β} (h₀ : Tendsto f (𝓝[s inte
r t] a) l) (h₁ : Tendsto g (𝓝[s inter tᶜ] a) l) : Tendsto (piecewise t f g) (𝓝[s
] a) l
参数：x in t；h₀ : Tendsto f (𝓝[s inter t] a) l；h₁ : Tendsto g (𝓝[s inter tᶜ] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.piecewise`：∀ {α : Type u_1} {β : Type u_2} {l₁ : Filter α
} {l₂ : Filter β} {f g : α → β} {s : Set α}   [inst : (x : α) → Decidable (x ∈ s
)],   Filter.T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_inter'`：nhdsWithin_inter' (a : α) (s t : Set α) : 𝓝[s inter t
] a = 𝓝[s] a ⊓ 𝓟 t
-/
theorem Filter.Tendsto.piecewise_nhdsWithin {f g : α → β} {t : Set α} [∀ x, Decidable (x ∈ t)]
    {a : α} {s : Set α} {l : Filter β} (h₀ : Tendsto f (𝓝[s ∩ t] a) l)
    (h₁ : Tendsto g (𝓝[s ∩ tᶜ] a) l) : Tendsto (piecewise t f g) (𝓝[s] a) l := by
  apply Tendsto.piecewise <;> rwa [← nhdsWithin_inter']
/-
**Filter.Tendsto.if_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.if_nhdsWithin {f g : α -> β} {p : α -> Prop} [DecidablePred
 p] {a : α} {s : Set α} {l : Filter β} (h₀ : Tendsto f (𝓝[s inter { x | p x }] a
) l) (h₁ : Tendsto g (𝓝[s inter { x | ¬p x }] a) l) : Tendsto (fun x => if p x t
hen f x else g x) (𝓝[s] a) l
参数：h₀ : Tendsto f (𝓝[s inter { x | p x }] a) l；h₁ : Tendsto g (𝓝[s inter { x | ¬
p x }] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.piecewise_nhdsWithin`：Filter.Tendsto.piecewise_nhdsWithin
 {f g : α -> β} {t : Set α} [forall x, Decidable (x in t)] {a : α} {s : Set α} {
l : Filter β} (h₀ : Tends…
-/
theorem Filter.Tendsto.if_nhdsWithin {f g : α → β} {p : α → Prop} [DecidablePred p] {a : α}
    {s : Set α} {l : Filter β} (h₀ : Tendsto f (𝓝[s ∩ { x | p x }] a) l)
    (h₁ : Tendsto g (𝓝[s ∩ { x | ¬p x }] a) l) :
    Tendsto (fun x => if p x then f x else g x) (𝓝[s] a) l :=
  h₀.piecewise_nhdsWithin h₁
/-
**map_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nhdsWithin (f : α -> β) (a : α) (s : Set α) : map f (𝓝[s] a) = ⨅ t in 
{ t : Set α | a in t ∧ IsOpen t }, 𝓟 (f '' (t inter s))
参数：f : α -> β；a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `nhdsWithin_basis_open`：nhdsWithin_basis_open (a : α) (t : Set α) : (𝓝[t]
 a).HasBasis (fun u => a in u ∧ IsOpen u) fun u => u inter t
-/
theorem map_nhdsWithin (f : α → β) (a : α) (s : Set α) :
    map f (𝓝[s] a) = ⨅ t ∈ { t : Set α | a ∈ t ∧ IsOpen t }, 𝓟 (f '' (t ∩ s)) :=
  ((nhdsWithin_basis_open a s).map f).eq_biInf
/-
**tendsto_nhdsWithin_mono_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhdsWithin_mono_left {f : α -> β} {a : α} {s t : Set α} {l : Filte
r β} (hst : s subseteq t) (h : Tendsto f (𝓝[t] a) l) : Tendsto f (𝓝[s] a) l
参数：hst : s subseteq t；h : Tendsto f (𝓝[t] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
theorem tendsto_nhdsWithin_mono_left {f : α → β} {a : α} {s t : Set α} {l : Filter β} (hst : s ⊆ t)
    (h : Tendsto f (𝓝[t] a) l) : Tendsto f (𝓝[s] a) l :=
  h.mono_left <| nhdsWithin_mono a hst
/-
**tendsto_nhdsWithin_mono_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhdsWithin_mono_right {f : β -> α} {l : Filter β} {a : α} {s t : S
et α} (hst : s subseteq t) (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝[t] a)
参数：hst : s subseteq t；h : Tendsto f l (𝓝[s] a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
theorem tendsto_nhdsWithin_mono_right {f : β → α} {l : Filter β} {a : α} {s t : Set α} (hst : s ⊆ t)
    (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝[t] a) :=
  h.mono_right (nhdsWithin_mono a hst)
/-
**tendsto_nhdsWithin_of_tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhdsWithin_of_tendsto_nhds {f : α -> β} {a : α} {s : Set α} {l : F
ilter β} (h : Tendsto f (𝓝 a) l) : Tendsto f (𝓝[s] a) l
参数：h : Tendsto f (𝓝 a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem tendsto_nhdsWithin_of_tendsto_nhds {f : α → β} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f (𝓝 a) l) : Tendsto f (𝓝[s] a) l :=
  h.mono_left inf_le_left
/-
**eventually_mem_of_tendsto_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_mem_of_tendsto_nhdsWithin {f : β -> α} {a : α} {s : Set α} {l :
 Filter β} (h : Tendsto f l (𝓝[s] a)) : forallᶠ i in l, f i in s
参数：h : Tendsto f l (𝓝[s] a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhdsWithin_eq`：nhdsWithin_eq (a : α) (s : Set α) : 𝓝[s] a = ⨅ t in { t :
 Set α | a in t ∧ IsOpen t }, 𝓟 (t inter s)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem eventually_mem_of_tendsto_nhdsWithin {f : β → α} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f l (𝓝[s] a)) : ∀ᶠ i in l, f i ∈ s := by
  simp_rw [nhdsWithin_eq, tendsto_iInf, mem_ofPred_eq, tendsto_principal, mem_inter_iff,
    eventually_and] at h
  exact (h univ ⟨mem_univ a, isOpen_univ⟩).2
/-
**tendsto_nhds_of_tendsto_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_of_tendsto_nhdsWithin {f : β -> α} {a : α} {s : Set α} {l : F
ilter β} (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝 a)
参数：h : Tendsto f l (𝓝[s] a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
theorem tendsto_nhds_of_tendsto_nhdsWithin {f : β → α} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝 a) :=
  h.mono_right nhdsWithin_le_nhds
/-
**nhdsWithin_neBot_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_neBot_of_mem {s : Set α} {x : α} (hx : x in s) : NeBot (𝓝[s] x)
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem nhdsWithin_neBot_of_mem {s : Set α} {x : α} (hx : x ∈ s) : NeBot (𝓝[s] x) :=
  mem_closure_iff_nhdsWithin_neBot.1 <| subset_closure hx
/-
**IsClosed.mem_of_nhdsWithin_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.mem_of_nhdsWithin_neBot {s : Set α} (hs : IsClosed s) {x : α} (hx
 : NeBot <| 𝓝[s] x) : x in s
参数：hs : IsClosed s；hx : NeBot <| 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem IsClosed.mem_of_nhdsWithin_neBot {s : Set α} (hs : IsClosed s) {x : α}
    (hx : NeBot <| 𝓝[s] x) : x ∈ s :=
  hs.closure_eq ▸ mem_closure_iff_nhdsWithin_neBot.2 hx
/-
**DenseRange.nhdsWithin_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.nhdsWithin_neBot {ι : Type*} {f : ι -> α} (h : DenseRange f) (x
 : α) : NeBot (𝓝[range f] x)
参数：h : DenseRange f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
-/
theorem DenseRange.nhdsWithin_neBot {ι : Type*} {f : ι → α} (h : DenseRange f) (x : α) :
    NeBot (𝓝[range f] x) :=
  mem_closure_iff_clusterPt.1 (h x)
/-
**mem_closure_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_pi {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α
 i)] {I : Set ι} {s : forall i, Set (α i)} {x : forall i, α i} : x in closure (p
i I s) ↔ forall i in I, x i in closure (s i)
参数：α i；α i。
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
theorem mem_closure_pi {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {I : Set ι}
    {s : ∀ i, Set (α i)} {x : ∀ i, α i} : x ∈ closure (pi I s) ↔ ∀ i ∈ I, x i ∈ closure (s i) := by
  simp only [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_pi_neBot]
/-
**closure_pi_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_pi_set {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α
 i)] (I : Set ι) (s : forall i, Set (α i)) : closure (pi I s) = pi I fun i => cl
osure (s i)
参数：α i；I : Set ι；s : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `mem_closure_pi`：mem_closure_pi {ι : Type*} {α : ι -> Type*} [forall i, T
opologicalSpace (α i)] {I : Set ι} {s : forall i, Set (α i)} {x : forall i, α i}
 : x…
-/
theorem closure_pi_set {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] (I : Set ι)
    (s : ∀ i, Set (α i)) : closure (pi I s) = pi I fun i => closure (s i) :=
  Set.ext fun _ => mem_closure_pi
/-
**dense_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_pi {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α i)] {
s : forall i, Set (α i)} (I : Set ι) (hs : forall i in I, Dense (s i)) : Dense (
pi I s)
参数：α i；α i；I : Set ι；hs : forall i in I, Dense (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_pi_set`：closure_pi_set {ι : Type*} {α : ι -> Type*} [forall i, T
opologicalSpace (α i)] (I : Set ι) (s : forall i, Set (α i)) : closure (pi I s) 
= pi…
· 使用定理 `Set.pi_congr`：pi_congr (h : s₁ = s₂) (h' : forall i in s₁, t₁ i = t₂ i) 
: s₁.pi t₁ = s₂.pi t₂
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dense_pi {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {s : ∀ i, Set (α i)}
    (I : Set ι) (hs : ∀ i ∈ I, Dense (s i)) : Dense (pi I s) := by
  simp only [dense_iff_closure_eq, closure_pi_set, pi_congr rfl fun i hi => (hs i hi).closure_eq,
    pi_univ]
/-
**DenseRange.piMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.piMap {ι : Type*} {X Y : ι -> Type*} [forall i, TopologicalSpac
e (Y i)] {f : (i : ι) -> (X i) -> (Y i)} (hf : forall i, DenseRange (f i)) : Den
seRange (Pi.map f)
参数：Y i；i : ι；X i；Y i；hf : forall i, DenseRange (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DenseRange.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] {α : Type u_
1} (f : α → X), DenseRange f = Dense (Set.range f)
· 使用定理 `Set.range_piMap`：range_piMap (f : forall i, α i -> β i) : range (Pi.map 
f) = pi univ fun i => range (f i)
· 使用定理 `dense_pi`：dense_pi {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSp
ace (α i)] {s : forall i, Set (α i)} (I : Set ι) (hs : forall i in I, Dense (s…
-/
theorem DenseRange.piMap {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : (i : ι) → (X i) → (Y i)} (hf : ∀ i, DenseRange (f i)) :
    DenseRange (Pi.map f) := by
  rw [DenseRange, Set.range_piMap]
  exact dense_pi Set.univ (fun i _ => hf i)
/-
**eventuallyEq_nhdsWithin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyEq_nhdsWithin_iff {f g : α -> β} {s : Set α} {a : α} : f =ᶠ[𝓝[s]
 a] g ↔ forallᶠ x in 𝓝 a, x in s -> f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.mem_inf_principal`：mem_inf_principal {f : Filter α} {s t : Set α}
 : s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f
-/
theorem eventuallyEq_nhdsWithin_iff {f g : α → β} {s : Set α} {a : α} :
    f =ᶠ[𝓝[s] a] g ↔ ∀ᶠ x in 𝓝 a, x ∈ s → f x = g x :=
  mem_inf_principal

/-- Two functions agree on a neighborhood of `x` if they agree at `x` and in a punctured
neighborhood. -/
/-
**eventuallyEq_nhds_of_eventuallyEq_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyEq_nhds_of_eventuallyEq_nhdsNE {f g : α -> β} {a : α} (h₁ : f =ᶠ
[𝓝[!=] a] g) (h₂ : f a = g a) : f =ᶠ[𝓝 a] g
参数：h₁ : f =ᶠ[𝓝[!=] a] g；h₂ : f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
Two functions agree on a neighborhood of `x` if they agree at `x` and in a punct
ured
neighborhood.
-/
theorem eventuallyEq_nhds_of_eventuallyEq_nhdsNE {f g : α → β} {a : α} (h₁ : f =ᶠ[𝓝[≠] a] g)
    (h₂ : f a = g a) :
    f =ᶠ[𝓝 a] g := by
  filter_upwards [eventually_nhdsWithin_iff.1 h₁]
  grind
/-
**eventuallyEq_nhdsWithin_of_eqOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyEq_nhdsWithin_of_eqOn {f g : α -> β} {s : Set α} {a : α} (h : Eq
On f g s) : f =ᶠ[𝓝[s] a] g
参数：h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
-/
theorem eventuallyEq_nhdsWithin_of_eqOn {f g : α → β} {s : Set α} {a : α} (h : EqOn f g s) :
    f =ᶠ[𝓝[s] a] g :=
  mem_inf_of_right h
/-
**Set.EqOn.eventuallyEq_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.EqOn.eventuallyEq_nhdsWithin {f g : α -> β} {s : Set α} {a : α} (h : E
qOn f g s) : f =ᶠ[𝓝[s] a] g
参数：h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventuallyEq_nhdsWithin_of_eqOn`：eventuallyEq_nhdsWithin_of_eqOn {f g : 
α -> β} {s : Set α} {a : α} (h : EqOn f g s) : f =ᶠ[𝓝[s] a] g
-/
theorem Set.EqOn.eventuallyEq_nhdsWithin {f g : α → β} {s : Set α} {a : α} (h : EqOn f g s) :
    f =ᶠ[𝓝[s] a] g :=
  eventuallyEq_nhdsWithin_of_eqOn h
/-
**tendsto_nhdsWithin_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhdsWithin_congr {f g : α -> β} {s : Set α} {a : α} {l : Filter β}
 (hfg : forall x in s, f x = g x) (hf : Tendsto f (𝓝[s] a) l) : Tendsto g (𝓝[s] 
a) l
参数：hfg : forall x in s, f x = g x；hf : Tendsto f (𝓝[s] a) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `eventuallyEq_nhdsWithin_of_eqOn`：eventuallyEq_nhdsWithin_of_eqOn {f g : 
α -> β} {s : Set α} {a : α} (h : EqOn f g s) : f =ᶠ[𝓝[s] a] g
-/
theorem tendsto_nhdsWithin_congr {f g : α → β} {s : Set α} {a : α} {l : Filter β}
    (hfg : ∀ x ∈ s, f x = g x) (hf : Tendsto f (𝓝[s] a) l) : Tendsto g (𝓝[s] a) l :=
  (tendsto_congr' <| eventuallyEq_nhdsWithin_of_eqOn hfg).1 hf
/-
**eventually_nhdsWithin_of_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhdsWithin_of_forall {s : Set α} {a : α} {p : α -> Prop} (h : f
orall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
参数：h : forall x in s, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
-/
theorem eventually_nhdsWithin_of_forall {s : Set α} {a : α} {p : α → Prop} (h : ∀ x ∈ s, p x) :
    ∀ᶠ x in 𝓝[s] a, p x :=
  mem_inf_of_right h
/-
**tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filte
r β} {s : Set α} (f : β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : forallᶠ x in l, f x
 in s) : Tendsto f l (𝓝[s] a)
参数：f : β -> α；h1 : Tendsto f l (𝓝 a)；h2 : forallᶠ x in l, f x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
-/
theorem tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α}
    (f : β → α) (h1 : Tendsto f l (𝓝 a)) (h2 : ∀ᶠ x in l, f x ∈ s) : Tendsto f l (𝓝[s] a) :=
  tendsto_inf.2 ⟨h1, tendsto_principal.2 h2⟩
/-
**tendsto_nhdsWithin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s : Set α} {f : β -> α} : T
endsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in l, f n in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_of_tendsto_nhdsWithin`：tendsto_nhds_of_tendsto_nhdsWithin {
f : β -> α} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f l (𝓝[s] a)) : Tend
sto f l (𝓝 a)
· 使用定理 `eventually_mem_of_tendsto_nhdsWithin`：eventually_mem_of_tendsto_nhdsWith
in {f : β -> α} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f l (𝓝[s] a)) : 
forallᶠ i in l, f i in s
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s : Set α} {f : β → α} :
    Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ ∀ᶠ n in l, f n ∈ s :=
  ⟨fun h => ⟨tendsto_nhds_of_tendsto_nhdsWithin h, eventually_mem_of_tendsto_nhdsWithin h⟩, fun h =>
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h.1 h.2⟩

@[simp]
/-
**tendsto_nhdsWithin_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhdsWithin_range {a : α} {l : Filter β} {f : β -> α} : Tendsto f l
 (𝓝[range f] a) ↔ Tendsto f l (𝓝 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem tendsto_nhdsWithin_range {a : α} {l : Filter β} {f : β → α} :
    Tendsto f l (𝓝[range f] a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => h.mono_right inf_le_left, fun h =>
    tendsto_inf.2 ⟨h, tendsto_principal.2 <| Eventually.of_forall mem_range_self⟩⟩
/-
**Filter.EventuallyEq.eq_of_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.eq_of_nhdsWithin {s : Set α} {f g : α -> β} {a : α} (h
 : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a = g a
参数：h : f =ᶠ[𝓝[s] a] g；hmem : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x
-/
theorem Filter.EventuallyEq.eq_of_nhdsWithin {s : Set α} {f g : α → β} {a : α} (h : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : f a = g a :=
  h.self_of_nhdsWithin hmem
/-
**eventually_nhdsWithin_of_eventually_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhdsWithin_of_eventually_nhds {s : Set α} {a : α} {p : α -> Pro
p} (h : forallᶠ x in 𝓝 a, p x) : forallᶠ x in 𝓝[s] a, p x
参数：h : forallᶠ x in 𝓝 a, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
-/
theorem eventually_nhdsWithin_of_eventually_nhds {s : Set α}
    {a : α} {p : α → Prop} (h : ∀ᶠ x in 𝓝 a, p x) : ∀ᶠ x in 𝓝[s] a, p x :=
  mem_nhdsWithin_of_mem_nhds h
/-
**Set.MapsTo.preimage_mem_nhdsWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.MapsTo.preimage_mem_nhdsWithin {f : α -> β} {s : Set α} {t : Set β} {x
 : α} (hst : MapsTo f s t) : f ⁻¹' t in 𝓝[s] x
参数：hst : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
lemma Set.MapsTo.preimage_mem_nhdsWithin {f : α → β} {s : Set α} {t : Set β} {x : α}
    (hst : MapsTo f s t) : f ⁻¹' t ∈ 𝓝[s] x :=
  Filter.mem_of_superset self_mem_nhdsWithin hst

/-!
### `nhdsWithin` and subtypes
-/

/-
**mem_nhdsWithin_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsWithin_subtype {s : Set α} {a : { x // x in s }} {t u : Set { x //
 x in s }} : t in 𝓝[u] a ↔ t in comap ((↑) : s -> α) (𝓝[(↑) '' u] a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `nhds_subtype`：nhds_subtype (s : Set X) (x : { x // x in s }) : 𝓝 x = com
ap (↑) (𝓝 (x : X))
· 使用定理 `Filter.principal_subtype`：principal_subtype {α : Type*} (s : Set α) (t :
 Set s) : 𝓟 t = comap (↑) (𝓟 (((↑) : s -> α) '' t))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### `nhdsWithin` and subtypes
-/
theorem mem_nhdsWithin_subtype {s : Set α} {a : { x // x ∈ s }} {t u : Set { x // x ∈ s }} :
    t ∈ 𝓝[u] a ↔ t ∈ comap ((↑) : s → α) (𝓝[(↑) '' u] a) := by
  rw [nhdsWithin, nhds_subtype, principal_subtype, ← comap_inf, ← nhdsWithin]
/-
**nhdsWithin_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_subtype (s : Set α) (a : { x // x in s }) (t : Set { x // x in 
s }) : 𝓝[t] a = comap ((↑) : s -> α) (𝓝[(↑) '' t] a)
参数：s : Set α；a : { x // x in s }；t : Set { x // x in s }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `mem_nhdsWithin_subtype`：mem_nhdsWithin_subtype {s : Set α} {a : { x // x
 in s }} {t u : Set { x // x in s }} : t in 𝓝[u] a ↔ t in comap ((↑) : s -> α) (
𝓝[(↑) '' u] …
-/
theorem nhdsWithin_subtype (s : Set α) (a : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    𝓝[t] a = comap ((↑) : s → α) (𝓝[(↑) '' t] a) :=
  Filter.ext fun _ => mem_nhdsWithin_subtype
/-
**nhdsWithin_eq_map_subtype_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_eq_map_subtype_coe {s : Set α} {a : α} (h : a in s) : 𝓝[s] a = 
map ((↑) : s -> α) (𝓝 ⟨a, h⟩)
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_nhds_subtype_val`：map_nhds_subtype_val {s : Set X} (x : s) : map ((↑
) : s -> X) (𝓝 x) = 𝓝[s] ↑x
-/
theorem nhdsWithin_eq_map_subtype_coe {s : Set α} {a : α} (h : a ∈ s) :
    𝓝[s] a = map ((↑) : s → α) (𝓝 ⟨a, h⟩) :=
  (map_nhds_subtype_val ⟨a, h⟩).symm
/-
**mem_nhds_subtype_iff_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_subtype_iff_nhdsWithin {s : Set α} {a : s} {t : Set s} : t in 𝓝 a
 ↔ (↑) '' t in 𝓝[s] (a : α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_nhds_subtype_val`：map_nhds_subtype_val {s : Set X} (x : s) : map ((↑
) : s -> X) (𝓝 x) = 𝓝[s] ↑x
· 使用定理 `Filter.image_mem_map_iff`：image_mem_map_iff (hf : Injective m) : m '' s 
in map m f ↔ s in f
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nhds_subtype_iff_nhdsWithin {s : Set α} {a : s} {t : Set s} :
    t ∈ 𝓝 a ↔ (↑) '' t ∈ 𝓝[s] (a : α) := by
  rw [← map_nhds_subtype_val, image_mem_map_iff Subtype.val_injective]
/-
**preimage_coe_mem_nhds_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_coe_mem_nhds_subtype {s t : Set α} {a : s} : (↑) ⁻¹' t in 𝓝 a ↔ t
 in 𝓝[s] ↑a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_nhds_subtype_val`：map_nhds_subtype_val {s : Set X} (x : s) : map ((↑
) : s -> X) (𝓝 x) = 𝓝[s] ↑x
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem preimage_coe_mem_nhds_subtype {s t : Set α} {a : s} : (↑) ⁻¹' t ∈ 𝓝 a ↔ t ∈ 𝓝[s] ↑a := by
  rw [← map_nhds_subtype_val, mem_map]
/-
**eventually_nhds_subtype_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhds_subtype_iff (s : Set α) (a : s) (P : α -> Prop) : (forallᶠ
 x : s in 𝓝 a, P x) ↔ forallᶠ x in 𝓝[s] a, P x
参数：s : Set α；a : s；P : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `preimage_coe_mem_nhds_subtype`：preimage_coe_mem_nhds_subtype {s t : Set 
α} {a : s} : (↑) ⁻¹' t in 𝓝 a ↔ t in 𝓝[s] ↑a
-/
theorem eventually_nhds_subtype_iff (s : Set α) (a : s) (P : α → Prop) :
    (∀ᶠ x : s in 𝓝 a, P x) ↔ ∀ᶠ x in 𝓝[s] a, P x :=
  preimage_coe_mem_nhds_subtype
/-
**frequently_nhds_subtype_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frequently_nhds_subtype_iff (s : Set α) (a : s) (P : α -> Prop) : (existsᶠ
 x : s in 𝓝 a, P x) ↔ existsᶠ x in 𝓝[s] a, P x
参数：s : Set α；a : s；P : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `eventually_nhds_subtype_iff`：eventually_nhds_subtype_iff (s : Set α) (a 
: s) (P : α -> Prop) : (forallᶠ x : s in 𝓝 a, P x) ↔ forallᶠ x in 𝓝[s] a, P x
-/
theorem frequently_nhds_subtype_iff (s : Set α) (a : s) (P : α → Prop) :
    (∃ᶠ x : s in 𝓝 a, P x) ↔ ∃ᶠ x in 𝓝[s] a, P x :=
  eventually_nhds_subtype_iff s a (¬ P ·) |>.not
/-
**tendsto_nhdsWithin_iff_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhdsWithin_iff_subtype {s : Set α} {a : α} (h : a in s) (f : α -> 
β) (l : Filter β) : Tendsto f (𝓝[s] a) l ↔ Tendsto (s.domRestrict f) (𝓝 ⟨a, h⟩) 
l
参数：h : a in s；f : α -> β；l : Filter β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_eq_map_subtype_coe`：nhdsWithin_eq_map_subtype_coe {s : Set α}
 {a : α} (h : a in s) : 𝓝[s] a = map ((↑) : s -> α) (𝓝 ⟨a, h⟩)
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_nhdsWithin_iff_subtype {s : Set α} {a : α} (h : a ∈ s) (f : α → β) (l : Filter β) :
    Tendsto f (𝓝[s] a) l ↔ Tendsto (s.domRestrict f) (𝓝 ⟨a, h⟩) l := by
  rw [nhdsWithin_eq_map_subtype_coe h, tendsto_map'_iff]; rfl
/-
**clusterPt_principal_subtype_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_principal_subtype_iff_frequently {s t : Set α} (hst : s subseteq
 t) {J : Set s} {a : s} : ClusterPt a (Filter.principal J) ↔ existsᶠ x in nhdsWi
thin a t, exists h : x in s, (⟨x, h⟩ : s) in J
参数：hst : s subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_eq_map_subtype_coe`：nhdsWithin_eq_map_subtype_coe {s : Set α}
 {a : α} (h : a in s) : 𝓝[s] a = map ((↑) : s -> α) (𝓝 ⟨a, h⟩)
· 使用定理 `Filter.frequently_map`：frequently_map {P : β -> Prop} : (existsᶠ b in ma
p m f, P b) ↔ existsᶠ a in f, P (m a)
· 使用定理 `clusterPt_principal_iff_frequently`：clusterPt_principal_iff_frequently :
 ClusterPt x (𝓟 s) ↔ existsᶠ y in 𝓝 x, y in s
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Filter.frequently_comap`：frequently_comap : (existsᶠ a in comap f l, p a
) ↔ existsᶠ b in l, exists a, f a = b ∧ p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用引理 `Filter.frequently_congr`：frequently_congr {p q : α -> Prop} {f : Filter 
α} (h : forallᶠ x in f, p x ↔ q x) : (existsᶠ x in f, p x) ↔ existsᶠ x in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
-/
theorem clusterPt_principal_subtype_iff_frequently {s t : Set α} (hst : s ⊆ t) {J : Set s} {a : s} :
    ClusterPt a (Filter.principal J) ↔ ∃ᶠ x in nhdsWithin a t, ∃ h : x ∈ s, (⟨x, h⟩ : s) ∈ J := by
  rw [nhdsWithin_eq_map_subtype_coe (hst a.prop), Filter.frequently_map,
    clusterPt_principal_iff_frequently,
    Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.frequently_comap,
    Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.frequently_comap, Subtype.coe_mk]
  apply frequently_congr
  apply Eventually.of_forall
  intro x
  simp only [SetCoe.exists, exists_and_left, exists_eq_left]
  exact ⟨fun ⟨h, hx⟩ => ⟨hst h, h, hx⟩, fun ⟨_, hx⟩ => hx⟩

/-!
## The `nhdsSetWithin`-filter
-/

variable [TopologicalSpace β]

@[gcongr, mono]
/-
**nhdsSetWithin_mono_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_mono_left {s s' t : Set α} (h : s subseteq s') : 𝓝ˢ[t] s <= 
𝓝ˢ[t] s'
参数：h : s subseteq s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
-/
lemma nhdsSetWithin_mono_left {s s' t : Set α} (h : s ⊆ s') : 𝓝ˢ[t] s ≤ 𝓝ˢ[t] s' :=
  inf_le_inf_right _ <| nhdsSet_mono h

@[gcongr, mono]
/-
**nhdsSetWithin_mono_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_mono_right {s t t' : Set α} (h : t subseteq t') : 𝓝ˢ[t] s <=
 𝓝ˢ[t'] s
参数：h : t subseteq t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
lemma nhdsSetWithin_mono_right {s t t' : Set α} (h : t ⊆ t') : 𝓝ˢ[t] s ≤ 𝓝ˢ[t'] s :=
  inf_le_inf_left _ <| principal_mono.2 h
/-
**nhdsSetWithin_hasBasis** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s' : ι -> Set α} {s : 
Set α} (h : (𝓝ˢ s).HasBasis p s') (t : Set α) : (𝓝ˢ[t] s).HasBasis p fun i => s'
 i inter t
参数：h : (𝓝ˢ s).HasBasis p s'；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
-/
lemma nhdsSetWithin_hasBasis {ι : Sort*} {p : ι → Prop} {s' : ι → Set α} {s : Set α}
    (h : (𝓝ˢ s).HasBasis p s') (t : Set α) : (𝓝ˢ[t] s).HasBasis p fun i => s' i ∩ t :=
  h.inf_principal t
/-
**nhdsSetWithin_basis_open** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_basis_open (s t : Set α) : (𝓝ˢ[t] s).HasBasis (fun u => IsOp
en u ∧ s subseteq u) fun u => u inter t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nhdsSetWithin_hasBasis`：nhdsSetWithin_hasBasis {ι : Sort*} {p : ι -> Pro
p} {s' : ι -> Set α} {s : Set α} (h : (𝓝ˢ s).HasBasis p s') (t : Set α) : (𝓝ˢ[t]
 s).HasBasis…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
-/
lemma nhdsSetWithin_basis_open (s t : Set α) :
    (𝓝ˢ[t] s).HasBasis (fun u => IsOpen u ∧ s ⊆ u) fun u => u ∩ t :=
  nhdsSetWithin_hasBasis (hasBasis_nhdsSet s) t
/-
**mem_nhdsSetWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nhdsSetWithin {s t u : Set α} : u in 𝓝ˢ[t] s ↔ exists v, IsOpen v ∧ s 
subseteq v ∧ v inter t subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用引理 `nhdsSetWithin_basis_open`：nhdsSetWithin_basis_open (s t : Set α) : (𝓝ˢ[t
] s).HasBasis (fun u => IsOpen u ∧ s subseteq u) fun u => u inter t
-/
lemma mem_nhdsSetWithin {s t u : Set α} : u ∈ 𝓝ˢ[t] s ↔ ∃ v, IsOpen v ∧ s ⊆ v ∧ v ∩ t ⊆ u := by
  simpa [and_assoc] using (nhdsSetWithin_basis_open s t).mem_iff

@[simp]
/-
**nhdsSetWithin_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_singleton {x : α} {s : Set α} : 𝓝ˢ[s] {x} = 𝓝[s] x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsSetWithin_singleton {x : α} {s : Set α} : 𝓝ˢ[s] {x} = 𝓝[s] x := by
  simp [nhdsSetWithin, nhdsWithin]

@[simp]
/-
**nhdsSetWithin_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_univ {s : Set α} : 𝓝ˢ[univ] s = 𝓝ˢ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsSetWithin_univ {s : Set α} : 𝓝ˢ[univ] s = 𝓝ˢ s := by
  simp [nhdsSetWithin]
/-
**mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsSet {s t : Set α} : s in 𝓝ˢ t ↔ exists u subseteq s, IsOpen u ∧ t 
subseteq u
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhdsSet {s t : Set α} : s ∈ 𝓝ˢ t ↔ ∃ u ⊆ s, IsOpen u ∧ t ⊆ u := by
  simp [← nhdsSetWithin_univ, mem_nhdsSetWithin, and_comm, and_assoc]

@[simp]
/-
**nhdsSetWithin_univ'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_univ' {s : Set α} : 𝓝ˢ[s] univ = 𝓟 s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_univ`：nhdsSet_univ : 𝓝ˢ (univ : Set X) = ⊤
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsSetWithin_univ' {s : Set α} : 𝓝ˢ[s] univ = 𝓟 s := by
  simp [nhdsSetWithin]

@[simp]
/-
**nhdsSetWithin_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_self {s : Set α} : 𝓝ˢ[s] s = 𝓟 s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsSetWithin_self {s : Set α} : 𝓝ˢ[s] s = 𝓟 s := by
  simp [nhdsSetWithin, principal_le_nhdsSet]
/-
**nhdsSetWithin_eq_principal_of_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_eq_principal_of_subset {s t : Set α} (h : t subseteq s) : 𝓝ˢ
[t] s = 𝓟 t
参数：h : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `principal_le_nhdsSet`：principal_le_nhdsSet : 𝓟 s <= 𝓝ˢ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsSetWithin_eq_principal_of_subset {s t : Set α} (h : t ⊆ s) : 𝓝ˢ[t] s = 𝓟 t := by
  simp [nhdsSetWithin, (principal_mono.2 h).trans principal_le_nhdsSet]

@[simp]
/-
**nhdsSetWithin_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_empty {s : Set α} : 𝓝ˢ[∅] s = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsSetWithin_empty {s : Set α} : 𝓝ˢ[∅] s = ⊥ := by
  simp [nhdsSetWithin]

@[simp]
/-
**nhdsSetWithin_empty'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_empty' {s : Set α} : 𝓝ˢ[s] ∅ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_empty`：nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsSetWithin_empty' {s : Set α} : 𝓝ˢ[s] ∅ = ⊥ := by
  simp [nhdsSetWithin]
/-
**principal_inter_le_nhdsSetWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：principal_inter_le_nhdsSetWithin {s t : Set α} : 𝓟 (s inter t) <= 𝓝ˢ[t] s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `inf_le_of_left_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α},
 a ≤ c → a ⊓ b ≤ c
· 使用定理 `principal_le_nhdsSet`：principal_le_nhdsSet : 𝓟 s <= 𝓝ˢ s
-/
lemma principal_inter_le_nhdsSetWithin {s t : Set α} : 𝓟 (s ∩ t) ≤ 𝓝ˢ[t] s := by
  simpa [nhdsSetWithin] using inf_le_of_left_le (b := 𝓟 t) <| principal_le_nhdsSet
/-
**nhdsSetWithin_prod_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSetWithin_prod_le {s s' : Set α} {t t' : Set β} : 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t
) <= 𝓝ˢ[s'] s ×ˢ 𝓝ˢ[t'] t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_principal_principal`：prod_principal_principal {s : Set α} {t
 : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `inf_le_of_left_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α},
 a ≤ c → a ⊓ b ≤ c
· 使用定理 `nhdsSet_prod_le`：nhdsSet_prod_le (s : Set X) (t : Set Y) : 𝓝ˢ (s ×ˢ t) <
= 𝓝ˢ s ×ˢ 𝓝ˢ t
-/
lemma nhdsSetWithin_prod_le {s s' : Set α} {t t' : Set β} :
    𝓝ˢ[s' ×ˢ t'] (s ×ˢ t) ≤ 𝓝ˢ[s'] s ×ˢ 𝓝ˢ[t'] t := by
  simpa [nhdsSetWithin, ← prod_inf_prod] using inf_le_of_left_le <| nhdsSet_prod_le _ _
/-
**mem_nhdsSet_induced** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nhdsSet_induced {α β : Type*} {t : TopologicalSpace β} (f : α -> β) (s
 u : Set α) : u in @nhdsSet α (t.induced f) s ↔ exists v in 𝓝ˢ (f '' s), f ⁻¹' v
 subseteq u
参数：f : α -> β；s u : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
lemma mem_nhdsSet_induced {α β : Type*} {t : TopologicalSpace β} (f : α → β) (s u : Set α) :
    u ∈ @nhdsSet α (t.induced f) s ↔ ∃ v ∈ 𝓝ˢ (f '' s), f ⁻¹' v ⊆ u := by
  let := t.induced f
  simp_rw [mem_nhdsSet_iff_exists, isOpen_induced_iff]
  refine ⟨fun ⟨v, ⟨v', hv'⟩, hv⟩ ↦ ?_, fun ⟨v, ⟨v', hv'⟩, hv⟩ ↦ ?_⟩
  · refine ⟨v', ⟨v', hv'.1, ?_, subset_rfl⟩, hv'.2.trans_subset hv.2⟩
    exact (image_mono hv.1).trans (by simp [hv'])
  · exact ⟨f ⁻¹' v', ⟨v', hv'.1, rfl⟩, image_subset_iff.1 hv'.2.1, (preimage_mono hv'.2.2).trans hv⟩
/-
**nhdsSet_induced** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsSet_induced {α β : Type*} {t : TopologicalSpace β} (f : α -> β) (s : S
et α) : @nhdsSet α (t.induced f) s = comap f (𝓝ˢ (f '' s))
参数：f : α -> β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_nhdsSet_induced`：mem_nhdsSet_induced {α β : Type*} {t : TopologicalS
pace β} (f : α -> β) (s u : Set α) : u in @nhdsSet α (t.induced f) s ↔ exists v 
in 𝓝ˢ (f …
· 使用定理 `Filter.mem_comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α 
→ β} {s : Set α}, s ∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nhdsSet_induced {α β : Type*} {t : TopologicalSpace β} (f : α → β) (s : Set α) :
    @nhdsSet α (t.induced f) s = comap f (𝓝ˢ (f '' s)) := by
  ext s
  rw [mem_nhdsSet_induced, mem_comap]
/-
**map_nhdsSet_induced_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_nhdsSet_induced_eq {α β : Type*} {t : TopologicalSpace β} {f : α -> β}
 (s : Set α) : map f (@nhdsSet α (t.induced f) s) = 𝓝ˢ[range f] (f '' s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nhdsSet_induced`：nhdsSet_induced {α β : Type*} {t : TopologicalSpace β} 
(f : α -> β) (s : Set α) : @nhdsSet α (t.induced f) s = comap f (𝓝ˢ (f '' s))
· 使用定理 `Filter.map_comap`：map_comap (f : Filter β) (m : α -> β) : (f.comap m).ma
p m = f ⊓ 𝓟 (range m)
· 使用定理 `nhdsSetWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s t : 
Set X), nhdsSetWithin s t = nhdsSet s ⊓ Filter.principal t
-/
lemma map_nhdsSet_induced_eq {α β : Type*} {t : TopologicalSpace β} {f : α → β} (s : Set α) :
    map f (@nhdsSet α (t.induced f) s) = 𝓝ˢ[range f] (f '' s) := by
  rw [nhdsSet_induced, Filter.map_comap, nhdsSetWithin]
/-
**Topology.IsInducing.map_nhdsSet_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.map_nhdsSet_eq {f : α -> β} (hf : IsInducing f) (s : S
et α) : (𝓝ˢ s).map f = 𝓝ˢ[range f] (f '' s)
参数：hf : IsInducing f；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `map_nhdsSet_induced_eq`：map_nhdsSet_induced_eq {α β : Type*} {t : Topolo
gicalSpace β} {f : α -> β} (s : Set α) : map f (@nhdsSet α (t.induced f) s) = 𝓝ˢ
[range f] (f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
-/
lemma Topology.IsInducing.map_nhdsSet_eq {f : α → β} (hf : IsInducing f) (s : Set α) :
    (𝓝ˢ s).map f = 𝓝ˢ[range f] (f '' s) :=
  hf.eq_induced ▸ map_nhdsSet_induced_eq s
/-
**map_nhdsSet_subtype_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_nhdsSet_subtype_val {s : Set α} (t : Set s) : map (↑) (𝓝ˢ t) = 𝓝ˢ[s] (
(↑) '' t)
参数：t : Set s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.map_nhdsSet_eq`：Topology.IsInducing.map_nhdsSet_eq {
f : α -> β} (hf : IsInducing f) (s : Set α) : (𝓝ˢ s).map f = 𝓝ˢ[range f] (f '' s
)
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
lemma map_nhdsSet_subtype_val {s : Set α} (t : Set s) :
    map (↑) (𝓝ˢ t) = 𝓝ˢ[s] ((↑) '' t) := by
  rw [IsInducing.subtypeVal.map_nhdsSet_eq, Subtype.range_val]
/-
**mem_nhdsSet_subtype_iff_nhdsSetWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nhdsSet_subtype_iff_nhdsSetWithin {s : Set α} {t u : Set s} : u in 𝓝ˢ 
t ↔ (↑) '' u in 𝓝ˢ[s] ((↑) '' t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `map_nhdsSet_subtype_val`：map_nhdsSet_subtype_val {s : Set α} (t : Set s)
 : map (↑) (𝓝ˢ t) = 𝓝ˢ[s] ((↑) '' t)
· 使用定理 `Filter.image_mem_map_iff`：image_mem_map_iff (hf : Injective m) : m '' s 
in map m f ↔ s in f
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_nhdsSet_subtype_iff_nhdsSetWithin {s : Set α} {t u : Set s} :
    u ∈ 𝓝ˢ t ↔ (↑) '' u ∈ 𝓝ˢ[s] ((↑) '' t) := by
  rw [← map_nhdsSet_subtype_val, image_mem_map_iff Subtype.val_injective]
