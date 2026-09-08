/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.SetAccumulate
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Ultrafilter
public import Mathlib.Topology.Defs.Ultrafilter

/-!
# Compact sets and compact spaces

## Main results

* `isCompact_univ_pi`: **Tychonov's theorem** - an arbitrary product of compact sets
  is compact.

* `isCompact_generateFrom`: **Alexander's subbasis theorem** - suppose `X` is a topological space
  with a subbasis `S` and `s` is a subset of `X`, then `s` is compact if for any open cover of `s`
  with all elements taken from `S`, there is a finite subcover.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace Function

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X} {f : X → Y}

-- compact sets
section Compact

/-
**IsCompact.exists_clusterPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.exists_clusterPt (hs : IsCompact s) {f : Filter X} [NeBot f] (hf
 : f <= 𝓟 s) : exists x in s, ClusterPt x f
参数：hs : IsCompact s；hf : f <= 𝓟 s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCompact.exists_clusterPt (hs : IsCompact s) {f : Filter X} [NeBot f] (hf : f ≤ 𝓟 s) :
    ∃ x ∈ s, ClusterPt x f := hs hf
/-
**IsCompact.exists_mapClusterPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.exists_mapClusterPt {ι : Type*} (hs : IsCompact s) {f : Filter ι
} [NeBot f] {u : ι -> X} (hf : Filter.map u f <= 𝓟 s) : exists x in s, MapCluste
rPt x f u
参数：hs : IsCompact s；hf : Filter.map u f <= 𝓟 s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCompact.exists_mapClusterPt {ι : Type*} (hs : IsCompact s) {f : Filter ι} [NeBot f]
    {u : ι → X} (hf : Filter.map u f ≤ 𝓟 s) :
    ∃ x ∈ s, MapClusterPt x f u := hs hf
/-
**IsCompact.exists_clusterPt_of_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.exists_clusterPt_of_frequently {l : Filter X} (hs : IsCompact s)
 (hl : existsᶠ x in l, x in s) : exists a in s, ClusterPt a l
参数：hs : IsCompact s；hl : existsᶠ x in l, x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.frequently_mem_iff_neBot`：frequently_mem_iff_neBot {l : Filter α}
 {s : Set α} : (existsᶠ x in l, x in s) ↔ NeBot (l ⊓ 𝓟 s)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
lemma IsCompact.exists_clusterPt_of_frequently {l : Filter X} (hs : IsCompact s)
    (hl : ∃ᶠ x in l, x ∈ s) : ∃ a ∈ s, ClusterPt a l :=
  let ⟨a, has, ha⟩ := @hs _ (frequently_mem_iff_neBot.mp hl) inf_le_right
  ⟨a, has, ha.mono inf_le_left⟩
/-
**IsCompact.exists_mapClusterPt_of_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.exists_mapClusterPt_of_frequently {l : Filter ι} {f : ι -> X} (h
s : IsCompact s) (hf : existsᶠ x in l, f x in s) : exists a in s, MapClusterPt a
 l f
参数：hs : IsCompact s；hf : existsᶠ x in l, f x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompact.exists_clusterPt_of_frequently`：IsCompact.exists_clusterPt_of_
frequently {l : Filter X} (hs : IsCompact s) (hl : existsᶠ x in l, x in s) : exi
sts a in s, ClusterPt a l
-/
lemma IsCompact.exists_mapClusterPt_of_frequently {l : Filter ι} {f : ι → X} (hs : IsCompact s)
    (hf : ∃ᶠ x in l, f x ∈ s) : ∃ a ∈ s, MapClusterPt a l f :=
  hs.exists_clusterPt_of_frequently hf

/-- The complement to a compact set belongs to a filter `f` if it belongs to each filter
`𝓝 x ⊓ f`, `x ∈ s`. -/
/-
**IsCompact.compl_mem_sets** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.compl_mem_sets (hs : IsCompact s) {f : Filter X} (hf : forall x 
in s, sᶜ in 𝓝 x ⊓ f) : sᶜ in f
参数：hs : IsCompact s；hf : forall x in s, sᶜ in 𝓝 x ⊓ f。
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
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
The complement to a compact set belongs to a filter `f` if it belongs to each fi
lter
`𝓝 x ⊓ f`, `x ∈ s`.
-/
theorem IsCompact.compl_mem_sets (hs : IsCompact s) {f : Filter X} (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) :
    sᶜ ∈ f := by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact @hs _ hf inf_le_right

/-- The complement to a compact set belongs to a filter `f` if each `x ∈ s` has a neighborhood `t`
within `s` such that `tᶜ` belongs to `f`. -/
/-
**IsCompact.compl_mem_sets_of_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.compl_mem_sets_of_nhdsWithin (hs : IsCompact s) {f : Filter X} (
hf : forall x in s, exists t in 𝓝[s] x, tᶜ in f) : sᶜ in f
参数：hs : IsCompact s；hf : forall x in s, exists t in 𝓝[s] x, tᶜ in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.compl_mem_sets`：IsCompact.compl_mem_sets (hs : IsCompact s) {f
 : Filter X} (hf : forall x in s, sᶜ in 𝓝 x ⊓ f) : sᶜ in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.mem_inf_principal`：mem_inf_principal {f : Filter α} {s t : Set α}
 : s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f
· 使用定理 `Filter.mem_inf_of_inter`：mem_inf_of_inter {f g : Filter α} {s t u : Set 
α} (hs : s in f) (ht : t in g) (h : s inter t subseteq u) : u in f ⊓ g

--- 原说明 ---
The complement to a compact set belongs to a filter `f` if each `x ∈ s` has a ne
ighborhood `t`
within `s` such that `tᶜ` belongs to `f`.
-/
theorem IsCompact.compl_mem_sets_of_nhdsWithin (hs : IsCompact s) {f : Filter X}
    (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine hs.compl_mem_sets fun x hx => ?_
  rcases hf x hx with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  rintro x ⟨h₁, h₂⟩ hs
  exact h₂ (h₁ hs)

/-- If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a compact set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
/-
**IsCompact.induction_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.induction_on (hs : IsCompact s) {p : Set X -> Prop} (he : p ∅) (
hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hunion : forall ⦃s t⦄, p s ->
 p t -> p (s union t)) (hnhds : forall x in s, exists t in 𝓝[s] x, p t) : p s
参数：hs : IsCompact s；he : p ∅；hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s；hu
nion : forall ⦃s t⦄, p s -> p t -> p (s union t)；hnhds : forall x in s, exists t
 in 𝓝[s] x, p t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.compl_mem_sets_of_nhdsWithin`：IsCompact.compl_mem_sets_of_nhds
Within (hs : IsCompact s) {f : Filter X} (hf : forall x in s, exists t in 𝓝[s] x
, tᶜ in f) : sᶜ in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a compact set `s` has a neighborhood `t` within `s` such that `p t`, then `
p s` holds.
-/
theorem IsCompact.induction_on (hs : IsCompact s) {p : Set X → Prop} (he : p ∅)
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s) (hunion : ∀ ⦃s t⦄, p s → p t → p (s ∪ t))
    (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter X := comk p he (fun _t ht _s hsub ↦ hmono hsub ht) (fun _s hs _t ht ↦ hunion hs ht)
  have : sᶜ ∈ f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using hnhds)
  rwa [← compl_compl s]

/-- The intersection of a compact set and a closed set is a compact set. -/
@[compactness .]
/-
**IsCompact.inter_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.inter_right (hs : IsCompact s) (ht : IsClosed t) : IsCompact (s 
inter t)
参数：hs : IsCompact s；ht : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `IsClosed.mem_of_nhdsWithin_neBot`：IsClosed.mem_of_nhdsWithin_neBot {s : 
Set α} (hs : IsClosed s) {x : α} (hx : NeBot <| 𝓝[s] x) : x in s
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
The intersection of a compact set and a closed set is a compact set.
-/
theorem IsCompact.inter_right (hs : IsCompact s) (ht : IsClosed t) : IsCompact (s ∩ t) := by
  intro f hnf hstf
  obtain ⟨x, hsx, hx⟩ : ∃ x ∈ s, ClusterPt x f :=
    hs (le_trans hstf (le_principal_iff.2 inter_subset_left))
  have : x ∈ t := ht.mem_of_nhdsWithin_neBot <|
    hx.mono <| le_trans hstf (le_principal_iff.2 inter_subset_right)
  exact ⟨x, ⟨hsx, this⟩, hx⟩

/-- The intersection of a closed set and a compact set is a compact set. -/
@[compactness .]
/-
**IsCompact.inter_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.inter_left (ht : IsCompact t) (hs : IsClosed s) : IsCompact (s i
nter t)
参数：ht : IsCompact t；hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
The intersection of a closed set and a compact set is a compact set.
-/
theorem IsCompact.inter_left (ht : IsCompact t) (hs : IsClosed s) : IsCompact (s ∩ t) :=
  inter_comm t s ▸ ht.inter_right hs

/-- The set difference of a compact set and an open set is a compact set. -/
@[compactness .]
/-
**IsCompact.diff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCompact (s \ t)
参数：hs : IsCompact s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s

--- 原说明 ---
The set difference of a compact set and an open set is a compact set.
-/
theorem IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCompact (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)

/-- A closed subset of a compact set is a compact set. -/
/-
**IsCompact.of_isClosed_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.of_isClosed_subset (hs : IsCompact s) (ht : IsClosed t) (h : t s
ubseteq s) : IsCompact t
参数：hs : IsCompact s；ht : IsClosed t；h : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t

--- 原说明 ---
A closed subset of a compact set is a compact set.
-/
theorem IsCompact.of_isClosed_subset (hs : IsCompact s) (ht : IsClosed t) (h : t ⊆ s) :
    IsCompact t :=
  inter_eq_self_of_subset_right h ▸ hs.inter_right ht

@[compactness .]
/-
**IsCompact.image_of_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.image_of_continuousOn {f : X -> Y} (hs : IsCompact s) (hf : Cont
inuousOn f s) : IsCompact (f '' s)
参数：hs : IsCompact s；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_inf_principal_neBot_of_image_mem`：comap_inf_principal_neBot
_of_image_mem {f : Filter β} {m : α -> β} (hf : NeBot f) {s : Set α} (hs : m '' 
s in f) : NeBot (comap m f ⊓ 𝓟 s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `ClusterPt.neBot`：ClusterPt.neBot {F : Filter X} (h : ClusterPt x F) : Ne
Bot (𝓝 x ⊓ F)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `Filter.Tendsto.neBot`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : F
ilter α} {y : Filter β},   Filter.Tendsto f x y → ∀ [hx : x.NeBot], y.NeBot
-/
theorem IsCompact.image_of_continuousOn {f : X → Y} (hs : IsCompact s) (hf : ContinuousOn f s) :
    IsCompact (f '' s) := by
  intro l lne ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this inf_le_right
  have := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert! (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot
/-
**IsCompact.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : Continuous f) : IsCo
mpact (f '' s)
参数：hs : IsCompact s；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem IsCompact.image {f : X → Y} (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn
/-
**IsCompact.adherence_nhdset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.adherence_nhdset {f : Filter X} (hs : IsCompact s) (hf₂ : f <= 𝓟
 s) (ht₁ : IsOpen t) (ht₂ : forall x in s, ClusterPt x f -> x in t) : t in f
参数：hs : IsCompact s；hf₂ : f <= 𝓟 s；ht₁ : IsOpen t；ht₂ : forall x in s, ClusterPt
 x f -> x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.by_cases`：∀ {p q : Prop}, (p → q) → (¬p → q) → q
· 使用定理 `Filter.mem_of_eq_bot`：mem_of_eq_bot {f : Filter α} {s : Set α} (h : f ⊓ 
𝓟 sᶜ = ⊥) : s in f
· 使用定理 `inf_le_of_left_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α},
 a ≤ c → a ⊓ b ≤ c
· 使用定理 `ClusterPt.of_inf_left`：ClusterPt.of_inf_left {f g : Filter X} (H : Clust
erPt x <| f ⊓ g) : ClusterPt x f
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
· 使用定理 `ClusterPt.of_inf_right`：ClusterPt.of_inf_right {f g : Filter X} (H : Clu
sterPt x <| f ⊓ g) : ClusterPt x g
-/
theorem IsCompact.adherence_nhdset {f : Filter X} (hs : IsCompact s) (hf₂ : f ≤ 𝓟 s)
    (ht₁ : IsOpen t) (ht₂ : ∀ x ∈ s, ClusterPt x f → x ∈ t) : t ∈ f :=
  Classical.by_cases mem_of_eq_bot fun (this : f ⊓ 𝓟 tᶜ ≠ ⊥) =>
    let ⟨x, hx, (hfx : ClusterPt x <| f ⊓ 𝓟 tᶜ)⟩ := @hs _ ⟨this⟩ <| inf_le_of_left_le hf₂
    have : x ∈ t := ht₂ x hx hfx.of_inf_left
    have : tᶜ ∩ t ∈ 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (IsOpen.mem_nhds ht₁ this)
    have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 <| compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x ≠ ⊥ := hfx.of_inf_right.ne
    absurd A this
/-
**isCompact_iff_ultrafilter_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_iff_ultrafilter_le_nhds : IsCompact s ↔ forall f : Ultrafilter X
, ↑f <= 𝓟 s -> exists x in s, ↑f <= 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.forall_neBot_le_iff`：forall_neBot_le_iff {g : Filter α} {p : Filt
er α -> Prop} (hp : Monotone p) : (forall f : Filter α, NeBot f -> f <= g -> p f
) ↔ forall f : U…
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCompact_iff_ultrafilter_le_nhds :
    IsCompact s ↔ ∀ f : Ultrafilter X, ↑f ≤ 𝓟 s → ∃ x ∈ s, ↑f ≤ 𝓝 x := by
  refine (forall_neBot_le_iff ?_).trans ?_
  · rintro f g hle ⟨x, hxs, hxf⟩
    exact ⟨x, hxs, hxf.mono hle⟩
  · simp only [Ultrafilter.clusterPt_iff]

alias ⟨IsCompact.ultrafilter_le_nhds, _⟩ := isCompact_iff_ultrafilter_le_nhds
/-
**isCompact_iff_ultrafilter_le_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_iff_ultrafilter_le_nhds' : IsCompact s ↔ forall f : Ultrafilter 
X, s in f -> exists x in s, ↑f <= 𝓝 x
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
theorem isCompact_iff_ultrafilter_le_nhds' :
    IsCompact s ↔ ∀ f : Ultrafilter X, s ∈ f → ∃ x ∈ s, ↑f ≤ 𝓝 x := by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff, Ultrafilter.mem_coe]

alias ⟨IsCompact.ultrafilter_le_nhds', _⟩ := isCompact_iff_ultrafilter_le_nhds'

/-- If a compact set belongs to a filter and all cluster points in this set and in the filter
lie in a set `s'` then the filter is less than or equal to `𝓝ˢ s'`. -/
/-
**IsCompact.le_nhdsSet_of_clusterPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.le_nhdsSet_of_clusterPt (hs : IsCompact s) {l : Filter X} {s' : 
Set X} (hmem : s in l) (h : forall x in s, ClusterPt x l -> x in s') : l <= 𝓝ˢ s
'
参数：hs : IsCompact s；hmem : s in l；h : forall x in s, ClusterPt x l -> x in s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_iff_ultrafilter`：le_iff_ultrafilter {f₁ f₂ : Filter α} : f₁ <=
 f₂ ↔ forall g : Ultrafilter α, ↑g <= f₁ -> ↑g <= f₂
· 使用定理 `IsCompact.ultrafilter_le_nhds'`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s : Set X},   IsCompact s → ∀ (f : Ultrafilter X), s ∈ f → ∃ x ∈ s, ↑f ≤ nhd
s x
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `nhds_le_nhdsSet`：nhds_le_nhdsSet (h : x in s) : 𝓝 x <= 𝓝ˢ s
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `ClusterPt.of_le_nhds`：ClusterPt.of_le_nhds {f : Filter X} (H : f <= 𝓝 x)
 [NeBot f] : ClusterPt x f

--- 原说明 ---
If a compact set belongs to a filter and all cluster points in this set and in t
he filter
lie in a set `s'` then the filter is less than or equal to `𝓝ˢ s'`.
-/
lemma IsCompact.le_nhdsSet_of_clusterPt (hs : IsCompact s) {l : Filter X} {s' : Set X}
    (hmem : s ∈ l) (h : ∀ x ∈ s, ClusterPt x l → x ∈ s') : l ≤ 𝓝ˢ s' := by
  refine le_iff_ultrafilter.2 fun f hf ↦ ?_
  rcases hs.ultrafilter_le_nhds' f (hf hmem) with ⟨x, hxs, hx⟩
  grw [hx]
  refine nhds_le_nhdsSet ?_
  exact h x hxs (.mono (.of_le_nhds hx) hf)

/-- If a compact set belongs to a filter and this filter has a unique cluster point `y` in this set,
then the filter is less than or equal to `𝓝 y`. -/
/-
**IsCompact.le_nhds_of_unique_clusterPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.le_nhds_of_unique_clusterPt (hs : IsCompact s) {l : Filter X} {y
 : X} (hmem : s in l) (h : forall x in s, ClusterPt x l -> x = y) : l <= 𝓝 y
参数：hs : IsCompact s；hmem : s in l；h : forall x in s, ClusterPt x l -> x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用引理 `IsCompact.le_nhdsSet_of_clusterPt`：IsCompact.le_nhdsSet_of_clusterPt (hs
 : IsCompact s) {l : Filter X} {s' : Set X} (hmem : s in l) (h : forall x in s, 
ClusterPt x l -> x in s…

--- 原说明 ---
If a compact set belongs to a filter and this filter has a unique cluster point 
`y` in this set,
then the filter is less than or equal to `𝓝 y`.
-/
lemma IsCompact.le_nhds_of_unique_clusterPt (hs : IsCompact s) {l : Filter X} {y : X}
    (hmem : s ∈ l) (h : ∀ x ∈ s, ClusterPt x l → x = y) : l ≤ 𝓝 y := by
  rw [← nhdsSet_singleton]
  exact hs.le_nhdsSet_of_clusterPt hmem h

/-- If values of `f : Y → X` belong to a compact set `s` eventually along a filter `l`
and `s'` is the set of `MapClusterPt` for `f` along `l` in `s`,
then `f` tends to `𝓝ˢ s'` along `l`. -/
/-
**IsCompact.tendsto_nhdsSet_of_mapClusterPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.tendsto_nhdsSet_of_mapClusterPt {Y} {l : Filter Y} {s' : Set X} 
{f : Y -> X} (hs : IsCompact s) (hmem : forallᶠ x in l, f x in s) (h : forall x 
in s, MapClusterPt x l f -> x in s') : Tendsto f l (𝓝ˢ s')
参数：hs : IsCompact s；hmem : forallᶠ x in l, f x in s；h : forall x in s, MapCluste
rPt x l f -> x in s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompact.le_nhdsSet_of_clusterPt`：IsCompact.le_nhdsSet_of_clusterPt (hs
 : IsCompact s) {l : Filter X} {s' : Set X} (hmem : s in l) (h : forall x in s, 
ClusterPt x l -> x in s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f

--- 原说明 ---
If values of `f : Y → X` belong to a compact set `s` eventually along a filter `
l`
and `s'` is the set of `MapClusterPt` for `f` along `l` in `s`,
then `f` tends to `𝓝ˢ s'` along `l`.
-/
lemma IsCompact.tendsto_nhdsSet_of_mapClusterPt {Y} {l : Filter Y} {s' : Set X} {f : Y → X}
    (hs : IsCompact s) (hmem : ∀ᶠ x in l, f x ∈ s) (h : ∀ x ∈ s, MapClusterPt x l f → x ∈ s') :
    Tendsto f l (𝓝ˢ s') :=
  hs.le_nhdsSet_of_clusterPt (mem_map.2 hmem) h

/-- If values of `f : Y → X` belong to a compact set `s` eventually along a filter `l`
and `y` is a unique `MapClusterPt` for `f` along `l` in `s`,
then `f` tends to `𝓝 y` along `l`. -/
/-
**IsCompact.tendsto_nhds_of_unique_mapClusterPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.tendsto_nhds_of_unique_mapClusterPt {Y} {l : Filter Y} {y : X} {
f : Y -> X} (hs : IsCompact s) (hmem : forallᶠ x in l, f x in s) (h : forall x i
n s, MapClusterPt x l f -> x = y) : Tendsto f l (𝓝 y)
参数：hs : IsCompact s；hmem : forallᶠ x in l, f x in s；h : forall x in s, MapCluste
rPt x l f -> x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用引理 `IsCompact.tendsto_nhdsSet_of_mapClusterPt`：IsCompact.tendsto_nhdsSet_of_
mapClusterPt {Y} {l : Filter Y} {s' : Set X} {f : Y -> X} (hs : IsCompact s) (hm
em : forallᶠ x in l, f x in s) …

--- 原说明 ---
If values of `f : Y → X` belong to a compact set `s` eventually along a filter `
l`
and `y` is a unique `MapClusterPt` for `f` along `l` in `s`,
then `f` tends to `𝓝 y` along `l`.
-/
lemma IsCompact.tendsto_nhds_of_unique_mapClusterPt {Y} {l : Filter Y} {y : X} {f : Y → X}
    (hs : IsCompact s) (hmem : ∀ᶠ x in l, f x ∈ s) (h : ∀ x ∈ s, MapClusterPt x l f → x = y) :
    Tendsto f l (𝓝 y) := by
  rw [← nhdsSet_singleton]
  exact hs.tendsto_nhdsSet_of_mapClusterPt hmem h

/-- For every open directed cover of a compact set, there exists a single element of the
cover which itself includes the set. -/
/-
**IsCompact.elim_directed_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.elim_directed_cover {ι : Type v} [hι : Nonempty ι] (hs : IsCompa
ct s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s subseteq ⋃ i, U i
) (hdU : Directed (· subseteq ·) U) : exists i, s subseteq U i
参数：hs : IsCompact s；U : ι -> Set X；hUo : forall i, IsOpen (U i)；hsU : s subseteq
 ⋃ i, U i；hdU : Directed (· subseteq ·) U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a

--- 原说明 ---
For every open directed cover of a compact set, there exists a single element of
 the
cover which itself includes the set.
-/
theorem IsCompact.elim_directed_cover {ι : Type v} [hι : Nonempty ι] (hs : IsCompact s)
    (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) (hdU : Directed (· ⊆ ·) U) :
    ∃ i, s ⊆ U i :=
  hι.elim fun i₀ =>
    IsCompact.induction_on hs ⟨i₀, empty_subset _⟩ (fun _ _ hs ⟨i, hi⟩ => ⟨i, hs.trans hi⟩)
      (fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ =>
        let ⟨k, hki, hkj⟩ := hdU i j
        ⟨k, union_subset (Subset.trans hi hki) (Subset.trans hj hkj)⟩)
      fun _x hx =>
      let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
      ⟨U i, mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (hUo i) hi), i, Subset.refl _⟩

/-- For every open cover of a compact set, there exists a finite subcover. -/
/-
**IsCompact.elim_finite_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.elim_finite_subcover {ι : Type v} (hs : IsCompact s) (U : ι -> S
et X) (hUo : forall i, IsOpen (U i)) (hsU : s subseteq ⋃ i, U i) : exists t : Fi
nset ι, s subseteq ⋃ i in t, U i
参数：hs : IsCompact s；U : ι -> Set X；hUo : forall i, IsOpen (U i)；hsU : s subseteq
 ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_directed_cover`：IsCompact.elim_directed_cover {ι : Type v
} [hι : Nonempty ι] (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen 
(U i)) (hsU : s sub…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `Set.iUnion_eq_iUnion_finset`：iUnion_eq_iUnion_finset (s : ι -> Set α) : 
⋃ i, s i = ⋃ t : Finset ι, ⋃ i in t, s i
· 使用定理 `directed_of_isDirected_le`：directed_of_isDirected_le [LE α] [IsDirectedO
rder α] {f : α -> β} {r : β -> β -> Prop} (H : forall ⦃i j⦄, i <= j -> r (f i) (
f j)) : Directe…
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x

--- 原说明 ---
For every open cover of a compact set, there exists a finite subcover.
-/
theorem IsCompact.elim_finite_subcover {ι : Type v} (hs : IsCompact s) (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hsU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)
/-
**IsCompact.elim_nhds_subcover_nhdsSet'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.elim_nhds_subcover_nhdsSet' (hs : IsCompact s) (U : forall x in 
s, Set X) (hU : forall x hx, U x hx in 𝓝 x) : exists t : Finset s, (⋃ x in t, U 
x.1 x.2) in 𝓝ˢ s
参数：hs : IsCompact s；U : forall x in s, Set X；hU : forall x hx, U x hx in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
-/
lemma IsCompact.elim_nhds_subcover_nhdsSet' (hs : IsCompact s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x hx, U x hx ∈ 𝓝 x) : ∃ t : Finset s, (⋃ x ∈ t, U x.1 x.2) ∈ 𝓝ˢ s := by
  rcases hs.elim_finite_subcover (fun x : s ↦ interior (U x x.2)) (fun _ ↦ isOpen_interior)
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 <| hU _ _⟩ with ⟨t, hst⟩
  refine ⟨t, mem_nhdsSet_iff_forall.2 fun x hx ↦ ?_⟩
  rcases mem_iUnion₂.1 (hst hx) with ⟨y, hyt, hy⟩
  refine mem_of_superset ?_ (subset_biUnion_of_mem hyt)
  exact mem_interior_iff_mem_nhds.1 hy
/-
**IsCompact.elim_nhds_subcover_nhdsSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.elim_nhds_subcover_nhdsSet (hs : IsCompact s) {U : X -> Set X} (
hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (forall x in t, x in s) ∧
 (⋃ x in t, U x) in 𝓝ˢ s
参数：hs : IsCompact s；hU : forall x in s, U x in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompact.elim_nhds_subcover_nhdsSet'`：IsCompact.elim_nhds_subcover_nhds
Set' (hs : IsCompact s) (U : forall x in s, Set X) (hU : forall x hx, U x hx in 
𝓝 x) : exists t : Finset s,…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.set_biUnion_finset_image`：set_biUnion_finset_image {f : γ -> α} {
g : α -> Set β} {s : Finset γ} : ⋃ x in s.image f, g x = ⋃ y in s, g (f y)
-/
lemma IsCompact.elim_nhds_subcover_nhdsSet (hs : IsCompact s) {U : X → Set X}
    (hU : ∀ x ∈ s, U x ∈ 𝓝 x) : ∃ t : Finset X, (∀ x ∈ t, x ∈ s) ∧ (⋃ x ∈ t, U x) ∈ 𝓝ˢ s := by
  let ⟨t, ht⟩ := hs.elim_nhds_subcover_nhdsSet' (fun x _ => U x) hU
  classical
  exact ⟨t.image (↑), fun x hx =>
    let ⟨y, _, hyx⟩ := Finset.mem_image.1 hx
    hyx ▸ y.2,
    by rwa [Finset.set_biUnion_finset_image]⟩
/-
**IsCompact.elim_nhds_subcover'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.elim_nhds_subcover' (hs : IsCompact s) (U : forall x in s, Set X
) (hU : forall x (hx : x in s), U x ‹x in s› in 𝓝 x) : exists t : Finset s, s su
bseteq ⋃ x in t, U (x : s) x.2
参数：hs : IsCompact s；U : forall x in s, Set X；hU : forall x (hx : x in s), U x ‹x
 in s› in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `subset_of_mem_nhdsSet`：subset_of_mem_nhdsSet (h : t in 𝓝ˢ s) : s subsete
q t
· 使用引理 `IsCompact.elim_nhds_subcover_nhdsSet'`：IsCompact.elim_nhds_subcover_nhds
Set' (hs : IsCompact s) (U : forall x in s, Set X) (hU : forall x hx, U x hx in 
𝓝 x) : exists t : Finset s,…
-/
theorem IsCompact.elim_nhds_subcover' (hs : IsCompact s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x (hx : x ∈ s), U x ‹x ∈ s› ∈ 𝓝 x) : ∃ t : Finset s, s ⊆ ⋃ x ∈ t, U (x : s) x.2 :=
  (hs.elim_nhds_subcover_nhdsSet' U hU).imp fun _ ↦ subset_of_mem_nhdsSet
/-
**IsCompact.elim_nhds_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.elim_nhds_subcover (hs : IsCompact s) (U : X -> Set X) (hU : for
all x in s, U x in 𝓝 x) : exists t : Finset X, (forall x in t, x in s) ∧ s subse
teq ⋃ x in t, U x
参数：hs : IsCompact s；U : X -> Set X；hU : forall x in s, U x in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `subset_of_mem_nhdsSet`：subset_of_mem_nhdsSet (h : t in 𝓝ˢ s) : s subsete
q t
· 使用引理 `IsCompact.elim_nhds_subcover_nhdsSet`：IsCompact.elim_nhds_subcover_nhdsS
et (hs : IsCompact s) {U : X -> Set X} (hU : forall x in s, U x in 𝓝 x) : exists
 t : Finset X, (forall x i…
-/
theorem IsCompact.elim_nhds_subcover (hs : IsCompact s) (U : X → Set X) (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ t : Finset X, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x :=
  (hs.elim_nhds_subcover_nhdsSet hU).imp fun _ h ↦ h.imp_right subset_of_mem_nhdsSet
/-
**IsCompact.elim_nhdsWithin_subcover'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.elim_nhdsWithin_subcover' (hs : IsCompact s) (U : forall x in s,
 Set X) (hU : forall x (hx : x in s), U x hx in 𝓝[s] x) : exists t : Finset s, s
 subseteq ⋃ x in t, U x x.2
参数：hs : IsCompact s；U : forall x in s, Set X；hU : forall x (hx : x in s), U x hx
 in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsCompact.elim_nhds_subcover'`：IsCompact.elim_nhds_subcover' (hs : IsCom
pact s) (U : forall x in s, Set X) (hU : forall x (hx : x in s), U x ‹x in s› in
 𝓝 x) : exists t : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem IsCompact.elim_nhdsWithin_subcover' (hs : IsCompact s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x (hx : x ∈ s), U x hx ∈ 𝓝[s] x) : ∃ t : Finset s, s ⊆ ⋃ x ∈ t, U x x.2 := by
  choose V V_nhds hV using fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hU x hx)
  refine (hs.elim_nhds_subcover' V V_nhds).imp fun t ht =>
    subset_trans ?_ (iUnion₂_mono fun x _ => hV x x.2)
  simpa [← iUnion_inter, ← iUnion_coe_set]
/-
**IsCompact.elim_nhdsWithin_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.elim_nhdsWithin_subcover (hs : IsCompact s) (U : X -> Set X) (hU
 : forall x in s, U x in 𝓝[s] x) : exists t : Finset X, (forall x in t, x in s) 
∧ s subseteq ⋃ x in t, U x
参数：hs : IsCompact s；U : X -> Set X；hU : forall x in s, U x in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem IsCompact.elim_nhdsWithin_subcover (hs : IsCompact s) (U : X → Set X)
    (hU : ∀ x ∈ s, U x ∈ 𝓝[s] x) : ∃ t : Finset X, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x := by
  choose! V V_nhds hV using fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hU x hx)
  refine (hs.elim_nhds_subcover V V_nhds).imp fun t ⟨t_sub_s, ht⟩ =>
    ⟨t_sub_s, subset_trans ?_ (iUnion₂_mono fun x hx => hV x (t_sub_s x hx))⟩
  simpa [← iUnion_inter]

/-- The neighborhood filter of a compact set is disjoint with a filter `l` if and only if the
neighborhood filter of each point of this set is disjoint with `l`. -/
/-
**IsCompact.disjoint_nhdsSet_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.disjoint_nhdsSet_left {l : Filter X} (hs : IsCompact s) : Disjoi
nt (𝓝ˢ s) l ↔ forall x in s, Disjoint (𝓝 x) l
参数：hs : IsCompact s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `nhds_le_nhdsSet`：nhds_le_nhdsSet (h : x in s) : 𝓝 x <= 𝓝ˢ s
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.disjoint_iff_left`：∀ {α : Type u_1} {ι : Sort u_4} {l l'
 : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l l' ↔
 ∃ i, p i ∧ (s i)ᶜ ∈ l'…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iUnion₂`：compl_iUnion₂ (s : forall i, κ i -> Set α) : (⋃ (i) (
j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ
· 使用定理 `Filter.biInter_finset_mem`：biInter_finset_mem {β : Type v} {s : β -> Set
 α} (is : Finset β) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The neighborhood filter of a compact set is disjoint with a filter `l` if and on
ly if the
neighborhood filter of each point of this set is disjoint with `l`.
-/
theorem IsCompact.disjoint_nhdsSet_left {l : Filter X} (hs : IsCompact s) :
    Disjoint (𝓝ˢ s) l ↔ ∀ x ∈ s, Disjoint (𝓝 x) l := by
  refine ⟨fun h x hx => h.mono_left <| nhds_le_nhdsSet hx, fun H => ?_⟩
  choose! U hxU hUl using fun x hx => (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx => (hUo x hx).mem_nhds (hxU x hx) with ⟨t, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x ∈ t, U x, ⟨isOpen_biUnion fun x hx => hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂, biInter_finset_mem]
  exact fun x hx => hUl x (hts x hx)

/-- A filter `l` is disjoint with the neighborhood filter of a compact set if and only if it is
disjoint with the neighborhood filter of each point of this set. -/
/-
**IsCompact.disjoint_nhdsSet_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.disjoint_nhdsSet_right {l : Filter X} (hs : IsCompact s) : Disjo
int l (𝓝ˢ s) ↔ forall x in s, Disjoint l (𝓝 x)
参数：hs : IsCompact s。
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
· 使用定理 `IsCompact.disjoint_nhdsSet_left`：IsCompact.disjoint_nhdsSet_left {l : Fi
lter X} (hs : IsCompact s) : Disjoint (𝓝ˢ s) l ↔ forall x in s, Disjoint (𝓝 x) l

--- 原说明 ---
A filter `l` is disjoint with the neighborhood filter of a compact set if and on
ly if it is
disjoint with the neighborhood filter of each point of this set.
-/
theorem IsCompact.disjoint_nhdsSet_right {l : Filter X} (hs : IsCompact s) :
    Disjoint l (𝓝ˢ s) ↔ ∀ x ∈ s, Disjoint l (𝓝 x) := by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

-- TODO: reformulate using `Disjoint`
/-- For every directed family of closed sets whose intersection avoids a compact set,
there exists a single element of the family which itself avoids this compact set. -/
/-
**IsCompact.elim_directed_family_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.elim_directed_family_closed {ι : Type v} [Nonempty ι] (hs : IsCo
mpact s) (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst : (s inter ⋂ i, 
t i) = ∅) (hdt : Directed (· ⊇ ·) t) : exists i : ι, s inter t i = ∅
参数：hs : IsCompact s；t : ι -> Set X；htc : forall i, IsClosed (t i)；hst : (s inter
 ⋂ i, t i) = ∅；hdt : Directed (· ⊇ ·) t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_directed_cover`：IsCompact.elim_directed_cover {ι : Type v
} [hι : Nonempty ι] (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen 
(U i)) (hsU : s sub…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Directed.mono_comp`：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β 
-> β -> Prop} {g : α -> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g
 y)) (hf…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s

--- 原说明 ---
For every directed family of closed sets whose intersection avoids a compact set
,
there exists a single element of the family which itself avoids this compact set
.
-/
theorem IsCompact.elim_directed_family_closed {ι : Type v} [Nonempty ι] (hs : IsCompact s)
    (t : ι → Set X) (htc : ∀ i, IsClosed (t i)) (hst : (s ∩ ⋂ i, t i) = ∅)
    (hdt : Directed (· ⊇ ·) t) : ∃ i : ι, s ∩ t i = ∅ :=
  let ⟨t, ht⟩ :=
    hs.elim_directed_cover (compl ∘ t) (fun i => (htc i).isOpen_compl)
      (by
        simpa only [subset_def, not_forall, eq_empty_iff_forall_notMem, mem_iUnion, exists_prop,
          mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using! hst)
      (hdt.mono_comp _ fun _ _ => compl_subset_compl.mpr)
  ⟨t, by
    simpa only [subset_def, not_forall, eq_empty_iff_forall_notMem, mem_iUnion, exists_prop,
      mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using! ht⟩

-- TODO: reformulate using `Disjoint`
/-- For every family of closed sets whose intersection avoids a compact set,
there exists a finite subfamily whose intersection avoids this compact set. -/
/-
**IsCompact.elim_finite_subfamily_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.elim_finite_subfamily_closed {ι : Type v} (hs : IsCompact s) (t 
: ι -> Set X) (htc : forall i, IsClosed (t i)) (hst : (s inter ⋂ i, t i) = ∅) : 
exists u : Finset ι, (s inter ⋂ i in u, t i) = ∅
参数：hs : IsCompact s；t : ι -> Set X；htc : forall i, IsClosed (t i)；hst : (s inter
 ⋂ i, t i) = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_directed_family_closed`：IsCompact.elim_directed_family_cl
osed {ι : Type v} [Nonempty ι] (hs : IsCompact s) (t : ι -> Set X) (htc : forall
 i, IsClosed (t i)) (hst : …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iInter_eq_iInter_finset`：iInter_eq_iInter_finset (s : ι -> Set α) : 
⋂ i, s i = ⋂ t : Finset ι, ⋂ i in t, s i
· 使用定理 `directed_of_isDirected_le`：directed_of_isDirected_le [LE α] [IsDirectedO
rder α] {f : α -> β} {r : β -> β -> Prop} (H : forall ⦃i j⦄, i <= j -> r (f i) (
f j)) : Directe…
· 使用定理 `Set.biInter_subset_biInter_left`：biInter_subset_biInter_left {s s' : Set
 α} {t : α -> Set β} (h : s' subseteq s) : ⋂ x in s, t x subseteq ⋂ x in s', t x

--- 原说明 ---
For every family of closed sets whose intersection avoids a compact set,
there exists a finite subfamily whose intersection avoids this compact set.
-/
theorem IsCompact.elim_finite_subfamily_closed {ι : Type v} (hs : IsCompact s)
    (t : ι → Set X) (htc : ∀ i, IsClosed (t i)) (hst : (s ∩ ⋂ i, t i) = ∅) :
    ∃ u : Finset ι, (s ∩ ⋂ i ∈ u, t i) = ∅ :=
  hs.elim_directed_family_closed _ (fun _ ↦ isClosed_biInter fun _ _ ↦ htc _)
    (by rwa [← iInter_eq_iInter_finset])
    (directed_of_isDirected_le fun _ _ h ↦ biInter_subset_biInter_left h)

/-- To show that a compact set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every finite subfamily. -/
/-
**IsCompact.inter_iInter_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.inter_iInter_nonempty {ι : Type v} (hs : IsCompact s) (t : ι -> 
Set X) (htc : forall i, IsClosed (t i)) (hst : forall u : Finset ι, (s inter ⋂ i
 in u, t i).Nonempty) : (s inter ⋂ i, t i).Nonempty
参数：hs : IsCompact s；t : ι -> Set X；htc : forall i, IsClosed (t i)；hst : forall u
 : Finset ι, (s inter ⋂ i in u, t i).Nonempty。
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
· 使用定理 `IsCompact.elim_finite_subfamily_closed`：IsCompact.elim_finite_subfamily_
closed {ι : Type v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClose
d (t i)) (hst : (s inter ⋂ i…

--- 原说明 ---
To show that a compact set intersects the intersection of a family of closed set
s,
  it is sufficient to show that it intersects every finite subfamily.
-/
theorem IsCompact.inter_iInter_nonempty {ι : Type v} (hs : IsCompact s) (t : ι → Set X)
    (htc : ∀ i, IsClosed (t i)) (hst : ∀ u : Finset ι, (s ∩ ⋂ i ∈ u, t i).Nonempty) :
    (s ∩ ⋂ i, t i).Nonempty := by
  contrapose! hst
  exact hs.elim_finite_subfamily_closed t htc hst
/-
**IsCompact.nonempty_inter_sInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.nonempty_inter_sInter (hs : IsCompact s) {t : Set (Set X)} (ht :
 forall a in t, IsClosed a) (h : forall a subseteq t, a.Finite -> (s inter ⋂₀ a)
.Nonempty) : (s inter ⋂₀ t).Nonempty
参数：hs : IsCompact s；Set X；ht : forall a in t, IsClosed a；h : forall a subseteq t
, a.Finite -> (s inter ⋂₀ a).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_iInter`：sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : 
s, i
· 使用定理 `IsCompact.inter_iInter_nonempty`：IsCompact.inter_iInter_nonempty {ι : Ty
pe v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst 
: forall u : Finset ι…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
lemma IsCompact.nonempty_inter_sInter (hs : IsCompact s) {t : Set (Set X)}
    (ht : ∀ a ∈ t, IsClosed a) (h : ∀ a ⊆ t, a.Finite → (s ∩ ⋂₀ a).Nonempty) :
    (s ∩ ⋂₀ t).Nonempty := by
  rw [Set.sInter_eq_iInter]
  refine hs.inter_iInter_nonempty _ (fun i ↦ ht _ i.2) fun a ↦ ?_
  simpa using h (Subtype.val '' (a : Set t)) (by simp) (a.finite_toSet.image _)
/-
**CompactSpace.nonempty_sInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompactSpace.nonempty_sInter [CompactSpace X] {s : Set (Set X)} (hsc : for
all t in s, IsClosed t) (hs : forall t subseteq s, t.Finite -> (⋂₀ t).Nonempty) 
: (⋂₀ s).Nonempty
参数：Set X；hsc : forall t in s, IsClosed t；hs : forall t subseteq s, t.Finite -> (
⋂₀ t).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用引理 `IsCompact.nonempty_inter_sInter`：IsCompact.nonempty_inter_sInter (hs : I
sCompact s) {t : Set (Set X)} (ht : forall a in t, IsClosed a) (h : forall a sub
seteq t, a.Finite -> …
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma CompactSpace.nonempty_sInter [CompactSpace X] {s : Set (Set X)} (hsc : ∀ t ∈ s, IsClosed t)
    (hs : ∀ t ⊆ s, t.Finite → (⋂₀ t).Nonempty) : (⋂₀ s).Nonempty := by
  simpa using isCompact_univ.nonempty_inter_sInter hsc (by simpa using hs)

/-- Cantor's intersection theorem for `iInter`:
the intersection of a directed family of nonempty compact closed sets is nonempty. -/
/-
**IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Typ
e v} [hι : Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t) (htn : forall
 i, (t i).Nonempty) (htc : forall i, IsCompact (t i)) (htcl : forall i, IsClosed
 (t i)) : (⋂ i, t i).Nonempty
参数：t : ι -> Set X；htd : Directed (· ⊇ ·) t；htn : forall i, (t i).Nonempty；htc : 
forall i, IsCompact (t i)；htcl : forall i, IsClosed (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `IsCompact.elim_directed_family_closed`：IsCompact.elim_directed_family_cl
osed {ι : Type v} [Nonempty ι] (hs : IsCompact s) (t : ι -> Set X) (htc : forall
 i, IsClosed (t i)) (hst : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i

--- 原说明 ---
Cantor's intersection theorem for `iInter`:
the intersection of a directed family of nonempty compact closed sets is nonempt
y.
-/
theorem IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    {ι : Type v} [hι : Nonempty ι] (t : ι → Set X) (htd : Directed (· ⊇ ·) t)
    (htn : ∀ i, (t i).Nonempty) (htc : ∀ i, IsCompact (t i)) (htcl : ∀ i, IsClosed (t i)) :
    (⋂ i, t i).Nonempty := by
  let i₀ := hι.some
  suffices (t i₀ ∩ ⋂ i, t i).Nonempty by
    rwa [inter_eq_right.mpr (iInter_subset _ i₀)] at this
  simp only [nonempty_iff_ne_empty] at htn ⊢
  apply mt ((htc i₀).elim_directed_family_closed t htcl)
  push Not
  simp only [← nonempty_iff_ne_empty] at htn ⊢
  refine ⟨htd, fun i => ?_⟩
  rcases htd i₀ i with ⟨j, hji₀, hji⟩
  exact (htn j).mono (subset_inter hji₀ hji)

/-- Cantor's intersection theorem for `sInter`:
the intersection of a directed family of nonempty compact closed sets is nonempty. -/
/-
**IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed {S : Set
 (Set X)} [hS : Nonempty S] (hSd : DirectedOn (· ⊇ ·) S) (hSn : forall U in S, U
.Nonempty) (hSc : forall U in S, IsCompact U) (hScl : forall U in S, IsClosed U)
 : (⋂₀ S).Nonempty
参数：Set X；hSd : DirectedOn (· ⊇ ·) S；hSn : forall U in S, U.Nonempty；hSc : forall
 U in S, IsCompact U；hScl : forall U in S, IsClosed U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_iInter`：sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : 
s, i
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Cantor's intersection theorem for `sInter`:
the intersection of a directed family of nonempty compact closed sets is nonempt
y.
-/
theorem IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    {S : Set (Set X)} [hS : Nonempty S] (hSd : DirectedOn (· ⊇ ·) S) (hSn : ∀ U ∈ S, U.Nonempty)
    (hSc : ∀ U ∈ S, IsCompact U) (hScl : ∀ U ∈ S, IsClosed U) : (⋂₀ S).Nonempty := by
  rw [sInter_eq_iInter]
  exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
    (DirectedOn.directed_val hSd) (fun i ↦ hSn i i.2) (fun i ↦ hSc i i.2) (fun i ↦ hScl i i.2)

/-- Cantor's intersection theorem for sequences indexed by `ℕ`:
the intersection of a decreasing sequence of nonempty compact closed sets is nonempty. -/
/-
**IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (t : Nat
 -> Set X) (htd : forall i, t (i + 1) subseteq t i) (htn : forall i, (t i).Nonem
pty) (ht0 : IsCompact (t 0)) (htcl : forall i, IsClosed (t i)) : (⋂ i, t i).None
mpty
参数：t : Nat -> Set X；htd : forall i, t (i + 1) subseteq t i；htn : forall i, (t i)
.Nonempty；ht0 : IsCompact (t 0)；htcl : forall i, IsClosed (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `Antitone.directed_ge`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α
] [IsDirectedOrder α] [inst_2 : Preorder β] {f : α → β},   Antitone f → Directed
 (fun x1 x…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
Cantor's intersection theorem for sequences indexed by `ℕ`:
the intersection of a decreasing sequence of nonempty compact closed sets is non
empty.
-/
theorem IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (t : ℕ → Set X)
    (htd : ∀ i, t (i + 1) ⊆ t i) (htn : ∀ i, (t i).Nonempty) (ht0 : IsCompact (t 0))
    (htcl : ∀ i, IsClosed (t i)) : (⋂ i, t i).Nonempty :=
  have tmono : Antitone t := antitone_nat_of_succ_le htd
  have htd : Directed (· ⊇ ·) t := tmono.directed_ge
  have : ∀ i, t i ⊆ t 0 := fun i => tmono <| Nat.zero_le i
  have htc : ∀ i, IsCompact (t i) := fun i => ht0.of_isClosed_subset (htcl i) (this i)
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl

/-- For every open cover of a compact set, there exists a finite subcover. -/
/-
**IsCompact.elim_finite_subcover_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.elim_finite_subcover_image {b : Set ι} {c : ι -> Set X} (hs : Is
Compact s) (hc₁ : forall i in b, IsOpen (c i)) (hc₂ : s subseteq ⋃ i in b, c i) 
: exists b', b' subseteq b ∧ Set.Finite b' ∧ s subseteq ⋃ i in b', c i
参数：hs : IsCompact s；hc₁ : forall i in b, IsOpen (c i)；hc₂ : s subseteq ⋃ i in b,
 c i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.biUnion_image`：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y
)

--- 原说明 ---
For every open cover of a compact set, there exists a finite subcover.
-/
theorem IsCompact.elim_finite_subcover_image {b : Set ι} {c : ι → Set X} (hs : IsCompact s)
    (hc₁ : ∀ i ∈ b, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b', b' ⊆ b ∧ Set.Finite b' ∧ s ⊆ ⋃ i ∈ b', c i := by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_finite_subcover (fun i => c i : b → Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' (d : Set b), ?_, d.finite_toSet.image _, ?_⟩
  · simp
  · rwa [biUnion_image]

/-- A set `s` is compact if for every open cover of `s`, there exists a finite subcover. -/
/-
**isCompact_of_finite_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_of_finite_subcover (h : forall {ι : Type u} (U : ι -> Set X), (f
orall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) -> exists t : Finset ι, s subset
eq ⋃ i in t, U i) : IsCompact s
参数：h : forall {ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subs
eteq ⋃ i, U i) -> exists t : Finset ι, s subseteq ⋃ i in t, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Filter.compl_notMem`：compl_notMem {f : Filter α} {s : Set α} [NeBot f] (
h : s in f) : sᶜ ∉ f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.biInter_finset_mem`：biInter_finset_mem {β : Type v} {s : β -> Set
 α} (is : Finset β) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `Set.compl_iInter₂`：compl_iInter₂ (s : forall i, κ i -> Set α) : (⋂ (i) (
j), s i j)ᶜ = ⋃ (i) (j), (s i j)ᶜ
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Filter.HasBasis.disjoint_iff_left`：∀ {α : Type u_1} {ι : Sort u_4} {l l'
 : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l l' ↔
 ∃ i, p i ∧ (s i)ᶜ ∈ l'…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A set `s` is compact if for every open cover of `s`, there exists a finite subco
ver.
-/
theorem isCompact_of_finite_subcover
    (h : ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) →
      ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i) :
    IsCompact s := fun f hf hfs => by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose U hU hUf using h
  refine ⟨s, U, fun x => (hU x).2, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1⟩, fun t ht => ?_⟩
  refine compl_notMem (le_principal_iff.1 hfs) ?_
  refine mem_of_superset ((biInter_finset_mem t).2 fun x _ => hUf x) ?_
  rw [subset_compl_comm, compl_iInter₂]
  simpa only [compl_compl]

-- TODO: reformulate using `Disjoint`
/-- A set `s` is compact if for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
/-
**isCompact_of_finite_subfamily_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_of_finite_subfamily_closed (h : forall {ι : Type u} (t : ι -> Se
t X), (forall i, IsClosed (t i)) -> (s inter ⋂ i, t i) = ∅ -> exists u : Finset 
ι, (s inter ⋂ i in u, t i) = ∅) : IsCompact s
参数：h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> (s in
ter ⋂ i, t i) = ∅ -> exists u : Finset ι, (s inter ⋂ i in u, t i) = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_of_finite_subcover`：isCompact_of_finite_subcover (h : forall {
ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) 
-> exists t : Fins…
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.disjoint_compl_right_iff_subset`：disjoint_compl_right_iff_subset : D
isjoint s tᶜ ↔ s subseteq t
· 使用定理 `Set.compl_iUnion₂`：compl_iUnion₂ (s : forall i, κ i -> Set α) : (⋃ (i) (
j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ

--- 原说明 ---
A set `s` is compact if for every family of closed sets whose intersection avoid
s `s`,
there exists a finite subfamily whose intersection avoids `s`.
-/
theorem isCompact_of_finite_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ →
      ∃ u : Finset ι, (s ∩ ⋂ i ∈ u, t i) = ∅) :
    IsCompact s :=
  isCompact_of_finite_subcover fun U hUo hsU => by
    rw [← disjoint_compl_right_iff_subset, compl_iUnion, disjoint_iff] at hsU
    rcases h (fun i => (U i)ᶜ) (fun i => (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]

/-- A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover. -/
/-
**isCompact_iff_finite_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_iff_finite_subcover : IsCompact s ↔ forall {ι : Type u} (U : ι -
> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) -> exists t : Finset
 ι, s subseteq ⋃ i in t, U i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `isCompact_of_finite_subcover`：isCompact_of_finite_subcover (h : forall {
ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) 
-> exists t : Fins…

--- 原说明 ---
A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover.
-/
theorem isCompact_iff_finite_subcover :
    IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩

/-- A set `s` is compact if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
/-
**isCompact_iff_finite_subfamily_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_iff_finite_subfamily_closed : IsCompact s ↔ forall {ι : Type u} 
(t : ι -> Set X), (forall i, IsClosed (t i)) -> (s inter ⋂ i, t i) = ∅ -> exists
 u : Finset ι, (s inter ⋂ i in u, t i) = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subfamily_closed`：IsCompact.elim_finite_subfamily_
closed {ι : Type v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClose
d (t i)) (hst : (s inter ⋂ i…
· 使用定理 `isCompact_of_finite_subfamily_closed`：isCompact_of_finite_subfamily_clos
ed (h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> (s i
nter ⋂ i, t i) = ∅ -> exis…

--- 原说明 ---
A set `s` is compact if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`.
-/
theorem isCompact_iff_finite_subfamily_closed :
    IsCompact s ↔ ∀ {ι : Type u} (t : ι → Set X),
      (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ → ∃ u : Finset ι, (s ∩ ⋂ i ∈ u, t i) = ∅ :=
  ⟨fun hs => hs.elim_finite_subfamily_closed, isCompact_of_finite_subfamily_closed⟩

/-- If `s : Set (X × Y)` belongs to `𝓝 x ×ˢ l` for all `x` from a compact set `K`,
then it belongs to `(𝓝ˢ K) ×ˢ l`,
i.e., there exist an open `U ⊇ K` and `t ∈ l` such that `U ×ˢ t ⊆ s`. -/
/-
**IsCompact.mem_nhdsSet_prod_of_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.mem_nhdsSet_prod_of_forall {K : Set X} {Y} {l : Filter Y} {s : S
et (X × Y)} (hK : IsCompact K) (hs : forall x in K, s in 𝓝 x ×ˢ l) : s in (𝓝ˢ K)
 ×ˢ l
参数：X × Y；hK : IsCompact K；hs : forall x in K, s in 𝓝 x ×ˢ l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_empty`：nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥
· 使用定理 `Filter.bot_prod`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β}, ⊥ ×ˢ g 
= ⊥
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `nhdsSet_union`：nhdsSet_union (s t : Set X) : 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ 
t
· 使用定理 `Filter.sup_prod`：sup_prod (f₁ f₂ : Filter α) (g : Filter β) : (f₁ ⊔ f₂) 
×ˢ g = (f₁ ×ˢ g) ⊔ (f₂ ×ˢ g)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {l
b : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} 
{pb : ι' →…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
If `s : Set (X × Y)` belongs to `𝓝 x ×ˢ l` for all `x` from a compact set `K`,
then it belongs to `(𝓝ˢ K) ×ˢ l`,
i.e., there exist an open `U ⊇ K` and `t ∈ l` such that `U ×ˢ t ⊆ s`.
-/
theorem IsCompact.mem_nhdsSet_prod_of_forall {K : Set X} {Y} {l : Filter Y} {s : Set (X × Y)}
    (hK : IsCompact K) (hs : ∀ x ∈ K, s ∈ 𝓝 x ×ˢ l) : s ∈ (𝓝ˢ K) ×ˢ l := by
  refine hK.induction_on (by simp) (fun t t' ht hs ↦ ?_) (fun t t' ht ht' ↦ ?_) fun x hx ↦ ?_
  · exact prod_mono (nhdsSet_mono ht) le_rfl hs
  · simp [sup_prod, *]
  · rcases ((nhds_basis_opens _).prod l.basis_sets).mem_iff.1 (hs x hx)
      with ⟨⟨u, v⟩, ⟨⟨hx, huo⟩, hv⟩, hs⟩
    refine ⟨u, nhdsWithin_le_nhds (huo.mem_nhds hx), mem_of_superset ?_ hs⟩
    exact prod_mem_prod (huo.mem_nhdsSet.2 Subset.rfl) hv
/-
**IsCompact.nhdsSet_prod_eq_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nhdsSet_prod_eq_biSup {K : Set X} (hK : IsCompact K) {Y} (l : Fi
lter Y) : (𝓝ˢ K) ×ˢ l = ⨆ x in K, 𝓝 x ×ˢ l
参数：hK : IsCompact K；l : Filter Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsCompact.mem_nhdsSet_prod_of_forall`：IsCompact.mem_nhdsSet_prod_of_fora
ll {K : Set X} {Y} {l : Filter Y} {s : Set (X × Y)} (hK : IsCompact K) (hs : for
all x in K, s in 𝓝 x ×ˢ l)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `nhds_le_nhdsSet`：nhds_le_nhdsSet (h : x in s) : 𝓝 x <= 𝓝ˢ s
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IsCompact.nhdsSet_prod_eq_biSup {K : Set X} (hK : IsCompact K) {Y} (l : Filter Y) :
    (𝓝ˢ K) ×ˢ l = ⨆ x ∈ K, 𝓝 x ×ˢ l :=
  le_antisymm (fun s hs ↦ hK.mem_nhdsSet_prod_of_forall <| by simpa using hs)
    (iSup₂_le fun _ hx ↦ prod_mono (nhds_le_nhdsSet hx) le_rfl)
/-
**IsCompact.prod_nhdsSet_eq_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.prod_nhdsSet_eq_biSup {K : Set Y} (hK : IsCompact K) {X} (l : Fi
lter X) : l ×ˢ (𝓝ˢ K) = ⨆ y in K, l ×ˢ 𝓝 y
参数：hK : IsCompact K；l : Filter X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_comm`：prod_comm : f ×ˢ g = map Prod.swap (g ×ˢ f)
· 使用定理 `IsCompact.nhdsSet_prod_eq_biSup`：IsCompact.nhdsSet_prod_eq_biSup {K : Se
t X} (hK : IsCompact K) {Y} (l : Filter Y) : (𝓝ˢ K) ×ˢ l = ⨆ x in K, 𝓝 x ×ˢ l
· 使用定理 `Filter.map_iSup`：map_iSup {f : ι -> Filter α} : map m (⨆ i, f i) = ⨆ i, 
map m (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCompact.prod_nhdsSet_eq_biSup {K : Set Y} (hK : IsCompact K) {X} (l : Filter X) :
    l ×ˢ (𝓝ˢ K) = ⨆ y ∈ K, l ×ˢ 𝓝 y := by
  simp only [prod_comm (f := l), hK.nhdsSet_prod_eq_biSup, map_iSup]

/-- If `s : Set (X × Y)` belongs to `l ×ˢ 𝓝 y` for all `y` from a compact set `K`,
then it belongs to `l ×ˢ (𝓝ˢ K)`,
i.e., there exist `t ∈ l` and an open `U ⊇ K` such that `t ×ˢ U ⊆ s`. -/
/-
**IsCompact.mem_prod_nhdsSet_of_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.mem_prod_nhdsSet_of_forall {K : Set Y} {X} {l : Filter X} {s : S
et (X × Y)} (hK : IsCompact K) (hs : forall y in K, s in l ×ˢ 𝓝 y) : s in l ×ˢ 𝓝
ˢ K
参数：X × Y；hK : IsCompact K；hs : forall y in K, s in l ×ˢ 𝓝 y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.prod_nhdsSet_eq_biSup`：IsCompact.prod_nhdsSet_eq_biSup {K : Se
t Y} (hK : IsCompact K) {X} (l : Filter X) : l ×ˢ (𝓝ˢ K) = ⨆ y in K, l ×ˢ 𝓝 y

--- 原说明 ---
If `s : Set (X × Y)` belongs to `l ×ˢ 𝓝 y` for all `y` from a compact set `K`,
then it belongs to `l ×ˢ (𝓝ˢ K)`,
i.e., there exist `t ∈ l` and an open `U ⊇ K` such that `t ×ˢ U ⊆ s`.
-/
theorem IsCompact.mem_prod_nhdsSet_of_forall {K : Set Y} {X} {l : Filter X} {s : Set (X × Y)}
    (hK : IsCompact K) (hs : ∀ y ∈ K, s ∈ l ×ˢ 𝓝 y) : s ∈ l ×ˢ 𝓝ˢ K :=
  (hK.prod_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

-- TODO: Is there a way to prove directly the `inf` version and then deduce the `Prod` one ?
-- That would seem a bit more natural.
/-
**IsCompact.nhdsSet_inf_eq_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nhdsSet_inf_eq_biSup {K : Set X} (hK : IsCompact K) (l : Filter 
X) : (𝓝ˢ K) ⊓ l = ⨆ x in K, 𝓝 x ⊓ l
参数：hK : IsCompact K；l : Filter X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_prod`：comap_prod (f : α -> β × γ) (b : Filter β) (c : Filte
r γ) : comap f (b ×ˢ c) = comap (Prod.fst ∘ f) b ⊓ comap (Prod.snd ∘ f) c
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_id`：comap_id : comap id f = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsCompact.nhdsSet_prod_eq_biSup`：IsCompact.nhdsSet_prod_eq_biSup {K : Se
t X} (hK : IsCompact K) {Y} (l : Filter Y) : (𝓝ˢ K) ×ˢ l = ⨆ x in K, 𝓝 x ×ˢ l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCompact.nhdsSet_inf_eq_biSup {K : Set X} (hK : IsCompact K) (l : Filter X) :
    (𝓝ˢ K) ⊓ l = ⨆ x ∈ K, 𝓝 x ⊓ l := by
  have : ∀ f : Filter X, f ⊓ l = comap Function.diag (f ×ˢ l) := fun f ↦ by
    simpa only [comap_prod] using! congrArg₂ (· ⊓ ·) comap_id.symm comap_id.symm
  simp_rw [this, ← comap_iSup, hK.nhdsSet_prod_eq_biSup]
/-
**IsCompact.inf_nhdsSet_eq_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.inf_nhdsSet_eq_biSup {K : Set X} (hK : IsCompact K) (l : Filter 
X) : l ⊓ (𝓝ˢ K) = ⨆ x in K, l ⊓ 𝓝 x
参数：hK : IsCompact K；l : Filter X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `IsCompact.nhdsSet_inf_eq_biSup`：IsCompact.nhdsSet_inf_eq_biSup {K : Set 
X} (hK : IsCompact K) (l : Filter X) : (𝓝ˢ K) ⊓ l = ⨆ x in K, 𝓝 x ⊓ l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCompact.inf_nhdsSet_eq_biSup {K : Set X} (hK : IsCompact K) (l : Filter X) :
    l ⊓ (𝓝ˢ K) = ⨆ x ∈ K, l ⊓ 𝓝 x := by
  simp only [inf_comm l, hK.nhdsSet_inf_eq_biSup]

/-- If `s : Set X` belongs to `𝓝 x ⊓ l` for all `x` from a compact set `K`,
then it belongs to `(𝓝ˢ K) ⊓ l`,
i.e., there exist an open `U ⊇ K` and `T ∈ l` such that `U ∩ T ⊆ s`. -/
/-
**IsCompact.mem_nhdsSet_inf_of_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.mem_nhdsSet_inf_of_forall {K : Set X} {l : Filter X} {s : Set X}
 (hK : IsCompact K) (hs : forall x in K, s in 𝓝 x ⊓ l) : s in (𝓝ˢ K) ⊓ l
参数：hK : IsCompact K；hs : forall x in K, s in 𝓝 x ⊓ l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.nhdsSet_inf_eq_biSup`：IsCompact.nhdsSet_inf_eq_biSup {K : Set 
X} (hK : IsCompact K) (l : Filter X) : (𝓝ˢ K) ⊓ l = ⨆ x in K, 𝓝 x ⊓ l

--- 原说明 ---
If `s : Set X` belongs to `𝓝 x ⊓ l` for all `x` from a compact set `K`,
then it belongs to `(𝓝ˢ K) ⊓ l`,
i.e., there exist an open `U ⊇ K` and `T ∈ l` such that `U ∩ T ⊆ s`.
-/
theorem IsCompact.mem_nhdsSet_inf_of_forall {K : Set X} {l : Filter X} {s : Set X}
    (hK : IsCompact K) (hs : ∀ x ∈ K, s ∈ 𝓝 x ⊓ l) : s ∈ (𝓝ˢ K) ⊓ l :=
  (hK.nhdsSet_inf_eq_biSup l).symm ▸ by simpa using hs

/-- If `s : Set S` belongs to `l ⊓ 𝓝 x` for all `x` from a compact set `K`,
then it belongs to `l ⊓ (𝓝ˢ K)`,
i.e., there exist `T ∈ l` and an open `U ⊇ K` such that `T ∩ U ⊆ s`. -/
/-
**IsCompact.mem_inf_nhdsSet_of_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.mem_inf_nhdsSet_of_forall {K : Set X} {l : Filter X} {s : Set X}
 (hK : IsCompact K) (hs : forall y in K, s in l ⊓ 𝓝 y) : s in l ⊓ 𝓝ˢ K
参数：hK : IsCompact K；hs : forall y in K, s in l ⊓ 𝓝 y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.inf_nhdsSet_eq_biSup`：IsCompact.inf_nhdsSet_eq_biSup {K : Set 
X} (hK : IsCompact K) (l : Filter X) : l ⊓ (𝓝ˢ K) = ⨆ x in K, l ⊓ 𝓝 x

--- 原说明 ---
If `s : Set S` belongs to `l ⊓ 𝓝 x` for all `x` from a compact set `K`,
then it belongs to `l ⊓ (𝓝ˢ K)`,
i.e., there exist `T ∈ l` and an open `U ⊇ K` such that `T ∩ U ⊆ s`.
-/
theorem IsCompact.mem_inf_nhdsSet_of_forall {K : Set X} {l : Filter X} {s : Set X}
    (hK : IsCompact K) (hs : ∀ y ∈ K, s ∈ l ⊓ 𝓝 y) : s ∈ l ⊓ 𝓝ˢ K :=
  (hK.inf_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

/-- To show that `∀ y ∈ K, P x y` holds for `x` close enough to `x₀` when `K` is compact,
it is sufficient to show that for all `y₀ ∈ K` there `P x y` holds for `(x, y)` close enough
to `(x₀, y₀)`.

Provided for backwards compatibility,
see `IsCompact.mem_prod_nhdsSet_of_forall` for a stronger statement.
-/
/-
**IsCompact.eventually_forall_of_forall_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.eventually_forall_of_forall_eventually {x₀ : X} {K : Set Y} (hK 
: IsCompact K) {P : X -> Y -> Prop} (hP : forall y in K, forallᶠ z : X × Y in 𝓝 
(x₀, y), P z.1 z.2) : forallᶠ x in 𝓝 x₀, forall y in K, P x y
参数：hK : IsCompact K；hP : forall y in K, forallᶠ z : X × Y in 𝓝 (x₀, y), P z.1 z.
2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.curry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α}
 {lb : Filter β} {p : α × β → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x
 : α) in la, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.prod_nhdsSet_eq_biSup`：IsCompact.prod_nhdsSet_eq_biSup {K : Se
t Y} (hK : IsCompact K) {X} (l : Filter X) : l ×ˢ (𝓝ˢ K) = ⨆ y in K, l ×ˢ 𝓝 y
· 使用定理 `Filter.Eventually.self_of_nhdsSet`：Filter.Eventually.self_of_nhdsSet {p 
: X -> Prop} (h : forallᶠ x in 𝓝ˢ s, p x) : forall x in s, p x

--- 原说明 ---
To show that `∀ y ∈ K, P x y` holds for `x` close enough to `x₀` when `K` is com
pact,
it is sufficient to show that for all `y₀ ∈ K` there `P x y` holds for `(x, y)` 
close enough
to `(x₀, y₀)`.

Provided for backwards compatibility,
see `IsCompact.mem_prod_nhdsSet_of_forall` for a stronger statement.
-/
theorem IsCompact.eventually_forall_of_forall_eventually {x₀ : X} {K : Set Y} (hK : IsCompact K)
    {P : X → Y → Prop} (hP : ∀ y ∈ K, ∀ᶠ z : X × Y in 𝓝 (x₀, y), P z.1 z.2) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, P x y := by
  simp only [nhds_prod_eq, ← eventually_iSup, ← hK.prod_nhdsSet_eq_biSup] at hP
  exact hP.curry.mono fun _ h ↦ h.self_of_nhdsSet

@[compactness ., grind .]
/-
**isCompact_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_empty : IsCompact (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem isCompact_empty : IsCompact (∅ : Set X) := fun _f hnf hsf =>
  Not.elim hnf.ne <| empty_mem_iff_bot.1 <| le_principal_iff.1 hsf

@[compactness ., grind .]
/-
**isCompact_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_singleton {x : X} : IsCompact ({x} : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.of_le_nhds'`：ClusterPt.of_le_nhds' {f : Filter X} (H : f <= 𝓝 
x) (_hf : NeBot f) : ClusterPt x f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem isCompact_singleton {x : X} : IsCompact ({x} : Set X) := fun _ hf hfa =>
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩
/-
**Set.Subsingleton.isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.isCompact (hs : s.Subsingleton) : IsCompact s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.induction_on`：∀ {α : Type u} {s : Set α} {p : Set α → P
rop}, s.Subsingleton → p ∅ → (∀ (x : α), p {x}) → p s
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
-/
theorem Set.Subsingleton.isCompact (hs : s.Subsingleton) : IsCompact s :=
  Subsingleton.induction_on hs isCompact_empty fun _ => isCompact_singleton
/-
**Set.Finite.isCompact_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isCompact_biUnion {s : Set ι} {f : ι -> Set X} (hs : s.Finite) 
(hf : forall i in s, IsCompact (f i)) : IsCompact (⋃ i in s, f i)
参数：hs : s.Finite；hf : forall i in s, IsCompact (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_ultrafilter_le_nhds'`：isCompact_iff_ultrafilter_le_nhds' :
 IsCompact s ↔ forall f : Ultrafilter X, s in f -> exists x in s, ↑f <= 𝓝 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ultrafilter.finite_biUnion_mem_iff`：finite_biUnion_mem_iff {is : Set β} 
{s : β -> Set α} (his : is.Finite) : (⋃ i in is, s i) in f ↔ exists i in is, s i
 in f
· 使用定理 `IsCompact.ultrafilter_le_nhds`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X},   IsCompact s → ∀ (f : Ultrafilter X), ↑f ≤ Filter.principal s → 
∃ x ∈ s, ↑f ≤ nhds …
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
-/
theorem Set.Finite.isCompact_biUnion {s : Set ι} {f : ι → Set X} (hs : s.Finite)
    (hf : ∀ i ∈ s, IsCompact (f i)) : IsCompact (⋃ i ∈ s, f i) :=
  isCompact_iff_ultrafilter_le_nhds'.2 fun l hl => by
    rw [Ultrafilter.finite_biUnion_mem_iff hs] at hl
    rcases hl with ⟨i, his, hi⟩
    rcases (hf i his).ultrafilter_le_nhds _ (le_principal_iff.2 hi) with ⟨x, hxi, hlx⟩
    exact ⟨x, mem_iUnion₂.2 ⟨i, his, hxi⟩, hlx⟩
/-
**Finset.isCompact_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.isCompact_biUnion (s : Finset ι) {f : ι -> Set X} (hf : forall i in
 s, IsCompact (f i)) : IsCompact (⋃ i in s, f i)
参数：s : Finset ι；hf : forall i in s, IsCompact (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isCompact_biUnion`：Set.Finite.isCompact_biUnion {s : Set ι} {
f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsCompact (f i)) : IsCompac
t (⋃ i in s, f i)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem Finset.isCompact_biUnion (s : Finset ι) {f : ι → Set X} (hf : ∀ i ∈ s, IsCompact (f i)) :
    IsCompact (⋃ i ∈ s, f i) :=
  s.finite_toSet.isCompact_biUnion hf

@[compactness .]
/-
**isCompact_accumulate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_accumulate {K : Nat -> Set X} (hK : forall n, IsCompact (K n)) (
n : Nat) : IsCompact (accumulate K n)
参数：hK : forall n, IsCompact (K n)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isCompact_biUnion`：Set.Finite.isCompact_biUnion {s : Set ι} {
f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsCompact (f i)) : IsCompac
t (⋃ i in s, f i)
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
-/
theorem isCompact_accumulate {K : ℕ → Set X} (hK : ∀ n, IsCompact (K n)) (n : ℕ) :
    IsCompact (accumulate K n) :=
  (finite_le_nat n).isCompact_biUnion fun k _ => hK k

@[compactness .]
/-
**Set.Finite.isCompact_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isCompact_sUnion {S : Set (Set X)} (hf : S.Finite) (hc : forall
 s in S, IsCompact s) : IsCompact (⋃₀ S)
参数：Set X；hf : S.Finite；hc : forall s in S, IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.Finite.isCompact_biUnion`：Set.Finite.isCompact_biUnion {s : Set ι} {
f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsCompact (f i)) : IsCompac
t (⋃ i in s, f i)
-/
theorem Set.Finite.isCompact_sUnion {S : Set (Set X)} (hf : S.Finite) (hc : ∀ s ∈ S, IsCompact s) :
    IsCompact (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isCompact_biUnion hc

@[compactness .]
/-
**isCompact_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_iUnion {ι : Sort*} {f : ι -> Set X} [Finite ι] (h : forall i, Is
Compact (f i)) : IsCompact (⋃ i, f i)
参数：h : forall i, IsCompact (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isCompact_sUnion`：Set.Finite.isCompact_sUnion {S : Set (Set X
)} (hf : S.Finite) (hc : forall s in S, IsCompact s) : IsCompact (⋃₀ S)
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isCompact_iUnion {ι : Sort*} {f : ι → Set X} [Finite ι] (h : ∀ i, IsCompact (f i)) :
    IsCompact (⋃ i, f i) :=
  (finite_range f).isCompact_sUnion <| forall_mem_range.2 h
/-
**Set.Finite.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, s.Finite → IsCompa
ct s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isCompact_biUnion`：Set.Finite.isCompact_biUnion {s : Set ι} {
f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsCompact (f i)) : IsCompac
t (⋃ i in s, f i)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
-/
@[simp, compactness .] theorem Set.Finite.isCompact (hs : s.Finite) : IsCompact s :=
  biUnion_of_singleton s ▸ hs.isCompact_biUnion fun _ _ => isCompact_singleton
/-
**Set.sUnion_isCompact_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X], ⋃₀ {s | IsCompact s} = Set.uni
v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] theorem Set.sUnion_isCompact_eq_univ : ⋃₀ {(s : Set X) | IsCompact s} = univ :=
  eq_univ_of_forall <| fun x ↦ ⟨{x}, by simp⟩
/-
**IsCompact.finite_of_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.finite_of_discrete [DiscreteTopology X] (hs : IsCompact s) : s.F
inite
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.set_biUnion_coe`：set_biUnion_coe (s : Finset α) (t : α -> Set β) 
: ⋃ x in (↑s : Set α), t x = ⋃ x in s, t x
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
-/
theorem IsCompact.finite_of_discrete [DiscreteTopology X] (hs : IsCompact s) : s.Finite := by
  have : ∀ x : X, ({x} : Set X) ∈ 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, _, hst⟩
  simp only [← t.set_biUnion_coe, biUnion_of_singleton] at hst
  exact t.finite_toSet.subset hst
/-
**isCompact_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_iff_finite [DiscreteTopology X] : IsCompact s ↔ s.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.finite_of_discrete`：IsCompact.finite_of_discrete [DiscreteTopo
logy X] (hs : IsCompact s) : s.Finite
· 使用定理 `Set.Finite.isCompact`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, s.Finite → IsCompact s
-/
theorem isCompact_iff_finite [DiscreteTopology X] : IsCompact s ↔ s.Finite :=
  ⟨fun h => h.finite_of_discrete, fun h => h.isCompact⟩

@[compactness .]
/-
**IsCompact.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s union
 t)
参数：hs : IsCompact s；ht : IsCompact t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `isCompact_iUnion`：isCompact_iUnion {ι : Sort*} {f : ι -> Set X} [Finite 
ι] (h : forall i, IsCompact (f i)) : IsCompact (⋃ i, f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsCompact.union (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∪ t) := by
  rw [union_eq_iUnion]; exact isCompact_iUnion fun b => by cases b <;> assumption

@[compactness .]
/-
**IsCompact.insert** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, IsCompact s → ∀ (a
 : X), IsCompact (insert a s)
参数：a : X；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
-/
protected theorem IsCompact.insert (hs : IsCompact s) (a) : IsCompact (insert a s) :=
  isCompact_singleton.union hs

-- TODO: reformulate using `𝓝ˢ`
/-- If `V : ι → Set X` is a decreasing family of closed compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. We assume each `V i` is compact *and* closed because `X` is
not assumed to be Hausdorff. See `exists_subset_nhds_of_compact` for version assuming this. -/
/-
**exists_subset_nhds_of_isCompact'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_subset_nhds_of_isCompact' [Nonempty ι] {V : ι -> Set X} (hV : Direc
ted (· ⊇ ·) V) (hV_cpct : forall i, IsCompact (V i)) (hV_closed : forall i, IsCl
osed (V i)) {U : Set X} (hU : forall x in ⋂ i, V i, U in 𝓝 x) : exists i, V i su
bseteq U
参数：hV : Directed (· ⊇ ·) V；hV_cpct : forall i, IsCompact (V i)；hV_closed : foral
l i, IsClosed (V i)；hU : forall x in ⋂ i, V i, U in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_open_set_nhds`：exists_open_set_nhds {U : Set X} (h : forall x in 
s, U in 𝓝 x) : exists V : Set X, s subseteq V ∧ IsOpen V ∧ V subseteq U
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_compl_nonempty_iff`：inter_compl_nonempty_iff {s t : Set α} : (
s inter tᶜ).Nonempty ↔ ¬s subseteq t
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
If `V : ι → Set X` is a decreasing family of closed compact sets then any neighb
orhood of
`⋂ i, V i` contains some `V i`. We assume each `V i` is compact *and* closed bec
ause `X` is
not assumed to be Hausdorff. See `exists_subset_nhds_of_compact` for version ass
uming this.
-/
theorem exists_subset_nhds_of_isCompact' [Nonempty ι] {V : ι → Set X}
    (hV : Directed (· ⊇ ·) V) (hV_cpct : ∀ i, IsCompact (V i)) (hV_closed : ∀ i, IsClosed (V i))
    {U : Set X} (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U := by
  obtain ⟨W, hsubW, W_op, hWU⟩ := exists_open_set_nhds hU
  suffices ∃ i, V i ⊆ W from this.imp fun i hi => hi.trans hWU
  by_contra! H
  replace H : ∀ i, (V i ∩ Wᶜ).Nonempty := fun i => Set.inter_compl_nonempty_iff.mpr (H i)
  have : (⋂ i, V i ∩ Wᶜ).Nonempty := by
    refine
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun i j => ?_) H
        (fun i => (hV_cpct i).inter_right W_op.isClosed_compl) fun i =>
        (hV_closed i).inter W_op.isClosed_compl
    rcases hV i j with ⟨k, hki, hkj⟩
    refine ⟨k, ⟨fun x => ?_, fun x => ?_⟩⟩ <;> simp only [and_imp, mem_inter_iff, mem_compl_iff] <;>
      tauto
  have : ¬⋂ i : ι, V i ⊆ W := by simpa [← iInter_inter, inter_compl_nonempty_iff]
  contradiction

omit [TopologicalSpace X] in
/--
**Alexander's subbasis theorem**. Suppose `X` is a topological space with a subbasis `S` and `s` is
a subset of `X`. Then `s` is compact if for any open cover of `s` with all elements taken from `S`,
there is a finite subcover.
-/
/-
**isCompact_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_generateFrom [T : TopologicalSpace X] {S : Set (Set X)} (hTS : T
 = generateFrom S) {s : Set X} (h : forall P subseteq S, s subseteq ⋃₀ P -> exis
ts Q subseteq P, Q.Finite ∧ s subseteq ⋃₀ Q) : IsCompact s
参数：Set X；hTS : T = generateFrom S；h : forall P subseteq S, s subseteq ⋃₀ P -> ex
ists Q subseteq P, Q.Finite ∧ s subseteq ⋃₀ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompact_iff_ultrafilter_le_nhds'`：isCompact_iff_ultrafilter_le_nhds' :
 IsCompact s ↔ forall f : Ultrafilter X, s in f -> exists x in s, ↑f <= 𝓝 x
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TopologicalSpace.nhds_generateFrom`：nhds_generateFrom {g : Set (Set α)} 
{a : α} : @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_sUnion_of_mem`：mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (S
et α)} (hx : x in t) (ht : t in S) : x in ⋃₀ S
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Ultrafilter.compl_mem_iff_notMem`：compl_mem_iff_notMem : sᶜ in f ↔ s ∉ f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
**Alexander's subbasis theorem**. Suppose `X` is a topological space with a subb
asis `S` and `s` is
a subset of `X`. Then `s` is compact if for any open cover of `s` with all eleme
nts taken from `S`,
there is a finite subcover.
-/
theorem isCompact_generateFrom [T : TopologicalSpace X]
    {S : Set (Set X)} (hTS : T = generateFrom S) {s : Set X}
    (h : ∀ P ⊆ S, s ⊆ ⋃₀ P → ∃ Q ⊆ P, Q.Finite ∧ s ⊆ ⋃₀ Q) :
    IsCompact s := by
  rw [isCompact_iff_ultrafilter_le_nhds', hTS]
  intro F hsF
  by_contra hF
  have hSF : ∀ x ∈ s, ∃ t, x ∈ t ∧ t ∈ S ∧ t ∉ F := by simpa [nhds_generateFrom] using hF
  choose! U hxU hSU hUF using hSF
  obtain ⟨Q, hQU, hQ, hsQ⟩ := h (U '' s) (by simpa [Set.subset_def])
    (fun x hx ↦ Set.mem_sUnion_of_mem (hxU _ hx) (by grind))
  have : ∀ s ∈ Q, s ∉ F := fun s hsQ ↦ (hQU hsQ).choose_spec.2 ▸ hUF _ (hQU hsQ).choose_spec.1
  have hQF : ⋂₀ (compl '' Q) ∈ F.sets := by simpa [Filter.biInter_mem hQ, F.compl_mem_iff_notMem]
  have : ⋃₀ Q ∉ F := by
    simpa [-Set.sInter_image, ← Set.compl_sUnion, hsQ, F.compl_mem_iff_notMem] using hQF
  exact this (F.mem_of_superset hsF hsQ)

omit [TopologicalSpace X] in
/-
**isCompact_generateFrom'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_generateFrom' [T : TopologicalSpace X] {S : Set (Set X)} (hTS : 
T = generateFrom S) {s : Set X} (h : forall (ι : Type u) (U : ι -> S), s subsete
q ⋃ i, U i -> exists J : Set ι, J.Finite ∧ s subseteq ⋃ i in J, U i) : IsCompact
 s
参数：Set X；hTS : T = generateFrom S；h : forall (ι : Type u) (U : ι -> S), s subset
eq ⋃ i, U i -> exists J : Set ι, J.Finite ∧ s subseteq ⋃ i in J, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_generateFrom`：isCompact_generateFrom [T : TopologicalSpace X] 
{S : Set (Set X)} (hTS : T = generateFrom S) {s : Set X} (h : forall P subseteq 
S, s subsete…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem isCompact_generateFrom' [T : TopologicalSpace X]
    {S : Set (Set X)} (hTS : T = generateFrom S) {s : Set X}
    (h : ∀ (ι : Type u) (U : ι → S), s ⊆ ⋃ i, U i → ∃ J : Set ι, J.Finite ∧ s ⊆ ⋃ i ∈ J, U i) :
    IsCompact s :=
  isCompact_generateFrom hTS fun P hP hs ↦
    have ⟨J, hJ, cover⟩ := h P (fun a ↦ ⟨a.1, hP a.2⟩) (sUnion_eq_iUnion ▸ hs)
    ⟨(·.1) '' J, ⟨by simp, hJ.image _, by aesop⟩⟩

namespace Filter

/-
**Filter.hasBasis_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_cocompact : (cocompact X).HasBasis IsCompact compl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_biInf_principal'`：hasBasis_biInf_principal' {ι : Type*} 
{p : ι -> Prop} {s : ι -> Set α} (h : forall i, p i -> forall j, p j -> exists k
, p k ∧ s k subseteq s…
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
-/
theorem hasBasis_cocompact : (cocompact X).HasBasis IsCompact compl :=
  hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s ∪ t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isCompact_empty⟩
/-
**Filter.mem_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_cocompact : s in cocompact X ↔ exists t, IsCompact t ∧ tᶜ subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
-/
theorem mem_cocompact : s ∈ cocompact X ↔ ∃ t, IsCompact t ∧ tᶜ ⊆ s :=
  hasBasis_cocompact.mem_iff
/-
**Filter.mem_cocompact'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_cocompact' : s in cocompact X ↔ exists t, IsCompact t ∧ sᶜ subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
-/
theorem mem_cocompact' : s ∈ cocompact X ↔ ∃ t, IsCompact t ∧ sᶜ ⊆ t :=
  mem_cocompact.trans <| exists_congr fun _ => and_congr_right fun _ => compl_subset_comm
/-
**Filter._root_.IsCompact.compl_mem_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `Filter`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsCompact.compl_mem_cocompact (hs : IsCompact s) : sᶜ ∈ Filter.cocompact X :=
  hasBasis_cocompact.mem_of_mem hs
/-
**Filter.cocompact_le_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：cocompact_le_cofinite : cocompact X <= cofinite
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.compl_mem_cocompact`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X}, IsCompact s → sᶜ ∈ Filter.cocompact X
· 使用定理 `Set.Finite.isCompact`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, s.Finite → IsCompact s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem cocompact_le_cofinite : cocompact X ≤ cofinite := fun s hs =>
  compl_compl s ▸ hs.isCompact.compl_mem_cocompact
/-
**Filter.cocompact_eq_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：cocompact_eq_cofinite (X : Type*) [TopologicalSpace X] [DiscreteTopology X
] : cocompact X = cofinite
参数：X : Type*。
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
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `Filter.hasBasis_cofinite`：hasBasis_cofinite : HasBasis cofinite (fun s :
 Set α => s.Finite) compl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cocompact_eq_cofinite (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    cocompact X = cofinite := by
  simp only [cocompact, hasBasis_cofinite.eq_biInf, isCompact_iff_finite]

/-- A filter is disjoint from the cocompact filter if and only if it contains a compact set. -/
/-
**Filter.disjoint_cocompact_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_cocompact_left (f : Filter X) : Disjoint (Filter.cocompact X) f ↔
 exists K in f, IsCompact K
参数：f : Filter X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.disjoint_iff_left`：∀ {α : Type u_1} {ι : Sort u_4} {l l'
 : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l l' ↔
 ∃ i, p i ∧ (s i)ᶜ ∈ l'…
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x

--- 原说明 ---
A filter is disjoint from the cocompact filter if and only if it contains a comp
act set.
-/
theorem disjoint_cocompact_left (f : Filter X) :
    Disjoint (Filter.cocompact X) f ↔ ∃ K ∈ f, IsCompact K := by
  simp_rw [hasBasis_cocompact.disjoint_iff_left, compl_compl]
  tauto

/-- A filter is disjoint from the cocompact filter if and only if it contains a compact set. -/
/-
**Filter.disjoint_cocompact_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_cocompact_right (f : Filter X) : Disjoint f (Filter.cocompact X) 
↔ exists K in f, IsCompact K
参数：f : Filter X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.disjoint_iff_right`：∀ {α : Type u_1} {ι : Sort u_4} {l l
' : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l' l 
↔ ∃ i, p i ∧ (s i)ᶜ ∈ l'…
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x

--- 原说明 ---
A filter is disjoint from the cocompact filter if and only if it contains a comp
act set.
-/
theorem disjoint_cocompact_right (f : Filter X) :
    Disjoint f (Filter.cocompact X) ↔ ∃ K ∈ f, IsCompact K := by
  simp_rw [hasBasis_cocompact.disjoint_iff_right, compl_compl]
  tauto
/-
**Filter.Tendsto.isCompact_insert_range_of_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `
Filter.Tendsto`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {f : X → Y} {y : Y},   Filter.Tendsto f (Filter.cocompact X) (nhds y
) → Continuous f → IsCompact (insert y (Set.range f))
参数：Filter.cocompact X；nhds y；insert y (Set.range f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem Tendsto.isCompact_insert_range_of_cocompact {f : X → Y} {y}
    (hf : Tendsto f (cocompact X) (𝓝 y)) (hfc : Continuous f) : IsCompact (insert y (range f)) := by
  intro l hne hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff_nonempty, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_cocompact.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K ∈ l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsy, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
  exact ⟨y, Or.inr <| image_subset_range _ _ hy, hyl⟩
/-
**Filter.Tendsto.isCompact_insert_range_of_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `F
ilter.Tendsto`。
形式化陈述：∀ {X : Type u} {ι : Type u_1} [inst : TopologicalSpace X] {f : ι → X} {x :
 X},   Filter.Tendsto f Filter.cofinite (nhds x) → IsCompact (insert x (Set.rang
e f))
参数：nhds x；insert x (Set.range f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.isCompact_insert_range_of_cocompact`：∀ {X : Type u} {Y : 
Type v} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {y
 : Y},   Filter.Tendsto f (Filter.cocomp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.cocompact_eq_cofinite`：cocompact_eq_cofinite (X : Type*) [Topolog
icalSpace X] [DiscreteTopology X] : cocompact X = cofinite
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
-/
theorem Tendsto.isCompact_insert_range_of_cofinite {f : ι → X} {x} (hf : Tendsto f cofinite (𝓝 x)) :
    IsCompact (insert x (range f)) := by
  let : TopologicalSpace ι := ⊥; have h : DiscreteTopology ι := ⟨rfl⟩
  rw [← cocompact_eq_cofinite ι] at hf
  exact hf.isCompact_insert_range_of_cocompact continuous_of_discreteTopology
/-
**Filter.Tendsto.isCompact_insert_range** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendst
o`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {f : ℕ → X} {x : X},   Filter.T
endsto f Filter.atTop (nhds x) → IsCompact (insert x (Set.range f))
参数：nhds x；insert x (Set.range f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.isCompact_insert_range_of_cofinite`：∀ {X : Type u} {ι : T
ype u_1} [inst : TopologicalSpace X] {f : ι → X} {x : X},   Filter.Tendsto f Fil
ter.cofinite (nhds x) → IsCompact (inse…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
-/
theorem Tendsto.isCompact_insert_range {f : ℕ → X} {x} (hf : Tendsto f atTop (𝓝 x)) :
    IsCompact (insert x (range f)) :=
  Filter.Tendsto.isCompact_insert_range_of_cofinite <| Nat.cofinite_eq_atTop.symm ▸ hf
/-
**Filter.hasBasis_coclosedCompact** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_coclosedCompact : (Filter.coclosedCompact X).HasBasis (fun s => I
sClosed s ∧ IsCompact s) compl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_and'`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s :
 p → q → α},   ⨅ (h₁ : p), ⨅ (h₂ : q), s h₁ h₂ = ⨅ (h : p ∧ q), s ⋯ ⋯
· 使用定理 `Filter.hasBasis_biInf_principal'`：hasBasis_biInf_principal' {ι : Type*} 
{p : ι -> Prop} {s : ι -> Set α} (h : forall i, p i -> forall j, p j -> exists k
, p k ∧ s k subseteq s…
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
-/
theorem hasBasis_coclosedCompact :
    (Filter.coclosedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl := by
  simp only [Filter.coclosedCompact, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isCompact_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s ∪ t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩⟩

/-- A set belongs to `coclosedCompact` if and only if the closure of its complement is compact. -/
/-
**Filter.mem_coclosedCompact_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_coclosedCompact_iff : s in coclosedCompact X ↔ IsCompact (closure sᶜ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.hasBasis_coclosedCompact`：hasBasis_coclosedCompact : (Filter.cocl
osedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
A set belongs to `coclosedCompact` if and only if the closure of its complement 
is compact.
-/
theorem mem_coclosedCompact_iff :
    s ∈ coclosedCompact X ↔ IsCompact (closure sᶜ) := by
  refine hasBasis_coclosedCompact.mem_iff.trans ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨t, ⟨htcl, htco⟩, hst⟩
    exact htco.of_isClosed_subset isClosed_closure <|
      closure_minimal (compl_subset_comm.2 hst) htcl
  · exact ⟨closure sᶜ, ⟨isClosed_closure, h⟩, compl_subset_comm.2 subset_closure⟩

/-- Complement of a set belongs to `coclosedCompact` if and only if its closure is compact. -/
/-
**Filter.compl_mem_coclosedCompact** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：compl_mem_coclosedCompact : sᶜ in coclosedCompact X ↔ IsCompact (closure s
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_coclosedCompact_iff`：mem_coclosedCompact_iff : s in coclosedC
ompact X ↔ IsCompact (closure sᶜ)
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Complement of a set belongs to `coclosedCompact` if and only if its closure is c
ompact.
-/
theorem compl_mem_coclosedCompact : sᶜ ∈ coclosedCompact X ↔ IsCompact (closure s) := by
  rw [mem_coclosedCompact_iff, compl_compl]
/-
**Filter.cocompact_le_coclosedCompact** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：cocompact_le_coclosedCompact : cocompact X <= coclosedCompact X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem cocompact_le_coclosedCompact : cocompact X ≤ coclosedCompact X :=
  iInf_mono fun _ => le_iInf fun _ => le_rfl

end Filter

/-
**IsCompact.compl_mem_coclosedCompact_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.compl_mem_coclosedCompact_of_isClosed (hs : IsCompact s) (hs' : 
IsClosed s) : sᶜ in Filter.coclosedCompact X
参数：hs : IsCompact s；hs' : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Filter.hasBasis_coclosedCompact`：hasBasis_coclosedCompact : (Filter.cocl
osedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl
-/
theorem IsCompact.compl_mem_coclosedCompact_of_isClosed (hs : IsCompact s) (hs' : IsClosed s) :
    sᶜ ∈ Filter.coclosedCompact X :=
  hasBasis_coclosedCompact.mem_of_mem ⟨hs', hs⟩

namespace Bornology

variable (X) in
/-- Sets that are contained in a compact set form a bornology. Its `cobounded` filter is
`Filter.cocompact`. See also `Bornology.relativelyCompact` the bornology of sets with compact
closure. -/
@[instance_reducible]
/-
**Bornology.inCompact** 是 Mathlib 中的一个定义，位于命名空间 `Bornology`。
形式化陈述：inCompact : Bornology X where cobounded
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.cocompact_le_cofinite`：cocompact_le_cofinite : cocompact X <= cof
inite

--- 原说明 ---
Sets that are contained in a compact set form a bornology. Its `cobounded` filte
r is
`Filter.cocompact`. See also `Bornology.relativelyCompact` the bornology of sets
 with compact
closure.
-/
def inCompact : Bornology X where
  cobounded := Filter.cocompact X
  le_cofinite := Filter.cocompact_le_cofinite
/-
**Bornology.inCompact.isBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.inCompa
ct`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, Bornology.IsBounde
d s ↔ ∃ t, IsCompact t ∧ s ⊆ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inCompact.isBounded_iff : @IsBounded _ (inCompact X) s ↔ ∃ t, IsCompact t ∧ s ⊆ t := by
  change sᶜ ∈ Filter.cocompact X ↔ _
  rw [Filter.mem_cocompact]
  simp

/-- A locally bounded function maps a compact set to a bounded set. -/
/-
**Bornology.isBounded_image_of_isLocallyBounded_of_isCompact** 是 Mathlib 中的一个引理，
位于命名空间 `Bornology`。
形式化陈述：isBounded_image_of_isLocallyBounded_of_isCompact {Y : Type*} [Bornology Y]
 {s : Set X} (hs : IsCompact s) {f : X -> Y} (hf : forall x, exists t in 𝓝 x, Is
Bounded (f '' t)) : IsBounded (f '' s)
参数：hs : IsCompact s；hf : forall x, exists t in 𝓝 x, IsBounded (f '' t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_iUnion₂`：image_iUnion₂ (f : α -> β) (s : forall i, κ i -> Set 
α) : (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bornology.isBounded_biUnion_finset`：isBounded_biUnion_finset (s : Finset
 ι) {f : ι -> Set α} : IsBounded (⋃ i in s, f i) ↔ forall i in s, IsBounded (f i
)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A locally bounded function maps a compact set to a bounded set.
-/
lemma isBounded_image_of_isLocallyBounded_of_isCompact {Y : Type*}
    [Bornology Y] {s : Set X} (hs : IsCompact s) {f : X → Y}
    (hf : ∀ x, ∃ t ∈ 𝓝 x, IsBounded (f '' t)) :
    IsBounded (f '' s) := by
  choose U hU using hf
  obtain ⟨I, hI⟩ := hs.elim_nhds_subcover U (fun x _ => (hU x).1)
  have : f '' ⋃ x ∈ I, U x = ⋃ x ∈ I, f '' U x := by simp [Set.image_iUnion₂]
  exact ((isBounded_biUnion_finset I).2 fun i _ => (hU i).2).subset (this ▸ Set.image_mono hI.2)

end Bornology

/-- If `s` and `t` are compact sets, then the set neighborhoods filter of `s ×ˢ t`
is the product of set neighborhoods filters for `s` and `t`.

For general sets, only the `≤` inequality holds, see `nhdsSet_prod_le`. -/
/-
**IsCompact.nhdsSet_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nhdsSet_prod_eq {t : Set Y} (hs : IsCompact s) (ht : IsCompact t
) : 𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t
参数：hs : IsCompact s；ht : IsCompact t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.nhdsSet_prod_eq_biSup`：IsCompact.nhdsSet_prod_eq_biSup {K : Se
t X} (hK : IsCompact K) {Y} (l : Filter Y) : (𝓝ˢ K) ×ˢ l = ⨆ x in K, 𝓝 x ×ˢ l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsCompact.prod_nhdsSet_eq_biSup`：IsCompact.prod_nhdsSet_eq_biSup {K : Se
t Y} (hK : IsCompact K) {X} (l : Filter X) : l ×ˢ (𝓝ˢ K) = ⨆ y in K, l ×ˢ 𝓝 y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `biSup_prod`：biSup_prod {f : β × γ -> α} {s : Set β} {t : Set γ} : ⨆ x in
 s ×ˢ t, f x = ⨆ (a in s) (b in t), f (a, b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `s` and `t` are compact sets, then the set neighborhoods filter of `s ×ˢ t`
is the product of set neighborhoods filters for `s` and `t`.

For general sets, only the `≤` inequality holds, see `nhdsSet_prod_le`.
-/
theorem IsCompact.nhdsSet_prod_eq {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t := by
  simp_rw [hs.nhdsSet_prod_eq_biSup, ht.prod_nhdsSet_eq_biSup, nhdsSet, sSup_image, biSup_prod,
    nhds_prod_eq]
/-
**nhdsSet_prod_le_of_disjoint_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_prod_le_of_disjoint_cocompact {f : Filter Y} (hs : IsCompact s) (h
f : Disjoint f (Filter.cocompact Y)) : 𝓝ˢ s ×ˢ f <= 𝓝ˢ (s ×ˢ Set.univ)
参数：hs : IsCompact s；hf : Disjoint f (Filter.cocompact Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.disjoint_cocompact_right`：disjoint_cocompact_right (f : Filter X)
 : Disjoint f (Filter.cocompact X) ↔ exists K in f, IsCompact K
· 使用定理 `Filter.prod_mono_right`：prod_mono_right (f : Filter α) {g₁ g₂ : Filter β
} (hf : g₁ <= g₂) : f ×ˢ g₁ <= f ×ˢ g₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `principal_le_nhdsSet`：principal_le_nhdsSet : 𝓟 s <= 𝓝ˢ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.nhdsSet_prod_eq`：IsCompact.nhdsSet_prod_eq {t : Set Y} (hs : I
sCompact s) (ht : IsCompact t) : 𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.prod_mono_right`：prod_mono_right (ht : t₁ subseteq t₂) : s ×ˢ t₁ sub
seteq s ×ˢ t₂
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem nhdsSet_prod_le_of_disjoint_cocompact {f : Filter Y} (hs : IsCompact s)
    (hf : Disjoint f (Filter.cocompact Y)) :
    𝓝ˢ s ×ˢ f ≤ 𝓝ˢ (s ×ˢ Set.univ) := by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    𝓝ˢ s ×ˢ f
    _ ≤ 𝓝ˢ s ×ˢ 𝓟 K := Filter.prod_mono_right _ (Filter.le_principal_iff.mpr hKf)
    _ ≤ 𝓝ˢ s ×ˢ 𝓝ˢ K := Filter.prod_mono_right _ principal_le_nhdsSet
    _ = 𝓝ˢ (s ×ˢ K) := (hs.nhdsSet_prod_eq hK).symm
    _ ≤ 𝓝ˢ (s ×ˢ Set.univ) := nhdsSet_mono (prod_mono_right le_top)
/-
**prod_nhdsSet_le_of_disjoint_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_nhdsSet_le_of_disjoint_cocompact {t : Set Y} {f : Filter X} (ht : IsC
ompact t) (hf : Disjoint f (Filter.cocompact X)) : f ×ˢ 𝓝ˢ t <= 𝓝ˢ (Set.univ ×ˢ 
t)
参数：ht : IsCompact t；hf : Disjoint f (Filter.cocompact X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.disjoint_cocompact_right`：disjoint_cocompact_right (f : Filter X)
 : Disjoint f (Filter.cocompact X) ↔ exists K in f, IsCompact K
· 使用定理 `Filter.prod_mono_left`：prod_mono_left (g : Filter β) {f₁ f₂ : Filter α} 
(hf : f₁ <= f₂) : f₁ ×ˢ g <= f₂ ×ˢ g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `principal_le_nhdsSet`：principal_le_nhdsSet : 𝓟 s <= 𝓝ˢ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.nhdsSet_prod_eq`：IsCompact.nhdsSet_prod_eq {t : Set Y} (hs : I
sCompact s) (ht : IsCompact t) : 𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.prod_mono_left`：prod_mono_left (hs : s₁ subseteq s₂) : s₁ ×ˢ t subse
teq s₂ ×ˢ t
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem prod_nhdsSet_le_of_disjoint_cocompact {t : Set Y} {f : Filter X} (ht : IsCompact t)
    (hf : Disjoint f (Filter.cocompact X)) :
    f ×ˢ 𝓝ˢ t ≤ 𝓝ˢ (Set.univ ×ˢ t) := by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    f ×ˢ 𝓝ˢ t
    _ ≤ (𝓟 K) ×ˢ 𝓝ˢ t := Filter.prod_mono_left _ (Filter.le_principal_iff.mpr hKf)
    _ ≤ 𝓝ˢ K ×ˢ 𝓝ˢ t := Filter.prod_mono_left _ principal_le_nhdsSet
    _ = 𝓝ˢ (K ×ˢ t) := (hK.nhdsSet_prod_eq ht).symm
    _ ≤ 𝓝ˢ (Set.univ ×ˢ t) := nhdsSet_mono (prod_mono_left le_top)
/-
**nhds_prod_le_of_disjoint_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_prod_le_of_disjoint_cocompact {f : Filter Y} (x : X) (hf : Disjoint f
 (Filter.cocompact Y)) : 𝓝 x ×ˢ f <= 𝓝ˢ ({x} ×ˢ Set.univ)
参数：x : X；hf : Disjoint f (Filter.cocompact Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `nhdsSet_prod_le_of_disjoint_cocompact`：nhdsSet_prod_le_of_disjoint_cocom
pact {f : Filter Y} (hs : IsCompact s) (hf : Disjoint f (Filter.cocompact Y)) : 
𝓝ˢ s ×ˢ f <= 𝓝ˢ (s ×ˢ Set.u…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
-/
theorem nhds_prod_le_of_disjoint_cocompact {f : Filter Y} (x : X)
    (hf : Disjoint f (Filter.cocompact Y)) :
    𝓝 x ×ˢ f ≤ 𝓝ˢ ({x} ×ˢ Set.univ) := by
  simpa using nhdsSet_prod_le_of_disjoint_cocompact isCompact_singleton hf
/-
**prod_nhds_le_of_disjoint_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_nhds_le_of_disjoint_cocompact {f : Filter X} (y : Y) (hf : Disjoint f
 (Filter.cocompact X)) : f ×ˢ 𝓝 y <= 𝓝ˢ (Set.univ ×ˢ {y})
参数：y : Y；hf : Disjoint f (Filter.cocompact X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `prod_nhdsSet_le_of_disjoint_cocompact`：prod_nhdsSet_le_of_disjoint_cocom
pact {t : Set Y} {f : Filter X} (ht : IsCompact t) (hf : Disjoint f (Filter.coco
mpact X)) : f ×ˢ 𝓝ˢ t <= 𝓝ˢ…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
-/
theorem prod_nhds_le_of_disjoint_cocompact {f : Filter X} (y : Y)
    (hf : Disjoint f (Filter.cocompact X)) :
    f ×ˢ 𝓝 y ≤ 𝓝ˢ (Set.univ ×ˢ {y}) := by
  simpa using prod_nhdsSet_le_of_disjoint_cocompact isCompact_singleton hf

/-- If `s` and `t` are compact sets and `n` is an open neighborhood of `s × t`, then there exist
open neighborhoods `u ⊇ s` and `v ⊇ t` such that `u × v ⊆ n`.

See also `IsCompact.nhdsSet_prod_eq`. -/
/-
**generalized_tube_lemma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：generalized_tube_lemma (hs : IsCompact s) {t : Set Y} (ht : IsCompact t) {
n : Set (X × Y)} (hn : IsOpen n) (hp : s ×ˢ t subseteq n) : exists (u : Set X) (
v : Set Y), IsOpen u ∧ IsOpen v ∧ s subseteq u ∧ t subseteq v ∧ u ×ˢ v subseteq 
n
参数：hs : IsCompact s；ht : IsCompact t；X × Y；hn : IsOpen n；hp : s ×ˢ t subseteq n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {l
b : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} 
{pb : ι' →…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `IsCompact.nhdsSet_prod_eq`：IsCompact.nhdsSet_prod_eq {t : Set Y} (hs : I
sCompact s) (ht : IsCompact t) : 𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s

--- 原说明 ---
If `s` and `t` are compact sets and `n` is an open neighborhood of `s × t`, then
 there exist
open neighborhoods `u ⊇ s` and `v ⊇ t` such that `u × v ⊆ n`.

See also `IsCompact.nhdsSet_prod_eq`.
-/
theorem generalized_tube_lemma (hs : IsCompact s) {t : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : IsOpen n) (hp : s ×ˢ t ⊆ n) :
    ∃ (u : Set X) (v : Set Y), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n := by
  rw [← hn.mem_nhdsSet, hs.nhdsSet_prod_eq ht,
    ((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).mem_iff] at hp
  rcases hp with ⟨⟨u, v⟩, ⟨⟨huo, hsu⟩, hvo, htv⟩, hn⟩
  exact ⟨u, v, huo, hvo, hsu, htv, hn⟩

/-- A relative version of `IsCompact.nhdsSet_prod_eq`: if `s` and `t` are compact sets,
then the neighborhoods filter of `s ×ˢ t` within `s' ×ˢ t'` is the product of the neighborhoods
filters of `s` and `t` within `s'` and `t'`.

For general sets, only the `≤` inequality holds, see `nhdsSetWithin_prod_le`. -/
/-
**IsCompact.nhdsSetWithin_prod_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.nhdsSetWithin_prod_eq {s s' : Set X} {t t' : Set Y} (hs : IsComp
act s) (ht : IsCompact t) : 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t) = 𝓝ˢ[s'] s ×ˢ 𝓝ˢ[t'] t
参数：hs : IsCompact s；ht : IsCompact t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsCompact.nhdsSet_prod_eq`：IsCompact.nhdsSet_prod_eq {t : Set Y} (hs : I
sCompact s) (ht : IsCompact t) : 𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t
· 使用定理 `Filter.prod_principal_principal`：prod_principal_principal {s : Set α} {t
 : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A relative version of `IsCompact.nhdsSet_prod_eq`: if `s` and `t` are compact se
ts,
then the neighborhoods filter of `s ×ˢ t` within `s' ×ˢ t'` is the product of th
e neighborhoods
filters of `s` and `t` within `s'` and `t'`.

For general sets, only the `≤` inequality holds, see `nhdsSetWithin_prod_le`.
-/
lemma IsCompact.nhdsSetWithin_prod_eq {s s' : Set X} {t t' : Set Y} (hs : IsCompact s)
    (ht : IsCompact t) : 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t) = 𝓝ˢ[s'] s ×ˢ 𝓝ˢ[t'] t := by
  simp [nhdsSetWithin, ← prod_inf_prod, hs.nhdsSet_prod_eq ht]

open Topology Set in
/-- A variant of `generalized_tube_lemma` in terms of `nhdsSetWithin`. -/
/-
**generalized_tube_lemma'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：generalized_tube_lemma' {s s' : Set X} (hs : IsCompact s) {t t' : Set Y} (
ht : IsCompact t) {n : Set (X × Y)} (hn : n in 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t)) : exists u
 in 𝓝ˢ[s'] s, exists v in 𝓝ˢ[t'] t, u ×ˢ v subseteq n
参数：hs : IsCompact s；ht : IsCompact t；X × Y；hn : n in 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用引理 `IsCompact.nhdsSetWithin_prod_eq`：IsCompact.nhdsSetWithin_prod_eq {s s' :
 Set X} {t t' : Set Y} (hs : IsCompact s) (ht : IsCompact t) : 𝓝ˢ[s' ×ˢ t'] (s ×
ˢ t) = 𝓝ˢ[s'] s ×ˢ 𝓝ˢ…

--- 原说明 ---
A variant of `generalized_tube_lemma` in terms of `nhdsSetWithin`.
-/
lemma generalized_tube_lemma' {s s' : Set X} (hs : IsCompact s) {t t' : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : n ∈ 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t)) :
    ∃ u ∈ 𝓝ˢ[s'] s, ∃ v ∈ 𝓝ˢ[t'] t, u ×ˢ v ⊆ n := by
  rwa [hs.nhdsSetWithin_prod_eq ht, Filter.mem_prod_iff] at hn

open Topology Set in
/-- A variant of `generalized_tube_lemma` that only replaces the set in one direction. -/
/-
**generalized_tube_lemma_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：generalized_tube_lemma_left {s s' : Set X} (hs : IsCompact s) {t : Set Y} 
(ht : IsCompact t) {n : Set (X × Y)} (hn : n in 𝓝ˢ[s' ×ˢ t] (s ×ˢ t)) : exists u
 in 𝓝ˢ[s'] s, u ×ˢ t subseteq n
参数：hs : IsCompact s；ht : IsCompact t；X × Y；hn : n in 𝓝ˢ[s' ×ˢ t] (s ×ˢ t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_prod_principal`：mem_prod_principal {s : Set (α × β)} : s in f
 ×ˢ 𝓟 t ↔ { a | forall b in t, (a, b) in s } in f
· 使用引理 `nhdsSetWithin_self`：nhdsSetWithin_self {s : Set α} : 𝓝ˢ[s] s = 𝓟 s
· 使用引理 `IsCompact.nhdsSetWithin_prod_eq`：IsCompact.nhdsSetWithin_prod_eq {s s' :
 Set X} {t t' : Set Y} (hs : IsCompact s) (ht : IsCompact t) : 𝓝ˢ[s' ×ˢ t'] (s ×
ˢ t) = 𝓝ˢ[s'] s ×ˢ 𝓝ˢ…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A variant of `generalized_tube_lemma` that only replaces the set in one directio
n.
-/
lemma generalized_tube_lemma_left {s s' : Set X} (hs : IsCompact s) {t : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : n ∈ 𝓝ˢ[s' ×ˢ t] (s ×ˢ t)) : ∃ u ∈ 𝓝ˢ[s'] s, u ×ˢ t ⊆ n := by
  rw [hs.nhdsSetWithin_prod_eq ht, nhdsSetWithin_self, Filter.mem_prod_principal] at hn
  exact ⟨_, hn, fun x hx ↦ hx.1 _ hx.2⟩

open Topology Set in
/-- A variant of `generalized_tube_lemma` that only replaces the set in one direction. -/
/-
**generalized_tube_lemma_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：generalized_tube_lemma_right {s : Set X} (hs : IsCompact s) {t t' : Set Y}
 (ht : IsCompact t) {n : Set (X × Y)} (hn : n in 𝓝ˢ[s ×ˢ t'] (s ×ˢ t)) : exists 
u in 𝓝ˢ[t'] t, s ×ˢ u subseteq n
参数：hs : IsCompact s；ht : IsCompact t；X × Y；hn : n in 𝓝ˢ[s ×ˢ t'] (s ×ˢ t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用引理 `nhdsSetWithin_self`：nhdsSetWithin_self {s : Set α} : 𝓝ˢ[s] s = 𝓟 s
· 使用引理 `IsCompact.nhdsSetWithin_prod_eq`：IsCompact.nhdsSetWithin_prod_eq {s s' :
 Set X} {t t' : Set Y} (hs : IsCompact s) (ht : IsCompact t) : 𝓝ˢ[s' ×ˢ t'] (s ×
ˢ t) = 𝓝ˢ[s'] s ×ˢ 𝓝ˢ…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.prod_mono_left`：prod_mono_left (hs : s₁ subseteq s₂) : s₁ ×ˢ t subse
teq s₂ ×ˢ t

--- 原说明 ---
A variant of `generalized_tube_lemma` that only replaces the set in one directio
n.
-/
lemma generalized_tube_lemma_right {s : Set X} (hs : IsCompact s) {t t' : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : n ∈ 𝓝ˢ[s ×ˢ t'] (s ×ˢ t)) : ∃ u ∈ 𝓝ˢ[t'] t, s ×ˢ u ⊆ n := by
  rw [hs.nhdsSetWithin_prod_eq ht, nhdsSetWithin_self, Filter.mem_prod_iff] at hn
  obtain ⟨s', hs', u, hu, h⟩ := hn
  exact ⟨u, hu, (prod_mono_left hs').trans h⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) Subsingleton.compactSpace [Subsingleton X] : CompactSpace X :=
  ⟨subsingleton_univ.isCompact⟩
/-
**isCompact_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_univ_iff : IsCompact (univ : Set X) ↔ CompactSpace X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
-/
theorem isCompact_univ_iff : IsCompact (univ : Set X) ↔ CompactSpace X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

@[compactness ., grind .]
/-
**isCompact_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_univ [h : CompactSpace X] : IsCompact (univ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
-/
theorem isCompact_univ [h : CompactSpace X] : IsCompact (univ : Set X) :=
  h.isCompact_univ
/-
**exists_clusterPt_of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_clusterPt_of_compactSpace [CompactSpace X] (f : Filter X) [NeBot f]
 : exists x, ClusterPt x f
参数：f : Filter X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
-/
theorem exists_clusterPt_of_compactSpace [CompactSpace X] (f : Filter X) [NeBot f] :
    ∃ x, ClusterPt x f := by
  simpa using isCompact_univ (show f ≤ 𝓟 univ by simp)

nonrec theorem Ultrafilter.le_nhds_lim [CompactSpace X] (F : Ultrafilter X) : ↑F ≤ 𝓝 F.lim :=
  have ⟨x, _, h⟩ := isCompact_univ.ultrafilter_le_nhds F (by simp)
  le_nhds_lim ⟨x, h⟩
/-
**CompactSpace.elim_nhds_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompactSpace.elim_nhds_subcover [CompactSpace X] (U : X -> Set X) (hU : fo
rall x, U x in 𝓝 x) : exists t : Finset X, ⋃ x in t, U x = ⊤
参数：U : X -> Set X；hU : forall x, U x in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
-/
theorem CompactSpace.elim_nhds_subcover [CompactSpace X] (U : X → Set X) (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset X, ⋃ x ∈ t, U x = ⊤ :=
  have ⟨t, _, s⟩ := IsCompact.elim_nhds_subcover isCompact_univ U fun x _ => hU x
  ⟨t, top_unique s⟩
/-
**compactSpace_of_finite_subfamily_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactSpace_of_finite_subfamily_closed (h : forall {ι : Type u} (t : ι ->
 Set X), (forall i, IsClosed (t i)) -> ⋂ i, t i = ∅ -> exists u : Finset ι, ⋂ i 
in u, t i = ∅) : CompactSpace X where isCompact_univ
参数：h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> ⋂ i, 
t i = ∅ -> exists u : Finset ι, ⋂ i in u, t i = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_of_finite_subfamily_closed`：isCompact_of_finite_subfamily_clos
ed (h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> (s i
nter ⋂ i, t i) = ∅ -> exis…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem compactSpace_of_finite_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → ⋂ i, t i = ∅ →
      ∃ u : Finset ι, ⋂ i ∈ u, t i = ∅) :
    CompactSpace X where
  isCompact_univ := isCompact_of_finite_subfamily_closed fun t => by simpa using h t

/--
Given a family of closed sets `t i` in a compact space, if they satisfy the Finite Intersection
Property, then the intersection of all `t i` is nonempty.
-/
/-
**CompactSpace.iInter_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompactSpace.iInter_nonempty {ι : Type v} [CompactSpace X] {t : ι -> Set X
} (htc : forall i, IsClosed (t i)) (hst : forall s : Finset ι, (⋂ i in s, t i).N
onempty) : (⋂ i, t i).Nonempty
参数：htc : forall i, IsClosed (t i)；hst : forall s : Finset ι, (⋂ i in s, t i).Non
empty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `IsCompact.inter_iInter_nonempty`：IsCompact.inter_iInter_nonempty {ι : Ty
pe v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst 
: forall u : Finset ι…
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Given a family of closed sets `t i` in a compact space, if they satisfy the Fini
te Intersection
Property, then the intersection of all `t i` is nonempty.
-/
lemma CompactSpace.iInter_nonempty {ι : Type v} [CompactSpace X] {t : ι → Set X}
    (htc : ∀ i, IsClosed (t i))
    (hst : ∀ s : Finset ι, (⋂ i ∈ s, t i).Nonempty) :
    (⋂ i, t i).Nonempty := by
  simpa using isCompact_univ.inter_iInter_nonempty t htc (by simpa using hst)

omit [TopologicalSpace X] in
/--
The `CompactSpace` version of **Alexander's subbasis theorem**. If `X` is a topological space with a
subbasis `S`, then `X` is compact if for any open cover of `X` all of whose elements belong to `S`,
there is a finite subcover.
-/
/-
**compactSpace_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactSpace_generateFrom [T : TopologicalSpace X] {S : Set (Set X)} (hTS 
: T = generateFrom S) (h : forall P subseteq S, ⋃₀ P = univ -> exists Q subseteq
 P, Q.Finite ∧ ⋃₀ Q = univ) : CompactSpace X
参数：Set X；hTS : T = generateFrom S；h : forall P subseteq S, ⋃₀ P = univ -> exists
 Q subseteq P, Q.Finite ∧ ⋃₀ Q = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
· 使用定理 `isCompact_generateFrom`：isCompact_generateFrom [T : TopologicalSpace X] 
{S : Set (Set X)} (hTS : T = generateFrom S) {s : Set X} (h : forall P subseteq 
S, s subsete…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
The `CompactSpace` version of **Alexander's subbasis theorem**. If `X` is a topo
logical space with a
subbasis `S`, then `X` is compact if for any open cover of `X` all of whose elem
ents belong to `S`,
there is a finite subcover.
-/
theorem compactSpace_generateFrom [T : TopologicalSpace X] {S : Set (Set X)}
    (hTS : T = generateFrom S) (h : ∀ P ⊆ S, ⋃₀ P = univ → ∃ Q ⊆ P, Q.Finite ∧ ⋃₀ Q = univ) :
    CompactSpace X :=
  isCompact_univ_iff.mp <| isCompact_generateFrom hTS <| by simpa

omit [TopologicalSpace X] in
/-
**compactSpace_generateFrom'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactSpace_generateFrom' [T : TopologicalSpace X] {S : Set (Set X)} (hTS
 : T = generateFrom S) (h : forall (ι : Type u) (U : ι -> S), ⋃ i, U i = (univ (
α
参数：Set X；hTS : T = generateFrom S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
· 使用定理 `isCompact_generateFrom'`：isCompact_generateFrom' [T : TopologicalSpace X
] {S : Set (Set X)} (hTS : T = generateFrom S) {s : Set X} (h : forall (ι : Type
 u) (U : ι ->…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem compactSpace_generateFrom' [T : TopologicalSpace X] {S : Set (Set X)}
    (hTS : T = generateFrom S)
    (h : ∀ (ι : Type u) (U : ι → S),
      ⋃ i, U i = (univ (α := X)) → ∃ J : Set ι, J.Finite ∧ ⋃ i ∈ J, U i = (univ (α := X))) :
    CompactSpace X :=
  isCompact_univ_iff.mp <| isCompact_generateFrom' hTS <| by simpa

omit [TopologicalSpace X] in
/-
**compactSpace_generateFrom_of_compl_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compactSpace_generateFrom_of_compl_mem [T : TopologicalSpace X] (𝔅 : Set (
Set X)) (hT : T = TopologicalSpace.generateFrom 𝔅) (h𝔅 : forall s in 𝔅, sᶜ in 𝔅)
 (h : forall P subseteq 𝔅, (forall Q subseteq P, Q.Finite -> (⋂₀ Q).Nonempty) ->
 (⋂₀ P).Nonempty) : CompactSpace X
参数：𝔅 : Set (Set X)；hT : T = TopologicalSpace.generateFrom 𝔅；h𝔅 : forall s in 𝔅, 
sᶜ in 𝔅；h : forall P subseteq 𝔅, (forall Q subseteq P, Q.Finite -> (⋂₀ Q).Nonemp
ty) -> (⋂₀ P).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compactSpace_generateFrom`：compactSpace_generateFrom [T : TopologicalSpa
ce X] {S : Set (Set X)} (hTS : T = generateFrom S) (h : forall P subseteq S, ⋃₀ 
P = univ -> exi…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_sUnion`：compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '
' S)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Involutive.image_eq_preimage_symm`：∀ {α : Type u_1} {f : α → α}
, Function.Involutive f → Set.image f = Set.preimage f
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
lemma compactSpace_generateFrom_of_compl_mem [T : TopologicalSpace X]
    (𝔅 : Set (Set X)) (hT : T = TopologicalSpace.generateFrom 𝔅) (h𝔅 : ∀ s ∈ 𝔅, sᶜ ∈ 𝔅)
    (h : ∀ P ⊆ 𝔅, (∀ Q ⊆ P, Q.Finite → (⋂₀ Q).Nonempty) → (⋂₀ P).Nonempty) :
    CompactSpace X := by
  refine compactSpace_generateFrom hT fun P hP𝔅 hP ↦ ?_
  contrapose! hP
  simp_rw [← Set.nonempty_compl, Set.compl_sUnion] at hP ⊢
  refine h _ ?_ fun Q hQP hQ ↦ ?_
  · rintro _ ⟨S, hS, rfl⟩
    exact h𝔅 _ (hP𝔅 hS)
  · replace hP : Q ⊆ compl '' P → (compl '' Q).Finite → (⋂₀ Q).Nonempty := by
      simpa [← compl_involutive.image_eq_preimage_symm] using hP (compl '' Q)
    exact hP hQP (hQ.image _)
/-
**IsClosed.isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.isCompact [CompactSpace X] (h : IsClosed s) : IsCompact s
参数：h : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem IsClosed.isCompact [CompactSpace X] (h : IsClosed s) : IsCompact s :=
  isCompact_univ.of_isClosed_subset h (subset_univ _)

/-- If a filter has a unique cluster point `y` in a compact topological space,
then the filter is less than or equal to `𝓝 y`. -/
/-
**le_nhds_of_unique_clusterPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_nhds_of_unique_clusterPt [CompactSpace X] {l : Filter X} {y : X} (h : f
orall x, ClusterPt x l -> x = y) : l <= 𝓝 y
参数：h : forall x, ClusterPt x l -> x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompact.le_nhds_of_unique_clusterPt`：IsCompact.le_nhds_of_unique_clust
erPt (hs : IsCompact s) {l : Filter X} {y : X} (hmem : s in l) (h : forall x in 
s, ClusterPt x l -> x = y) …
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
If a filter has a unique cluster point `y` in a compact topological space,
then the filter is less than or equal to `𝓝 y`.
-/
lemma le_nhds_of_unique_clusterPt [CompactSpace X] {l : Filter X} {y : X}
    (h : ∀ x, ClusterPt x l → x = y) : l ≤ 𝓝 y :=
  isCompact_univ.le_nhds_of_unique_clusterPt univ_mem fun x _ ↦ h x

/-- If `y` is a unique `MapClusterPt` for `f` along `l`
and the codomain of `f` is a compact space,
then `f` tends to `𝓝 y` along `l`. -/
/-
**tendsto_nhds_of_unique_mapClusterPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_nhds_of_unique_mapClusterPt [CompactSpace X] {Y} {l : Filter Y} {y
 : X} {f : Y -> X} (h : forall x, MapClusterPt x l f -> x = y) : Tendsto f l (𝓝 
y)
参数：h : forall x, MapClusterPt x l f -> x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_nhds_of_unique_clusterPt`：le_nhds_of_unique_clusterPt [CompactSpace X
] {l : Filter X} {y : X} (h : forall x, ClusterPt x l -> x = y) : l <= 𝓝 y

--- 原说明 ---
If `y` is a unique `MapClusterPt` for `f` along `l`
and the codomain of `f` is a compact space,
then `f` tends to `𝓝 y` along `l`.
-/
lemma tendsto_nhds_of_unique_mapClusterPt [CompactSpace X] {Y} {l : Filter Y} {y : X} {f : Y → X}
    (h : ∀ x, MapClusterPt x l f → x = y) :
    Tendsto f l (𝓝 y) :=
  le_nhds_of_unique_clusterPt h
/-
**noncompact_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：noncompact_univ (X : Type*) [TopologicalSpace X] [NoncompactSpace X] : ¬Is
Compact (univ : Set X)
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoncompactSpace.noncompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpa
ce X} [self : NoncompactSpace X], ¬IsCompact Set.univ
-/
lemma noncompact_univ (X : Type*) [TopologicalSpace X] [NoncompactSpace X] :
    ¬IsCompact (univ : Set X) :=
  NoncompactSpace.noncompact_univ
/-
**IsCompact.ne_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.ne_univ [NoncompactSpace X] (hs : IsCompact s) : s != univ
参数：hs : IsCompact s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `noncompact_univ`：noncompact_univ (X : Type*) [TopologicalSpace X] [Nonco
mpactSpace X] : ¬IsCompact (univ : Set X)
-/
theorem IsCompact.ne_univ [NoncompactSpace X] (hs : IsCompact s) : s ≠ univ := fun h =>
  noncompact_univ X (h ▸ hs)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoncompactSpace X] : NeBot (Filter.cocompact X) := by
  refine Filter.hasBasis_cocompact.neBot_iff.2 fun hs => ?_
  contrapose hs; rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]; exact noncompact_univ X

@[simp]
/-
**Filter.cocompact_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.cocompact_eq_bot [CompactSpace X] : Filter.cocompact X = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.eq_bot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l = ⊥ ↔ ∃ i, p i ∧ s i = 
∅)
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
-/
theorem Filter.cocompact_eq_bot [CompactSpace X] : Filter.cocompact X = ⊥ :=
  Filter.hasBasis_cocompact.eq_bot_iff.mpr ⟨Set.univ, isCompact_univ, Set.compl_univ⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoncompactSpace X] : NeBot (Filter.coclosedCompact X) :=
  neBot_of_le Filter.cocompact_le_coclosedCompact
/-
**noncompactSpace_of_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：noncompactSpace_of_neBot (_ : NeBot (Filter.cocompact X)) : NoncompactSpac
e X
参数：_ : NeBot (Filter.cocompact X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `IsCompact.compl_mem_cocompact`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X}, IsCompact s → sᶜ ∈ Filter.cocompact X
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
-/
theorem noncompactSpace_of_neBot (_ : NeBot (Filter.cocompact X)) : NoncompactSpace X :=
  ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_cocompact).ne_empty compl_univ⟩
/-
**Filter.cocompact_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.cocompact_neBot_iff : NeBot (Filter.cocompact X) ↔ NoncompactSpace 
X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noncompactSpace_of_neBot`：noncompactSpace_of_neBot (_ : NeBot (Filter.co
compact X)) : NoncompactSpace X
· 使用定理 `instNeBotCocompactOfNoncompactSpace`：∀ {X : Type u} [inst : TopologicalS
pace X] [NoncompactSpace X], (Filter.cocompact X).NeBot
-/
theorem Filter.cocompact_neBot_iff : NeBot (Filter.cocompact X) ↔ NoncompactSpace X :=
  ⟨noncompactSpace_of_neBot, fun _ => inferInstance⟩
/-
**not_compactSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_compactSpace_iff : ¬CompactSpace X ↔ NoncompactSpace X
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_compactSpace_iff : ¬CompactSpace X ↔ NoncompactSpace X :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoncompactSpace ℤ :=
  noncompactSpace_of_neBot <| by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

-- Note: We can't make this into an instance because it loops with `Finite.compactSpace`.
/-- A compact discrete space is finite. -/
/-
**finite_of_compact_of_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_of_compact_of_discrete [CompactSpace X] [DiscreteTopology X] : Fini
te X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_finite_univ`：∀ {α : Type u}, Set.univ.Finite → Finite α
· 使用定理 `IsCompact.finite_of_discrete`：IsCompact.finite_of_discrete [DiscreteTopo
logy X] (hs : IsCompact s) : s.Finite
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)

--- 原说明 ---
A compact discrete space is finite.
-/
theorem finite_of_compact_of_discrete [CompactSpace X] [DiscreteTopology X] : Finite X :=
  Finite.of_finite_univ <| isCompact_univ.finite_of_discrete
/-
**Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact** 是 Mathl
ib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact {K : 
Set X} (hs : s.Infinite) (hK : IsCompact K) (hsub : s subseteq K) : exists x in 
K, AccPt x (cofinite ⊓ 𝓟 s)
参数：hs : s.Infinite；hK : IsCompact K；hsub : s subseteq K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `accPt_iff_clusterPt`：accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt 
x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F)
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_right_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a 
⊓ b ⊓ c = a ⊓ c ⊓ b
· 使用引理 `Set.Finite.cofinite_inf_principal_compl`：Set.Finite.cofinite_inf_princip
al_compl {s : Set α} (hs : s.Finite) : cofinite ⊓ 𝓟 sᶜ = cofinite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Set.Infinite.cofinite_inf_principal_neBot`：∀ {α : Type u_2} {s : Set α},
 s.Infinite → (Filter.cofinite ⊓ Filter.principal s).NeBot
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
lemma Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact
    {K : Set X} (hs : s.Infinite) (hK : IsCompact K) (hsub : s ⊆ K) :
    ∃ x ∈ K, AccPt x (cofinite ⊓ 𝓟 s) :=
  (@hK _ hs.cofinite_inf_principal_neBot (inf_le_right.trans <| principal_mono.2 hsub)).imp
    fun x hx ↦ by rwa [accPt_iff_clusterPt, inf_comm, inf_right_comm,
      (finite_singleton _).cofinite_inf_principal_compl]
/-
**Set.Infinite.exists_accPt_of_subset_isCompact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Infinite.exists_accPt_of_subset_isCompact {K : Set X} (hs : s.Infinite
) (hK : IsCompact K) (hsub : s subseteq K) : exists x in K, AccPt x (𝓟 s)
参数：hs : s.Infinite；hK : IsCompact K；hsub : s subseteq K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact`：Se
t.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact {K : Set X} (
hs : s.Infinite) (hK : IsCompact K) (hsub : s subseteq K) …
· 使用定理 `AccPt.mono`：AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F <= G) :
 AccPt x G
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma Set.Infinite.exists_accPt_of_subset_isCompact {K : Set X} (hs : s.Infinite)
    (hK : IsCompact K) (hsub : s ⊆ K) : ∃ x ∈ K, AccPt x (𝓟 s) :=
  let ⟨x, hxK, hx⟩ := hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact hK hsub
  ⟨x, hxK, hx.mono inf_le_right⟩
/-
**Set.Infinite.exists_accPt_cofinite_inf_principal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Infinite.exists_accPt_cofinite_inf_principal [CompactSpace X] (hs : s.
Infinite) : exists x, AccPt x (cofinite ⊓ 𝓟 s)
参数：hs : s.Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact`：Se
t.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact {K : Set X} (
hs : s.Infinite) (hK : IsCompact K) (hsub : s subseteq K) …
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma Set.Infinite.exists_accPt_cofinite_inf_principal [CompactSpace X] (hs : s.Infinite) :
    ∃ x, AccPt x (cofinite ⊓ 𝓟 s) := by
  simpa only [mem_univ, true_and]
    using hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact isCompact_univ s.subset_univ
/-
**Set.Infinite.exists_accPt_principal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Infinite.exists_accPt_principal [CompactSpace X] (hs : s.Infinite) : e
xists x, AccPt x (𝓟 s)
参数：hs : s.Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `AccPt.mono`：AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F <= G) :
 AccPt x G
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用引理 `Set.Infinite.exists_accPt_cofinite_inf_principal`：Set.Infinite.exists_ac
cPt_cofinite_inf_principal [CompactSpace X] (hs : s.Infinite) : exists x, AccPt 
x (cofinite ⊓ 𝓟 s)
-/
lemma Set.Infinite.exists_accPt_principal [CompactSpace X] (hs : s.Infinite) : ∃ x, AccPt x (𝓟 s) :=
  hs.exists_accPt_cofinite_inf_principal.imp fun _x hx ↦ hx.mono inf_le_right
/-
**exists_nhds_ne_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nhds_ne_neBot (X : Type*) [TopologicalSpace X] [CompactSpace X] [In
finite X] : exists z : X, (𝓝[!=] z).NeBot
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Set.Infinite.exists_accPt_principal`：Set.Infinite.exists_accPt_principal
 [CompactSpace X] (hs : s.Infinite) : exists x, AccPt x (𝓟 s)
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite
-/
theorem exists_nhds_ne_neBot (X : Type*) [TopologicalSpace X] [CompactSpace X] [Infinite X] :
    ∃ z : X, (𝓝[≠] z).NeBot := by
  simpa [AccPt] using (@infinite_univ X _).exists_accPt_principal
/-
**finite_cover_nhds_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_cover_nhds_interior [CompactSpace X] {U : X -> Set X} (hU : forall 
x, U x in 𝓝 x) : exists t : Finset X, ⋃ x in t, interior (U x) = univ
参数：hU : forall x, U x in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
-/
theorem finite_cover_nhds_interior [CompactSpace X] {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset X, ⋃ x ∈ t, interior (U x) = univ :=
  let ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, univ_subset_iff.1 ht⟩
/-
**finite_cover_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_cover_nhds [CompactSpace X] {U : X -> Set X} (hU : forall x, U x in
 𝓝 x) : exists t : Finset X, ⋃ x in t, U x = univ
参数：hU : forall x, U x in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_cover_nhds_interior`：finite_cover_nhds_interior [CompactSpace X] 
{U : X -> Set X} (hU : forall x, U x in 𝓝 x) : exists t : Finset X, ⋃ x in t, in
terior (U x) = u…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem finite_cover_nhds [CompactSpace X] {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset X, ⋃ x ∈ t, U x = univ :=
  let ⟨t, ht⟩ := finite_cover_nhds_interior hU
  ⟨t, univ_subset_iff.1 <| ht.symm.subset.trans <| iUnion₂_mono fun _ _ => interior_subset⟩

/-- The comap of the cocompact filter on `Y` by a continuous function `f : X → Y` is less than or
equal to the cocompact filter on `X`.
This is a reformulation of the fact that images of compact sets are compact. -/
/-
**Filter.comap_cocompact_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.comap_cocompact_le {f : X -> Y} (hf : Continuous f) : (Filter.cocom
pact Y).comap f <= Filter.cocompact X
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s

--- 原说明 ---
The comap of the cocompact filter on `Y` by a continuous function `f : X → Y` is
 less than or
equal to the cocompact filter on `X`.
This is a reformulation of the fact that images of compact sets are compact.
-/
theorem Filter.comap_cocompact_le {f : X → Y} (hf : Continuous f) :
    (Filter.cocompact Y).comap f ≤ Filter.cocompact X := by
  rw [(Filter.hasBasis_cocompact.comap f).le_basis_iff Filter.hasBasis_cocompact]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

/-- If a filter is disjoint from the cocompact filter, so is its image under any continuous
function. -/
/-
**disjoint_map_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_map_cocompact {g : X -> Y} {f : Filter X} (hg : Continuous g) (hf
 : Disjoint f (Filter.cocompact X)) : Disjoint (map g f) (Filter.cocompact Y)
参数：hg : Continuous g；hf : Disjoint f (Filter.cocompact X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.disjoint_comap_iff_map`：disjoint_comap_iff_map {f : α -> β} {F : 
Filter α} {G : Filter β} : Disjoint F (comap f G) ↔ Disjoint (map f F) G
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Filter.comap_cocompact_le`：Filter.comap_cocompact_le {f : X -> Y} (hf : 
Continuous f) : (Filter.cocompact Y).comap f <= Filter.cocompact X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥

--- 原说明 ---
If a filter is disjoint from the cocompact filter, so is its image under any con
tinuous
function.
-/
theorem disjoint_map_cocompact {g : X → Y} {f : Filter X} (hg : Continuous g)
    (hf : Disjoint f (Filter.cocompact X)) : Disjoint (map g f) (Filter.cocompact Y) := by
  rw [← Filter.disjoint_comap_iff_map, disjoint_iff_inf_le]
  calc
    f ⊓ (comap g (cocompact Y))
    _ ≤ f ⊓ Filter.cocompact X := inf_le_inf_left f (Filter.comap_cocompact_le hg)
    _ = ⊥ := disjoint_iff.mp hf

@[compactness .]
/-
**isCompact_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Continuous f) : IsComp
act (range f)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
-/
theorem isCompact_range [CompactSpace X] {f : X → Y} (hf : Continuous f) : IsCompact (range f) := by
  rw [← image_univ]; exact isCompact_univ.image hf
/-
**Function.Surjective.compactSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Surjective.compactSpace {f : X -> Y} (hf : Continuous f) [Compact
Space X] (hf' : f.Surjective) : CompactSpace Y where isCompact_univ
参数：hf : Continuous f；hf' : f.Surjective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
-/
lemma Function.Surjective.compactSpace {f : X → Y} (hf : Continuous f) [CompactSpace X]
    (hf' : f.Surjective) : CompactSpace Y where
  isCompact_univ := by
    rw [← hf'.range_eq]
    exact isCompact_range hf

@[compactness .]
/-
**isCompact_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_diagonal [CompactSpace X] : IsCompact (diagonal X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Set.range_diag`：range_diag : range Function.diag = diagonal α
-/
theorem isCompact_diagonal [CompactSpace X] : IsCompact (diagonal X) :=
  @range_diag X ▸ isCompact_range (continuous_id.prodMk continuous_id)
/-
**exists_subset_nhds_of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_subset_nhds_of_compactSpace [CompactSpace X] [Nonempty ι] {V : ι ->
 Set X} (hV : Directed (· ⊇ ·) V) (hV_closed : forall i, IsClosed (V i)) {U : Se
t X} (hU : forall x in ⋂ i, V i, U in 𝓝 x) : exists i, V i subseteq U
参数：hV : Directed (· ⊇ ·) V；hV_closed : forall i, IsClosed (V i)；hU : forall x in
 ⋂ i, V i, U in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_nhds_of_isCompact'`：exists_subset_nhds_of_isCompact' [None
mpty ι] {V : ι -> Set X} (hV : Directed (· ⊇ ·) V) (hV_cpct : forall i, IsCompac
t (V i)) (hV_closed : …
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
-/
theorem exists_subset_nhds_of_compactSpace [CompactSpace X] [Nonempty ι]
    {V : ι → Set X} (hV : Directed (· ⊇ ·) V) (hV_closed : ∀ i, IsClosed (V i)) {U : Set X}
    (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
  exists_subset_nhds_of_isCompact' hV (fun i => (hV_closed i).isCompact) hV_closed hU

/-- If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is compact
  if and only if `s` is compact. -/
/-
**Topology.IsInducing.isCompact_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isCompact_iff {f : X -> Y} (hf : IsInducing f) : IsCom
pact s ↔ IsCompact (f '' s)
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Topology.IsInducing.mapClusterPt_iff`：mapClusterPt_iff (hf : IsInducing 
f) {x : X} {l : Filter X} : MapClusterPt (f x) l f ↔ ClusterPt x l

--- 原说明 ---
If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is compact
  if and only if `s` is compact.
-/
theorem Topology.IsInducing.isCompact_iff {f : X → Y} (hf : IsInducing f) :
    IsCompact s ↔ IsCompact (f '' s) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x ∈ s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/-- If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is compact
if and only if `s` is compact. -/
/-
**Topology.IsEmbedding.isCompact_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.isCompact_iff {f : X -> Y} (hf : IsEmbedding f) : IsC
ompact s ↔ IsCompact (f '' s)
参数：hf : IsEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isCompact_iff`：Topology.IsInducing.isCompact_iff {f 
: X -> Y} (hf : IsInducing f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…

--- 原说明 ---
If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is compact
if and only if `s` is compact.
-/
theorem Topology.IsEmbedding.isCompact_iff {f : X → Y} (hf : IsEmbedding f) :
    IsCompact s ↔ IsCompact (f '' s) := hf.isInducing.isCompact_iff

/-- The preimage of a compact set under an inducing map is a compact set. -/
/-
**Topology.IsInducing.isCompact_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isCompact_preimage (hf : IsInducing f) (hf' : IsClosed
 (range f)) {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K)
参数：hf : IsInducing f；hf' : IsClosed (range f)；hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.isCompact_iff`：Topology.IsInducing.isCompact_iff {f 
: X -> Y} (hf : IsInducing f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f

--- 原说明 ---
The preimage of a compact set under an inducing map is a compact set.
-/
theorem Topology.IsInducing.isCompact_preimage (hf : IsInducing f) (hf' : IsClosed (range f))
    {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [hf.isCompact_iff, image_preimage_eq_inter_range]
/-
**Topology.IsInducing.isCompact_preimage_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isCompact_preimage_iff {f : X -> Y} (hf : IsInducing f
) {K : Set Y} (Kf : K subseteq range f) : IsCompact (f ⁻¹' K) ↔ IsCompact K
参数：hf : IsInducing f；Kf : K subseteq range f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.isCompact_iff`：Topology.IsInducing.isCompact_iff {f 
: X -> Y} (hf : IsInducing f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Topology.IsInducing.isCompact_preimage_iff {f : X → Y} (hf : IsInducing f) {K : Set Y}
    (Kf : K ⊆ range f) : IsCompact (f ⁻¹' K) ↔ IsCompact K := by
  rw [hf.isCompact_iff, image_preimage_eq_of_subset Kf]

/-- The preimage of a compact set in the image of an inducing map is compact. -/
/-
**Topology.IsInducing.isCompact_preimage'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isCompact_preimage' (hf : IsInducing f) {K : Set Y} (h
K : IsCompact K) (Kf : K subseteq range f) : IsCompact (f ⁻¹' K)
参数：hf : IsInducing f；hK : IsCompact K；Kf : K subseteq range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsInducing.isCompact_preimage_iff`：Topology.IsInducing.isCompac
t_preimage_iff {f : X -> Y} (hf : IsInducing f) {K : Set Y} (Kf : K subseteq ran
ge f) : IsCompact (f ⁻¹' K) ↔ Is…

--- 原说明 ---
The preimage of a compact set in the image of an inducing map is compact.
-/
lemma Topology.IsInducing.isCompact_preimage' (hf : IsInducing f) {K : Set Y}
    (hK : IsCompact K) (Kf : K ⊆ range f) : IsCompact (f ⁻¹' K) :=
  (hf.isCompact_preimage_iff Kf).2 hK

/-- The preimage of a compact set under a closed embedding is a compact set. -/
/-
**Topology.IsClosedEmbedding.isCompact_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.isCompact_preimage (hf : IsClosedEmbedding f) {
K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K)
参数：hf : IsClosedEmbedding f；hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isCompact_preimage`：Topology.IsInducing.isCompact_pr
eimage (hf : IsInducing f) (hf' : IsClosed (range f)) {K : Set Y} (hK : IsCompac
t K) : IsCompact (f ⁻¹' K)
· 使用定理 `Topology.IsClosedEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Topo…
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…

--- 原说明 ---
The preimage of a compact set under a closed embedding is a compact set.
-/
theorem Topology.IsClosedEmbedding.isCompact_preimage (hf : IsClosedEmbedding f)
    {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K) :=
  hf.isInducing.isCompact_preimage (hf.isClosed_range) hK

/-- A closed embedding is proper, i.e., inverse images of compact sets are contained in compacts.
Moreover, the preimage of a compact set is compact, see `IsClosedEmbedding.isCompact_preimage`. -/
/-
**Topology.IsClosedEmbedding.tendsto_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.tendsto_cocompact (hf : IsClosedEmbedding f) : 
Tendsto f (Filter.cocompact X) (Filter.cocompact Y)
参数：hf : IsClosedEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `IsCompact.compl_mem_cocompact`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X}, IsCompact s → sᶜ ∈ Filter.cocompact X
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)

--- 原说明 ---
A closed embedding is proper, i.e., inverse images of compact sets are contained
 in compacts.
Moreover, the preimage of a compact set is compact, see `IsClosedEmbedding.isCom
pact_preimage`.
-/
theorem Topology.IsClosedEmbedding.tendsto_cocompact (hf : IsClosedEmbedding f) :
    Tendsto f (Filter.cocompact X) (Filter.cocompact Y) :=
  Filter.hasBasis_cocompact.tendsto_right_iff.mpr fun _K hK =>
    (hf.isCompact_preimage hK).compl_mem_cocompact

/-- Sets of subtype are compact iff the image under a coercion is. -/
/-
**Subtype.isCompact_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.isCompact_iff {p : X -> Prop} {s : Set { x // p x }} : IsCompact s
 ↔ IsCompact ((↑) '' s : Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)

--- 原说明 ---
Sets of subtype are compact iff the image under a coercion is.
-/
theorem Subtype.isCompact_iff {p : X → Prop} {s : Set { x // p x }} :
    IsCompact s ↔ IsCompact ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isCompact_iff
/-
**isCompact_iff_isCompact_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_iff_isCompact_univ : IsCompact s ↔ IsCompact (univ : Set s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.isCompact_iff`：Subtype.isCompact_iff {p : X -> Prop} {s : Set { 
x // p x }} : IsCompact s ↔ IsCompact ((↑) '' s : Set X)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCompact_iff_isCompact_univ : IsCompact s ↔ IsCompact (univ : Set s) := by
  rw [Subtype.isCompact_iff, image_univ, Subtype.range_coe]

open scoped Set.Notation in
/-- An elimination theorem for empty intersections of a family of sets
in a compact subset which are closed in the compact subset
but not necessarily in the ambient space. -/
/-
**IsCompact.elim_finite_subfamily_isClosed_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.elim_finite_subfamily_isClosed_subtype {X : Type*} [TopologicalS
pace X] {s : Set X} (ks : IsCompact s) {ι : Type*} (t : ι -> Set X) {I : Set ι} 
(htc : forall i in I, IsClosed (s ↓inter (t i) : Set s)) (hst : s inter ⋂ i in I
, t i = ∅) : exists u : Finset I, s inter ⋂ i in u, t i = ∅
参数：ks : IsCompact s；t : ι -> Set X；htc : forall i in I, IsClosed (s ↓inter (t i)
 : Set s)；hst : s inter ⋂ i in I, t i = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `IsCompact.elim_finite_subfamily_closed`：IsCompact.elim_finite_subfamily_
closed {ι : Type v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClose
d (t i)) (hst : (s inter ⋂ i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_isCompact_univ`：isCompact_iff_isCompact_univ : IsCompact s
 ↔ IsCompact (univ : Set s)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
An elimination theorem for empty intersections of a family of sets
in a compact subset which are closed in the compact subset
but not necessarily in the ambient space.
-/
theorem IsCompact.elim_finite_subfamily_isClosed_subtype
    {X : Type*} [TopologicalSpace X] {s : Set X} (ks : IsCompact s)
    {ι : Type*} (t : ι → Set X) {I : Set ι}
    (htc : ∀ i ∈ I, IsClosed (s ↓∩ (t i) : Set s))
    (hst : s ∩ ⋂ i ∈ I, t i = ∅) :
    ∃ u : Finset I, s ∩ ⋂ i ∈ u, t i = ∅ := by
  suffices univ ∩ ⋂ i, (fun i : I ↦ s ↓∩ t i) i = ∅ by
    simpa [eq_empty_iff_forall_notMem] using
      (isCompact_iff_isCompact_univ.mp ks).elim_finite_subfamily_closed
      (fun i : I ↦ s ↓∩ t i) (fun i ↦ htc i.val i.prop) this
  simpa [Set.eq_empty_iff_forall_notMem, Subtype.forall] using hst
/-
**isCompact_iff_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_iff_compactSpace : IsCompact s ↔ CompactSpace s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isCompact_iff_isCompact_univ`：isCompact_iff_isCompact_univ : IsCompact s
 ↔ IsCompact (univ : Set s)
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
-/
theorem isCompact_iff_compactSpace : IsCompact s ↔ CompactSpace s :=
  isCompact_iff_isCompact_univ.trans isCompact_univ_iff
/-
**IsCompact.finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.finite (hs : IsCompact s) (hs' : IsDiscrete s) : s.Finite
参数：hs : IsCompact s；hs' : IsDiscrete s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `finite_of_compact_of_discrete`：finite_of_compact_of_discrete [CompactSpa
ce X] [DiscreteTopology X] : Finite X
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `IsDiscrete.to_subtype`：∀ {X : Type u_5} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → DiscreteTopology ↑s
-/
theorem IsCompact.finite (hs : IsCompact s) (hs' : IsDiscrete s) : s.Finite :=
  finite_coe_iff.mp (@finite_of_compact_of_discrete _ _
    (isCompact_iff_compactSpace.mp hs) hs'.to_subtype)
/-
**exists_nhds_ne_inf_principal_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nhds_ne_inf_principal_neBot (hs : IsCompact s) (hs' : s.Infinite) :
 exists z in s, (𝓝[!=] z ⊓ 𝓟 s).NeBot
参数：hs : IsCompact s；hs' : s.Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Infinite.exists_accPt_of_subset_isCompact`：Set.Infinite.exists_accPt
_of_subset_isCompact {K : Set X} (hs : s.Infinite) (hK : IsCompact K) (hsub : s 
subseteq K) : exists x in K, AccPt …
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem exists_nhds_ne_inf_principal_neBot (hs : IsCompact s) (hs' : s.Infinite) :
    ∃ z ∈ s, (𝓝[≠] z ⊓ 𝓟 s).NeBot :=
  hs'.exists_accPt_of_subset_isCompact hs Subset.rfl
/-
**Topology.IsClosedEmbedding.noncompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `Topology
.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] [NoncompactSpace X] {f : X → Y},   Topology.IsClosedEmbedding f → No
ncompactSpace Y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noncompactSpace_of_neBot`：noncompactSpace_of_neBot (_ : NeBot (Filter.co
compact X)) : NoncompactSpace X
· 使用定理 `Filter.Tendsto.neBot`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : F
ilter α} {y : Filter β},   Filter.Tendsto f x y → ∀ [hx : x.NeBot], y.NeBot
· 使用定理 `Topology.IsClosedEmbedding.tendsto_cocompact`：Topology.IsClosedEmbedding
.tendsto_cocompact (hf : IsClosedEmbedding f) : Tendsto f (Filter.cocompact X) (
Filter.cocompact Y)
· 使用定理 `instNeBotCocompactOfNoncompactSpace`：∀ {X : Type u} [inst : TopologicalS
pace X] [NoncompactSpace X], (Filter.cocompact X).NeBot
-/
protected theorem Topology.IsClosedEmbedding.noncompactSpace [NoncompactSpace X] {f : X → Y}
    (hf : IsClosedEmbedding f) : NoncompactSpace Y :=
  noncompactSpace_of_neBot hf.tendsto_cocompact.neBot
/-
**Topology.IsClosedEmbedding.compactSpace** 是 Mathlib 中的一个定理，位于命名空间 `Topology.Is
ClosedEmbedding`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] [h : CompactSpace Y] {f : X → Y},   Topology.IsClosedEmbedding f → C
ompactSpace X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.isCompact_iff`：Topology.IsInducing.isCompact_iff {f 
: X -> Y} (hf : IsInducing f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `Topology.IsClosedEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Topo…
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
-/
protected theorem Topology.IsClosedEmbedding.compactSpace [h : CompactSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) : CompactSpace X :=
  ⟨by rw [hf.isInducing.isCompact_iff, image_univ]; exact hf.isClosed_range.isCompact⟩

@[compactness .]
/-
**IsCompact.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) : IsCompa
ct (s ×ˢ t)
参数：hs : IsCompact s；ht : IsCompact t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompact_iff_ultrafilter_le_nhds'`：isCompact_iff_ultrafilter_le_nhds' :
 IsCompact s ↔ forall f : Ultrafilter X, s in f -> exists x in s, ↑f <= 𝓝 x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
-/
theorem IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ˢ t) := by
  rw [isCompact_iff_ultrafilter_le_nhds'] at hs ht ⊢
  intro f hfs
  obtain ⟨x : X, sx : x ∈ s, hx : map Prod.fst f.1 ≤ 𝓝 x⟩ :=
    hs (f.map Prod.fst) (mem_map.2 <| mem_of_superset hfs fun x => And.left)
  obtain ⟨y : Y, ty : y ∈ t, hy : map Prod.snd f.1 ≤ 𝓝 y⟩ :=
    ht (f.map Prod.snd) (mem_map.2 <| mem_of_superset hfs fun x => And.right)
  rw [map_le_iff_le_comap] at hx hy
  refine ⟨⟨x, y⟩, ⟨sx, ty⟩, ?_⟩
  rw [nhds_prod_eq]; exact le_inf hx hy

/-- Finite topological spaces are compact. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite topological spaces are compact.
-/
instance (priority := 100) Finite.compactSpace [Finite X] : CompactSpace X where
  isCompact_univ := finite_univ.isCompact

/-- The indiscrete topology is compact -/
-- see note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instCompactSpace [IndiscreteTopology X] : CompactSpace X where
  isCompact_univ f hf := by simp [clusterPt_of_indiscreteTopology, nonempty_of_neBot f]
/-
**ULift.compactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.compactSpace [CompactSpace X] : CompactSpace (ULift.{v} X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.compactSpace`：∀ {X : Type u} {Y : Type v} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [h : CompactSpace Y] {f :
 X → Y},   Topology.IsClosedE…
· 使用引理 `Topology.IsClosedEmbedding.uliftDown`：Topology.IsClosedEmbedding.uliftDo
wn [TopologicalSpace X] : IsClosedEmbedding (ULift.down : ULift.{v, u} X -> X)
-/
instance ULift.compactSpace [CompactSpace X] : CompactSpace (ULift.{v} X) :=
  IsClosedEmbedding.uliftDown.compactSpace

/-- The product of two compact spaces is compact. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two compact spaces is compact.
-/
instance [CompactSpace X] [CompactSpace Y] : CompactSpace (X × Y) :=
  ⟨by rw [← univ_prod_univ]; exact isCompact_univ.prod isCompact_univ⟩

/-- The disjoint union of two compact spaces is compact. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The disjoint union of two compact spaces is compact.
-/
instance [CompactSpace X] [CompactSpace Y] : CompactSpace (X ⊕ Y) :=
  ⟨by
    rw [← range_inl_union_range_inr]
    exact (isCompact_range continuous_inl).union (isCompact_range continuous_inr)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : ι → Type*} [Finite ι] [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] :
    CompactSpace (Σ i, X i) := by
  refine ⟨?_⟩
  rw [Sigma.univ]
  exact isCompact_iUnion fun i => isCompact_range continuous_sigmaMk

@[compactness .]
/-
**Set.isCompact_sigma** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.isCompact_sigma {X : ι -> Type*} [forall i, TopologicalSpace (X i)] {s
 : Set ι} {t : forall i, Set (X i)} (hs : s.Finite) (ht : forall i in s, IsCompa
ct (t i)) : IsCompact (s.sigma t)
参数：X i；X i；hs : s.Finite；ht : forall i in s, IsCompact (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.sigma_eq_biUnion`：sigma_eq_biUnion : s.sigma t = ⋃ i in s, Sigma.mk 
i '' t i
· 使用定理 `Set.Finite.isCompact_biUnion`：Set.Finite.isCompact_biUnion {s : Set ι} {
f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsCompact (f i)) : IsCompac
t (⋃ i in s, f i)
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)
-/
lemma Set.isCompact_sigma {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {s : Set ι}
    {t : ∀ i, Set (X i)} (hs : s.Finite) (ht : ∀ i ∈ s, IsCompact (t i)) :
    IsCompact (s.sigma t) := by
  rw [Set.sigma_eq_biUnion]
  exact hs.isCompact_biUnion fun i hi ↦ (ht i hi).image continuous_sigmaMk
/-
**IsCompact.sigma_exists_finite_sigma_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.sigma_exists_finite_sigma_eq {X : ι -> Type*} [forall i, Topolog
icalSpace (X i)] (u : Set (Σ i, X i)) (hu : IsCompact u) : exists (s : Set ι) (t
 : forall i, Set (X i)), s.Finite ∧ (forall i, IsCompact (t i)) ∧ s.sigma t = u
参数：X i；u : Set (Σ i, X i)；hu : IsCompact u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `isOpenMap_sigmaMk`：isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ 
i)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.range_sigmaMk`：range_sigmaMk (i : ι) : range (Sigma.mk i : α i -> Si
gma α) = Sigma.fst ⁻¹' {i}
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用引理 `Topology.IsClosedEmbedding.sigmaMk`：Topology.IsClosedEmbedding.sigmaMk {
i : ι} : IsClosedEmbedding (@Sigma.mk ι σ i)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma IsCompact.sigma_exists_finite_sigma_eq {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (u : Set (Σ i, X i)) (hu : IsCompact u) :
    ∃ (s : Set ι) (t : ∀ i, Set (X i)), s.Finite ∧ (∀ i, IsCompact (t i)) ∧ s.sigma t = u := by
  obtain ⟨s, hs⟩ := hu.elim_finite_subcover (fun i : ι ↦ Sigma.mk i '' Sigma.mk i ⁻¹' Set.univ)
    (fun i ↦ isOpenMap_sigmaMk _ <| isOpen_univ.preimage continuous_sigmaMk)
    fun x hx ↦ (by simp)
  use s, fun i ↦ Sigma.mk i ⁻¹' u, s.finite_toSet, fun i ↦ ?_, ?_
  · exact Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hu
  · ext x
    simp only [Set.mem_sigma_iff, Finset.mem_coe, Set.mem_preimage, and_iff_right_iff_imp]
    intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    simp_all

/-- The coproduct of the cocompact filters on two topological spaces is the cocompact filter on
their product. -/
/-
**Filter.coprod_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.coprod_cocompact : (Filter.cocompact X).coprod (Filter.cocompact Y)
 = Filter.cocompact (X × Y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Filter.comap_cocompact_le`：Filter.comap_cocompact_le {f : X -> Y} (hf : 
Continuous f) : (Filter.cocompact Y).comap f <= Filter.cocompact X
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Filter.HasBasis.coprod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} 
{lb : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α
} {pb : ι' →…
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用引理 `Set.compl_prod_eq_union`：compl_prod_eq_union {α β : Type*} (s : Set α) (
t : Set β) : (s ×ˢ t)ᶜ = (sᶜ ×ˢ univ) union (univ ×ˢ tᶜ)
· 使用定理 `IsCompact.compl_mem_cocompact`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X}, IsCompact s → sᶜ ∈ Filter.cocompact X
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The coproduct of the cocompact filters on two topological spaces is the cocompac
t filter on
their product.
-/
theorem Filter.coprod_cocompact :
    (Filter.cocompact X).coprod (Filter.cocompact Y) = Filter.cocompact (X × Y) := by
  apply le_antisymm
  · exact sup_le (comap_cocompact_le continuous_fst) (comap_cocompact_le continuous_snd)
  · refine (hasBasis_cocompact.coprod hasBasis_cocompact).ge_iff.2 fun K hK ↦ ?_
    rw [← univ_prod, ← prod_univ, ← compl_prod_eq_union]
    exact (hK.1.prod hK.2).compl_mem_cocompact
/-
**Prod.noncompactSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.noncompactSpace_iff : NoncompactSpace (X × Y) ↔ NoncompactSpace X ∧ N
onempty Y ∨ Nonempty X ∧ NoncompactSpace Y
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Prod.noncompactSpace_iff :
    NoncompactSpace (X × Y) ↔ NoncompactSpace X ∧ Nonempty Y ∨ Nonempty X ∧ NoncompactSpace Y := by
  simp [← Filter.cocompact_neBot_iff, ← Filter.coprod_cocompact, Filter.coprod_neBot_iff]

-- See Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Prod.noncompactSpace_left [NoncompactSpace X] [Nonempty Y] :
    NoncompactSpace (X × Y) :=
  Prod.noncompactSpace_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

-- See Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Prod.noncompactSpace_right [Nonempty X] [NoncompactSpace Y] :
    NoncompactSpace (X × Y) :=
  Prod.noncompactSpace_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

section Tychonoff

variable {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- **Tychonoff's theorem**: product of compact sets is compact. -/
/-
**isCompact_pi_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_pi_infinite {s : forall i, Set (X i)} : (forall i, IsCompact (s 
i)) -> IsCompact { x : forall i, X i | forall i, x i in s i }
参数：X i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
**Tychonoff's theorem**: product of compact sets is compact.
-/
theorem isCompact_pi_infinite {s : ∀ i, Set (X i)} :
    (∀ i, IsCompact (s i)) → IsCompact { x : ∀ i, X i | ∀ i, x i ∈ s i } := by
  simp only [isCompact_iff_ultrafilter_le_nhds, nhds_pi, le_pi, le_principal_iff]
  intro h f hfs
  have : ∀ i : ι, ∃ x, x ∈ s i ∧ Tendsto (Function.eval i) f (𝓝 x) := by
    refine fun i => h i (f.map _) (mem_map.2 ?_)
    exact mem_of_superset hfs fun x hx => hx i
  choose x hx using this
  exact ⟨x, fun i => (hx i).left, fun i => (hx i).right⟩

/-- **Tychonoff's theorem** formulated using `Set.pi`: product of compact sets is compact. -/
/-
**isCompact_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_univ_pi {s : forall i, Set (X i)} (h : forall i, IsCompact (s i)
) : IsCompact (pi univ s)
参数：X i；h : forall i, IsCompact (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isCompact_pi_infinite`：isCompact_pi_infinite {s : forall i, Set (X i)} :
 (forall i, IsCompact (s i)) -> IsCompact { x : forall i, X i | forall i, x i in
 s i }

--- 原说明 ---
**Tychonoff's theorem** formulated using `Set.pi`: product of compact sets is co
mpact.
-/
theorem isCompact_univ_pi {s : ∀ i, Set (X i)} (h : ∀ i, IsCompact (s i)) :
    IsCompact (pi univ s) := by
  convert! isCompact_pi_infinite h
  simp only [← mem_univ_pi, ofPred_mem_eq]
/-
**Pi.compactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.compactSpace [forall i, CompactSpace (X i)] : CompactSpace (forall i, X
 i)
参数：X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
-/
instance Pi.compactSpace [∀ i, CompactSpace (X i)] : CompactSpace (∀ i, X i) :=
  ⟨by rw [← pi_univ univ]; exact isCompact_univ_pi fun i => isCompact_univ⟩
/-
**Function.compactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.compactSpace [CompactSpace Y] : CompactSpace (ι -> Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Function.compactSpace [CompactSpace Y] : CompactSpace (ι → Y) :=
  Pi.compactSpace
/-
**Pi.isCompact_iff_of_isClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.isCompact_iff_of_isClosed {s : Set (Π i, X i)} (hs : IsClosed s) : IsCo
mpact s ↔ forall i, IsCompact (eval i '' s)
参数：Π i, X i；hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `Set.subset_pi_eval_image`：subset_pi_eval_image (s : Set ι) (u : Set (for
all i, α i)) : u subseteq pi s fun i => eval i '' u
-/
lemma Pi.isCompact_iff_of_isClosed {s : Set (Π i, X i)} (hs : IsClosed s) :
    IsCompact s ↔ ∀ i, IsCompact (eval i '' s) := by
  constructor <;> intro H
  · exact fun i ↦ H.image <| continuous_apply i
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H) hs (subset_pi_eval_image univ s)
/-
**Pi.exists_compact_superset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_1} {X : ι → Type u_2} [inst : (i : ι) → TopologicalSpace (X 
i)] {s : Set ((i : ι) → X i)},   (∃ K, IsCompact K ∧ s ⊆ K) ↔ ∀ (i : ι), ∃ Ki, I
sCompact Ki ∧ s ⊆ Function.eval i ⁻¹' Ki
参数：i : ι；X i；(i : ι) → X i；∃ K, IsCompact K ∧ s ⊆ K；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
protected lemma Pi.exists_compact_superset_iff {s : Set (Π i, X i)} :
    (∃ K, IsCompact K ∧ s ⊆ K) ↔ ∀ i, ∃ Ki, IsCompact Ki ∧ s ⊆ eval i ⁻¹' Ki := by
  constructor
  · intro ⟨K, hK, hsK⟩ i
    exact ⟨eval i '' K, hK.image <| continuous_apply i, hsK.trans <| K.subset_preimage_image _⟩
  · intro H
    choose K hK hsK using H
    exact ⟨pi univ K, isCompact_univ_pi hK, fun _ hx i _ ↦ hsK i hx⟩

/-- **Tychonoff's theorem** formulated in terms of filters: `Filter.cocompact` on an indexed product
type `Π d, X d` the `Filter.coprodᵢ` of filters `Filter.cocompact` on `X d`. -/
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Tychonoff's theorem** formulated in terms of filters: `Filter.cocompact` on an
 indexed product
type `Π d, X d` the `Filter.coprodᵢ` of filters `Filter.cocompact` on `X d`.
-/
theorem Filter.coprodᵢ_cocompact {X : ι → Type*} [∀ d, TopologicalSpace (X d)] :
    (Filter.coprodᵢ fun d => Filter.cocompact (X d)) = Filter.cocompact (∀ d, X d) := by
  refine le_antisymm (iSup_le fun i => Filter.comap_cocompact_le (continuous_apply i)) ?_
  refine compl_surjective.forall.2 fun s H => ?_
  simp only [compl_mem_coprodᵢ, Filter.mem_cocompact, compl_subset_compl, image_subset_iff] at H ⊢
  choose K hKc htK using H
  exact ⟨Set.pi univ K, isCompact_univ_pi hKc, fun f hf i _ => htK i hf⟩

end Tychonoff

/-
**Quot.compactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quot.compactSpace {r : X -> X -> Prop} [CompactSpace X] : CompactSpace (Qu
ot r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_quot_mk`：range_quot_mk (r : α -> α -> Prop) : range (Quot.mk r
) = univ
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
-/
instance Quot.compactSpace {r : X → X → Prop} [CompactSpace X] : CompactSpace (Quot r) :=
  ⟨by
    rw [← range_quot_mk]
    exact isCompact_range continuous_quot_mk⟩
/-
**Quotient.compactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.compactSpace {s : Setoid X} [CompactSpace X] : CompactSpace (Quot
ient s)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Quotient.compactSpace {s : Setoid X} [CompactSpace X] : CompactSpace (Quotient s) :=
  Quot.compactSpace
/-
**IsClosed.exists_minimal_nonempty_closed_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.exists_minimal_nonempty_closed_subset [CompactSpace X] {S : Set X
} (hS : IsClosed S) (hne : S.Nonempty) : exists V : Set X, V subseteq S ∧ V.None
mpty ∧ IsClosed V ∧ forall V' : Set X, V' subseteq V -> V'.Nonempty -> IsClosed 
V' -> V' = V
参数：hS : IsClosed S；hne : S.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_subset`：zorn_subset (S : Set (Set α)) (h : forall c subseteq S, IsC
hain (· subseteq ·) c -> exists ub in S, forall s in c, s subseteq ub) : exists 
m…
· 使用定理 `isOpen_sUnion`：isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpe
n t) : IsOpen (⋃₀ s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `Maximal.eq_of_ge`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Part
ialOrder α], Maximal P x → P y → x ≤ y → y = x
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem IsClosed.exists_minimal_nonempty_closed_subset [CompactSpace X] {S : Set X}
    (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ V : Set X, V ⊆ S ∧ V.Nonempty ∧ IsClosed V ∧
      ∀ V' : Set X, V' ⊆ V → V'.Nonempty → IsClosed V' → V' = V := by
  let opens := { U : Set X | Sᶜ ⊆ U ∧ IsOpen U ∧ Uᶜ.Nonempty }
  obtain ⟨U, h⟩ :=
    zorn_subset opens fun c hc hz => by
      by_cases hcne : c.Nonempty
      · obtain ⟨U₀, hU₀⟩ := hcne
        have : Nonempty { U // U ∈ c } := ⟨⟨U₀, hU₀⟩⟩
        obtain ⟨U₀compl, -, -⟩ := hc hU₀
        use ⋃₀ c
        refine ⟨⟨?_, ?_, ?_⟩, fun U hU _ hx => ⟨U, hU, hx⟩⟩
        · exact fun _ hx => ⟨U₀, hU₀, U₀compl hx⟩
        · exact isOpen_sUnion fun _ h => (hc h).2.1
        · convert_to (⋂ U : { U // U ∈ c }, U.1ᶜ).Nonempty
          · ext
            simp only [not_exists, not_and, Set.mem_iInter, Subtype.forall,
              mem_compl_iff, mem_sUnion]
          apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          · rintro ⟨U, hU⟩ ⟨U', hU'⟩
            obtain ⟨V, hVc, hVU, hVU'⟩ := hz.directedOn U hU U' hU'
            exact ⟨⟨V, hVc⟩, Set.compl_subset_compl.mpr hVU, Set.compl_subset_compl.mpr hVU'⟩
          · exact fun U => (hc U.2).2.2
          · exact fun U => (hc U.2).2.1.isClosed_compl.isCompact
          · exact fun U => (hc U.2).2.1.isClosed_compl
      · use Sᶜ
        refine ⟨⟨Set.Subset.refl _, isOpen_compl_iff.mpr hS, ?_⟩, fun U Uc => (hcne ⟨U, Uc⟩).elim⟩
        rw [compl_compl]
        exact hne
  obtain ⟨Uc, Uo, Ucne⟩ := h.prop
  refine ⟨Uᶜ, Set.compl_subset_comm.mp Uc, Ucne, Uo.isClosed_compl, ?_⟩
  intro V' V'sub V'ne V'cls
  have : V'ᶜ = U := by
    refine h.eq_of_ge ⟨?_, isOpen_compl_iff.mpr V'cls, ?_⟩ (subset_compl_comm.2 V'sub)
    · exact Set.Subset.trans Uc (Set.subset_compl_comm.mp V'sub)
    · simp only [compl_compl, V'ne]
  rw [← this, compl_compl]

end Compact

