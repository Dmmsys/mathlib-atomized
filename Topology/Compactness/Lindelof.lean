/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Lindelöf sets and Lindelöf spaces

## Main definitions

We define the following properties for sets in a topological space:

* `IsLindelof s`: Two definitions are possible here. The more standard definition is that
  every open cover that contains `s` contains a countable subcover. We choose for the equivalent
  definition where we require that every nontrivial filter on `s` with the countable intersection
  property has a cluster point. Equivalence is established in `isLindelof_iff_countable_subcover`.
* `LindelofSpace X`: `X` is Lindelöf if it is Lindelöf as a set.
* `NonLindelofSpace`: a space that is not a Lindelöf space, e.g. the Long Line.

## Main results

* `isLindelof_iff_countable_subcover`: A set is Lindelöf iff every open cover has a
  countable subcover.

## Implementation details

* This API is mainly based on the API for IsCompact and follows notation and style as much
  as possible.
-/

@[expose] public section
open Set Filter Topology TopologicalSpace


universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Lindelof

/-- A set `s` is Lindelöf if every nontrivial filter `f` with the countable intersection
  property that contains `s`, has a cluster point in `s`. The filter-free definition is given by
  `isLindelof_iff_countable_subcover`. -/
/-
**IsLindelof** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLindelof (s : Set X)
参数：s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is Lindelöf if every nontrivial filter `f` with the countable intersec
tion
  property that contains `s`, has a cluster point in `s`. The filter-free defini
tion is given by
  `isLindelof_iff_countable_subcover`.
-/
def IsLindelof (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f] [CountableInterFilter f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

/-- The complement to a Lindelöf set belongs to a filter `f` with the countable intersection
  property if it belongs to each filter `𝓝 x ⊓ f`, `x ∈ s`. -/
/-
**IsLindelof.compl_mem_sets** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.compl_mem_sets (hs : IsLindelof s) {f : Filter X} [CountableInt
erFilter f] (hf : forall x in s, sᶜ in 𝓝 x ⊓ f) : sᶜ in f
参数：hs : IsLindelof s；hf : forall x in s, sᶜ in 𝓝 x ⊓ f。
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
The complement to a Lindelöf set belongs to a filter `f` with the countable inte
rsection
  property if it belongs to each filter `𝓝 x ⊓ f`, `x ∈ s`.
-/
theorem IsLindelof.compl_mem_sets (hs : IsLindelof s) {f : Filter X} [CountableInterFilter f]
    (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) : sᶜ ∈ f := by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact hs inf_le_right

/-- The complement to a Lindelöf set belongs to a filter `f` with the countable intersection
  property if each `x ∈ s` has a neighborhood `t` within `s` such that `tᶜ` belongs to `f`. -/
/-
**IsLindelof.compl_mem_sets_of_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.compl_mem_sets_of_nhdsWithin (hs : IsLindelof s) {f : Filter X}
 [CountableInterFilter f] (hf : forall x in s, exists t in 𝓝[s] x, tᶜ in f) : sᶜ
 in f
参数：hs : IsLindelof s；hf : forall x in s, exists t in 𝓝[s] x, tᶜ in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.compl_mem_sets`：IsLindelof.compl_mem_sets (hs : IsLindelof s)
 {f : Filter X} [CountableInterFilter f] (hf : forall x in s, sᶜ in 𝓝 x ⊓ f) : s
ᶜ in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.disjoint_principal_right`：disjoint_principal_right {f : Filter α}
 {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ in f
· 使用定理 `disjoint_right_comm`：disjoint_right_comm : Disjoint (a ⊓ b) c ↔ Disjoint
 (a ⊓ c) b
· 使用定理 `Filter.HasBasis.disjoint_iff_left`：∀ {α : Type u_1} {ι : Sort u_4} {l l'
 : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l l' ↔
 ∃ i, p i ∧ (s i)ᶜ ∈ l'…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id

--- 原说明 ---
The complement to a Lindelöf set belongs to a filter `f` with the countable inte
rsection
  property if each `x ∈ s` has a neighborhood `t` within `s` such that `tᶜ` belo
ngs to `f`.
-/
theorem IsLindelof.compl_mem_sets_of_nhdsWithin (hs : IsLindelof s) {f : Filter X}
    [CountableInterFilter f] (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine hs.compl_mem_sets fun x hx ↦ ?_
  rw [← disjoint_principal_right, disjoint_right_comm, (basis_sets _).disjoint_iff_left]
  exact hf x hx

set_option backward.isDefEq.respectTransparency false in
/-- If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a Lindelöf set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
/-
**IsLindelof.induction_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.induction_on (hs : IsLindelof s) {p : Set X -> Prop} (hmono : f
orall ⦃s t⦄, s subseteq t -> p t -> p s) (hcountable_union : forall (S : Set (Se
t X)), S.Countable -> (forall s in S, p s) -> p (⋃₀ S)) (hnhds : forall x in s, 
exists t in 𝓝[s] x, p t) : p s
参数：hs : IsLindelof s；hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s；hcountable
_union : forall (S : Set (Set X)), S.Countable -> (forall s in S, p s) -> p (⋃₀ 
S)；hnhds : forall x in s, exists t in 𝓝[s] x, p t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.compl_mem_sets_of_nhdsWithin`：IsLindelof.compl_mem_sets_of_nh
dsWithin (hs : IsLindelof s) {f : Filter X} [CountableInterFilter f] (hf : foral
l x in s, exists t in 𝓝[s] x,…
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
  of a Lindelöf set `s` has a neighborhood `t` within `s` such that `p t`, then 
`p s` holds.
-/
theorem IsLindelof.induction_on (hs : IsLindelof s) {p : Set X → Prop}
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s)
    (hcountable_union : ∀ (S : Set (Set X)), S.Countable → (∀ s ∈ S, p s) → p (⋃₀ S))
    (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter X := ofCountableUnion {t | p t} hcountable_union (fun t ht _ hsub ↦ hmono hsub ht)
  have : sᶜ ∈ f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using! hnhds)
  rwa [← compl_compl s]

/-- The intersection of a Lindelöf set and a closed set is a Lindelöf set. -/
/-
**IsLindelof.inter_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.inter_right (hs : IsLindelof s) (ht : IsClosed t) : IsLindelof 
(s inter t)
参数：hs : IsLindelof s；ht : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `IsClosed.mem_of_nhdsWithin_neBot`：IsClosed.mem_of_nhdsWithin_neBot {s : 
Set α} (hs : IsClosed s) {x : α} (hx : NeBot <| 𝓝[s] x) : x in s
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The intersection of a Lindelöf set and a closed set is a Lindelöf set.
-/
theorem IsLindelof.inter_right (hs : IsLindelof s) (ht : IsClosed t) : IsLindelof (s ∩ t) := by
  intro f hnf _ hstf
  rw [← inf_principal, le_inf_iff] at hstf
  obtain ⟨x, hsx, hx⟩ : ∃ x ∈ s, ClusterPt x f := hs hstf.1
  have hxt : x ∈ t := ht.mem_of_nhdsWithin_neBot <| hx.mono hstf.2
  exact ⟨x, ⟨hsx, hxt⟩, hx⟩

/-- The intersection of a closed set and a Lindelöf set is a Lindelöf set. -/
/-
**IsLindelof.inter_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.inter_left (ht : IsLindelof t) (hs : IsClosed s) : IsLindelof (
s inter t)
参数：ht : IsLindelof t；hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.inter_right`：IsLindelof.inter_right (hs : IsLindelof s) (ht :
 IsClosed t) : IsLindelof (s inter t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
The intersection of a closed set and a Lindelöf set is a Lindelöf set.
-/
theorem IsLindelof.inter_left (ht : IsLindelof t) (hs : IsClosed s) : IsLindelof (s ∩ t) :=
  inter_comm t s ▸ ht.inter_right hs

/-- The set difference of a Lindelöf set and an open set is a Lindelöf set. -/
/-
**IsLindelof.diff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.diff (hs : IsLindelof s) (ht : IsOpen t) : IsLindelof (s \ t)
参数：hs : IsLindelof s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.inter_right`：IsLindelof.inter_right (hs : IsLindelof s) (ht :
 IsClosed t) : IsLindelof (s inter t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s

--- 原说明 ---
The set difference of a Lindelöf set and an open set is a Lindelöf set.
-/
theorem IsLindelof.diff (hs : IsLindelof s) (ht : IsOpen t) : IsLindelof (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)

/-- A closed subset of a Lindelöf set is a Lindelöf set. -/
/-
**IsLindelof.of_isClosed_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.of_isClosed_subset (hs : IsLindelof s) (ht : IsClosed t) (h : t
 subseteq s) : IsLindelof t
参数：hs : IsLindelof s；ht : IsClosed t；h : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.inter_right`：IsLindelof.inter_right (hs : IsLindelof s) (ht :
 IsClosed t) : IsLindelof (s inter t)
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t

--- 原说明 ---
A closed subset of a Lindelöf set is a Lindelöf set.
-/
theorem IsLindelof.of_isClosed_subset (hs : IsLindelof s) (ht : IsClosed t) (h : t ⊆ s) :
    IsLindelof t := inter_eq_self_of_subset_right h ▸ hs.inter_right ht

/-- A continuous image of a Lindelöf set is a Lindelöf set. -/
/-
**IsLindelof.image_of_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.image_of_continuousOn {f : X -> Y} (hs : IsLindelof s) (hf : Co
ntinuousOn f s) : IsLindelof (f '' s)
参数：hs : IsLindelof s；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_inf_principal_neBot_of_image_mem`：comap_inf_principal_neBot
_of_image_mem {f : Filter β} {m : α -> β} (hf : NeBot f) {s : Set α} (hs : m '' 
s in f) : NeBot (comap m f ⊓ 𝓟 s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `instCountableInterFilterComap`：∀ {α : Type u_2} {β : Type u_3} (l : Filt
er β) [CountableInterFilter l] (f : α → β),   CountableInterFilter (Filter.comap
 f l)
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

--- 原说明 ---
A continuous image of a Lindelöf set is a Lindelöf set.
-/
theorem IsLindelof.image_of_continuousOn {f : X → Y} (hs : IsLindelof s) (hf : ContinuousOn f s) :
    IsLindelof (f '' s) := by
  intro l lne _ ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this _ inf_le_right
  have := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert! (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

/-- A continuous image of a Lindelöf set is a Lindelöf set within the codomain. -/
/-
**IsLindelof.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.image {f : X -> Y} (hs : IsLindelof s) (hf : Continuous f) : Is
Lindelof (f '' s)
参数：hs : IsLindelof s；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.image_of_continuousOn`：IsLindelof.image_of_continuousOn {f : 
X -> Y} (hs : IsLindelof s) (hf : ContinuousOn f s) : IsLindelof (f '' s)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
A continuous image of a Lindelöf set is a Lindelöf set within the codomain.
-/
theorem IsLindelof.image {f : X → Y} (hs : IsLindelof s) (hf : Continuous f) :
    IsLindelof (f '' s) := hs.image_of_continuousOn hf.continuousOn

/-- A filter with the countable intersection property that is finer than the principal filter on
a Lindelöf set `s` contains any open set that contains all cluster points of `s`. -/
/-
**IsLindelof.adherence_nhdset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.adherence_nhdset {f : Filter X} [CountableInterFilter f] (hs : 
IsLindelof s) (hf₂ : f <= 𝓟 s) (ht₁ : IsOpen t) (ht₂ : forall x in s, ClusterPt 
x f -> x in t) : t in f
参数：hs : IsLindelof s；hf₂ : f <= 𝓟 s；ht₁ : IsOpen t；ht₂ : forall x in s, ClusterP
t x f -> x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
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

--- 原说明 ---
A filter with the countable intersection property that is finer than the princip
al filter on
a Lindelöf set `s` contains any open set that contains all cluster points of `s`
.
-/
theorem IsLindelof.adherence_nhdset {f : Filter X} [CountableInterFilter f] (hs : IsLindelof s)
    (hf₂ : f ≤ 𝓟 s) (ht₁ : IsOpen t) (ht₂ : ∀ x ∈ s, ClusterPt x f → x ∈ t) : t ∈ f :=
  (eq_or_neBot _).casesOn mem_of_eq_bot fun _ ↦
    let ⟨x, hx, hfx⟩ := @hs (f ⊓ 𝓟 tᶜ) _ _ <| inf_le_of_left_le hf₂
    have : x ∈ t := ht₂ x hx hfx.of_inf_left
    have : tᶜ ∩ t ∈ 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (ht₁.mem_nhds this)
    have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 <| compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x ≠ ⊥ := hfx.of_inf_right.ne
    absurd A this

/-- For every open cover of a Lindelöf set, there exists a countable subcover. -/
/-
**IsLindelof.elim_countable_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.elim_countable_subcover {ι : Type v} (hs : IsLindelof s) (U : ι
 -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s subseteq ⋃ i, U i) : exists r
 : Set ι, r.Countable ∧ (s subseteq ⋃ i in r, U i)
参数：hs : IsLindelof s；U : ι -> Set X；hUo : forall i, IsOpen (U i)；hsU : s subsete
q ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Countable.biUnion_iff`：∀ {α : Type u} {β : Type v} {s : Set α} {t : 
(a : α) → a ∈ s → Set β},   s.Countable → ((⋃ a, ⋃ (h : a ∈ s), t a h).Countable
 ↔ ∀ (a : α) (h…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.sUnion_subset`：sUnion_subset {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t' subseteq t) : ⋃₀ S subseteq t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_and'`：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `IsLindelof.induction_on`：IsLindelof.induction_on (hs : IsLindelof s) {p 
: Set X -> Prop} (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hcountable_
union : foral…

--- 原说明 ---
For every open cover of a Lindelöf set, there exists a countable subcover.
-/
theorem IsLindelof.elim_countable_subcover {ι : Type v} (hs : IsLindelof s) (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) :
    ∃ r : Set ι, r.Countable ∧ (s ⊆ ⋃ i ∈ r, U i) := by
  have hmono : ∀ ⦃s t : Set X⦄, s ⊆ t → (∃ r : Set ι, r.Countable ∧ t ⊆ ⋃ i ∈ r, U i)
      → (∃ r : Set ι, r.Countable ∧ s ⊆ ⋃ i ∈ r, U i) := by
    intro _ _ hst ⟨r, ⟨hrcountable, hsub⟩⟩
    exact ⟨r, hrcountable, Subset.trans hst hsub⟩
  have hcountable_union : ∀ (S : Set (Set X)), S.Countable
      → (∀ s ∈ S, ∃ r : Set ι, r.Countable ∧ (s ⊆ ⋃ i ∈ r, U i))
      → ∃ r : Set ι, r.Countable ∧ (⋃₀ S ⊆ ⋃ i ∈ r, U i) := by
    intro S hS hsr
    choose! r hr using hsr
    refine ⟨⋃ s ∈ S, r s, hS.biUnion_iff.mpr (fun s hs ↦ (hr s hs).1), ?_⟩
    refine sUnion_subset ?h.right.h
    simp only [mem_iUnion, exists_prop, iUnion_exists, biUnion_and']
    exact fun i is x hx ↦ mem_biUnion is ((hr i is).2 hx)
  have h_nhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∃ r : Set ι, r.Countable ∧ (t ⊆ ⋃ i ∈ r, U i) := by
    intro x hx
    let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
    refine ⟨U i, mem_nhdsWithin_of_mem_nhds ((hUo i).mem_nhds hi), {i}, by simp, ?_⟩
    simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
    exact Subset.refl _
  exact hs.induction_on hmono hcountable_union h_nhds
/-
**IsLindelof.elim_nhds_subcover'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.elim_nhds_subcover' (hs : IsLindelof s) (U : forall x in s, Set
 X) (hU : forall x (hx : x in s), U x ‹x in s› in 𝓝 x) : exists t : Set s, t.Cou
ntable ∧ s subseteq ⋃ x in t, U (x : s) x.2
参数：hs : IsLindelof s；U : forall x in s, Set X；hU : forall x (hx : x in s), U x ‹
x in s› in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsLindelof.elim_countable_subcover`：IsLindelof.elim_countable_subcover {
ι : Type v} (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) 
(hsU : s subseteq ⋃ i, U…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem IsLindelof.elim_nhds_subcover' (hs : IsLindelof s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x (hx : x ∈ s), U x ‹x ∈ s› ∈ 𝓝 x) :
    ∃ t : Set s, t.Countable ∧ s ⊆ ⋃ x ∈ t, U (x : s) x.2 := by
  have := hs.elim_countable_subcover (fun x : s ↦ interior (U x x.2)) (fun _ ↦ isOpen_interior)
    fun x hx ↦
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 <| hU _ _⟩
  rcases this with ⟨r, ⟨hr, hs⟩⟩
  use r, hr
  apply Subset.trans hs
  apply iUnion₂_subset
  intro i hi
  apply Subset.trans interior_subset
  exact subset_iUnion_of_subset i (subset_iUnion_of_subset hi (Subset.refl _))
/-
**IsLindelof.elim_nhds_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.elim_nhds_subcover (hs : IsLindelof s) (U : X -> Set X) (hU : f
orall x in s, U x in 𝓝 x) : exists t : Set X, t.Countable ∧ (forall x in t, x in
 s) ∧ s subseteq ⋃ x in t, U x
参数：hs : IsLindelof s；U : X -> Set X；hU : forall x in s, U x in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.elim_nhds_subcover'`：IsLindelof.elim_nhds_subcover' (hs : IsL
indelof s) (U : forall x in s, Set X) (hU : forall x (hx : x in s), U x ‹x in s›
 in 𝓝 x) : exists t …
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_image`：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y
)
-/
theorem IsLindelof.elim_nhds_subcover (hs : IsLindelof s) (U : X → Set X)
    (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ t : Set X, t.Countable ∧ (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x := by
  let ⟨t, ⟨htc, htsub⟩⟩ := hs.elim_nhds_subcover' (fun x _ ↦ U x) hU
  refine ⟨↑t, Countable.image htc Subtype.val, ?_⟩
  constructor
  · intro _
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index]
    tauto
  · have : ⋃ x ∈ t, U ↑x = ⋃ x ∈ Subtype.val '' t, U x := biUnion_image.symm
    rwa [← this]

/-- For every nonempty open cover of a Lindelöf set, there exists a subcover indexed by ℕ. -/
/-
**IsLindelof.indexed_countable_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.indexed_countable_subcover {ι : Type v} [Nonempty ι] (hs : IsLi
ndelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s subseteq ⋃ i,
 U i) : exists f : Nat -> ι, s subseteq ⋃ n, U (f n)
参数：hs : IsLindelof s；U : ι -> Set X；hUo : forall i, IsOpen (U i)；hsU : s subsete
q ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.elim_countable_subcover`：IsLindelof.elim_countable_subcover {
ι : Type v} (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) 
(hsU : s subseteq ⋃ i, U…
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.subset_eq_empty`：subset_eq_empty {s t : Set α} (h : t subseteq s) (e
 : s = ∅) : t = ∅
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.countable_iff_exists_surjective`：∀ {α : Type u} {s : Set α}, s.Nonem
pty → (s.Countable ↔ ∃ f, Function.Surjective f)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion₂_subset_iff`：iUnion₂_subset_iff {s : forall i, κ i -> Set α} 
{t : Set α} : ⋃ (i) (j), s i j subseteq t ↔ forall i j, s i j subseteq t
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用定理 `subset_of_eq`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a = b → a ⊆ b

--- 原说明 ---
For every nonempty open cover of a Lindelöf set, there exists a subcover indexed
 by ℕ.
-/
theorem IsLindelof.indexed_countable_subcover {ι : Type v} [Nonempty ι]
    (hs : IsLindelof s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) :
    ∃ f : ℕ → ι, s ⊆ ⋃ n, U (f n) := by
  obtain ⟨c, ⟨c_count, c_cov⟩⟩ := hs.elim_countable_subcover U hUo hsU
  rcases c.eq_empty_or_nonempty with rfl | c_nonempty
  · simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at c_cov
    simp only [subset_eq_empty c_cov rfl, empty_subset, exists_const]
  obtain ⟨f, f_surj⟩ := (Set.countable_iff_exists_surjective c_nonempty).mp c_count
  refine ⟨fun x ↦ f x, c_cov.trans <| iUnion₂_subset_iff.mpr (?_ : ∀ i ∈ c, U i ⊆ ⋃ n, U (f n))⟩
  intro x hx
  obtain ⟨n, hn⟩ := f_surj ⟨x, hx⟩
  exact subset_iUnion_of_subset n <| subset_of_eq (by rw [hn])

/-- The neighborhood filter of a Lindelöf set is disjoint with a filter `l` with the countable
intersection property if and only if the neighborhood filter of each point of this set
is disjoint with `l`. -/
/-
**IsLindelof.disjoint_nhdsSet_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.disjoint_nhdsSet_left {l : Filter X} [CountableInterFilter l] (
hs : IsLindelof s) : Disjoint (𝓝ˢ s) l ↔ forall x in s, Disjoint (𝓝 x) l
参数：hs : IsLindelof s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `nhds_le_nhdsSet`：nhds_le_nhdsSet (h : x in s) : 𝓝 x <= 𝓝ˢ s
· 使用定理 `IsLindelof.elim_nhds_subcover`：IsLindelof.elim_nhds_subcover (hs : IsLin
delof s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Set X, t
.Countable ∧ (foral…
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
· 使用定理 `countable_bInter_mem`：countable_bInter_mem {ι : Type*} {S : Set ι} (hS :
 S.Countable) {s : forall i in S, Set α} : (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ 
forall i, …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The neighborhood filter of a Lindelöf set is disjoint with a filter `l` with the
 countable
intersection property if and only if the neighborhood filter of each point of th
is set
is disjoint with `l`.
-/
theorem IsLindelof.disjoint_nhdsSet_left {l : Filter X} [CountableInterFilter l]
    (hs : IsLindelof s) :
    Disjoint (𝓝ˢ s) l ↔ ∀ x ∈ s, Disjoint (𝓝 x) l := by
  refine ⟨fun h x hx ↦ h.mono_left <| nhds_le_nhdsSet hx, fun H ↦ ?_⟩
  choose! U hxU hUl using fun x hx ↦ (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx ↦ (hUo x hx).mem_nhds (hxU x hx) with ⟨t, htc, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x ∈ t, U x, ⟨isOpen_biUnion fun x hx ↦ hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂]
  exact (countable_bInter_mem htc).mpr (fun i hi ↦ hUl _ (hts _ hi))

/-- A filter `l` with the countable intersection property is disjoint with the neighborhood
filter of a Lindelöf set if and only if it is disjoint with the neighborhood filter of each point
of this set. -/
/-
**IsLindelof.disjoint_nhdsSet_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.disjoint_nhdsSet_right {l : Filter X} [CountableInterFilter l] 
(hs : IsLindelof s) : Disjoint l (𝓝ˢ s) ↔ forall x in s, Disjoint l (𝓝 x)
参数：hs : IsLindelof s。
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
· 使用定理 `IsLindelof.disjoint_nhdsSet_left`：IsLindelof.disjoint_nhdsSet_left {l : 
Filter X} [CountableInterFilter l] (hs : IsLindelof s) : Disjoint (𝓝ˢ s) l ↔ for
all x in s, Disjoint (…

--- 原说明 ---
A filter `l` with the countable intersection property is disjoint with the neigh
borhood
filter of a Lindelöf set if and only if it is disjoint with the neighborhood fil
ter of each point
of this set.
-/
theorem IsLindelof.disjoint_nhdsSet_right {l : Filter X} [CountableInterFilter l]
    (hs : IsLindelof s) : Disjoint l (𝓝ˢ s) ↔ ∀ x ∈ s, Disjoint l (𝓝 x) := by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

/-- For every family of closed sets whose intersection avoids a Lindelöf set,
there exists a countable subfamily whose intersection avoids this Lindelöf set. -/
/-
**IsLindelof.elim_countable_subfamily_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.elim_countable_subfamily_closed {ι : Type v} (hs : IsLindelof s
) (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst : (s inter ⋂ i, t i) = 
∅) : exists u : Set ι, u.Countable ∧ (s inter ⋂ i in u, t i) = ∅
参数：hs : IsLindelof s；t : ι -> Set X；htc : forall i, IsClosed (t i)；hst : (s inte
r ⋂ i, t i) = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.disjoint_compl_left_iff_subset`：disjoint_compl_left_iff_subset : Dis
joint sᶜ t ↔ t subseteq s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `IsLindelof.elim_countable_subcover`：IsLindelof.elim_countable_subcover {
ι : Type v} (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) 
(hsU : s subseteq ⋃ i, U…
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂

--- 原说明 ---
For every family of closed sets whose intersection avoids a Lindelöf set,
there exists a countable subfamily whose intersection avoids this Lindelöf set.
-/
theorem IsLindelof.elim_countable_subfamily_closed {ι : Type v} (hs : IsLindelof s)
    (t : ι → Set X) (htc : ∀ i, IsClosed (t i)) (hst : (s ∩ ⋂ i, t i) = ∅) :
    ∃ u : Set ι, u.Countable ∧ (s ∩ ⋂ i ∈ u, t i) = ∅ := by
  let U := tᶜ
  have hUo : ∀ i, IsOpen (U i) := by simp only [U, Pi.compl_apply, isOpen_compl_iff]; exact htc
  have hsU : s ⊆ ⋃ i, U i := by
    simp only [U, Pi.compl_apply]
    rw [← compl_iInter]
    apply disjoint_compl_left_iff_subset.mp
    simp only [compl_iInter, compl_iUnion, compl_compl]
    apply Disjoint.symm
    exact disjoint_iff_inter_eq_empty.mpr hst
  rcases hs.elim_countable_subcover U hUo hsU with ⟨u, ⟨hucount, husub⟩⟩
  use u, hucount
  rw [← disjoint_compl_left_iff_subset] at husub
  simp only [U, Pi.compl_apply, compl_iUnion, compl_compl] at husub
  exact disjoint_iff_inter_eq_empty.mp (Disjoint.symm husub)

/-- To show that a Lindelöf set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every countable subfamily. -/
/-
**IsLindelof.inter_iInter_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.inter_iInter_nonempty {ι : Type v} (hs : IsLindelof s) (t : ι -
> Set X) (htc : forall i, IsClosed (t i)) (hst : forall u : Set ι, u.Countable ∧
 (s inter ⋂ i in u, t i).Nonempty) : (s inter ⋂ i, t i).Nonempty
参数：hs : IsLindelof s；t : ι -> Set X；htc : forall i, IsClosed (t i)；hst : forall 
u : Set ι, u.Countable ∧ (s inter ⋂ i in u, t i).Nonempty。
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
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `IsLindelof.elim_countable_subfamily_closed`：IsLindelof.elim_countable_su
bfamily_closed {ι : Type v} (hs : IsLindelof s) (t : ι -> Set X) (htc : forall i
, IsClosed (t i)) (hst : (s inte…

--- 原说明 ---
To show that a Lindelöf set intersects the intersection of a family of closed se
ts,
  it is sufficient to show that it intersects every countable subfamily.
-/
theorem IsLindelof.inter_iInter_nonempty {ι : Type v} (hs : IsLindelof s) (t : ι → Set X)
    (htc : ∀ i, IsClosed (t i)) (hst : ∀ u : Set ι, u.Countable ∧ (s ∩ ⋂ i ∈ u, t i).Nonempty) :
    (s ∩ ⋂ i, t i).Nonempty := by
  contrapose! hst
  rcases hs.elim_countable_subfamily_closed t htc hst with ⟨u, ⟨_, husub⟩⟩
  exact ⟨u, fun _ ↦ husub⟩

/-- For every open cover of a Lindelöf set, there exists a countable subcover. -/
/-
**IsLindelof.elim_countable_subcover_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.elim_countable_subcover_image {b : Set ι} {c : ι -> Set X} (hs 
: IsLindelof s) (hc₁ : forall i in b, IsOpen (c i)) (hc₂ : s subseteq ⋃ i in b, 
c i) : exists b', b' subseteq b ∧ Set.Countable b' ∧ s subseteq ⋃ i in b', c i
参数：hs : IsLindelof s；hc₁ : forall i in b, IsOpen (c i)；hc₂ : s subseteq ⋃ i in b
, c i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.elim_countable_subcover`：IsLindelof.elim_countable_subcover {
ι : Type v} (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) 
(hsU : s subseteq ⋃ i, U…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.biUnion_image`：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y
)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
For every open cover of a Lindelöf set, there exists a countable subcover.
-/
theorem IsLindelof.elim_countable_subcover_image {b : Set ι} {c : ι → Set X} (hs : IsLindelof s)
    (hc₁ : ∀ i ∈ b, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b', b' ⊆ b ∧ Set.Countable b' ∧ s ⊆ ⋃ i ∈ b', c i := by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_countable_subcover (fun i ↦ c i : b → Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' d, by simp, Countable.image hd.1 Subtype.val, ?_⟩
  rw [biUnion_image]
  exact hd.2


/-- A set `s` is Lindelöf if for every open cover of `s`, there exists a countable subcover. -/
/-
**isLindelof_of_countable_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_of_countable_subcover (h : forall {ι : Type u} (U : ι -> Set X)
, (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) -> exists t : Set ι, t.Count
able ∧ s subseteq ⋃ i in t, U i) : IsLindelof s
参数：h : forall {ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subs
eteq ⋃ i, U i) -> exists t : Set ι, t.Countable ∧ s subseteq ⋃ i in t, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.HasBasis.disjoint_iff_left`：∀ {α : Type u_1} {ι : Sort u_4} {l l'
 : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l l' ↔
 ∃ i, p i ∧ (s i)ᶜ ∈ l'…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `countable_bInter_mem`：countable_bInter_mem {ι : Type*} {S : Set ι} (hS :
 S.Countable) {s : forall i in S, Set α} : (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ 
forall i, …
· 使用定理 `Filter.compl_notMem`：compl_notMem {f : Filter α} {s : Set α} [NeBot f] (
h : s in f) : sᶜ ∉ f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_iUnion₂`：compl_iUnion₂ (s : forall i, κ i -> Set α) : (⋃ (i) (
j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A set `s` is Lindelöf if for every open cover of `s`, there exists a countable s
ubcover.
-/
theorem isLindelof_of_countable_subcover
    (h : ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) →
    ∃ t : Set ι, t.Countable ∧ s ⊆ ⋃ i ∈ t, U i) :
    IsLindelof s := fun f hf hfs ↦ by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose fsub U hU hUf using h
  refine ⟨s, U, fun x ↦ (hU x).2, fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1 ⟩, ?_⟩
  intro t ht h
  have uinf := f.sets_of_superset (le_principal_iff.1 fsub) h
  have uninf : ⋂ i ∈ t, (U i)ᶜ ∈ f := (countable_bInter_mem ht).mpr (fun _ _ ↦ hUf _)
  rw [← compl_iUnion₂] at uninf
  have uninf := compl_notMem uninf
  simp only [compl_compl] at uninf
  contradiction

/-- A set `s` is Lindelöf if for every family of closed sets whose intersection avoids `s`,
there exists a countable subfamily whose intersection avoids `s`. -/
/-
**isLindelof_of_countable_subfamily_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_of_countable_subfamily_closed (h : forall {ι : Type u} (t : ι -
> Set X), (forall i, IsClosed (t i)) -> (s inter ⋂ i, t i) = ∅ -> exists u : Set
 ι, u.Countable ∧ (s inter ⋂ i in u, t i) = ∅) : IsLindelof s
参数：h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> (s in
ter ⋂ i, t i) = ∅ -> exists u : Set ι, u.Countable ∧ (s inter ⋂ i in u, t i) = ∅
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLindelof_of_countable_subcover`：isLindelof_of_countable_subcover (h : 
forall {ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ 
i, U i) -> exists t : …
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
A set `s` is Lindelöf if for every family of closed sets whose intersection avoi
ds `s`,
there exists a countable subfamily whose intersection avoids `s`.
-/
theorem isLindelof_of_countable_subfamily_closed
    (h :
      ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ →
        ∃ u : Set ι, u.Countable ∧ (s ∩ ⋂ i ∈ u, t i) = ∅) :
    IsLindelof s :=
  isLindelof_of_countable_subcover fun U hUo hsU ↦ by
    rw [← disjoint_compl_right_iff_subset, compl_iUnion, disjoint_iff] at hsU
    rcases h (fun i ↦ (U i)ᶜ) (fun i ↦ (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]

/-- A set `s` is Lindelöf if and only if
for every open cover of `s`, there exists a countable subcover. -/
/-
**isLindelof_iff_countable_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_iff_countable_subcover : IsLindelof s ↔ forall {ι : Type u} (U 
: ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) -> exists t : S
et ι, t.Countable ∧ s subseteq ⋃ i in t, U i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.elim_countable_subcover`：IsLindelof.elim_countable_subcover {
ι : Type v} (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) 
(hsU : s subseteq ⋃ i, U…
· 使用定理 `isLindelof_of_countable_subcover`：isLindelof_of_countable_subcover (h : 
forall {ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ 
i, U i) -> exists t : …

--- 原说明 ---
A set `s` is Lindelöf if and only if
for every open cover of `s`, there exists a countable subcover.
-/
theorem isLindelof_iff_countable_subcover :
    IsLindelof s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Set ι, t.Countable ∧ s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs ↦ hs.elim_countable_subcover, isLindelof_of_countable_subcover⟩

/-- A set `s` is Lindelöf if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a countable subfamily whose intersection avoids `s`. -/
/-
**isLindelof_iff_countable_subfamily_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_iff_countable_subfamily_closed : IsLindelof s ↔ forall {ι : Typ
e u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> (s inter ⋂ i, t i) = ∅ -> e
xists u : Set ι, u.Countable ∧ (s inter ⋂ i in u, t i) = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.elim_countable_subfamily_closed`：IsLindelof.elim_countable_su
bfamily_closed {ι : Type v} (hs : IsLindelof s) (t : ι -> Set X) (htc : forall i
, IsClosed (t i)) (hst : (s inte…
· 使用定理 `isLindelof_of_countable_subfamily_closed`：isLindelof_of_countable_subfam
ily_closed (h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i))
 -> (s inter ⋂ i, t i) = ∅ -> …

--- 原说明 ---
A set `s` is Lindelöf if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a countable subfamily whose intersection avoids `s`.
-/
theorem isLindelof_iff_countable_subfamily_closed :
    IsLindelof s ↔ ∀ {ι : Type u} (t : ι → Set X),
    (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅
    → ∃ u : Set ι, u.Countable ∧ (s ∩ ⋂ i ∈ u, t i) = ∅ :=
  ⟨fun hs ↦ hs.elim_countable_subfamily_closed, isLindelof_of_countable_subfamily_closed⟩

/-- The empty set is a Lindelof set. -/
@[simp]
/-
**isLindelof_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_empty : IsLindelof (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f

--- 原说明 ---
The empty set is a Lindelof set.
-/
theorem isLindelof_empty : IsLindelof (∅ : Set X) := fun _f hnf _ hsf ↦
  Not.elim hnf.ne <| empty_mem_iff_bot.1 <| le_principal_iff.1 hsf

/-- A singleton set is a Lindelof set. -/
@[simp]
/-
**isLindelof_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_singleton {x : X} : IsLindelof ({x} : Set X)
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

--- 原说明 ---
A singleton set is a Lindelof set.
-/
theorem isLindelof_singleton {x : X} : IsLindelof ({x} : Set X) := fun _ hf _ hfa ↦
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩
/-
**Set.Subsingleton.isLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.isLindelof (hs : s.Subsingleton) : IsLindelof s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.induction_on`：∀ {α : Type u} {s : Set α} {p : Set α → P
rop}, s.Subsingleton → p ∅ → (∀ (x : α), p {x}) → p s
· 使用定理 `isLindelof_empty`：isLindelof_empty : IsLindelof (∅ : Set X)
· 使用定理 `isLindelof_singleton`：isLindelof_singleton {x : X} : IsLindelof ({x} : S
et X)
-/
theorem Set.Subsingleton.isLindelof (hs : s.Subsingleton) : IsLindelof s :=
  Subsingleton.induction_on hs isLindelof_empty fun _ ↦ isLindelof_singleton
/-
**Set.Countable.isLindelof_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Countable.isLindelof_biUnion {s : Set ι} {f : ι -> Set X} (hs : s.Coun
table) (hf : forall i in s, IsLindelof (f i)) : IsLindelof (⋃ i in s, f i)
参数：hs : s.Countable；hf : forall i in s, IsLindelof (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLindelof_of_countable_subcover`：isLindelof_of_countable_subcover (h : 
forall {ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ 
i, U i) -> exists t : …
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
· 使用定理 `IsLindelof.elim_countable_subcover`：IsLindelof.elim_countable_subcover {
ι : Type v} (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) 
(hsU : s subseteq ⋃ i, U…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Countable.biUnion_iff`：∀ {α : Type u} {β : Type v} {s : Set α} {t : 
(a : α) → a ∈ s → Set β},   s.Countable → ((⋃ a, ⋃ (h : a ∈ s), t a h).Countable
 ↔ ∀ (a : α) (h…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_and'`：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Set.Countable.isLindelof_biUnion {s : Set ι} {f : ι → Set X} (hs : s.Countable)
    (hf : ∀ i ∈ s, IsLindelof (f i)) : IsLindelof (⋃ i ∈ s, f i) := by
  apply isLindelof_of_countable_subcover
  intro i U hU hUcover
  have hiU : ∀ i ∈ s, f i ⊆ ⋃ i, U i :=
    fun _ is ↦ _root_.subset_trans (subset_biUnion_of_mem is) hUcover
  have iSets := fun i is ↦ (hf i is).elim_countable_subcover U hU (hiU i is)
  choose! r hr using iSets
  use ⋃ i ∈ s, r i
  constructor
  · refine (Countable.biUnion_iff hs).mpr ?h.left.a
    exact fun s hs ↦ (hr s hs).1
  · refine iUnion₂_subset ?h.right.h
    intro i is
    simp only [mem_iUnion, exists_prop, iUnion_exists, biUnion_and']
    intro x hx
    exact mem_biUnion is ((hr i is).2 hx)
/-
**Set.Finite.isLindelof_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isLindelof_biUnion {s : Set ι} {f : ι -> Set X} (hs : s.Finite)
 (hf : forall i in s, IsLindelof (f i)) : IsLindelof (⋃ i in s, f i)
参数：hs : s.Finite；hf : forall i in s, IsLindelof (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.isLindelof_biUnion`：Set.Countable.isLindelof_biUnion {s : 
Set ι} {f : ι -> Set X} (hs : s.Countable) (hf : forall i in s, IsLindelof (f i)
) : IsLindelof (⋃ i in…
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
-/
theorem Set.Finite.isLindelof_biUnion {s : Set ι} {f : ι → Set X} (hs : s.Finite)
    (hf : ∀ i ∈ s, IsLindelof (f i)) : IsLindelof (⋃ i ∈ s, f i) :=
  Set.Countable.isLindelof_biUnion (countable hs) hf
/-
**Finset.isLindelof_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.isLindelof_biUnion (s : Finset ι) {f : ι -> Set X} (hf : forall i i
n s, IsLindelof (f i)) : IsLindelof (⋃ i in s, f i)
参数：s : Finset ι；hf : forall i in s, IsLindelof (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isLindelof_biUnion`：Set.Finite.isLindelof_biUnion {s : Set ι}
 {f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsLindelof (f i)) : IsLin
delof (⋃ i in s, f …
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem Finset.isLindelof_biUnion (s : Finset ι) {f : ι → Set X} (hf : ∀ i ∈ s, IsLindelof (f i)) :
    IsLindelof (⋃ i ∈ s, f i) :=
  s.finite_toSet.isLindelof_biUnion hf
/-
**isLindelof_accumulate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_accumulate {K : Nat -> Set X} (hK : forall n, IsLindelof (K n))
 (n : Nat) : IsLindelof (accumulate K n)
参数：hK : forall n, IsLindelof (K n)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isLindelof_biUnion`：Set.Finite.isLindelof_biUnion {s : Set ι}
 {f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsLindelof (f i)) : IsLin
delof (⋃ i in s, f …
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
-/
theorem isLindelof_accumulate {K : ℕ → Set X} (hK : ∀ n, IsLindelof (K n)) (n : ℕ) :
    IsLindelof (accumulate K n) :=
  (finite_le_nat n).isLindelof_biUnion fun k _ => hK k
/-
**Set.Countable.isLindelof_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Countable.isLindelof_sUnion {S : Set (Set X)} (hf : S.Countable) (hc :
 forall s in S, IsLindelof s) : IsLindelof (⋃₀ S)
参数：Set X；hf : S.Countable；hc : forall s in S, IsLindelof s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.Countable.isLindelof_biUnion`：Set.Countable.isLindelof_biUnion {s : 
Set ι} {f : ι -> Set X} (hs : s.Countable) (hf : forall i in s, IsLindelof (f i)
) : IsLindelof (⋃ i in…
-/
theorem Set.Countable.isLindelof_sUnion {S : Set (Set X)} (hf : S.Countable)
    (hc : ∀ s ∈ S, IsLindelof s) : IsLindelof (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isLindelof_biUnion hc
/-
**Set.Finite.isLindelof_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isLindelof_sUnion {S : Set (Set X)} (hf : S.Finite) (hc : foral
l s in S, IsLindelof s) : IsLindelof (⋃₀ S)
参数：Set X；hf : S.Finite；hc : forall s in S, IsLindelof s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.Finite.isLindelof_biUnion`：Set.Finite.isLindelof_biUnion {s : Set ι}
 {f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsLindelof (f i)) : IsLin
delof (⋃ i in s, f …
-/
theorem Set.Finite.isLindelof_sUnion {S : Set (Set X)} (hf : S.Finite)
    (hc : ∀ s ∈ S, IsLindelof s) : IsLindelof (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isLindelof_biUnion hc
/-
**isLindelof_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_iUnion {ι : Sort*} {f : ι -> Set X} [Countable ι] (h : forall i
, IsLindelof (f i)) : IsLindelof (⋃ i, f i)
参数：h : forall i, IsLindelof (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.isLindelof_sUnion`：Set.Countable.isLindelof_sUnion {S : Se
t (Set X)} (hf : S.Countable) (hc : forall s in S, IsLindelof s) : IsLindelof (⋃
₀ S)
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isLindelof_iUnion {ι : Sort*} {f : ι → Set X} [Countable ι] (h : ∀ i, IsLindelof (f i)) :
    IsLindelof (⋃ i, f i) := (countable_range f).isLindelof_sUnion <| forall_mem_range.2 h
/-
**Set.Countable.isLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Countable.isLindelof (hs : s.Countable) : IsLindelof s
参数：hs : s.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.isLindelof_biUnion`：Set.Countable.isLindelof_biUnion {s : 
Set ι} {f : ι -> Set X} (hs : s.Countable) (hf : forall i in s, IsLindelof (f i)
) : IsLindelof (⋃ i in…
· 使用定理 `isLindelof_singleton`：isLindelof_singleton {x : X} : IsLindelof ({x} : S
et X)
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
-/
theorem Set.Countable.isLindelof (hs : s.Countable) : IsLindelof s :=
  biUnion_of_singleton s ▸ hs.isLindelof_biUnion fun _ _ => isLindelof_singleton
/-
**Set.Finite.isLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isLindelof (hs : s.Finite) : IsLindelof s
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isLindelof_biUnion`：Set.Finite.isLindelof_biUnion {s : Set ι}
 {f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsLindelof (f i)) : IsLin
delof (⋃ i in s, f …
· 使用定理 `isLindelof_singleton`：isLindelof_singleton {x : X} : IsLindelof ({x} : S
et X)
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
-/
theorem Set.Finite.isLindelof (hs : s.Finite) : IsLindelof s :=
  biUnion_of_singleton s ▸ hs.isLindelof_biUnion fun _ _ => isLindelof_singleton
/-
**IsLindelof.countable_of_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.countable_of_discrete [DiscreteTopology X] (hs : IsLindelof s) 
: s.Countable
参数：hs : IsLindelof s。
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
· 使用定理 `IsLindelof.elim_nhds_subcover`：IsLindelof.elim_nhds_subcover (hs : IsLin
delof s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Set X, t
.Countable ∧ (foral…
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
-/
theorem IsLindelof.countable_of_discrete [DiscreteTopology X] (hs : IsLindelof s) :
    s.Countable := by
  have : ∀ x : X, ({x} : Set X) ∈ 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, ht, _, hssubt⟩
  rw [biUnion_of_singleton] at hssubt
  exact ht.mono hssubt
/-
**isLindelof_iff_countable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_iff_countable [DiscreteTopology X] : IsLindelof s ↔ s.Countable
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.countable_of_discrete`：IsLindelof.countable_of_discrete [Disc
reteTopology X] (hs : IsLindelof s) : s.Countable
· 使用定理 `Set.Countable.isLindelof`：Set.Countable.isLindelof (hs : s.Countable) : 
IsLindelof s
-/
theorem isLindelof_iff_countable [DiscreteTopology X] : IsLindelof s ↔ s.Countable :=
  ⟨fun h => h.countable_of_discrete, fun h => h.isLindelof⟩
/-
**IsLindelof.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.union (hs : IsLindelof s) (ht : IsLindelof t) : IsLindelof (s u
nion t)
参数：hs : IsLindelof s；ht : IsLindelof t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `isLindelof_iUnion`：isLindelof_iUnion {ι : Sort*} {f : ι -> Set X} [Count
able ι] (h : forall i, IsLindelof (f i)) : IsLindelof (⋃ i, f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsLindelof.union (hs : IsLindelof s) (ht : IsLindelof t) : IsLindelof (s ∪ t) := by
  rw [union_eq_iUnion]; exact isLindelof_iUnion fun b => by cases b <;> assumption
/-
**IsLindelof.insert** 是 Mathlib 中的一个定理，位于命名空间 `IsLindelof`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, IsLindelof s → ∀ (
a : X), IsLindelof (insert a s)
参数：a : X；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.union`：IsLindelof.union (hs : IsLindelof s) (ht : IsLindelof 
t) : IsLindelof (s union t)
· 使用定理 `isLindelof_singleton`：isLindelof_singleton {x : X} : IsLindelof ({x} : S
et X)
-/
protected theorem IsLindelof.insert (hs : IsLindelof s) (a) : IsLindelof (insert a s) :=
  isLindelof_singleton.union hs

/-- If `X` has a basis consisting of compact opens, then an open set in `X` is compact open iff
it is a finite union of some elements in the basis -/
/-
**isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis (b : ι -> Se
t X) (hb : IsTopologicalBasis (Set.range b)) (hb' : forall i, IsLindelof (b i)) 
(U : Set X) : IsLindelof U ∧ IsOpen U ↔ exists s : Set ι, s.Countable ∧ U = ⋃ i 
in s, b i
参数：b : ι -> Set X；hb : IsTopologicalBasis (Set.range b)；hb' : forall i, IsLindel
of (b i)；U : Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.open_eq_iUnion`：∀ {α : Type u} [t : 
TopologicalSpace α] {B : Set (Set α)},   TopologicalSpace.IsTopologicalBasis B →
 ∀ {u : Set α}, IsOpen u → ∃ β f, u = ⋃ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLindelof.elim_countable_subcover`：IsLindelof.elim_countable_subcover {
ι : Type v} (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) 
(hsU : s subseteq ⋃ i, U…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen`：∀ {α : Type u} [t : Topologi
calSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis
 b → s ∈ b → IsOpen s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_subtype`：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Set.Countable.isLindelof_biUnion`：Set.Countable.isLindelof_biUnion {s : 
Set ι} {f : ι -> Set X} (hs : s.Countable) (hf : forall i in s, IsLindelof (f i)
) : IsLindelof (⋃ i in…
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)

--- 原说明 ---
If `X` has a basis consisting of compact opens, then an open set in `X` is compa
ct open iff
it is a finite union of some elements in the basis
-/
theorem isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis (b : ι → Set X)
    (hb : IsTopologicalBasis (Set.range b)) (hb' : ∀ i, IsLindelof (b i)) (U : Set X) :
    IsLindelof U ∧ IsOpen U ↔ ∃ s : Set ι, s.Countable ∧ U = ⋃ i ∈ s, b i := by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨Y, f, rfl, hf⟩ := hb.open_eq_iUnion h₂
    choose f' hf' using hf
    have : b ∘ f' = f := funext hf'
    subst this
    obtain ⟨t, ht⟩ :=
      h₁.elim_countable_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) Subset.rfl
    refine ⟨t.image f', Countable.image (ht.1) f', le_antisymm ?_ ?_⟩
    · refine Set.Subset.trans ht.2 ?_
      simp only [Set.iUnion_subset_iff]
      intro i hi
      rw [← Set.iUnion_subtype (fun x : ι => x ∈ t.image f') fun i => b i.1]
      exact Set.subset_iUnion (fun i : t.image f' => b i) ⟨_, mem_image_of_mem _ hi⟩
    · apply Set.iUnion₂_subset
      rintro i hi
      obtain ⟨j, -, rfl⟩ := (mem_image ..).mp hi
      exact Set.subset_iUnion (b ∘ f') j
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact hs.isLindelof_biUnion fun i _ => hb' i
    · exact isOpen_biUnion fun i _ => hb.isOpen (Set.mem_range_self _)

/-- `Filter.coLindelof` is the filter generated by complements to Lindelöf sets. -/
/-
**Filter.coLindelof** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Filter.coLindelof (X : Type*) [TopologicalSpace X] : Filter X
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Filter.coLindelof` is the filter generated by complements to Lindelöf sets.
-/
def Filter.coLindelof (X : Type*) [TopologicalSpace X] : Filter X :=
  --`Filter.coLindelof` is the filter generated by complements to Lindelöf sets.
  ⨅ (s : Set X) (_ : IsLindelof s), 𝓟 sᶜ
/-
**hasBasis_coLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBasis_coLindelof : (coLindelof X).HasBasis IsLindelof compl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_biInf_principal'`：hasBasis_biInf_principal' {ι : Type*} 
{p : ι -> Prop} {s : ι -> Set α} (h : forall i, p i -> forall j, p j -> exists k
, p k ∧ s k subseteq s…
· 使用定理 `IsLindelof.union`：IsLindelof.union (hs : IsLindelof s) (ht : IsLindelof 
t) : IsLindelof (s union t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `isLindelof_empty`：isLindelof_empty : IsLindelof (∅ : Set X)
-/
theorem hasBasis_coLindelof : (coLindelof X).HasBasis IsLindelof compl :=
  hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s ∪ t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isLindelof_empty⟩
/-
**mem_coLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_coLindelof : s in coLindelof X ↔ exists t, IsLindelof t ∧ tᶜ subseteq 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `hasBasis_coLindelof`：hasBasis_coLindelof : (coLindelof X).HasBasis IsLin
delof compl
-/
theorem mem_coLindelof : s ∈ coLindelof X ↔ ∃ t, IsLindelof t ∧ tᶜ ⊆ s :=
  hasBasis_coLindelof.mem_iff
/-
**mem_coLindelof'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_coLindelof' : s in coLindelof X ↔ exists t, IsLindelof t ∧ sᶜ subseteq
 t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_coLindelof`：mem_coLindelof : s in coLindelof X ↔ exists t, IsLindelo
f t ∧ tᶜ subseteq s
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
-/
theorem mem_coLindelof' : s ∈ coLindelof X ↔ ∃ t, IsLindelof t ∧ sᶜ ⊆ t :=
  mem_coLindelof.trans <| exists_congr fun _ => and_congr_right fun _ => compl_subset_comm
/-
**_root_.IsLindelof.compl_mem_coLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.IsLindelof.compl_mem_coLindelof (hs : IsLindelof s) : sᶜ in coLinde
lof X
参数：hs : IsLindelof s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsLindelof.compl_mem_coLindelof (hs : IsLindelof s) : sᶜ ∈ coLindelof X :=
  hasBasis_coLindelof.mem_of_mem hs
/-
**coLindelof_le_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coLindelof_le_cofinite : coLindelof X <= cofinite
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.compl_mem_coLindelof`：∀ {X : Type u} [inst : TopologicalSpace
 X] {s : Set X}, IsLindelof s → sᶜ ∈ Filter.coLindelof X
· 使用定理 `Set.Finite.isLindelof`：Set.Finite.isLindelof (hs : s.Finite) : IsLindelo
f s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem coLindelof_le_cofinite : coLindelof X ≤ cofinite := fun s hs =>
  compl_compl s ▸ hs.isLindelof.compl_mem_coLindelof
/-
**Tendsto.isLindelof_insert_range_of_coLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Tendsto.isLindelof_insert_range_of_coLindelof {f : X -> Y} {y} (hf : Tends
to f (coLindelof X) (𝓝 y)) (hfc : Continuous f) : IsLindelof (insert y (range f)
)
参数：hf : Tendsto f (coLindelof X) (𝓝 y)；hfc : Continuous f。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `mem_coLindelof`：mem_coLindelof : s in coLindelof X ↔ exists t, IsLindelo
f t ∧ tᶜ subseteq s
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
· 使用定理 `IsLindelof.image`：IsLindelof.image {f : X -> Y} (hs : IsLindelof s) (hf 
: Continuous f) : IsLindelof (f '' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem Tendsto.isLindelof_insert_range_of_coLindelof {f : X → Y} {y}
    (hf : Tendsto f (coLindelof X) (𝓝 y)) (hfc : Continuous f) :
    IsLindelof (insert y (range f)) := by
  intro l hne _ hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff_nonempty, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_coLindelof.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K ∈ l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsy, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
  exact ⟨y, Or.inr <| image_subset_range _ _ hy, hyl⟩

/-- `Filter.coclosedLindelof` is the filter generated by complements to closed Lindelof sets. -/
/-
**Filter.coclosedLindelof** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Filter.coclosedLindelof (X : Type*) [TopologicalSpace X] : Filter X
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Filter.coclosedLindelof` is the filter generated by complements to closed Linde
lof sets.
-/
def Filter.coclosedLindelof (X : Type*) [TopologicalSpace X] : Filter X :=
  -- `Filter.coclosedLindelof` is the filter generated by complements to closed Lindelof sets.
  ⨅ (s : Set X) (_ : IsClosed s) (_ : IsLindelof s), 𝓟 sᶜ
/-
**hasBasis_coclosedLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBasis_coclosedLindelof : (Filter.coclosedLindelof X).HasBasis (fun s =>
 IsClosed s ∧ IsLindelof s) compl
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
· 使用定理 `IsLindelof.union`：IsLindelof.union (hs : IsLindelof s) (ht : IsLindelof 
t) : IsLindelof (s union t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `isLindelof_empty`：isLindelof_empty : IsLindelof (∅ : Set X)
-/
theorem hasBasis_coclosedLindelof :
    (Filter.coclosedLindelof X).HasBasis (fun s => IsClosed s ∧ IsLindelof s) compl := by
  simp only [Filter.coclosedLindelof, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isLindelof_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s ∪ t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩⟩
/-
**mem_coclosedLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_coclosedLindelof : s in coclosedLindelof X ↔ exists t, IsClosed t ∧ Is
Lindelof t ∧ tᶜ subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `hasBasis_coclosedLindelof`：hasBasis_coclosedLindelof : (Filter.coclosedL
indelof X).HasBasis (fun s => IsClosed s ∧ IsLindelof s) compl
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_coclosedLindelof : s ∈ coclosedLindelof X ↔
    ∃ t, IsClosed t ∧ IsLindelof t ∧ tᶜ ⊆ s := by
  simp only [hasBasis_coclosedLindelof.mem_iff, and_assoc]
/-
**mem_coclosed_Lindelof'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_coclosed_Lindelof' : s in coclosedLindelof X ↔ exists t, IsClosed t ∧ 
IsLindelof t ∧ sᶜ subseteq t
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
theorem mem_coclosed_Lindelof' : s ∈ coclosedLindelof X ↔
    ∃ t, IsClosed t ∧ IsLindelof t ∧ sᶜ ⊆ t := by
  simp only [mem_coclosedLindelof, compl_subset_comm]
/-
**coLindelof_le_coclosedLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coLindelof_le_coclosedLindelof : coLindelof X <= coclosedLindelof X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coLindelof_le_coclosedLindelof : coLindelof X ≤ coclosedLindelof X :=
  iInf_mono fun _ => le_iInf fun _ => le_rfl
/-
**IsLindeof.compl_mem_coclosedLindelof_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindeof.compl_mem_coclosedLindelof_of_isClosed (hs : IsLindelof s) (hs' 
: IsClosed s) : sᶜ in Filter.coclosedLindelof X
参数：hs : IsLindelof s；hs' : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `hasBasis_coclosedLindelof`：hasBasis_coclosedLindelof : (Filter.coclosedL
indelof X).HasBasis (fun s => IsClosed s ∧ IsLindelof s) compl
-/
theorem IsLindeof.compl_mem_coclosedLindelof_of_isClosed (hs : IsLindelof s) (hs' : IsClosed s) :
    sᶜ ∈ Filter.coclosedLindelof X :=
  hasBasis_coclosedLindelof.mem_of_mem ⟨hs', hs⟩

/-- X is a Lindelöf space iff every open cover has a countable subcover. -/
/-
**LindelofSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_2) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
X is a Lindelöf space iff every open cover has a countable subcover.
-/
class LindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a Lindelöf space, `Set.univ` is a Lindelöf set. -/
  isLindelof_univ : IsLindelof (univ : Set X)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) Subsingleton.lindelofSpace [Subsingleton X] : LindelofSpace X :=
  ⟨subsingleton_univ.isLindelof⟩
/-
**isLindelof_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_univ_iff : IsLindelof (univ : Set X) ↔ LindelofSpace X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LindelofSpace.isLindelof_univ`：∀ {X : Type u_2} {inst : TopologicalSpace
 X} [self : LindelofSpace X], IsLindelof Set.univ
-/
theorem isLindelof_univ_iff : IsLindelof (univ : Set X) ↔ LindelofSpace X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩
/-
**isLindelof_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_univ [h : LindelofSpace X] : IsLindelof (univ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LindelofSpace.isLindelof_univ`：∀ {X : Type u_2} {inst : TopologicalSpace
 X} [self : LindelofSpace X], IsLindelof Set.univ
-/
theorem isLindelof_univ [h : LindelofSpace X] : IsLindelof (univ : Set X) :=
  h.isLindelof_univ
/-
**cluster_point_of_Lindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cluster_point_of_Lindelof [LindelofSpace X] (f : Filter X) [NeBot f] [Coun
tableInterFilter f] : exists x, ClusterPt x f
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
· 使用定理 `isLindelof_univ`：isLindelof_univ [h : LindelofSpace X] : IsLindelof (uni
v : Set X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
-/
theorem cluster_point_of_Lindelof [LindelofSpace X] (f : Filter X) [NeBot f]
    [CountableInterFilter f] : ∃ x, ClusterPt x f := by
  simpa using isLindelof_univ (show f ≤ 𝓟 univ by simp)
/-
**LindelofSpace.elim_nhds_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LindelofSpace.elim_nhds_subcover [LindelofSpace X] (U : X -> Set X) (hU : 
forall x, U x in 𝓝 x) : exists t : Set X, t.Countable ∧ ⋃ x in t, U x = univ
参数：U : X -> Set X；hU : forall x, U x in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.elim_nhds_subcover`：IsLindelof.elim_nhds_subcover (hs : IsLin
delof s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Set X, t
.Countable ∧ (foral…
· 使用定理 `LindelofSpace.isLindelof_univ`：∀ {X : Type u_2} {inst : TopologicalSpace
 X} [self : LindelofSpace X], IsLindelof Set.univ
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
-/
theorem LindelofSpace.elim_nhds_subcover [LindelofSpace X] (U : X → Set X) (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Set X, t.Countable ∧ ⋃ x ∈ t, U x = univ := by
  obtain ⟨t, tc, -, s⟩ := IsLindelof.elim_nhds_subcover isLindelof_univ U fun x _ => hU x
  use t, tc
  apply top_unique s
/-
**lindelofSpace_of_countable_subfamily_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lindelofSpace_of_countable_subfamily_closed (h : forall {ι : Type u} (t : 
ι -> Set X), (forall i, IsClosed (t i)) -> ⋂ i, t i = ∅ -> exists u : Set ι, u.C
ountable ∧ ⋂ i in u, t i = ∅) : LindelofSpace X where isLindelof_univ
参数：h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> ⋂ i, 
t i = ∅ -> exists u : Set ι, u.Countable ∧ ⋂ i in u, t i = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLindelof_of_countable_subfamily_closed`：isLindelof_of_countable_subfam
ily_closed (h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i))
 -> (s inter ⋂ i, t i) = ∅ -> …
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
theorem lindelofSpace_of_countable_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → ⋂ i, t i = ∅ →
      ∃ u : Set ι, u.Countable ∧ ⋂ i ∈ u, t i = ∅) :
    LindelofSpace X where
  isLindelof_univ := isLindelof_of_countable_subfamily_closed fun t => by simpa using h t
/-
**IsClosed.isLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.isLindelof [LindelofSpace X] (h : IsClosed s) : IsLindelof s
参数：h : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.of_isClosed_subset`：IsLindelof.of_isClosed_subset (hs : IsLin
delof s) (ht : IsClosed t) (h : t subseteq s) : IsLindelof t
· 使用定理 `isLindelof_univ`：isLindelof_univ [h : LindelofSpace X] : IsLindelof (uni
v : Set X)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem IsClosed.isLindelof [LindelofSpace X] (h : IsClosed s) : IsLindelof s :=
  isLindelof_univ.of_isClosed_subset h (subset_univ _)

/-- A compact set `s` is Lindelöf. -/
/-
**IsCompact.isLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isLindelof (hs : IsCompact s) : IsLindelof s
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compact set `s` is Lindelöf.
-/
theorem IsCompact.isLindelof (hs : IsCompact s) :
    IsLindelof s := by tauto

/-- A σ-compact set `s` is Lindelöf -/
/-
**IsSigmaCompact.isLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSigmaCompact.isLindelof (hs : IsSigmaCompact s) : IsLindelof s
参数：hs : IsSigmaCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSigmaCompact.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : S
et X),   IsSigmaCompact s = ∃ K, (∀ (n : ℕ), IsCompact (K n)) ∧ ⋃ n, K n = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.isLindelof`：IsCompact.isLindelof (hs : IsCompact s) : IsLindel
of s
· 使用定理 `isLindelof_iUnion`：isLindelof_iUnion {ι : Sort*} {f : ι -> Set X} [Count
able ι] (h : forall i, IsLindelof (f i)) : IsLindelof (⋃ i, f i)
· 使用定理 `instCountableNat`：Countable ℕ

--- 原说明 ---
A σ-compact set `s` is Lindelöf
-/
theorem IsSigmaCompact.isLindelof (hs : IsSigmaCompact s) :
    IsLindelof s := by
  rw [IsSigmaCompact] at hs
  rcases hs with ⟨K, ⟨hc, huniv⟩⟩
  rw [← huniv]
  have hl : ∀ n, IsLindelof (K n) := fun n ↦ IsCompact.isLindelof (hc n)
  exact isLindelof_iUnion hl

/-- A compact space `X` is Lindelöf. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compact space `X` is Lindelöf.
-/
instance (priority := 100) [CompactSpace X] : LindelofSpace X :=
  { isLindelof_univ := isCompact_univ.isLindelof }

/-- A sigma-compact space `X` is Lindelöf. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sigma-compact space `X` is Lindelöf.
-/
instance (priority := 100) [SigmaCompactSpace X] : LindelofSpace X :=
  { isLindelof_univ := isSigmaCompact_univ.isLindelof }

/-- `X` is a non-Lindelöf topological space if it is not a Lindelöf space. -/
/-
**NonLindelofSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_2) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` is a non-Lindelöf topological space if it is not a Lindelöf space.
-/
class NonLindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a non-Lindelöf space, `Set.univ` is not a Lindelöf set. -/
  nonLindelof_univ : ¬IsLindelof (univ : Set X)
/-
**nonLindelof_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonLindelof_univ (X : Type*) [TopologicalSpace X] [NonLindelofSpace X] : ¬
IsLindelof (univ : Set X)
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonLindelofSpace.nonLindelof_univ`：∀ {X : Type u_2} {inst : TopologicalS
pace X} [self : NonLindelofSpace X], ¬IsLindelof Set.univ
-/
lemma nonLindelof_univ (X : Type*) [TopologicalSpace X] [NonLindelofSpace X] :
    ¬IsLindelof (univ : Set X) :=
  NonLindelofSpace.nonLindelof_univ
/-
**IsLindelof.ne_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.ne_univ [NonLindelofSpace X] (hs : IsLindelof s) : s != univ
参数：hs : IsLindelof s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonLindelof_univ`：nonLindelof_univ (X : Type*) [TopologicalSpace X] [Non
LindelofSpace X] : ¬IsLindelof (univ : Set X)
-/
theorem IsLindelof.ne_univ [NonLindelofSpace X] (hs : IsLindelof s) : s ≠ univ := fun h ↦
  nonLindelof_univ X (h ▸ hs)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonLindelofSpace X] : NeBot (Filter.coLindelof X) := by
  refine hasBasis_coLindelof.neBot_iff.2 fun {s} hs => ?_
  contrapose hs
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]
  exact nonLindelof_univ X

@[simp]
/-
**Filter.coLindelof_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.coLindelof_eq_bot [LindelofSpace X] : Filter.coLindelof X = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.eq_bot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l = ⊥ ↔ ∃ i, p i ∧ s i = 
∅)
· 使用定理 `hasBasis_coLindelof`：hasBasis_coLindelof : (coLindelof X).HasBasis IsLin
delof compl
· 使用定理 `isLindelof_univ`：isLindelof_univ [h : LindelofSpace X] : IsLindelof (uni
v : Set X)
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
-/
theorem Filter.coLindelof_eq_bot [LindelofSpace X] : Filter.coLindelof X = ⊥ :=
  hasBasis_coLindelof.eq_bot_iff.mpr ⟨Set.univ, isLindelof_univ, Set.compl_univ⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonLindelofSpace X] : NeBot (Filter.coclosedLindelof X) :=
  neBot_of_le coLindelof_le_coclosedLindelof
/-
**nonLindelofSpace_of_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonLindelofSpace_of_neBot (_ : NeBot (Filter.coLindelof X)) : NonLindelofS
pace X
参数：_ : NeBot (Filter.coLindelof X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `IsLindelof.compl_mem_coLindelof`：∀ {X : Type u} [inst : TopologicalSpace
 X] {s : Set X}, IsLindelof s → sᶜ ∈ Filter.coLindelof X
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
-/
theorem nonLindelofSpace_of_neBot (_ : NeBot (Filter.coLindelof X)) : NonLindelofSpace X :=
  ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_coLindelof).ne_empty compl_univ⟩
/-
**Filter.coLindelof_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.coLindelof_neBot_iff : NeBot (Filter.coLindelof X) ↔ NonLindelofSpa
ce X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonLindelofSpace_of_neBot`：nonLindelofSpace_of_neBot (_ : NeBot (Filter.
coLindelof X)) : NonLindelofSpace X
· 使用定理 `instNeBotCoLindelofOfNonLindelofSpace`：∀ {X : Type u} [inst : Topologica
lSpace X] [NonLindelofSpace X], (Filter.coLindelof X).NeBot
-/
theorem Filter.coLindelof_neBot_iff : NeBot (Filter.coLindelof X) ↔ NonLindelofSpace X :=
  ⟨nonLindelofSpace_of_neBot, fun _ => inferInstance⟩
/-
**not_LindelofSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_LindelofSpace_iff : ¬LindelofSpace X ↔ NonLindelofSpace X
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_LindelofSpace_iff : ¬LindelofSpace X ↔ NonLindelofSpace X :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩
/-
**countable_of_Lindelof_of_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_of_Lindelof_of_discrete [LindelofSpace X] [DiscreteTopology X] :
 Countable X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.countable_univ_iff`：countable_univ_iff : (univ : Set α).Countable ↔ 
Countable α
· 使用定理 `IsLindelof.countable_of_discrete`：IsLindelof.countable_of_discrete [Disc
reteTopology X] (hs : IsLindelof s) : s.Countable
· 使用定理 `isLindelof_univ`：isLindelof_univ [h : LindelofSpace X] : IsLindelof (uni
v : Set X)
-/
theorem countable_of_Lindelof_of_discrete [LindelofSpace X] [DiscreteTopology X] : Countable X :=
  countable_univ_iff.mp isLindelof_univ.countable_of_discrete
/-
**countable_cover_nhds_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_cover_nhds_interior [LindelofSpace X] {U : X -> Set X} (hU : for
all x, U x in 𝓝 x) : exists t : Set X, t.Countable ∧ ⋃ x in t, interior (U x) = 
univ
参数：hU : forall x, U x in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.elim_countable_subcover`：IsLindelof.elim_countable_subcover {
ι : Type v} (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) 
(hsU : s subseteq ⋃ i, U…
· 使用定理 `isLindelof_univ`：isLindelof_univ [h : LindelofSpace X] : IsLindelof (uni
v : Set X)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem countable_cover_nhds_interior [LindelofSpace X] {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Set X, t.Countable ∧ ⋃ x ∈ t, interior (U x) = univ :=
  let ⟨t, ht⟩ := isLindelof_univ.elim_countable_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, ⟨ht.1, univ_subset_iff.1 ht.2⟩⟩
/-
**countable_cover_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_cover_nhds [LindelofSpace X] {U : X -> Set X} (hU : forall x, U 
x in 𝓝 x) : exists t : Set X, t.Countable ∧ ⋃ x in t, U x = univ
参数：hU : forall x, U x in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `countable_cover_nhds_interior`：countable_cover_nhds_interior [LindelofSp
ace X] {U : X -> Set X} (hU : forall x, U x in 𝓝 x) : exists t : Set X, t.Counta
ble ∧ ⋃ x in t, int…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem countable_cover_nhds [LindelofSpace X] {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Set X, t.Countable ∧ ⋃ x ∈ t, U x = univ :=
  let ⟨t, ht⟩ := countable_cover_nhds_interior hU
  ⟨t, ⟨ht.1, univ_subset_iff.1 <| ht.2.symm.subset.trans <|
    iUnion₂_mono fun _ _ => interior_subset⟩⟩

/-- The comap of the coLindelöf filter on `Y` by a continuous function `f : X → Y` is less than or
equal to the coLindelöf filter on `X`.
This is a reformulation of the fact that images of Lindelöf sets are Lindelöf. -/
/-
**Filter.comap_coLindelof_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.comap_coLindelof_le {f : X -> Y} (hf : Continuous f) : (Filter.coLi
ndelof Y).comap f <= Filter.coLindelof X
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
· 使用定理 `hasBasis_coLindelof`：hasBasis_coLindelof : (coLindelof X).HasBasis IsLin
delof compl
· 使用定理 `IsLindelof.image`：IsLindelof.image {f : X -> Y} (hs : IsLindelof s) (hf 
: Continuous f) : IsLindelof (f '' s)
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s

--- 原说明 ---
The comap of the coLindelöf filter on `Y` by a continuous function `f : X → Y` i
s less than or
equal to the coLindelöf filter on `X`.
This is a reformulation of the fact that images of Lindelöf sets are Lindelöf.
-/
theorem Filter.comap_coLindelof_le {f : X → Y} (hf : Continuous f) :
    (Filter.coLindelof Y).comap f ≤ Filter.coLindelof X := by
  rw [(hasBasis_coLindelof.comap f).le_basis_iff hasBasis_coLindelof]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f
/-
**isLindelof_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_range [LindelofSpace X] {f : X -> Y} (hf : Continuous f) : IsLi
ndelof (range f)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsLindelof.image`：IsLindelof.image {f : X -> Y} (hs : IsLindelof s) (hf 
: Continuous f) : IsLindelof (f '' s)
· 使用定理 `isLindelof_univ`：isLindelof_univ [h : LindelofSpace X] : IsLindelof (uni
v : Set X)
-/
theorem isLindelof_range [LindelofSpace X] {f : X → Y} (hf : Continuous f) :
    IsLindelof (range f) := by rw [← image_univ]; exact isLindelof_univ.image hf
/-
**isLindelof_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_diagonal [LindelofSpace X] : IsLindelof (diagonal X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLindelof_range`：isLindelof_range [LindelofSpace X] {f : X -> Y} (hf : 
Continuous f) : IsLindelof (range f)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Set.range_diag`：range_diag : range Function.diag = diagonal α
-/
theorem isLindelof_diagonal [LindelofSpace X] : IsLindelof (diagonal X) :=
  @range_diag X ▸ isLindelof_range (continuous_id.prodMk continuous_id)

/-- If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is Lindelöf
  if and only if `s` is compact. -/
/-
**Topology.IsInducing.isLindelof_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isLindelof_iff {f : X -> Y} (hf : IsInducing f) : IsLi
ndelof s ↔ IsLindelof (f '' s)
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.image`：IsLindelof.image {f : X -> Y} (hs : IsLindelof s) (hf 
: Continuous f) : IsLindelof (f '' s)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `instCountableInterFilterMap`：∀ {α : Type u_2} {β : Type u_3} (l : Filter
 α) [CountableInterFilter l] (f : α → β),   CountableInterFilter (Filter.map f l
)
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Topology.IsInducing.mapClusterPt_iff`：mapClusterPt_iff (hf : IsInducing 
f) {x : X} {l : Filter X} : MapClusterPt (f x) l f ↔ ClusterPt x l

--- 原说明 ---
If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is Lindelöf
  if and only if `s` is compact.
-/
theorem Topology.IsInducing.isLindelof_iff {f : X → Y} (hf : IsInducing f) :
    IsLindelof s ↔ IsLindelof (f '' s) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot _ F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x ∈ s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/-- If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is Lindelöf
if and only if `s` is Lindelöf. -/
/-
**Topology.IsEmbedding.isLindelof_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.isLindelof_iff {f : X -> Y} (hf : IsEmbedding f) : Is
Lindelof s ↔ IsLindelof (f '' s)
参数：hf : IsEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isLindelof_iff`：Topology.IsInducing.isLindelof_iff {
f : X -> Y} (hf : IsInducing f) : IsLindelof s ↔ IsLindelof (f '' s)
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…

--- 原说明 ---
If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is Lindelöf
if and only if `s` is Lindelöf.
-/
theorem Topology.IsEmbedding.isLindelof_iff {f : X → Y} (hf : IsEmbedding f) :
    IsLindelof s ↔ IsLindelof (f '' s) := hf.isInducing.isLindelof_iff

/-- The preimage of a Lindelöf set under an inducing map is a Lindelöf set. -/
/-
**Topology.IsInducing.isLindelof_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isLindelof_preimage {f : X -> Y} (hf : IsInducing f) (
hf' : IsClosed (range f)) {K : Set Y} (hK : IsLindelof K) : IsLindelof (f ⁻¹' K)
参数：hf : IsInducing f；hf' : IsClosed (range f)；hK : IsLindelof K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.inter_right`：IsLindelof.inter_right (hs : IsLindelof s) (ht :
 IsClosed t) : IsLindelof (s inter t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.isLindelof_iff`：Topology.IsInducing.isLindelof_iff {
f : X -> Y} (hf : IsInducing f) : IsLindelof s ↔ IsLindelof (f '' s)
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f

--- 原说明 ---
The preimage of a Lindelöf set under an inducing map is a Lindelöf set.
-/
theorem Topology.IsInducing.isLindelof_preimage {f : X → Y} (hf : IsInducing f)
    (hf' : IsClosed (range f)) {K : Set Y} (hK : IsLindelof K) : IsLindelof (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [hf.isLindelof_iff, image_preimage_eq_inter_range]

/-- The preimage of a Lindelöf set under a closed embedding is a Lindelöf set. -/
/-
**Topology.IsClosedEmbedding.isLindelof_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.isLindelof_preimage {f : X -> Y} (hf : IsClosed
Embedding f) {K : Set Y} (hK : IsLindelof K) : IsLindelof (f ⁻¹' K)
参数：hf : IsClosedEmbedding f；hK : IsLindelof K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isLindelof_preimage`：Topology.IsInducing.isLindelof_
preimage {f : X -> Y} (hf : IsInducing f) (hf' : IsClosed (range f)) {K : Set Y}
 (hK : IsLindelof K) : IsLind…
· 使用定理 `Topology.IsClosedEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Topo…
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…

--- 原说明 ---
The preimage of a Lindelöf set under a closed embedding is a Lindelöf set.
-/
theorem Topology.IsClosedEmbedding.isLindelof_preimage {f : X → Y} (hf : IsClosedEmbedding f)
    {K : Set Y} (hK : IsLindelof K) : IsLindelof (f ⁻¹' K) :=
  hf.isInducing.isLindelof_preimage (hf.isClosed_range) hK

/-- A closed embedding is proper, i.e., inverse images of Lindelöf sets are contained in Lindelöf.
Moreover, the preimage of a Lindelöf set is Lindelöf, see
`Topology.IsClosedEmbedding.isLindelof_preimage`. -/
/-
**Topology.IsClosedEmbedding.tendsto_coLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.tendsto_coLindelof {f : X -> Y} (hf : IsClosedE
mbedding f) : Tendsto f (Filter.coLindelof X) (Filter.coLindelof Y)
参数：hf : IsClosedEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `hasBasis_coLindelof`：hasBasis_coLindelof : (coLindelof X).HasBasis IsLin
delof compl
· 使用定理 `IsLindelof.compl_mem_coLindelof`：∀ {X : Type u} [inst : TopologicalSpace
 X] {s : Set X}, IsLindelof s → sᶜ ∈ Filter.coLindelof X
· 使用定理 `Topology.IsClosedEmbedding.isLindelof_preimage`：Topology.IsClosedEmbeddi
ng.isLindelof_preimage {f : X -> Y} (hf : IsClosedEmbedding f) {K : Set Y} (hK :
 IsLindelof K) : IsLindelof (f ⁻¹' K…

--- 原说明 ---
A closed embedding is proper, i.e., inverse images of Lindelöf sets are containe
d in Lindelöf.
Moreover, the preimage of a Lindelöf set is Lindelöf, see
`Topology.IsClosedEmbedding.isLindelof_preimage`.
-/
theorem Topology.IsClosedEmbedding.tendsto_coLindelof {f : X → Y} (hf : IsClosedEmbedding f) :
    Tendsto f (Filter.coLindelof X) (Filter.coLindelof Y) :=
  hasBasis_coLindelof.tendsto_right_iff.mpr fun _K hK =>
    (hf.isLindelof_preimage hK).compl_mem_coLindelof

/-- Sets of subtype are Lindelöf iff the image under a coercion is. -/
/-
**Subtype.isLindelof_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.isLindelof_iff {p : X -> Prop} {s : Set { x // p x }} : IsLindelof
 s ↔ IsLindelof ((↑) '' s : Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.isLindelof_iff`：Topology.IsEmbedding.isLindelof_iff
 {f : X -> Y} (hf : IsEmbedding f) : IsLindelof s ↔ IsLindelof (f '' s)
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)

--- 原说明 ---
Sets of subtype are Lindelöf iff the image under a coercion is.
-/
theorem Subtype.isLindelof_iff {p : X → Prop} {s : Set { x // p x }} :
    IsLindelof s ↔ IsLindelof ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isLindelof_iff
/-
**isLindelof_iff_isLindelof_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_iff_isLindelof_univ : IsLindelof s ↔ IsLindelof (univ : Set s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.isLindelof_iff`：Subtype.isLindelof_iff {p : X -> Prop} {s : Set 
{ x // p x }} : IsLindelof s ↔ IsLindelof ((↑) '' s : Set X)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLindelof_iff_isLindelof_univ : IsLindelof s ↔ IsLindelof (univ : Set s) := by
  rw [Subtype.isLindelof_iff, image_univ, Subtype.range_coe]
/-
**isLindelof_iff_lindelofSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLindelof_iff_lindelofSpace : IsLindelof s ↔ LindelofSpace s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isLindelof_iff_isLindelof_univ`：isLindelof_iff_isLindelof_univ : IsLinde
lof s ↔ IsLindelof (univ : Set s)
· 使用定理 `isLindelof_univ_iff`：isLindelof_univ_iff : IsLindelof (univ : Set X) ↔ L
indelofSpace X
-/
theorem isLindelof_iff_lindelofSpace : IsLindelof s ↔ LindelofSpace s :=
  isLindelof_iff_isLindelof_univ.trans isLindelof_univ_iff

@[deprecated (since := "2026-01-12")]
alias isLindelof_iff_LindelofSpace := isLindelof_iff_lindelofSpace
/-
**IsLindelof.of_coe** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLindelof.of_coe [LindelofSpace s] : IsLindelof s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLindelof_iff_lindelofSpace`：isLindelof_iff_lindelofSpace : IsLindelof 
s ↔ LindelofSpace s
-/
lemma IsLindelof.of_coe [LindelofSpace s] : IsLindelof s := isLindelof_iff_lindelofSpace.mpr ‹_›
/-
**IsLindelof.countable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.countable (hs : IsLindelof s) (hs' : DiscreteTopology s) : s.Co
untable
参数：hs : IsLindelof s；hs' : DiscreteTopology s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.countable_coe_iff`：countable_coe_iff {s : Set α} : Countable s ↔ s.C
ountable
· 使用定理 `countable_of_Lindelof_of_discrete`：countable_of_Lindelof_of_discrete [Li
ndelofSpace X] [DiscreteTopology X] : Countable X
· 使用定理 `isLindelof_iff_lindelofSpace`：isLindelof_iff_lindelofSpace : IsLindelof 
s ↔ LindelofSpace s
-/
theorem IsLindelof.countable (hs : IsLindelof s) (hs' : DiscreteTopology s) : s.Countable :=
  countable_coe_iff.mp
  (@countable_of_Lindelof_of_discrete _ _ (isLindelof_iff_lindelofSpace.mp hs) hs')
/-
**IsLindelof.countable_of_isDiscrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.countable_of_isDiscrete (hs : IsLindelof s) (hs' : IsDiscrete s
) : s.Countable
参数：hs : IsLindelof s；hs' : IsDiscrete s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.countable`：IsLindelof.countable (hs : IsLindelof s) (hs' : Di
screteTopology s) : s.Countable
· 使用定理 `IsDiscrete.to_subtype`：∀ {X : Type u_5} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → DiscreteTopology ↑s
-/
theorem IsLindelof.countable_of_isDiscrete (hs : IsLindelof s) (hs' : IsDiscrete s) :
    s.Countable := hs.countable hs'.to_subtype
/-
**Topology.IsClosedEmbedding.nonLindelofSpace** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] [NonLindelofSpace X] {f : X → Y},   Topology.IsClosedEmbedding f → N
onLindelofSpace Y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonLindelofSpace_of_neBot`：nonLindelofSpace_of_neBot (_ : NeBot (Filter.
coLindelof X)) : NonLindelofSpace X
· 使用定理 `Filter.Tendsto.neBot`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : F
ilter α} {y : Filter β},   Filter.Tendsto f x y → ∀ [hx : x.NeBot], y.NeBot
· 使用定理 `Topology.IsClosedEmbedding.tendsto_coLindelof`：Topology.IsClosedEmbeddin
g.tendsto_coLindelof {f : X -> Y} (hf : IsClosedEmbedding f) : Tendsto f (Filter
.coLindelof X) (Filter.coLindelof Y…
· 使用定理 `instNeBotCoLindelofOfNonLindelofSpace`：∀ {X : Type u} [inst : Topologica
lSpace X] [NonLindelofSpace X], (Filter.coLindelof X).NeBot
-/
protected theorem Topology.IsClosedEmbedding.nonLindelofSpace [NonLindelofSpace X] {f : X → Y}
    (hf : IsClosedEmbedding f) : NonLindelofSpace Y :=
  nonLindelofSpace_of_neBot hf.tendsto_coLindelof.neBot
/-
**Topology.IsClosedEmbedding.LindelofSpace** 是 Mathlib 中的一个定理，位于命名空间 `Topology.I
sClosedEmbedding`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] [h : LindelofSpace Y] {f : X → Y},   Topology.IsClosedEmbedding f → 
LindelofSpace X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.isLindelof_iff`：Topology.IsInducing.isLindelof_iff {
f : X -> Y} (hf : IsInducing f) : IsLindelof s ↔ IsLindelof (f '' s)
· 使用定理 `Topology.IsClosedEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Topo…
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsClosed.isLindelof`：IsClosed.isLindelof [LindelofSpace X] (h : IsClosed
 s) : IsLindelof s
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
-/
protected theorem Topology.IsClosedEmbedding.LindelofSpace [h : LindelofSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) : LindelofSpace X :=
  ⟨by rw [hf.isInducing.isLindelof_iff, image_univ]; exact hf.isClosed_range.isLindelof⟩

/-- Countable topological spaces are Lindelof. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Countable topological spaces are Lindelof.
-/
instance (priority := 100) Countable.LindelofSpace [Countable X] : LindelofSpace X where
  isLindelof_univ := countable_univ.isLindelof

/-- The disjoint union of two Lindelöf spaces is Lindelöf. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The disjoint union of two Lindelöf spaces is Lindelöf.
-/
instance [LindelofSpace X] [LindelofSpace Y] : LindelofSpace (X ⊕ Y) where
  isLindelof_univ := by
    rw [← range_inl_union_range_inr]
    exact (isLindelof_range continuous_inl).union (isLindelof_range continuous_inr)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : ι → Type*} [Countable ι] [∀ i, TopologicalSpace (X i)] [∀ i, LindelofSpace (X i)] :
    LindelofSpace (Σ i, X i) where
  isLindelof_univ := by
    rw [Sigma.univ]
    exact isLindelof_iUnion fun i => isLindelof_range continuous_sigmaMk
/-
**Quot.lindelofSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quot.lindelofSpace {r : X -> X -> Prop} [LindelofSpace X] : LindelofSpace 
(Quot r) where isLindelof_univ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_quot_mk`：range_quot_mk (r : α -> α -> Prop) : range (Quot.mk r
) = univ
· 使用定理 `isLindelof_range`：isLindelof_range [LindelofSpace X] {f : X -> Y} (hf : 
Continuous f) : IsLindelof (range f)
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
-/
instance Quot.lindelofSpace {r : X → X → Prop} [LindelofSpace X] : LindelofSpace (Quot r) where
  isLindelof_univ := by
    rw [← range_quot_mk]
    exact isLindelof_range continuous_quot_mk

@[deprecated (since := "2026-01-12")]
alias Quot.LindelofSpace := Quot.lindelofSpace
/-
**Quotient.lindelofSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.lindelofSpace {s : Setoid X} [LindelofSpace X] : LindelofSpace (Q
uotient s)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Quotient.lindelofSpace {s : Setoid X} [LindelofSpace X] : LindelofSpace (Quotient s) :=
  Quot.lindelofSpace

@[deprecated (since := "2026-01-12")]
alias Quotient.LindelofSpace := Quotient.lindelofSpace

/-- A continuous image of a Lindelöf set is a Lindelöf set within the codomain. -/
/-
**LindelofSpace.of_continuous_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LindelofSpace.of_continuous_surjective {f : X -> Y} [LindelofSpace X] (hf 
: Continuous f) (hsur : Function.Surjective f) : LindelofSpace Y where isLindelo
f_univ
参数：hf : Continuous f；hsur : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `IsLindelof.image`：IsLindelof.image {f : X -> Y} (hs : IsLindelof s) (hf 
: Continuous f) : IsLindelof (f '' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLindelof_univ_iff`：isLindelof_univ_iff : IsLindelof (univ : Set X) ↔ L
indelofSpace X

--- 原说明 ---
A continuous image of a Lindelöf set is a Lindelöf set within the codomain.
-/
theorem LindelofSpace.of_continuous_surjective {f : X → Y} [LindelofSpace X] (hf : Continuous f)
    (hsur : Function.Surjective f) : LindelofSpace Y where
  isLindelof_univ := by
    rw [← Set.image_univ_of_surjective hsur]
    exact IsLindelof.image (isLindelof_univ_iff.mpr ‹_›) hf

/-- A set `s` is Hereditarily Lindelöf if every subset is a Lindelof set. We require this only
for open sets in the definition, and then conclude that this holds for all sets by ADD. -/
/-
**IsHereditarilyLindelof** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsHereditarilyLindelof (s : Set X)
参数：s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is Hereditarily Lindelöf if every subset is a Lindelof set. We require
 this only
for open sets in the definition, and then conclude that this holds for all sets 
by ADD.
-/
def IsHereditarilyLindelof (s : Set X) :=
  ∀ t ⊆ s, IsLindelof t

/-- Type class for Hereditarily Lindelöf spaces. -/
/-
**HereditarilyLindelofSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_2) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for Hereditarily Lindelöf spaces.
-/
class HereditarilyLindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a Hereditarily Lindelöf space, `Set.univ` is a Hereditarily Lindelöf set. -/
  isHereditarilyLindelof_univ : IsHereditarilyLindelof (univ : Set X)
/-
**IsHereditarilyLindelof.isLindelof_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsHereditarilyLindelof.isLindelof_subset (hs : IsHereditarilyLindelof s) (
ht : t subseteq s) : IsLindelof t
参数：hs : IsHereditarilyLindelof s；ht : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsHereditarilyLindelof.isLindelof_subset (hs : IsHereditarilyLindelof s) (ht : t ⊆ s) :
    IsLindelof t := hs t ht
/-
**IsHereditarilyLindelof.isLindelof** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsHereditarilyLindelof.isLindelof (hs : IsHereditarilyLindelof s) : IsLind
elof s
参数：hs : IsHereditarilyLindelof s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsHereditarilyLindelof.isLindelof_subset`：IsHereditarilyLindelof.isLinde
lof_subset (hs : IsHereditarilyLindelof s) (ht : t subseteq s) : IsLindelof t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma IsHereditarilyLindelof.isLindelof (hs : IsHereditarilyLindelof s) :
    IsLindelof s := hs.isLindelof_subset Subset.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) HereditarilyLindelof.to_Lindelof [HereditarilyLindelofSpace X] :
    LindelofSpace X where
  isLindelof_univ := HereditarilyLindelofSpace.isHereditarilyLindelof_univ.isLindelof
/-
**HereditarilyLindelofSpace.isLindelof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HereditarilyLindelofSpace.isLindelof [HereditarilyLindelofSpace X] (s : Se
t X) : IsLindelof s
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HereditarilyLindelofSpace.isHereditarilyLindelof_univ`：∀ {X : Type u_2} 
{inst : TopologicalSpace X} [self : HereditarilyLindelofSpace X], IsHereditarily
Lindelof Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem HereditarilyLindelofSpace.isLindelof [HereditarilyLindelofSpace X] (s : Set X) :
    IsLindelof s := by
  apply HereditarilyLindelofSpace.isHereditarilyLindelof_univ
  exact subset_univ s

@[deprecated (since := "2026-01-12")]
alias HereditarilyLindelof_LindelofSets := HereditarilyLindelofSpace.isLindelof
/-
**HereditarilyLindelofSpace.of_forall_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HereditarilyLindelofSpace.of_forall_isOpen (H : forall s : Set X, IsOpen s
 -> IsLindelof s) : HereditarilyLindelofSpace X
参数：H : forall s : Set X, IsOpen s -> IsLindelof s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLindelof_of_countable_subcover`：isLindelof_of_countable_subcover (h : 
forall {ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ 
i, U i) -> exists t : …
· 使用定理 `IsLindelof.elim_countable_subcover`：IsLindelof.elim_countable_subcover {
ι : Type v} (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) 
(hsU : s subseteq ⋃ i, U…
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem HereditarilyLindelofSpace.of_forall_isOpen (H : ∀ s : Set X, IsOpen s → IsLindelof s) :
    HereditarilyLindelofSpace X := by
  refine ⟨fun s _ ↦ isLindelof_of_countable_subcover fun U U_open hU ↦ ?_⟩
  obtain ⟨t, t_count, ht⟩ := H (⋃ i, U i) (isOpen_iUnion U_open)
    |>.elim_countable_subcover U U_open subset_rfl
  exact ⟨t, t_count, hU.trans ht⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SecondCountableTopology.toHereditarilyLindelof
    [SecondCountableTopology X] : HereditarilyLindelofSpace X where
  isHereditarilyLindelof_univ t _ _ := by
    apply isLindelof_iff_countable_subcover.mpr
    intro ι U hι hcover
    have := @isOpen_iUnion_countable X _ _ ι U hι
    rcases this with ⟨t, ⟨htc, htu⟩⟩
    use t, htc
    exact subset_of_subset_of_eq hcover (id htu.symm)
/-
**eq_open_union_countable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_open_union_countable [HereditarilyLindelofSpace X] {ι : Type*} (U : ι -
> Set X) (h : forall i, IsOpen (U i)) : exists t : Set ι, t.Countable ∧ ⋃ i in t
, U i = ⋃ i, U i
参数：U : ι -> Set X；h : forall i, IsOpen (U i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HereditarilyLindelofSpace.isLindelof`：HereditarilyLindelofSpace.isLindel
of [HereditarilyLindelofSpace X] (s : Set X) : IsLindelof s
· 使用定理 `IsLindelof.elim_countable_subcover`：IsLindelof.elim_countable_subcover {
ι : Type v} (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) 
(hsU : s subseteq ⋃ i, U…
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `Set.iUnion₂_subset_iUnion`：iUnion₂_subset_iUnion (κ : ι -> Sort*) (s : ι
 -> Set α) : ⋃ (i) (_ : κ i), s i subseteq ⋃ i, s i
-/
lemma eq_open_union_countable [HereditarilyLindelofSpace X] {ι : Type*} (U : ι → Set X)
    (h : ∀ i, IsOpen (U i)) : ∃ t : Set ι, t.Countable ∧ ⋃ i ∈ t, U i = ⋃ i, U i := by
  have : IsLindelof (⋃ i, U i) := HereditarilyLindelofSpace.isLindelof (⋃ i, U i)
  rcases this.elim_countable_subcover U h (Eq.subset rfl) with ⟨t, ⟨htc, htu⟩⟩
  use t, htc
  apply eq_of_subset_of_subset (iUnion₂_subset_iUnion (fun i ↦ i ∈ t) fun i ↦ U i) htu
/-
**eq_open_union_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_open_union_nat [HereditarilyLindelofSpace X] {ι : Type*} [Nonempty ι] (
U : ι -> Set X) (h : forall i, IsOpen (U i)) : exists k : Nat -> ι, ⋃ n, U (k n)
 = ⋃ i, U i
参数：U : ι -> Set X；h : forall i, IsOpen (U i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_open_union_countable`：eq_open_union_countable [HereditarilyLindelofSp
ace X] {ι : Type*} (U : ι -> Set X) (h : forall i, IsOpen (U i)) : exists t : Se
t ι, t.Counta…
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Set.iUnion_false`：iUnion_false {s : False -> Set α} : iUnion s = ∅
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Countable.exists_eq_range`：∀ {α : Type u} {s : Set α}, s.Countable →
 s.Nonempty → ∃ f, s = Set.range f
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
-/
lemma eq_open_union_nat [HereditarilyLindelofSpace X] {ι : Type*} [Nonempty ι] (U : ι → Set X)
    (h : ∀ i, IsOpen (U i)) : ∃ k : ℕ → ι, ⋃ n, U (k n) = ⋃ i, U i := by
  obtain ⟨t, htc, htu⟩ := eq_open_union_countable U h
  rcases eq_empty_or_nonempty t with rfl | t_ne
  · simp_rw [mem_empty_iff_false, iUnion_false, iUnion_empty, eq_comm (a := ∅), iUnion_eq_empty]
      at htu
    simp [htu]
  · obtain ⟨k, rfl⟩ := htc.exists_eq_range t_ne
    use k
    rwa [biUnion_range] at htu
/-
**eq_closed_inter_countable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_closed_inter_countable [HereditarilyLindelofSpace X] {ι : Type*} (C : ι
 -> Set X) (h : forall i, IsClosed (C i)) : exists t : Set ι, t.Countable ∧ ⋂ i 
in t, C i = ⋂ i, C i
参数：C : ι -> Set X；h : forall i, IsClosed (C i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用引理 `eq_open_union_countable`：eq_open_union_countable [HereditarilyLindelofSp
ace X] {ι : Type*} (U : ι -> Set X) (h : forall i, IsOpen (U i)) : exists t : Se
t ι, t.Counta…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
lemma eq_closed_inter_countable [HereditarilyLindelofSpace X] {ι : Type*} (C : ι → Set X)
    (h : ∀ i, IsClosed (C i)) : ∃ t : Set ι, t.Countable ∧ ⋂ i ∈ t, C i = ⋂ i, C i := by
  conv in _ = _ => rw [← compl_inj_iff]; simp
  exact eq_open_union_countable (fun i ↦ (C i)ᶜ) (fun i ↦ (h i).isOpen_compl)
/-
**eq_closed_inter_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_closed_inter_nat [HereditarilyLindelofSpace X] {ι : Type*} [Nonempty ι]
 (C : ι -> Set X) (h : forall i, IsClosed (C i)) : exists k : Nat -> ι, ⋂ n, C (
k n) = ⋂ i, C i
参数：C : ι -> Set X；h : forall i, IsClosed (C i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用引理 `eq_open_union_nat`：eq_open_union_nat [HereditarilyLindelofSpace X] {ι : 
Type*} [Nonempty ι] (U : ι -> Set X) (h : forall i, IsOpen (U i)) : exists k : N
at -> ι…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
lemma eq_closed_inter_nat [HereditarilyLindelofSpace X] {ι : Type*} [Nonempty ι] (C : ι → Set X)
    (h : ∀ i, IsClosed (C i)) : ∃ k : ℕ → ι, ⋂ n, C (k n) = ⋂ i, C i := by
  conv in _ = _ => rw [← compl_inj_iff]; simp
  exact eq_open_union_nat (fun i ↦ (C i)ᶜ) (fun i ↦ (h i).isOpen_compl)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HereditarilyLindelofSpace X] (p : X → Prop) :
    HereditarilyLindelofSpace {x // p x} :=
  HereditarilyLindelofSpace.of_forall_isOpen fun _ _ =>
    Subtype.isLindelof_iff.2 <| HereditarilyLindelofSpace.isLindelof _

end Lindelof

