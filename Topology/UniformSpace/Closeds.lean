/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.UniformSpace.UniformEmbedding

import Mathlib.Topology.UniformSpace.Compact

/-!
# Hausdorff uniformity

This file defines the Hausdorff uniformity on the types of closed subsets, compact subsets and
and nonempty compact subsets of a uniform space. This is the generalization of the uniformity
induced by the Hausdorff metric to hyperspaces of uniform spaces.
-/

@[expose] public section

open Topology
open scoped Uniformity Filter

variable {α β γ : Type*}

section hausdorffEntourage

open SetRel

/-- The set of pairs of sets contained in each other's thickening with respect to an entourage. -/
/-
**hausdorffEntourage** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：hausdorffEntourage (U : SetRel α α) : SetRel (Set α) (Set α)
参数：U : SetRel α α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of pairs of sets contained in each other's thickening with respect to an
 entourage.
-/
def hausdorffEntourage (U : SetRel α α) : SetRel (Set α) (Set α) :=
  {x | x.1 ⊆ U.preimage x.2 ∧ x.2 ⊆ U.image x.1}
/-
**mem_hausdorffEntourage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_hausdorffEntourage (U : SetRel α α) (s t : Set α) : (s, t) in hausdorf
fEntourage U ↔ s subseteq U.preimage t ∧ t subseteq U.image s
参数：U : SetRel α α；s t : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_hausdorffEntourage (U : SetRel α α) (s t : Set α) :
    (s, t) ∈ hausdorffEntourage U ↔ s ⊆ U.preimage t ∧ t ⊆ U.image s :=
  Iff.rfl

@[gcongr]
/-
**hausdorffEntourage_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hausdorffEntourage_mono {U V : SetRel α α} (h : U subseteq V) : hausdorffE
ntourage U subseteq hausdorffEntourage V
参数：h : U subseteq V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用引理 `Mathlib.Tactic.GCongr.and_mono`：and_mono (h₁ : a -> c) (h₂ : a -> b -> d
) : (a ∧ b) -> c ∧ d
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SetRel.preimage_subset_preimage_left`：∀ {α : Type u_1} {β : Type u_2} {R
₁ R₂ : SetRel α β} {t : Set β}, R₁ ⊆ R₂ → R₁.preimage t ⊆ R₂.preimage t
· 使用定理 `SetRel.image_subset_image_left`：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ :
 SetRel α β} {s : Set α}, R₁ ⊆ R₂ → R₁.image s ⊆ R₂.image s
-/
theorem hausdorffEntourage_mono {U V : SetRel α α} (h : U ⊆ V) :
    hausdorffEntourage U ⊆ hausdorffEntourage V := by
  unfold hausdorffEntourage
  gcongr
/-
**monotone_hausdorffEntourage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_hausdorffEntourage : Monotone (hausdorffEntourage (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hausdorffEntourage_mono`：hausdorffEntourage_mono {U V : SetRel α α} (h :
 U subseteq V) : hausdorffEntourage U subseteq hausdorffEntourage V
-/
theorem monotone_hausdorffEntourage : Monotone (hausdorffEntourage (α := α)) :=
  fun _ _ => hausdorffEntourage_mono

@[simp]
/-
**hausdorffEntourage_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hausdorffEntourage_id : hausdorffEntourage (.id : SetRel α α) = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SetRel.preimage_id`：∀ {α : Type u_1} (s : Set α), SetRel.id.preimage s =
 s
· 使用定理 `SetRel.image_id`：∀ {α : Type u_1} (s : Set α), SetRel.id.image s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hausdorffEntourage_id : hausdorffEntourage (.id : SetRel α α) = .id := by
  simp_rw [hausdorffEntourage, preimage_id, image_id, ← subset_antisymm_iff, SetRel.id]
/-
**isRefl_hausdorffEntourage** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isRefl_hausdorffEntourage (U : SetRel α α) [U.IsRefl] : (hausdorffEntourag
e U).IsRefl
参数：U : SetRel α α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.self_subset_preimage`：self_subset_preimage [R.IsRefl] (s : Set α)
 : s subseteq R.preimage s
· 使用引理 `SetRel.self_subset_image`：self_subset_image [R.IsRefl] (s : Set α) : s s
ubseteq R.image s
-/
instance isRefl_hausdorffEntourage (U : SetRel α α) [U.IsRefl] :
    (hausdorffEntourage U).IsRefl :=
  ⟨fun _ => ⟨U.self_subset_preimage _, U.self_subset_image _⟩⟩

@[simp]
/-
**inv_hausdorffEntourage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_hausdorffEntourage (U : SetRel α α) : (hausdorffEntourage U).inv = hau
sdorffEntourage U.inv
参数：U : SetRel α α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem inv_hausdorffEntourage (U : SetRel α α) :
    (hausdorffEntourage U).inv = hausdorffEntourage U.inv :=
  Set.ext fun _ => And.comm
/-
**isSymm_hausdorffEntourage** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isSymm_hausdorffEntourage (U : SetRel α α) [U.IsSymm] : (hausdorffEntourag
e U).IsSymm
参数：U : SetRel α α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SetRel.inv_eq_self_iff`：inv_eq_self_iff : R.inv = R ↔ R.IsSymm where mp 
hR
· 使用定理 `inv_hausdorffEntourage`：inv_hausdorffEntourage (U : SetRel α α) : (hausd
orffEntourage U).inv = hausdorffEntourage U.inv
· 使用定理 `SetRel.inv_eq_self`：∀ {α : Type u_1} (R : SetRel α α) [R.IsSymm], R.inv 
= R
-/
instance isSymm_hausdorffEntourage (U : SetRel α α) [U.IsSymm] :
    (hausdorffEntourage U).IsSymm := by
  rw [← inv_eq_self_iff, inv_hausdorffEntourage, inv_eq_self]
/-
**hausdorffEntourage_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hausdorffEntourage_comp (U V : SetRel α α) : hausdorffEntourage (U ○ V) = 
hausdorffEntourage U ○ hausdorffEntourage V
参数：U V : SetRel α α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `mem_hausdorffEntourage`：mem_hausdorffEntourage (U : SetRel α α) (s t : S
et α) : (s, t) in hausdorffEntourage U ↔ s subseteq U.preimage t ∧ t subseteq U.
image s
· 使用引理 `SetRel.preimage_comp`：preimage_comp : preimage (R ○ S) u = preimage R (p
reimage S u)
· 使用引理 `Mathlib.Tactic.GCongr.and_mono`：and_mono (h₁ : a -> c) (h₂ : a -> b -> d
) : (a ∧ b) -> c ∧ d
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SetRel.preimage_subset_preimage`：∀ {α : Type u_1} {β : Type u_2} {R : Se
tRel α β} {t₁ t₂ : Set β}, t₁ ⊆ t₂ → R.preimage t₁ ⊆ R.preimage t₂
· 使用引理 `SetRel.image_comp`：image_comp : image (R ○ S) s = image S (image R s)
· 使用定理 `SetRel.image_subset_image`：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α
 β} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → R.image s₁ ⊆ R.image s₂
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem hausdorffEntourage_comp (U V : SetRel α α) :
    hausdorffEntourage (U ○ V) = hausdorffEntourage U ○ hausdorffEntourage V := by
  apply subset_antisymm
  · intro ⟨s, t⟩ ⟨hst, hts⟩
    simp only [mem_comp, mem_hausdorffEntourage] at *
    refine ⟨U.image s ∩ V.preimage t, ⟨?_, Set.inter_subset_left⟩, ⟨Set.inter_subset_right, ?_⟩⟩
    · intro x hx
      obtain ⟨z, hz, y, hxy, hyz⟩ := hst hx
      exact ⟨y, ⟨⟨x, hx, hxy⟩, ⟨z, hz, hyz⟩⟩, hxy⟩
    · intro z hz
      obtain ⟨x, hx, y, hxy, hyz⟩ := hts hz
      exact ⟨y, ⟨⟨x, hx, hxy⟩, ⟨z, hz, hyz⟩⟩, hyz⟩
  · intro ⟨s₁, s₃⟩ ⟨s₂, ⟨h₁₂, h₂₁⟩, ⟨h₂₃, h₃₂⟩⟩
    simp only at *
    grw [mem_hausdorffEntourage, preimage_comp, ← h₂₃, ← h₁₂, image_comp, ← h₂₁, ← h₃₂]
    exact ⟨subset_rfl, subset_rfl⟩
/-
**isTrans_hausdorffEntourage** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isTrans_hausdorffEntourage (U : SetRel α α) [U.IsTrans] : (hausdorffEntour
age U).IsTrans
参数：U : SetRel α α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SetRel.isTrans_iff_comp_subset_self`：isTrans_iff_comp_subset_self : R.Is
Trans ↔ R ○ R subseteq R where mp _
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hausdorffEntourage_comp`：hausdorffEntourage_comp (U V : SetRel α α) : ha
usdorffEntourage (U ○ V) = hausdorffEntourage U ○ hausdorffEntourage V
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `hausdorffEntourage_mono`：hausdorffEntourage_mono {U V : SetRel α α} (h :
 U subseteq V) : hausdorffEntourage U subseteq hausdorffEntourage V
· 使用引理 `SetRel.comp_subset_self`：comp_subset_self [R.IsTrans] : R ○ R subseteq R
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
instance isTrans_hausdorffEntourage (U : SetRel α α) [U.IsTrans] :
    (hausdorffEntourage U).IsTrans := by
  grw [isTrans_iff_comp_subset_self, ← hausdorffEntourage_comp, comp_subset_self]

@[simp]
/-
**singleton_mem_hausdorffEntourage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_mem_hausdorffEntourage (U : SetRel α α) (x y : α) : ({x}, {y}) i
n hausdorffEntourage U ↔ (x, y) in U
参数：U : SetRel α α；x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_mem_hausdorffEntourage (U : SetRel α α) (x y : α) :
    ({x}, {y}) ∈ hausdorffEntourage U ↔ (x, y) ∈ U := by
  simp [hausdorffEntourage]
/-
**union_mem_hausdorffEntourage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：union_mem_hausdorffEntourage (U : SetRel α α) {s₁ s₂ t₁ t₂ : Set α} (h₁ : 
(s₁, t₁) in hausdorffEntourage U) (h₂ : (s₂, t₂) in hausdorffEntourage U) : (s₁ 
union s₂, t₁ union t₂) in hausdorffEntourage U
参数：U : SetRel α α；h₁ : (s₁, t₁) in hausdorffEntourage U；h₂ : (s₂, t₂) in hausdor
ffEntourage U。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_mem_hausdorffEntourage (U : SetRel α α) {s₁ s₂ t₁ t₂ : Set α}
    (h₁ : (s₁, t₁) ∈ hausdorffEntourage U) (h₂ : (s₂, t₂) ∈ hausdorffEntourage U) :
    (s₁ ∪ s₂, t₁ ∪ t₂) ∈ hausdorffEntourage U := by
  grind [mem_hausdorffEntourage, preimage_union, image_union]
/-
**TotallyBounded.exists_prodMk_finset_mem_hausdorffEntourage** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：TotallyBounded.exists_prodMk_finset_mem_hausdorffEntourage [UniformSpace α
] {s : Set α} (hs : TotallyBounded s) {U : SetRel α α} (hU : U in 𝓤 α) : exists 
t : Finset α, (↑t, s) in hausdorffEntourage U
参数：hs : TotallyBounded s；hU : U in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_le_uniformity`：symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) <= 𝓤
 _
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
-/
theorem TotallyBounded.exists_prodMk_finset_mem_hausdorffEntourage [UniformSpace α]
    {s : Set α} (hs : TotallyBounded s) {U : SetRel α α} (hU : U ∈ 𝓤 α) :
    ∃ t : Finset α, (↑t, s) ∈ hausdorffEntourage U := by
  obtain ⟨t, ht₁, ht₂⟩ := hs _ (symm_le_uniformity hU)
  lift t to Finset α using ht₁
  classical
  refine ⟨{x ∈ t | ∃ y ∈ s, (x, y) ∈ U}, ?_⟩
  rw [Finset.coe_filter]
  refine ⟨fun _ h => h.2, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht₂ hx)
  exact ⟨y, ⟨hy, x, hx, hxy⟩, hxy⟩
/-
**prod_mem_hausdorffEntourage_entourageProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_mem_hausdorffEntourage_entourageProd (U₁ : SetRel α α) (U₂ : SetRel β
 β) {s₁ t₁ : Set α} {s₂ t₂ : Set β} (h₁ : (s₁, t₁) in hausdorffEntourage U₁) (h₂
 : (s₂, t₂) in hausdorffEntourage U₂) : (s₁ ×ˢ s₂, t₁ ×ˢ t₂) in hausdorffEntoura
ge (entourageProd U₁ U₂)
参数：U₁ : SetRel α α；U₂ : SetRel β β；h₁ : (s₁, t₁) in hausdorffEntourage U₁；h₂ : (
s₂, t₂) in hausdorffEntourage U₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_mem_hausdorffEntourage_entourageProd
    (U₁ : SetRel α α) (U₂ : SetRel β β) {s₁ t₁ : Set α} {s₂ t₂ : Set β}
    (h₁ : (s₁, t₁) ∈ hausdorffEntourage U₁) (h₂ : (s₂, t₂) ∈ hausdorffEntourage U₂) :
    (s₁ ×ˢ s₂, t₁ ×ˢ t₂) ∈ hausdorffEntourage (entourageProd U₁ U₂) := by
  simp only [mem_hausdorffEntourage] at *
  grind [preimage_entourageProd_prod, image_entourageProd_prod]

end hausdorffEntourage

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

variable (α) in
/-- The Hausdorff uniformity on the powerset of a uniform space. Used for defining the uniformities
on `Closeds`, `Compacts` and `NonemptyCompacts`.
See note [reducible non-instances]. -/
/-
**UniformSpace.hausdorff** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace`。
形式化陈述：(α : Type u_1) → [UniformSpace α] → UniformSpace (Set α)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)

--- 原说明 ---
The Hausdorff uniformity on the powerset of a uniform space. Used for defining t
he uniformities
on `Closeds`, `Compacts` and `NonemptyCompacts`.
See note [reducible non-instances].
-/
protected abbrev UniformSpace.hausdorff : UniformSpace (Set α) := .ofCore
  { uniformity := (𝓤 α).lift' hausdorffEntourage
    refl := by
      simp_rw [Filter.principal_le_lift', SetRel.id_subset_iff]
      intro (U : SetRel α α) hU
      have := isRefl_of_mem_uniformity hU
      exact isRefl_hausdorffEntourage U
    symm :=
      Filter.tendsto_lift'.mpr fun U hU => Filter.mem_of_superset
        (Filter.mem_lift' (symm_le_uniformity hU)) (inv_hausdorffEntourage U).symm.subset
    comp := by
      rw [Filter.le_lift']
      intro U hU
      obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
      refine Filter.mem_of_superset (Filter.mem_lift' (Filter.mem_lift' hV)) ?_
      grw [← hausdorffEntourage_comp, hVU] }

attribute [local instance] UniformSpace.hausdorff
/-
**Filter.HasBasis.uniformity_hausdorff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformity_hausdorff {ι : Sort*} {p : ι -> Prop} {s : ι ->
 Set (α × α)} (h : (𝓤 α).HasBasis p s) : (𝓤 (Set α)).HasBasis p (hausdorffEntour
age ∘ s)
参数：α × α；h : (𝓤 α).HasBasis p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.lift'`：Filter.HasBasis.lift'_interior {l : Filter X} {p 
: ι -> Prop} {s : ι -> Set X} (h : l.HasBasis p s) : (l.lift' interior).HasBasis
 p fun i =>…
· 使用定理 `monotone_hausdorffEntourage`：monotone_hausdorffEntourage : Monotone (hau
sdorffEntourage (α
-/
theorem Filter.HasBasis.uniformity_hausdorff
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (Set α)).HasBasis p (hausdorffEntourage ∘ s) :=
  h.lift' monotone_hausdorffEntourage

namespace UniformSpace.hausdorff

/-
**UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen** 是 Mathlib 中的一个定理，位于命名
空间 `UniformSpace.hausdorff`。
形式化陈述：isOpen_inter_nonempty_of_isOpen {U : Set α} (hU : IsOpen U) : IsOpen {s | 
(s inter U).Nonempty}
参数：hU : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `UniformSpace.mem_nhds_iff`：UniformSpace.mem_nhds_iff {x : α} {s : Set α}
 : s in 𝓝 x ↔ exists V in 𝓤 α, ball x V subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.mem_nhds_iff`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} 
{s : Set X}, IsOpen s → (s ∈ nhds x ↔ x ∈ s)
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
-/
theorem isOpen_inter_nonempty_of_isOpen {U : Set α} (hU : IsOpen U) :
    IsOpen {s | (s ∩ U).Nonempty} := by
  rw [isOpen_iff_mem_nhds]
  intro s ⟨x, hx₁, hx₂⟩
  rw [← hU.mem_nhds_iff, mem_nhds_iff] at hx₂
  obtain ⟨V, hV, hVU⟩ := hx₂
  rw [mem_nhds_iff]
  refine ⟨_, Filter.mem_lift' hV, ?_⟩
  rintro s' ⟨hs', -⟩
  obtain ⟨y, hy, hxy⟩ := hs' hx₁
  exact ⟨y, hy, hVU hxy⟩

/-- In the Hausdorff uniformity, the powerset of a closed set is closed. -/
/-
**UniformSpace.hausdorff._root_.IsClosed.powerset_hausdorff** 是 Mathlib 中的一个定理，位
于命名空间 `UniformSpace.hausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the Hausdorff uniformity, the powerset of a closed set is closed.
-/
theorem _root_.IsClosed.powerset_hausdorff {F : Set α} (hF : IsClosed F) :
    IsClosed F.powerset := by
  simp_rw [Set.powerset, ← isOpen_compl_iff, Set.compl_ofPred, ← Set.inter_compl_nonempty_iff]
  exact isOpen_inter_nonempty_of_isOpen hF.isOpen_compl
/-
**UniformSpace.hausdorff.isClopen_singleton_empty** 是 Mathlib 中的一个定理，位于命名空间 `Uni
formSpace.hausdorff`。
形式化陈述：isClopen_singleton_empty : IsClopen {(∅ : Set α)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.powerset_empty`：powerset_empty : 𝒫 (∅ : Set α) = {∅}
· 使用定理 `IsClosed.powerset_hausdorff`：∀ {α : Type u_1} [inst : UniformSpace α] {F
 : Set α}, IsClosed F → IsClosed (𝒫 F)
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_eq_uniformity`：nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball
 x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SetRel.image_empty_right`：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α 
β}, R.image ∅ = ∅
-/
theorem isClopen_singleton_empty : IsClopen {(∅ : Set α)} := by
  constructor
  · rw [← Set.powerset_empty]
    exact isClosed_empty.powerset_hausdorff
  · simp_rw [isOpen_iff_mem_nhds, Set.mem_singleton_iff, forall_eq, nhds_eq_uniformity]
    filter_upwards [Filter.mem_lift' <| Filter.mem_lift' Filter.univ_mem] with F ⟨_, hF⟩
    simpa using hF
/-
**UniformSpace.hausdorff.isUniformEmbedding_singleton** 是 Mathlib 中的一个定理，位于命名空间 
`UniformSpace.hausdorff`。
形式化陈述：isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α -> Set α) where
 injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_lift'_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {h : Set α → Set β} {m : γ → β},   Filter.comap m (f.lift' h) = f.l
ift' (Set.p…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.lift'_id`：∀ {α : Type u_1} {f : Filter α}, f.lift' id = f
· 使用定理 `Set.singleton_injective`：singleton_injective : Injective (singleton : α 
-> Set α)
-/
theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α → Set α) where
  injective := Set.singleton_injective
  comap_uniformity := by
    change Filter.comap _ (Filter.lift' _ _) = _
    simp_rw [Filter.comap_lift'_eq, Function.comp_def, Set.preimage,
      singleton_mem_hausdorffEntourage]
    exact Filter.lift'_id
/-
**UniformSpace.hausdorff.isClosedEmbedding_singleton** 是 Mathlib 中的一个定理，位于命名空间 `
UniformSpace.hausdorff`。
形式化陈述：isClosedEmbedding_singleton [T0Space α] : Topology.IsClosedEmbedding ({·} 
: α -> Set α) where __
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `UniformSpace.hausdorff.isUniformEmbedding_singleton`：isUniformEmbedding_
singleton : IsUniformEmbedding ({·} : α -> Set α) where injective
· 使用定理 `TopologicalSpace.isClosed_range_singleton`：∀ {α : Type u_1} [inst : Topo
logicalSpace α] [T2Space α] {t : TopologicalSpace (Set α)},   IsOpen {∅} → (∀ {U
 : Set α}, IsOpen U → IsOpen {s…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `UniformSpace.hausdorff.isClopen_singleton_empty`：isClopen_singleton_empt
y : IsClopen {(∅ : Set α)}
· 使用定理 `UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen`：isOpen_inter_non
empty_of_isOpen {U : Set α} (hU : IsOpen U) : IsOpen {s | (s inter U).Nonempty}
-/
theorem isClosedEmbedding_singleton [T0Space α] :
    Topology.IsClosedEmbedding ({·} : α → Set α) where
  __ := isUniformEmbedding_singleton.isEmbedding
  isClosed_range :=
    TopologicalSpace.isClosed_range_singleton
      isClopen_singleton_empty.isOpen
      isOpen_inter_nonempty_of_isOpen
/-
**UniformSpace.hausdorff.uniformContinuous_union** 是 Mathlib 中的一个定理，位于命名空间 `Unif
ormSpace.hausdorff`。
形式化陈述：uniformContinuous_union : UniformContinuous (fun x : Set α × Set α => x.1 
union x.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.tendsto_lift'`：tendsto_lift' {m : γ -> β} {l : Filter γ} : Tendst
o m l (f.lift' h) ↔ forall s in f, forallᶠ a in l, m a in h s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `entourageProd_mem_uniformity`：entourageProd_mem_uniformity [t₁ : Uniform
Space α] [t₂ : UniformSpace β] {u : SetRel α α} {v : SetRel β β} (hu : u in 𝓤 α)
 (hv : v in 𝓤 β) :…
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `union_mem_hausdorffEntourage`：union_mem_hausdorffEntourage (U : SetRel α
 α) {s₁ s₂ t₁ t₂ : Set α} (h₁ : (s₁, t₁) in hausdorffEntourage U) (h₂ : (s₂, t₂)
 in hausdorffEntou…
-/
theorem uniformContinuous_union : UniformContinuous (fun x : Set α × Set α => x.1 ∪ x.2) := by
  refine Filter.tendsto_lift'.mpr fun U hU => ?_
  filter_upwards [entourageProd_mem_uniformity (Filter.mem_lift' hU) (Filter.mem_lift' hU)]
    with _ ⟨h₁, h₂⟩ using union_mem_hausdorffEntourage U h₁ h₂
/-
**UniformSpace.hausdorff.uniformContinuous_prod** 是 Mathlib 中的一个定理，位于命名空间 `Unifo
rmSpace.hausdorff`。
形式化陈述：uniformContinuous_prod : UniformContinuous (fun x : Set α × Set β => x.1 ×
ˢ x.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.HasBasis.lift'`：Filter.HasBasis.lift'_interior {l : Filter X} {p 
: ι -> Prop} {s : ι -> Set X} (h : l.HasBasis p s) : (l.lift' interior).HasBasis
 p fun i =>…
· 使用定理 `Filter.HasBasis.uniformity_prod`：Filter.HasBasis.uniformity_prod {ιa ιb 
: Type*} [UniformSpace α] [UniformSpace β] {pa : ιa -> Prop} {pb : ιb -> Prop} {
sa : ιa -> SetRel α α…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `monotone_hausdorffEntourage`：monotone_hausdorffEntourage : Monotone (hau
sdorffEntourage (α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `entourageProd_mem_uniformity`：entourageProd_mem_uniformity [t₁ : Uniform
Space α] [t₂ : UniformSpace β] {u : SetRel α α} {v : SetRel β β} (hu : u in 𝓤 α)
 (hv : v in 𝓤 β) :…
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `prod_mem_hausdorffEntourage_entourageProd`：prod_mem_hausdorffEntourage_e
ntourageProd (U₁ : SetRel α α) (U₂ : SetRel β β) {s₁ t₁ : Set α} {s₂ t₂ : Set β}
 (h₁ : (s₁, t₁) in hausdorffEnt…
-/
theorem uniformContinuous_prod : UniformContinuous (fun x : Set α × Set β => x.1 ×ˢ x.2) := by
  refine (𝓤 α).basis_sets.uniformity_prod (𝓤 β).basis_sets |>.lift' monotone_hausdorffEntourage
    |>.tendsto_right_iff.mpr fun ⟨U, V⟩ ⟨hU, hV⟩ => ?_
  filter_upwards [entourageProd_mem_uniformity (Filter.mem_lift' hU) (Filter.mem_lift' hV)]
    with ⟨⟨s₁, s₂⟩, ⟨t₁, t₂⟩⟩ ⟨h₁, h₂⟩ using prod_mem_hausdorffEntourage_entourageProd U V h₁ h₂
/-
**UniformSpace.hausdorff.uniformContinuous_closure** 是 Mathlib 中的一个定理，位于命名空间 `Un
iformSpace.hausdorff`。
形式化陈述：uniformContinuous_closure : UniformContinuous (closure (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.HasBasis.uniformity_hausdorff`：Filter.HasBasis.uniformity_hausdor
ff {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) :
 (𝓤 (Set α)).HasBasis p (h…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `UniformSpace.closure_subset_preimage`：UniformSpace.closure_subset_preima
ge {U : SetRel α α} (hU : U in 𝓤 α) (s : Set α) : closure s subseteq U.preimage 
s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SetRel.preimage_subset_preimage`：∀ {α : Type u_1} {β : Type u_2} {R : Se
tRel α β} {t₁ t₂ : Set β}, t₁ ⊆ t₂ → R.preimage t₁ ⊆ R.preimage t₂
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `SetRel.preimage_subset_preimage_left`：∀ {α : Type u_1} {β : Type u_2} {R
₁ R₂ : SetRel α β} {t : Set β}, R₁ ⊆ R₂ → R₁.preimage t ⊆ R₂.preimage t
· 使用引理 `SetRel.preimage_comp`：preimage_comp : preimage (R ○ S) u = preimage R (p
reimage S u)
· 使用定理 `UniformSpace.closure_subset_image`：UniformSpace.closure_subset_image {U 
: SetRel α α} (hU : U in 𝓤 α) (s : Set α) : closure s subseteq U.image s
· 使用定理 `SetRel.image_subset_image`：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α
 β} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → R.image s₁ ⊆ R.image s₂
· 使用定理 `SetRel.image_subset_image_left`：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ :
 SetRel α β} {s : Set α}, R₁ ⊆ R₂ → R₁.image s ⊆ R₂.image s
· 使用引理 `SetRel.image_comp`：image_comp : image (R ○ S) s = image S (image R s)
-/
theorem uniformContinuous_closure : UniformContinuous (closure (X := α)) := by
  simp_rw [UniformContinuous, (𝓤 α).basis_sets.uniformity_hausdorff.tendsto_iff
    (𝓤 α).basis_sets.uniformity_hausdorff, Function.comp_id, mem_hausdorffEntourage]
  intro U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  refine ⟨V, hV, fun ⟨s, t⟩ ⟨hst, hts⟩ => ?_⟩
  simp only at *
  constructor
  · grw [closure_subset_preimage hV s, hst, ← subset_closure, ← hVU, SetRel.preimage_comp]
  · grw [closure_subset_image hV t, hts, ← subset_closure, ← hVU, SetRel.image_comp]

@[fun_prop]
/-
**UniformSpace.hausdorff.continuous_closure** 是 Mathlib 中的一个定理，位于命名空间 `UniformSp
ace.hausdorff`。
形式化陈述：continuous_closure : Continuous (closure (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformSpace.hausdorff.uniformContinuous_closure`：uniformContinuous_clos
ure : UniformContinuous (closure (X
-/
theorem continuous_closure : Continuous (closure (X := α)) :=
  uniformContinuous_closure.continuous
/-
**UniformSpace.hausdorff.isUniformInducing_closure** 是 Mathlib 中的一个定理，位于命名空间 `Un
iformSpace.hausdorff`。
形式化陈述：isUniformInducing_closure : IsUniformInducing (closure (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.HasBasis.uniformity_hausdorff`：Filter.HasBasis.uniformity_hausdor
ff {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) :
 (𝓤 (Set α)).HasBasis p (h…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SetRel.preimage_subset_preimage`：∀ {α : Type u_1} {β : Type u_2} {R : Se
tRel α β} {t₁ t₂ : Set β}, t₁ ⊆ t₂ → R.preimage t₁ ⊆ R.preimage t₂
· 使用定理 `UniformSpace.closure_subset_preimage`：UniformSpace.closure_subset_preima
ge {U : SetRel α α} (hU : U in 𝓤 α) (s : Set α) : closure s subseteq U.preimage 
s
· 使用定理 `SetRel.preimage_subset_preimage_left`：∀ {α : Type u_1} {β : Type u_2} {R
₁ R₂ : SetRel α β} {t : Set β}, R₁ ⊆ R₂ → R₁.preimage t ⊆ R₂.preimage t
· 使用引理 `SetRel.preimage_comp`：preimage_comp : preimage (R ○ S) u = preimage R (p
reimage S u)
· 使用定理 `SetRel.image_subset_image`：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α
 β} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → R.image s₁ ⊆ R.image s₂
· 使用定理 `UniformSpace.closure_subset_image`：UniformSpace.closure_subset_image {U 
: SetRel α α} (hU : U in 𝓤 α) (s : Set α) : closure s subseteq U.image s
· 使用定理 `SetRel.image_subset_image_left`：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ :
 SetRel α β} {s : Set α}, R₁ ⊆ R₂ → R₁.image s ⊆ R₂.image s
· 使用引理 `SetRel.image_comp`：image_comp : image (R ○ S) s = image S (image R s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `UniformSpace.hausdorff.uniformContinuous_closure`：uniformContinuous_clos
ure : UniformContinuous (closure (X
-/
theorem isUniformInducing_closure : IsUniformInducing (closure (X := α)) := by
  refine ⟨le_antisymm ?_ <| Filter.map_le_iff_le_comap.mp uniformContinuous_closure⟩
  rw [(𝓤 α).basis_sets.uniformity_hausdorff.comap _ |>.le_basis_iff
    (𝓤 α).basis_sets.uniformity_hausdorff, Function.comp_id]
  intro U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  refine ⟨V, hV, fun ⟨s, t⟩ ⟨hst, hts⟩ => ?_⟩
  simp only [mem_hausdorffEntourage] at *
  constructor
  · grw [subset_closure (s := s), hst, closure_subset_preimage hV t, ← hVU, SetRel.preimage_comp]
  · grw [subset_closure (s := t), hts, closure_subset_image hV s, ← hVU, SetRel.image_comp]
/-
**UniformSpace.hausdorff.nhds_closure** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.ha
usdorff`。
形式化陈述：nhds_closure (s : Set α) : 𝓝 (closure s) = 𝓝 s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `UniformSpace.hausdorff.isUniformInducing_closure`：isUniformInducing_clos
ure : IsUniformInducing (closure (X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_closure`：closure_closure : closure (closure s) = closure s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_closure (s : Set α) : 𝓝 (closure s) = 𝓝 s := by
  simp_rw +singlePass [isUniformInducing_closure.isInducing.nhds_eq_comap, closure_closure]
/-
**UniformSpace.hausdorff.isClosed_setOfPred_totallyBounded** 是 Mathlib 中的一个定理，位于
命名空间 `UniformSpace.hausdorff`。
形式化陈述：isClosed_setOfPred_totallyBounded : IsClosed {s : Set α | TotallyBounded s
}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.HasBasis.uniformity_hausdorff`：Filter.HasBasis.uniformity_hausdor
ff {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) :
 (𝓤 (Set α)).HasBasis p (h…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SetRel.preimage_subset_preimage`：∀ {α : Type u_1} {β : Type u_2} {R : Se
tRel α β} {t₁ t₂ : Set β}, t₁ ⊆ t₂ → R.preimage t₁ ⊆ R.preimage t₂
· 使用定理 `Set.iUnion_mono''`：iUnion_mono'' {s t : ι -> Set α} (h : forall i, s i s
ubseteq t i) : iUnion s subseteq iUnion t
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
-/
theorem isClosed_setOfPred_totallyBounded : IsClosed {s : Set α | TotallyBounded s} := by
  simp_rw [isClosed_iff_frequently, nhds_eq_comap_uniformity]
  intro s hs U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  rw [(𝓤 α).basis_sets.uniformity_hausdorff.comap _ |>.frequently_iff] at hs
  obtain ⟨t, ⟨hst : s ⊆ V.preimage t, -⟩, ht⟩ := hs V hV
  obtain ⟨u, hu, htu⟩ := ht V hV
  refine ⟨u, hu, ?_⟩
  grw [hst, htu, ← hVU]
  simp [Set.subset_def]
  grind

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_totallyBounded := isClosed_setOfPred_totallyBounded
/-
**UniformSpace.hausdorff.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.hausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteUniformity α] : DiscreteUniformity (Set α) := by
  rw [discreteUniformity_iff_setRelId_mem_uniformity]
  convert! Filter.mem_lift' (DiscreteUniformity.relId_mem_uniformity α)
  rw [hausdorffEntourage_id]

end UniformSpace.hausdorff

/-- When `Set` is equipped with the Hausdorff uniformity, taking the image under a uniformly
continuous map is uniformly continuous. -/
/-
**UniformContinuous.image_hausdorff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.image_hausdorff {f : α -> β} (hf : UniformContinuous f) 
: UniformContinuous (f '' ·)
参数：hf : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.tendsto_lift'`：tendsto_lift' {m : γ -> β} {l : Filter γ} : Tendst
o m l (f.lift' h) ↔ forall s in f, forallᶠ a in l, m a in h s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
When `Set` is equipped with the Hausdorff uniformity, taking the image under a u
niformly
continuous map is uniformly continuous.
-/
theorem UniformContinuous.image_hausdorff {f : α → β} (hf : UniformContinuous f) :
    UniformContinuous (f '' ·) := by
  refine Filter.tendsto_lift'.mpr fun U hU => ?_
  filter_upwards [Filter.mem_lift' (hf hU)] with ⟨s, t⟩ ⟨h₁, h₂⟩
  simp_rw [mem_hausdorffEntourage, Set.image_subset_iff]
  exact ⟨h₁.trans fun x ⟨y, hy, hxy⟩ => ⟨f y, Set.mem_image_of_mem f hy, hxy⟩,
    h₂.trans fun x ⟨y, hy, hxy⟩ => ⟨f y, Set.mem_image_of_mem f hy, hxy⟩⟩

/-- When `Set` is equipped with the Hausdorff uniformity, taking the image under a uniform
inducing map is uniform inducing. -/
/-
**IsUniformInducing.image_hausdorff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.image_hausdorff {f : α -> β} (hf : IsUniformInducing f) 
: IsUniformInducing (f '' ·)
参数：hf : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_lift'_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {h : Set α → Set β} {m : γ → β},   Filter.comap m (f.lift' h) = f.l
ift' (Set.p…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
· 使用定理 `Filter.comap_lift'_eq2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
f : Filter α} {m : β → α} {g : Set β → Set γ},   Monotone g → (Filter.comap m f)
.lift' g = f…
· 使用定理 `monotone_hausdorffEntourage`：monotone_hausdorffEntourage : Monotone (hau
sdorffEntourage (α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
When `Set` is equipped with the Hausdorff uniformity, taking the image under a u
niform
inducing map is uniform inducing.
-/
theorem IsUniformInducing.image_hausdorff {f : α → β} (hf : IsUniformInducing f) :
    IsUniformInducing (f '' ·) := by
  constructor
  change Filter.comap _ (Filter.lift' _ _) = Filter.lift' _ _
  rw [Filter.comap_lift'_eq, ← hf.comap_uniformity,
    Filter.comap_lift'_eq2 monotone_hausdorffEntourage]
  congr with U ⟨s, t⟩
  simp only [Function.comp, hausdorffEntourage, SetRel.preimage, SetRel.image, Set.preimage,
    Set.mem_ofPred, Set.image_subset_iff, Set.exists_mem_image]

/-- When `Set` is equipped with the Hausdorff uniformity, taking the image under a uniform
embedding is a uniform embedding. -/
/-
**IsUniformEmbedding.image_hausdorff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.image_hausdorff {f : α -> β} (hf : IsUniformEmbedding f
) : IsUniformEmbedding (f '' ·) where __
参数：hf : IsUniformEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.image_hausdorff`：IsUniformInducing.image_hausdorff {f 
: α -> β} (hf : IsUniformInducing f) : IsUniformInducing (f '' ·)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `IsUniformEmbedding.injective`：∀ {α : Type ua} {β : Type ub} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Func
tion.Injective f

--- 原说明 ---
When `Set` is equipped with the Hausdorff uniformity, taking the image under a u
niform
embedding is a uniform embedding.
-/
theorem IsUniformEmbedding.image_hausdorff {f : α → β} (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (f '' ·) where
  __ := hf.isUniformInducing.image_hausdorff
  injective := hf.injective.image_injective

/-- In the Hausdorff uniformity, the powerset of a totally bounded set is totally bounded. -/
/-
**TotallyBounded.powerset_hausdorff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TotallyBounded.powerset_hausdorff {t : Set α} (ht : TotallyBounded t) : To
tallyBounded t.powerset
参数：ht : TotallyBounded t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.totallyBounded_iff`：Filter.HasBasis.totallyBounded_iff {
ι} {p : ι -> Prop} {U : ι -> SetRel α α} (H : (𝓤 α).HasBasis p U) {s : Set α} : 
TotallyBounded s ↔ foral…
· 使用定理 `Filter.HasBasis.uniformity_hausdorff`：Filter.HasBasis.uniformity_hausdor
ff {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) :
 (𝓤 (Set α)).HasBasis p (h…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Finite.powerset`：∀ {α : Type u} {s : Set α}, s.Finite → (𝒫 s).Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j

--- 原说明 ---
In the Hausdorff uniformity, the powerset of a totally bounded set is totally bo
unded.
-/
theorem TotallyBounded.powerset_hausdorff {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded t.powerset := by
  simp_rw [(𝓤 α).basis_sets.uniformity_hausdorff.totallyBounded_iff, Function.comp_id,
    Set.powerset, Set.ofPred_subset, Set.mem_iUnion]
  intro (U : SetRel α α) hU
  obtain ⟨u, hu, ht⟩ := ht U hU
  refine ⟨u.powerset, hu.powerset, fun s hs => ⟨u ∩ U.image s, by grind, fun x hx => ?_,
    fun x ⟨_, hx⟩ => hx⟩⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (hs hx))
  exact ⟨y, ⟨hy, ⟨x, hx, hxy⟩⟩, hxy⟩

/-- The neighborhoods of a totally bounded set in the Hausdorff uniformity are neighborhoods in the
Vietoris topology. -/
/-
**TotallyBounded.nhds_vietoris_le_nhds_hausdorff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TotallyBounded.nhds_vietoris_le_nhds_hausdorff {s : Set α} (hs : TotallyBo
unded s) : @nhds _ (.vietoris α) s <= 𝓝 s
参数：hs : TotallyBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.HasBasis.uniformity_hausdorff`：Filter.HasBasis.uniformity_hausdor
ff {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) :
 (𝓤 (Set α)).HasBasis p (h…
· 使用定理 `uniformity_hasBasis_open`：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun
 V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `comp_open_symm_mem_uniformity_sets`：comp_open_symm_mem_uniformity_sets {
s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, IsOpen t ∧ SetRel.IsSymm t ∧ 
t ○ t subseteq s
· 使用定理 `TotallyBounded.exists_prodMk_finset_mem_hausdorffEntourage`：TotallyBound
ed.exists_prodMk_finset_mem_hausdorffEntourage [UniformSpace α] {s : Set α} (hs 
: TotallyBounded s) {U : SetRel α α} (hU : U in …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all_finset`：∀ {α : Type u} {ι : Type u_2} (I : Finset 
ι) {l : Filter α} {p : ι → α → Prop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i 
∈ I, ∀ᶠ (x : α) in…
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `TopologicalSpace.vietoris.isOpen_inter_nonempty_of_isOpen`：isOpen_inter_
nonempty_of_isOpen {U : Set α} (h : IsOpen U) : IsOpen {s | (s inter U).Nonempty
}
· 使用引理 `UniformSpace.isOpen_ball`：isOpen_ball (x : α) {V : SetRel α α} (hV : IsO
pen V) : IsOpen (ball x V)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SetRel.preimage_eq_image`：preimage_eq_image [R.IsSymm] : R.preimage s = 
R.image s
· 使用定理 `SetRel.preimage_subset_preimage`：∀ {α : Type u_1} {β : Type u_2} {R : Se
tRel α β} {t₁ t₂ : Set β}, t₁ ⊆ t₂ → R.preimage t₁ ⊆ R.preimage t₂
· 使用定理 `SetRel.preimage_subset_preimage_left`：∀ {α : Type u_1} {β : Type u_2} {R
₁ R₂ : SetRel α β} {t : Set β}, R₁ ⊆ R₂ → R₁.preimage t ⊆ R₂.preimage t
· 使用引理 `SetRel.preimage_comp`：preimage_comp : preimage (R ○ S) u = preimage R (p
reimage S u)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.powerset_vietoris`：∀ {α : Type u_1} [inst : TopologicalSpace α] {
U : Set α}, IsOpen U → IsOpen (𝒫 U)
· 使用引理 `IsOpen.relImage`：IsOpen.relImage [TopologicalSpace α] [TopologicalSpace 
β] {s : SetRel α β} (hs : IsOpen s) {t : Set α} : IsOpen (s.image t)
· 使用引理 `SetRel.self_subset_image`：self_subset_image [R.IsRefl] (s : Set α) : s s
ubseteq R.image s

--- 原说明 ---
The neighborhoods of a totally bounded set in the Hausdorff uniformity are neigh
borhoods in the
Vietoris topology.
-/
theorem TotallyBounded.nhds_vietoris_le_nhds_hausdorff {s : Set α} (hs : TotallyBounded s) :
    @nhds _ (.vietoris α) s ≤ 𝓝 s := by
  open UniformSpace TopologicalSpace.vietoris in
  simp_rw [nhds_eq_comap_uniformity,
    uniformity_hasBasis_open.uniformity_hausdorff |>.comap _ |>.ge_iff, Function.comp_id,
    hausdorffEntourage, Set.preimage_ofPred_eq, Set.ofPred_and]
  intro U ⟨hU₁, hU₂⟩
  have : U.IsRefl := ⟨fun _ => refl_mem_uniformity hU₁⟩
  let := TopologicalSpace.vietoris α
  refine Filter.inter_mem ?_ <| hU₂.relImage.powerset_vietoris.mem_nhds <|
    SetRel.self_subset_image _
  obtain ⟨V : SetRel α α, hV₁, hV₂, _, hVU⟩ := comp_open_symm_mem_uniformity_sets hU₁
  obtain ⟨t, ht₁, ht₂⟩ := hs.exists_prodMk_finset_mem_hausdorffEntourage hV₁
  dsimp only at ht₁ ht₂
  filter_upwards [(Filter.eventually_all_finset t).mpr fun x hx =>
    isOpen_inter_nonempty_of_isOpen (isOpen_ball x hV₂) |>.eventually_mem (ht₁ hx)]
    with u (hu : ↑t ⊆ V.preimage ↑u)
  grw [ht₂, ← SetRel.preimage_eq_image, hu, ← hVU, SetRel.preimage_comp]

/-- A compact set has the same neighborhoods in the Hausdorff uniformity and the Vietoris topology.
-/
/-
**IsCompact.nhds_hausdorff_eq_nhds_vietoris** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nhds_hausdorff_eq_nhds_vietoris {s : Set α} (hs : IsCompact s) :
 𝓝 s = @nhds _ (.vietoris α) s
参数：hs : IsCompact s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.nhds_generateFrom`：nhds_generateFrom {g : Set (Set α)} 
{a : α} : @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `IsCompact.nhdsSet_basis_uniformity`：IsCompact.nhdsSet_basis_uniformity {
p : ι -> Prop} {V : ι -> Set (α × α)} (hbasis : (𝓤 α).HasBasis p V) (hK : IsComp
act K) : (𝓝ˢ K).HasBasis…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen`：isOpen_inter_non
empty_of_isOpen {U : Set α} (hU : IsOpen U) : IsOpen {s | (s inter U).Nonempty}
· 使用定理 `TotallyBounded.nhds_vietoris_le_nhds_hausdorff`：TotallyBounded.nhds_viet
oris_le_nhds_hausdorff {s : Set α} (hs : TotallyBounded s) : @nhds _ (.vietoris 
α) s <= 𝓝 s
· 使用定理 `IsCompact.totallyBounded`：∀ {α : Type u} [uniformSpace : UniformSpace α]
 {s : Set α}, IsCompact s → TotallyBounded s

--- 原说明 ---
A compact set has the same neighborhoods in the Hausdorff uniformity and the Vie
toris topology.
-/
theorem IsCompact.nhds_hausdorff_eq_nhds_vietoris {s : Set α} (hs : IsCompact s) :
    𝓝 s = @nhds _ (.vietoris α) s := by
  refine le_antisymm ?_ hs.totallyBounded.nhds_vietoris_le_nhds_hausdorff
  simp_rw [TopologicalSpace.nhds_generateFrom, le_iInf₂_iff, Filter.le_principal_iff]
  rintro _ ⟨hs', (⟨U, hU, rfl⟩ | ⟨U, hU, rfl⟩)⟩
  · obtain ⟨V : SetRel α α, hV₁, hV₂⟩ :=
      hs.nhdsSet_basis_uniformity (𝓤 α).basis_sets |>.mem_iff.mp (hU.mem_nhdsSet.mpr hs')
    filter_upwards [UniformSpace.ball_mem_nhds _ (Filter.mem_lift' hV₁)]
      with t ⟨_, ht⟩
    exact ht.trans fun x ⟨y, hy, hxy⟩ => hV₂ <| Set.mem_biUnion hy hxy
  · exact (UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen hU).mem_nhds hs'

namespace UniformSpace.hausdorff

/-
**UniformSpace.hausdorff.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.hausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] : CompactSpace (Set α) where
  isCompact_univ := by
    rw [isCompact_iff_ultrafilter_le_nhds]
    rintro f -
    let := TopologicalSpace.vietoris α
    -- `f.lim` is the limit of `f` in the Vietoris topology
    refine ⟨closure f.lim, Set.mem_univ _, ?_⟩
    grw [isClosed_closure.isCompact.nhds_hausdorff_eq_nhds_vietoris,
      ← TopologicalSpace.vietoris.specializes_closure.nhds_le_nhds, f.le_nhds_lim]

end UniformSpace.hausdorff

namespace TopologicalSpace.Closeds

/-
**TopologicalSpace.Closeds.uniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSp
ace.Closeds`。
形式化陈述：uniformSpace : UniformSpace (Closeds α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniformSpace : UniformSpace (Closeds α) :=
  .comap (↑) (.hausdorff α)
/-
**TopologicalSpace.Closeds.uniformity_def** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Closeds`。
形式化陈述：uniformity_def : 𝓤 (Closeds α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' ha
usdorffEntourage)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_def :
    𝓤 (Closeds α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' hausdorffEntourage) :=
  rfl
/-
**TopologicalSpace.Closeds._root_.Filter.HasBasis.uniformity_closeds** 是 Mathlib
 中的一个定理，位于命名空间 `TopologicalSpace.Closeds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.HasBasis.uniformity_closeds
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (Closeds α)).HasBasis p (fun i => Prod.map (↑) (↑) ⁻¹' (hausdorffEntourage (s i))) :=
  h.uniformity_hausdorff.comap _
/-
**TopologicalSpace.Closeds.isUniformEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.Closeds`。
形式化陈述：isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Closeds α -> Set α) whe
re injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Closeds α → Set α) where
  injective := SetLike.coe_injective
  comap_uniformity := rfl
/-
**TopologicalSpace.Closeds.uniformContinuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace.Closeds`。
形式化陈述：uniformContinuous_coe : UniformContinuous ((↑) : Closeds α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.Closeds.isUniformEmbedding_coe`：isUniformEmbedding_coe 
: IsUniformEmbedding ((↑) : Closeds α -> Set α) where injective
-/
theorem uniformContinuous_coe : UniformContinuous ((↑) : Closeds α → Set α) :=
  isUniformEmbedding_coe.uniformContinuous
/-
**TopologicalSpace.Closeds.isOpen_inter_nonempty_of_isOpen** 是 Mathlib 中的一个定理，位于
命名空间 `TopologicalSpace.Closeds`。
形式化陈述：isOpen_inter_nonempty_of_isOpen {s : Set α} (hs : IsOpen s) : IsOpen {t : 
Closeds α | ((t : Set α) inter s).Nonempty}
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_induced`：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induc
ed f t] (f ⁻¹' s)
· 使用定理 `UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen`：isOpen_inter_non
empty_of_isOpen {U : Set α} (hU : IsOpen U) : IsOpen {s | (s inter U).Nonempty}
-/
theorem isOpen_inter_nonempty_of_isOpen {s : Set α} (hs : IsOpen s) :
    IsOpen {t : Closeds α | ((t : Set α) ∩ s).Nonempty} :=
  isOpen_induced (UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen hs)
/-
**TopologicalSpace.Closeds.isClosed_subsets_of_isClosed** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.Closeds`。
形式化陈述：isClosed_subsets_of_isClosed {s : Set α} (hs : IsClosed s) : IsClosed {t :
 Closeds α | (t : Set α) subseteq s}
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_induced`：isClosed_induced {s : Set β} (h : IsClosed s) : IsClos
ed[induced f t] (f ⁻¹' s)
· 使用定理 `IsClosed.powerset_hausdorff`：∀ {α : Type u_1} [inst : UniformSpace α] {F
 : Set α}, IsClosed F → IsClosed (𝒫 F)
-/
theorem isClosed_subsets_of_isClosed {s : Set α} (hs : IsClosed s) :
    IsClosed {t : Closeds α | (t : Set α) ⊆ s} :=
  isClosed_induced hs.powerset_hausdorff
/-
**TopologicalSpace.Closeds.isClopen_singleton_bot** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.Closeds`。
形式化陈述：isClopen_singleton_bot : IsClopen {(⊥ : Closeds α)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClopen.preimage`：IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X
 -> Y} (hf : Continuous f) : IsClopen (f ⁻¹' s)
· 使用定理 `UniformSpace.hausdorff.isClopen_singleton_empty`：isClopen_singleton_empt
y : IsClopen {(∅ : Set α)}
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `TopologicalSpace.Closeds.uniformContinuous_coe`：uniformContinuous_coe : 
UniformContinuous ((↑) : Closeds α -> Set α)
-/
theorem isClopen_singleton_bot : IsClopen {(⊥ : Closeds α)} := by
  convert! UniformSpace.hausdorff.isClopen_singleton_empty.preimage uniformContinuous_coe.continuous
  ext; simp
/-
**TopologicalSpace.Closeds.totallyBounded_subsets_of_totallyBounded** 是 Mathlib 
中的一个定理，位于命名空间 `TopologicalSpace.Closeds`。
形式化陈述：totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded 
t) : TotallyBounded {F : Closeds α | ↑F subseteq t}
参数：ht : TotallyBounded t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `totallyBounded_preimage`：totallyBounded_preimage {f : α -> β} {s : Set β
} (hf : IsUniformInducing f) (hs : TotallyBounded s) : TotallyBounded (f ⁻¹' s)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `TopologicalSpace.Closeds.isUniformEmbedding_coe`：isUniformEmbedding_coe 
: IsUniformEmbedding ((↑) : Closeds α -> Set α) where injective
· 使用定理 `TotallyBounded.powerset_hausdorff`：TotallyBounded.powerset_hausdorff {t 
: Set α} (ht : TotallyBounded t) : TotallyBounded t.powerset
-/
theorem totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded {F : Closeds α | ↑F ⊆ t} :=
  totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff
/-
**TopologicalSpace.Closeds.isClosed_setOfPred_totallyBounded** 是 Mathlib 中的一个定理，
位于命名空间 `TopologicalSpace.Closeds`。
形式化陈述：isClosed_setOfPred_totallyBounded : IsClosed {s : Closeds α | TotallyBound
ed (s : Set α)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `TopologicalSpace.Closeds.uniformContinuous_coe`：uniformContinuous_coe : 
UniformContinuous ((↑) : Closeds α -> Set α)
· 使用定理 `UniformSpace.hausdorff.isClosed_setOfPred_totallyBounded`：isClosed_setOf
Pred_totallyBounded : IsClosed {s : Set α | TotallyBounded s}
-/
theorem isClosed_setOfPred_totallyBounded : IsClosed {s : Closeds α | TotallyBounded (s : Set α)} :=
  UniformSpace.hausdorff.isClosed_setOfPred_totallyBounded.preimage uniformContinuous_coe.continuous

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_totallyBounded := isClosed_setOfPred_totallyBounded
/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteUniformity α] : DiscreteUniformity (Closeds α) :=
  isUniformEmbedding_coe.discreteUniformity

section T0Space

variable [T0Space α]

/-
**TopologicalSpace.Closeds.isUniformEmbedding_singleton** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.Closeds`。
形式化陈述：isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α -> Closeds α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `IsUniformEmbedding.of_comp_iff`：IsUniformEmbedding.of_comp_iff {g : β ->
 γ} (hg : IsUniformEmbedding g) {f : α -> β} : IsUniformEmbedding (g ∘ f) ↔ IsUn
iformEmbedding f
· 使用定理 `TopologicalSpace.Closeds.isUniformEmbedding_coe`：isUniformEmbedding_coe 
: IsUniformEmbedding ((↑) : Closeds α -> Set α) where injective
· 使用定理 `UniformSpace.hausdorff.isUniformEmbedding_singleton`：isUniformEmbedding_
singleton : IsUniformEmbedding ({·} : α -> Set α) where injective
-/
theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α → Closeds α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton
/-
**TopologicalSpace.Closeds.uniformContinuous_singleton** 是 Mathlib 中的一个定理，位于命名空间
 `TopologicalSpace.Closeds`。
形式化陈述：uniformContinuous_singleton : UniformContinuous ({·} : α -> Closeds α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.Closeds.isUniformEmbedding_singleton`：isUniformEmbeddin
g_singleton : IsUniformEmbedding ({·} : α -> Closeds α)
-/
theorem uniformContinuous_singleton : UniformContinuous ({·} : α → Closeds α) :=
  isUniformEmbedding_singleton.uniformContinuous

@[fun_prop]
/-
**TopologicalSpace.Closeds.isEmbedding_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace.Closeds`。
形式化陈述：isEmbedding_singleton : IsEmbedding ({·} : α -> Closeds α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `TopologicalSpace.Closeds.isUniformEmbedding_singleton`：isUniformEmbeddin
g_singleton : IsUniformEmbedding ({·} : α -> Closeds α)
-/
theorem isEmbedding_singleton : IsEmbedding ({·} : α → Closeds α) :=
  isUniformEmbedding_singleton.isEmbedding

@[fun_prop]
/-
**TopologicalSpace.Closeds.continuous_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.Closeds`。
形式化陈述：continuous_singleton : Continuous ({·} : α -> Closeds α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `TopologicalSpace.Closeds.isEmbedding_singleton`：isEmbedding_singleton : 
IsEmbedding ({·} : α -> Closeds α)
-/
theorem continuous_singleton : Continuous ({·} : α → Closeds α) :=
  isEmbedding_singleton.continuous

@[fun_prop]
/-
**TopologicalSpace.Closeds.isClosedEmbedding_singleton** 是 Mathlib 中的一个定理，位于命名空间
 `TopologicalSpace.Closeds`。
形式化陈述：isClosedEmbedding_singleton : Topology.IsClosedEmbedding ({·} : α -> Close
ds α) where __
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `TopologicalSpace.Closeds.isUniformEmbedding_singleton`：isUniformEmbeddin
g_singleton : IsUniformEmbedding ({·} : α -> Closeds α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `TopologicalSpace.Closeds.uniformContinuous_coe`：uniformContinuous_coe : 
UniformContinuous ((↑) : Closeds α -> Set α)
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `UniformSpace.hausdorff.isClosedEmbedding_singleton`：isClosedEmbedding_si
ngleton [T0Space α] : Topology.IsClosedEmbedding ({·} : α -> Set α) where __
-/
theorem isClosedEmbedding_singleton : Topology.IsClosedEmbedding ({·} : α → Closeds α) where
  __ := isUniformEmbedding_singleton.isEmbedding
  isClosed_range := by
    rw [← SetLike.coe_injective.preimage_image (s := Set.range ({·})), ← Set.range_comp]
    exact UniformSpace.hausdorff.isClosedEmbedding_singleton.isClosed_range.preimage
      uniformContinuous_coe.continuous

@[simp]
/-
**TopologicalSpace.Closeds.discreteUniformity_iff** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.Closeds`。
形式化陈述：discreteUniformity_iff : DiscreteUniformity (Closeds α) ↔ DiscreteUniformi
ty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.discreteUniformity`：IsUniformEmbedding.discreteUnifor
mity [DiscreteUniformity β] {f : α -> β} (hf : IsUniformEmbedding f) : DiscreteU
niformity α
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `TopologicalSpace.Closeds.isUniformEmbedding_singleton`：isUniformEmbeddin
g_singleton : IsUniformEmbedding ({·} : α -> Closeds α)
· 使用定理 `TopologicalSpace.Closeds.instDiscreteUniformity`：∀ {α : Type u_1} [inst 
: UniformSpace α] [DiscreteUniformity α], DiscreteUniformity (TopologicalSpace.C
loseds α)
-/
theorem discreteUniformity_iff : DiscreteUniformity (Closeds α) ↔ DiscreteUniformity α :=
  ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

end T0Space

/-
**TopologicalSpace.Closeds.uniformContinuous_sup** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace.Closeds`。
形式化陈述：uniformContinuous_sup : UniformContinuous (fun x : Closeds α × Closeds α =
> x.1 ⊔ x.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.Closeds.isUniformEmbedding_coe`：isUniformEmbedding_coe 
: IsUniformEmbedding ((↑) : Closeds α -> Set α) where injective
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformSpace.hausdorff.uniformContinuous_union`：uniformContinuous_union 
: UniformContinuous (fun x : Set α × Set α => x.1 union x.2)
· 使用定理 `UniformContinuous.prodMap`：UniformContinuous.prodMap [UniformSpace δ] {f
 : α -> γ} {g : β -> δ} (hf : UniformContinuous f) (hg : UniformContinuous g) : 
UniformContinuo…
· 使用定理 `TopologicalSpace.Closeds.uniformContinuous_coe`：uniformContinuous_coe : 
UniformContinuous ((↑) : Closeds α -> Set α)
-/
theorem uniformContinuous_sup : UniformContinuous (fun x : Closeds α × Closeds α => x.1 ⊔ x.2) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <|
    UniformSpace.hausdorff.uniformContinuous_union.comp <|
      uniformContinuous_coe.prodMap uniformContinuous_coe
/-
**TopologicalSpace.Closeds._root_.UniformContinuous.sup_closeds** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.Closeds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.UniformContinuous.sup_closeds
    {f g : α → Closeds β} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ⊔ g x) :=
  uniformContinuous_sup.comp <| hf.prodMk hg
/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousSup (Closeds α) :=
  ⟨uniformContinuous_sup.continuous⟩
/-
**TopologicalSpace.Closeds.uniformContinuous_prod** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.Closeds`。
形式化陈述：uniformContinuous_prod : UniformContinuous (fun x : Closeds α × Closeds β 
=> x.1 ×ˢ x.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.Closeds.isUniformEmbedding_coe`：isUniformEmbedding_coe 
: IsUniformEmbedding ((↑) : Closeds α -> Set α) where injective
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformSpace.hausdorff.uniformContinuous_prod`：uniformContinuous_prod : 
UniformContinuous (fun x : Set α × Set β => x.1 ×ˢ x.2)
· 使用定理 `UniformContinuous.prodMap`：UniformContinuous.prodMap [UniformSpace δ] {f
 : α -> γ} {g : β -> δ} (hf : UniformContinuous f) (hg : UniformContinuous g) : 
UniformContinuo…
· 使用定理 `TopologicalSpace.Closeds.uniformContinuous_coe`：uniformContinuous_coe : 
UniformContinuous ((↑) : Closeds α -> Set α)
-/
theorem uniformContinuous_prod : UniformContinuous (fun x : Closeds α × Closeds β => x.1 ×ˢ x.2) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <|
    UniformSpace.hausdorff.uniformContinuous_prod.comp <|
      uniformContinuous_coe.prodMap uniformContinuous_coe
/-
**TopologicalSpace.Closeds._root_.UniformContinuous.prod_closeds** 是 Mathlib 中的一
个定理，位于命名空间 `TopologicalSpace.Closeds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.UniformContinuous.prod_closeds {f : α → Closeds β} {g : α → Closeds γ}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ×ˢ g x) :=
  uniformContinuous_prod.comp (hf.prodMk hg)

@[fun_prop]
/-
**TopologicalSpace.Closeds.continuous_prod** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.Closeds`。
形式化陈述：continuous_prod : Continuous (fun x : Closeds α × Closeds β => x.1 ×ˢ x.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `TopologicalSpace.Closeds.uniformContinuous_prod`：uniformContinuous_prod 
: UniformContinuous (fun x : Closeds α × Closeds β => x.1 ×ˢ x.2)
-/
theorem continuous_prod : Continuous (fun x : Closeds α × Closeds β => x.1 ×ˢ x.2) :=
  uniformContinuous_prod.continuous
/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T0Space (Closeds α) := by
  suffices ∀ F₁ F₂ : Closeds α, Inseparable F₁ F₂ → F₁ ≤ F₂ from
    ⟨fun F₁ F₂ h => le_antisymm (this F₁ F₂ h) (this F₂ F₁ h.symm)⟩
  refine fun F₁ F₂ h x hx₁ => isClosed_iff_frequently.mp F₂.isClosed _ ?_
  rw [nhds_eq_comap_uniformity, Filter.frequently_comap, Filter.frequently_iff]
  intro (U : SetRel α α) hU
  obtain ⟨h : (F₁ : Set α) ⊆ U.preimage F₂, -⟩ :=
    mem_of_mem_nhds <| h.nhds_le_uniformity <| Filter.preimage_mem_comap <| Filter.mem_lift' hU
  obtain ⟨y, hy, hxy⟩ := h hx₁
  exact ⟨(x, y), hxy, y, rfl, hy⟩
/-
**TopologicalSpace.Closeds.isUniformInducing_closure** 是 Mathlib 中的一个定理，位于命名空间 `
TopologicalSpace.Closeds`。
形式化陈述：isUniformInducing_closure : IsUniformInducing (Closeds.closure (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUniformInducing.of_comp_iff`：IsUniformInducing.of_comp_iff {g : β -> γ
} (hg : IsUniformInducing g) {f : α -> β} : IsUniformInducing (g ∘ f) ↔ IsUnifor
mInducing f
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `TopologicalSpace.Closeds.isUniformEmbedding_coe`：isUniformEmbedding_coe 
: IsUniformEmbedding ((↑) : Closeds α -> Set α) where injective
· 使用定理 `UniformSpace.hausdorff.isUniformInducing_closure`：isUniformInducing_clos
ure : IsUniformInducing (closure (X
-/
theorem isUniformInducing_closure : IsUniformInducing (Closeds.closure (α := α)) :=
  isUniformEmbedding_coe.isUniformInducing.of_comp_iff.mp
    UniformSpace.hausdorff.isUniformInducing_closure
/-
**TopologicalSpace.Closeds.uniformContinuous_closure** 是 Mathlib 中的一个定理，位于命名空间 `
TopologicalSpace.Closeds`。
形式化陈述：uniformContinuous_closure : UniformContinuous (Closeds.closure (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `TopologicalSpace.Closeds.isUniformInducing_closure`：isUniformInducing_cl
osure : IsUniformInducing (Closeds.closure (α
-/
theorem uniformContinuous_closure : UniformContinuous (Closeds.closure (α := α)) :=
  isUniformInducing_closure.uniformContinuous

@[fun_prop]
/-
**TopologicalSpace.Closeds.continuous_closure** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace.Closeds`。
形式化陈述：continuous_closure : Continuous (Closeds.closure (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `TopologicalSpace.Closeds.uniformContinuous_closure`：uniformContinuous_cl
osure : UniformContinuous (Closeds.closure (α
-/
theorem continuous_closure : Continuous (Closeds.closure (α := α)) :=
  uniformContinuous_closure.continuous
/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] : CompactSpace (Closeds α) where
  isCompact_univ := by simpa [gi.l_surjective.range_eq]
    using isCompact_univ.image continuous_closure

@[simp]
/-
**TopologicalSpace.Closeds.compactSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.Closeds`。
形式化陈述：compactSpace_iff : CompactSpace (Closeds α) ↔ CompactSpace α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compactSpace_of_finite_subfamily_closed`：compactSpace_of_finite_subfamil
y_closed (h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -
> ⋂ i, t i = ∅ -> exists u : …
· 使用定理 `IsCompact.elim_finite_subfamily_closed`：IsCompact.elim_finite_subfamily_
closed {ι : Type v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClose
d (t i)) (hst : (s inter ⋂ i…
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `IsClopen.isClosed`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X
}, IsClopen s → IsClosed s
· 使用定理 `IsClopen.compl`：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
· 使用定理 `TopologicalSpace.Closeds.isClopen_singleton_bot`：isClopen_singleton_bot 
: IsClopen {(⊥ : Closeds α)}
· 使用定理 `TopologicalSpace.Closeds.isClosed_subsets_of_isClosed`：isClosed_subsets_
of_isClosed {s : Set α} (hs : IsClosed s) : IsClosed {t : Closeds α | (t : Set α
) subseteq s}
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `TopologicalSpace.Closeds.instCompactSpace`：∀ {α : Type u_1} [inst : Unif
ormSpace α] [CompactSpace α], CompactSpace (TopologicalSpace.Closeds α)
-/
theorem compactSpace_iff : CompactSpace (Closeds α) ↔ CompactSpace α := by
  refine ⟨fun _ => compactSpace_of_finite_subfamily_closed fun {ι} F hF₁ hF₂ => ?_,
    fun _ => inferInstance⟩
  have := isClopen_singleton_bot.compl.isClosed.isCompact.elim_finite_subfamily_closed
    (fun i => {C : Closeds α | ↑C ⊆ F i})
    (fun i => isClosed_subsets_of_isClosed (hF₁ i))
  simp_rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_compl_left_iff_subset,
    ← Set.ofPred_forall, ← Set.subset_iInter_iff, hF₂, Set.subset_empty_iff, coe_eq_empty,
    Set.ofPred_eq_eq_singleton] at this
  obtain ⟨s, hs⟩ := this .rfl
  specialize @hs ⟨⋂ i ∈ s, F i, isClosed_biInter fun i _ => hF₁ i⟩ .rfl
  exact ⟨s, congr($hs)⟩

@[simp]
/-
**TopologicalSpace.Closeds.noncompactSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gicalSpace.Closeds`。
形式化陈述：noncompactSpace_iff : NoncompactSpace (Closeds α) ↔ NoncompactSpace α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem noncompactSpace_iff : NoncompactSpace (Closeds α) ↔ NoncompactSpace α := by
  simp_rw [← not_compactSpace_iff, compactSpace_iff]
/-
**TopologicalSpace.Closeds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Closeds`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoncompactSpace α] : NoncompactSpace (Closeds α) :=
  noncompactSpace_iff.mpr ‹_›

end TopologicalSpace.Closeds

namespace TopologicalSpace.Compacts

/-
**TopologicalSpace.Compacts.uniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalS
pace.Compacts`。
形式化陈述：uniformSpace : UniformSpace (Compacts α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniformSpace : UniformSpace (Compacts α) :=
  .replaceTopology (.comap (↑) (.hausdorff α)) <| ext_nhds fun K ↦ by
    simp_rw [nhds_induced, K.isCompact.nhds_hausdorff_eq_nhds_vietoris]
/-
**TopologicalSpace.Compacts.uniformity_def** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.Compacts`。
形式化陈述：uniformity_def : 𝓤 (Compacts α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' h
ausdorffEntourage)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_def :
    𝓤 (Compacts α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' hausdorffEntourage) :=
  rfl
/-
**TopologicalSpace.Compacts._root_.Filter.HasBasis.uniformity_compacts** 是 Mathl
ib 中的一个定理，位于命名空间 `TopologicalSpace.Compacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.HasBasis.uniformity_compacts
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (Compacts α)).HasBasis p (fun i => Prod.map (↑) (↑) ⁻¹' (hausdorffEntourage (s i))) :=
  h.uniformity_hausdorff.comap _
/-
**TopologicalSpace.Compacts.isUniformEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.Compacts`。
形式化陈述：isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Compacts α -> Set α) wh
ere injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Compacts α → Set α) where
  injective := SetLike.coe_injective
  comap_uniformity := rfl
/-
**TopologicalSpace.Compacts.uniformContinuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.Compacts`。
形式化陈述：uniformContinuous_coe : UniformContinuous ((↑) : Compacts α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.Compacts.isUniformEmbedding_coe`：isUniformEmbedding_coe
 : IsUniformEmbedding ((↑) : Compacts α -> Set α) where injective
-/
theorem uniformContinuous_coe : UniformContinuous ((↑) : Compacts α → Set α) :=
  isUniformEmbedding_coe.uniformContinuous
/-
**TopologicalSpace.Compacts.isUniformEmbedding_toCloseds** 是 Mathlib 中的一个定理，位于命名
空间 `TopologicalSpace.Compacts`。
形式化陈述：isUniformEmbedding_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (
α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `TopologicalSpace.Compacts.toCloseds_injective`：toCloseds_injective [T2Sp
ace α] : Function.Injective (toCloseds (α
-/
theorem isUniformEmbedding_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (α := α)) where
  injective := toCloseds_injective
  comap_uniformity := Filter.comap_comap
/-
**TopologicalSpace.Compacts.uniformContinuous_toCloseds** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.Compacts`。
形式化陈述：uniformContinuous_toCloseds [T2Space α] : UniformContinuous (toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.Compacts.isUniformEmbedding_toCloseds`：isUniformEmbeddi
ng_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (α
-/
theorem uniformContinuous_toCloseds [T2Space α] : UniformContinuous (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.uniformContinuous

@[fun_prop]
/-
**TopologicalSpace.Compacts.isEmbedding_toCloseds** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.Compacts`。
形式化陈述：isEmbedding_toCloseds [T2Space α] : IsEmbedding (toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `TopologicalSpace.Compacts.isUniformEmbedding_toCloseds`：isUniformEmbeddi
ng_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (α
-/
theorem isEmbedding_toCloseds [T2Space α] : IsEmbedding (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.isEmbedding

@[fun_prop]
/-
**TopologicalSpace.Compacts.continuous_toCloseds** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace.Compacts`。
形式化陈述：continuous_toCloseds [T2Space α] : Continuous (toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `TopologicalSpace.Compacts.uniformContinuous_toCloseds`：uniformContinuous
_toCloseds [T2Space α] : UniformContinuous (toCloseds (α
-/
theorem continuous_toCloseds [T2Space α] : Continuous (toCloseds (α := α)) :=
  uniformContinuous_toCloseds.continuous

@[fun_prop]
/-
**TopologicalSpace.Compacts.isClosedEmbedding_toCloseds** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.Compacts`。
形式化陈述：isClosedEmbedding_toCloseds [T2Space α] [CompleteSpace α] : IsClosedEmbedd
ing (toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Compacts.isEmbedding_toCloseds`：isEmbedding_toCloseds [
T2Space α] : IsEmbedding (toCloseds (α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `IsCompact.totallyBounded`：∀ {α : Type u} [uniformSpace : UniformSpace α]
 {s : Set α}, IsCompact s → TotallyBounded s
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `TotallyBounded.isCompact_of_isClosed`：TotallyBounded.isCompact_of_isClos
ed [CompleteSpace α] {s : Set α} (ht : TotallyBounded s) (hc : IsClosed s) : IsC
ompact s
· 使用定理 `TopologicalSpace.Closeds.isClosed`：isClosed (s : Closeds α) : IsClosed (
s : Set α)
· 使用定理 `TopologicalSpace.Closeds.isClosed_setOfPred_totallyBounded`：isClosed_set
OfPred_totallyBounded : IsClosed {s : Closeds α | TotallyBounded (s : Set α)}
-/
theorem isClosedEmbedding_toCloseds [T2Space α] [CompleteSpace α] :
    IsClosedEmbedding (toCloseds (α := α)) where
  __ := isEmbedding_toCloseds
  isClosed_range := by
    convert! Closeds.isClosed_setOfPred_totallyBounded
    exact subset_antisymm
      (Set.range_subset_iff.mpr fun K => K.isCompact.totallyBounded)
      (fun K hK => ⟨⟨K, hK.isCompact_of_isClosed K.isClosed⟩, rfl⟩)
/-
**TopologicalSpace.Compacts.totallyBounded_subsets_of_totallyBounded** 是 Mathlib
 中的一个定理，位于命名空间 `TopologicalSpace.Compacts`。
形式化陈述：totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded 
t) : TotallyBounded {K : Compacts α | ↑K subseteq t}
参数：ht : TotallyBounded t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `totallyBounded_preimage`：totallyBounded_preimage {f : α -> β} {s : Set β
} (hf : IsUniformInducing f) (hs : TotallyBounded s) : TotallyBounded (f ⁻¹' s)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `TopologicalSpace.Compacts.isUniformEmbedding_coe`：isUniformEmbedding_coe
 : IsUniformEmbedding ((↑) : Compacts α -> Set α) where injective
· 使用定理 `TotallyBounded.powerset_hausdorff`：TotallyBounded.powerset_hausdorff {t 
: Set α} (ht : TotallyBounded t) : TotallyBounded t.powerset
-/
theorem totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded {K : Compacts α | ↑K ⊆ t} :=
  totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff
/-
**TopologicalSpace.Compacts.isUniformEmbedding_singleton** 是 Mathlib 中的一个定理，位于命名
空间 `TopologicalSpace.Compacts`。
形式化陈述：isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α -> Compacts α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUniformEmbedding.of_comp_iff`：IsUniformEmbedding.of_comp_iff {g : β ->
 γ} (hg : IsUniformEmbedding g) {f : α -> β} : IsUniformEmbedding (g ∘ f) ↔ IsUn
iformEmbedding f
· 使用定理 `TopologicalSpace.Compacts.isUniformEmbedding_coe`：isUniformEmbedding_coe
 : IsUniformEmbedding ((↑) : Compacts α -> Set α) where injective
· 使用定理 `UniformSpace.hausdorff.isUniformEmbedding_singleton`：isUniformEmbedding_
singleton : IsUniformEmbedding ({·} : α -> Set α) where injective
-/
theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α → Compacts α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton
/-
**TopologicalSpace.Compacts.uniformContinuous_singleton** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.Compacts`。
形式化陈述：uniformContinuous_singleton : UniformContinuous ({·} : α -> Compacts α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.Compacts.isUniformEmbedding_singleton`：isUniformEmbeddi
ng_singleton : IsUniformEmbedding ({·} : α -> Compacts α)
-/
theorem uniformContinuous_singleton : UniformContinuous ({·} : α → Compacts α) :=
  isUniformEmbedding_singleton.uniformContinuous
/-
**TopologicalSpace.Compacts.uniformContinuous_sup** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.Compacts`。
形式化陈述：uniformContinuous_sup : UniformContinuous (fun x : Compacts α × Compacts α
 => x.1 ⊔ x.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.Compacts.isUniformEmbedding_coe`：isUniformEmbedding_coe
 : IsUniformEmbedding ((↑) : Compacts α -> Set α) where injective
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformSpace.hausdorff.uniformContinuous_union`：uniformContinuous_union 
: UniformContinuous (fun x : Set α × Set α => x.1 union x.2)
· 使用定理 `UniformContinuous.prodMap`：UniformContinuous.prodMap [UniformSpace δ] {f
 : α -> γ} {g : β -> δ} (hf : UniformContinuous f) (hg : UniformContinuous g) : 
UniformContinuo…
· 使用定理 `TopologicalSpace.Compacts.uniformContinuous_coe`：uniformContinuous_coe :
 UniformContinuous ((↑) : Compacts α -> Set α)
-/
theorem uniformContinuous_sup :
    UniformContinuous (fun x : Compacts α × Compacts α => x.1 ⊔ x.2) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <|
    UniformSpace.hausdorff.uniformContinuous_union.comp <|
      uniformContinuous_coe.prodMap uniformContinuous_coe
/-
**TopologicalSpace.Compacts._root_.UniformContinuous.sup_compacts** 是 Mathlib 中的
一个定理，位于命名空间 `TopologicalSpace.Compacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.UniformContinuous.sup_compacts
    {f g : α → Compacts β} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ⊔ g x) :=
  uniformContinuous_sup.comp <| hf.prodMk hg
/-
**TopologicalSpace.Compacts.uniformContinuous_prod** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.Compacts`。
形式化陈述：uniformContinuous_prod : UniformContinuous (fun x : Compacts α × Compacts 
β => x.1 ×ˢ x.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.Compacts.isUniformEmbedding_coe`：isUniformEmbedding_coe
 : IsUniformEmbedding ((↑) : Compacts α -> Set α) where injective
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformSpace.hausdorff.uniformContinuous_prod`：uniformContinuous_prod : 
UniformContinuous (fun x : Set α × Set β => x.1 ×ˢ x.2)
· 使用定理 `UniformContinuous.prodMap`：UniformContinuous.prodMap [UniformSpace δ] {f
 : α -> γ} {g : β -> δ} (hf : UniformContinuous f) (hg : UniformContinuous g) : 
UniformContinuo…
· 使用定理 `TopologicalSpace.Compacts.uniformContinuous_coe`：uniformContinuous_coe :
 UniformContinuous ((↑) : Compacts α -> Set α)
-/
theorem uniformContinuous_prod :
    UniformContinuous (fun x : Compacts α × Compacts β => x.1 ×ˢ x.2) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <|
    UniformSpace.hausdorff.uniformContinuous_prod.comp <|
      uniformContinuous_coe.prodMap uniformContinuous_coe
/-
**TopologicalSpace.Compacts._root_.UniformContinuous.prod_compacts** 是 Mathlib 中
的一个定理，位于命名空间 `TopologicalSpace.Compacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.UniformContinuous.prod_compacts {f : α → Compacts β} {g : α → Compacts γ}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ×ˢ g x) :=
  uniformContinuous_prod.comp (hf.prodMk hg)
/-
**TopologicalSpace.Compacts._root_.UniformContinuous.compacts_map** 是 Mathlib 中的
一个定理，位于命名空间 `TopologicalSpace.Compacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.UniformContinuous.compacts_map {f : α → β} (hf : UniformContinuous f) :
    UniformContinuous (Compacts.map f hf.continuous) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <| hf.image_hausdorff.comp uniformContinuous_coe
/-
**TopologicalSpace.Compacts._root_.IsUniformInducing.compacts_map** 是 Mathlib 中的
一个定理，位于命名空间 `TopologicalSpace.Compacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUniformInducing.compacts_map {f : α → β} (hf : IsUniformInducing f) :
    IsUniformInducing (Compacts.map f hf.uniformContinuous.continuous) :=
  .of_comp hf.uniformContinuous.compacts_map uniformContinuous_coe <|
    hf.image_hausdorff.comp isUniformEmbedding_coe.isUniformInducing
/-
**TopologicalSpace.Compacts._root_.IsUniformEmbedding.compacts_map** 是 Mathlib 中
的一个定理，位于命名空间 `TopologicalSpace.Compacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUniformEmbedding.compacts_map {f : α → β} (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (Compacts.map f hf.uniformContinuous.continuous) where
  __ := hf.isUniformInducing.compacts_map
  injective := map_injective hf.uniformContinuous.continuous hf.injective
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteUniformity α] : DiscreteUniformity (Compacts α) :=
  isUniformEmbedding_coe.discreteUniformity

@[simp]
/-
**TopologicalSpace.Compacts.discreteUniformity_iff** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.Compacts`。
形式化陈述：discreteUniformity_iff : DiscreteUniformity (Compacts α) ↔ DiscreteUniform
ity α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.discreteUniformity`：IsUniformEmbedding.discreteUnifor
mity [DiscreteUniformity β] {f : α -> β} (hf : IsUniformEmbedding f) : DiscreteU
niformity α
· 使用定理 `TopologicalSpace.Compacts.isUniformEmbedding_singleton`：isUniformEmbeddi
ng_singleton : IsUniformEmbedding ({·} : α -> Compacts α)
· 使用定理 `TopologicalSpace.Compacts.instDiscreteUniformity`：∀ {α : Type u_1} [inst
 : UniformSpace α] [DiscreteUniformity α], DiscreteUniformity (TopologicalSpace.
Compacts α)
-/
theorem discreteUniformity_iff : DiscreteUniformity (Compacts α) ↔ DiscreteUniformity α :=
  ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteSpace α] : CompleteSpace (Compacts α) := by
  refine ⟨fun {f} ⟨_, hf⟩ => ?_⟩
  grw [← Filter.curry_le_prod, (𝓤 α).basis_sets.uniformity_compacts.ge_iff] at hf
  change ∀ {U} (hU : U ∈ 𝓤 α), ∀ᶠ K in f, ∀ᶠ K' in f, (↑K, ↑K') ∈ hausdorffEntourage U at hf
  let l : Filter α := f.lift' fun s => ⋃ K ∈ s, K
  have hl : l.TotallyBounded := by
    intro U hU
    obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
    obtain ⟨K, hK⟩ := hf (symm_le_uniformity hV) |>.exists
    obtain ⟨t, ht₁, ht₂⟩ := K.isCompact.totallyBounded V hV
    rw [← SetRel.preimage_eq_biUnion] at ht₂
    refine ⟨t, ht₁, Filter.mem_of_superset (Filter.mem_lift' hK) ?_⟩
    rw [Set.iUnion₂_subset_iff]
    intro K' ⟨_, (hK' : ↑K' ⊆ V.preimage K)⟩
    grw [← hVU, SetRel.preimage_comp, ← ht₂, hK']
  let L : Compacts α := ⟨{x | ClusterPt x l}, hl.isCompact_setOfPred_clusterPt⟩
  exists L
  simp_rw [nhds_eq_comap_uniformity']
  rw [uniformity_hasBasis_closed.uniformity_compacts.comap _ |>.ge_iff]
  intro U ⟨hU₁, hU₂⟩
  filter_upwards [hf hU₁] with K hK
  simp_rw [Set.mem_preimage, Prod.map, id, mem_hausdorffEntourage]
  constructor
  · intro x hx
    set lx := l ⊓ 𝓟 (UniformSpace.ball x U) with le_def
    have hlx : lx.TotallyBounded := hl.mono inf_le_left
    have : lx.NeBot := by
      rw [le_def, Filter.lift'_inf_principal_eq, Filter.lift'_neBot_iff fun _ _ h =>
        Set.inter_subset_inter_left _ <| Set.biUnion_subset_biUnion_left h]
      intro s hs
      obtain ⟨K', ⟨h₁, -⟩, h₂⟩ := Filter.nonempty_of_mem <| Filter.inter_mem hK hs
      obtain ⟨y, hy, hxy⟩ := h₁ hx
      exact ⟨y, Set.mem_iUnion₂_of_mem h₂ hy, hxy⟩
    obtain ⟨y, hy⟩ := hlx.exists_clusterPt
    have hy₁ : ClusterPt y l := .of_inf_left hy
    have hy₂ : ClusterPt y (𝓟 (UniformSpace.ball x U)) := .of_inf_right hy
    rw [← mem_closure_iff_clusterPt, (UniformSpace.isClosed_ball x hU₂).closure_eq] at hy₂
    exact ⟨y, hy₁, hy₂⟩
  · intro x (hx : ClusterPt x l)
    rw [← (hU₂.relImage_of_isCompact K.isCompact).closure_eq, mem_closure_iff_clusterPt]
    refine hx.mono ?_
    rw [Filter.le_principal_iff]
    refine Filter.mem_of_superset (Filter.mem_lift' hK) ?_
    rw [Set.iUnion₂_subset_iff]
    exact fun _ ⟨_, h⟩ => h

end TopologicalSpace.Compacts

namespace TopologicalSpace.NonemptyCompacts

/-
**TopologicalSpace.NonemptyCompacts.uniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `Topo
logicalSpace.NonemptyCompacts`。
形式化陈述：uniformSpace : UniformSpace (NonemptyCompacts α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniformSpace : UniformSpace (NonemptyCompacts α) :=
  .replaceTopology (.comap (↑) (.hausdorff α)) <| ext_nhds fun K ↦ by
    simp_rw [nhds_induced, K.isCompact.nhds_hausdorff_eq_nhds_vietoris]
/-
**TopologicalSpace.NonemptyCompacts.uniformity_def** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.NonemptyCompacts`。
形式化陈述：uniformity_def : 𝓤 (NonemptyCompacts α) = .comap (Prod.map (↑) (↑)) ((𝓤 α)
.lift' hausdorffEntourage)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_def :
    𝓤 (NonemptyCompacts α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' hausdorffEntourage) :=
  rfl
/-
**TopologicalSpace.NonemptyCompacts._root_.Filter.HasBasis.uniformity_nonemptyCo
mpacts** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.HasBasis.uniformity_nonemptyCompacts
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (NonemptyCompacts α)).HasBasis p
      (fun i => Prod.map (↑) (↑) ⁻¹' (hausdorffEntourage (s i))) :=
  h.uniformity_hausdorff.comap _
/-
**TopologicalSpace.NonemptyCompacts.isUniformEmbedding_coe** 是 Mathlib 中的一个定理，位于
命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：isUniformEmbedding_coe : IsUniformEmbedding ((↑) : NonemptyCompacts α -> S
et α) where injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : NonemptyCompacts α → Set α) where
  injective := SetLike.coe_injective
  comap_uniformity := rfl
/-
**TopologicalSpace.NonemptyCompacts.uniformContinuous_coe** 是 Mathlib 中的一个定理，位于命
名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：uniformContinuous_coe : UniformContinuous ((↑) : NonemptyCompacts α -> Set
 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.NonemptyCompacts.isUniformEmbedding_coe`：isUniformEmbed
ding_coe : IsUniformEmbedding ((↑) : NonemptyCompacts α -> Set α) where injectiv
e
-/
theorem uniformContinuous_coe : UniformContinuous ((↑) : NonemptyCompacts α → Set α) :=
  isUniformEmbedding_coe.uniformContinuous
/-
**TopologicalSpace.NonemptyCompacts.isUniformEmbedding_toCloseds** 是 Mathlib 中的一
个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：isUniformEmbedding_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (
α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `TopologicalSpace.NonemptyCompacts.toCloseds_injective`：toCloseds_injecti
ve [T2Space α] : Function.Injective (toCloseds (α
-/
theorem isUniformEmbedding_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (α := α)) where
  injective := toCloseds_injective
  comap_uniformity := Filter.comap_comap
/-
**TopologicalSpace.NonemptyCompacts.uniformContinuous_toCloseds** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：uniformContinuous_toCloseds [T2Space α] : UniformContinuous (toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.NonemptyCompacts.isUniformEmbedding_toCloseds`：isUnifor
mEmbedding_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (α
-/
theorem uniformContinuous_toCloseds [T2Space α] : UniformContinuous (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.uniformContinuous

@[fun_prop]
/-
**TopologicalSpace.NonemptyCompacts.isEmbedding_toCloseds** 是 Mathlib 中的一个定理，位于命
名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：isEmbedding_toCloseds [T2Space α] : IsEmbedding (toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `TopologicalSpace.NonemptyCompacts.isUniformEmbedding_toCloseds`：isUnifor
mEmbedding_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (α
-/
theorem isEmbedding_toCloseds [T2Space α] : IsEmbedding (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.isEmbedding

@[fun_prop]
/-
**TopologicalSpace.NonemptyCompacts.continuous_toCloseds** 是 Mathlib 中的一个定理，位于命名
空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：continuous_toCloseds [T2Space α] : Continuous (toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `TopologicalSpace.NonemptyCompacts.uniformContinuous_toCloseds`：uniformCo
ntinuous_toCloseds [T2Space α] : UniformContinuous (toCloseds (α
-/
theorem continuous_toCloseds [T2Space α] : Continuous (toCloseds (α := α)) :=
  uniformContinuous_toCloseds.continuous

@[fun_prop]
/-
**TopologicalSpace.NonemptyCompacts.isClosedEmbedding_toCloseds** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：isClosedEmbedding_toCloseds [T2Space α] [CompleteSpace α] : IsClosedEmbedd
ing (toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologi
calSpace Y] [inst_2 :…
· 使用定理 `TopologicalSpace.Compacts.isClosedEmbedding_toCloseds`：isClosedEmbedding
_toCloseds [T2Space α] [CompleteSpace α] : IsClosedEmbedding (toCloseds (α
· 使用定理 `TopologicalSpace.NonemptyCompacts.isClosedEmbedding_toCompacts`：isClosed
Embedding_toCompacts : IsClosedEmbedding (toCompacts (α
-/
theorem isClosedEmbedding_toCloseds [T2Space α] [CompleteSpace α] :
    IsClosedEmbedding (toCloseds (α := α)) :=
  Compacts.isClosedEmbedding_toCloseds.comp isClosedEmbedding_toCompacts
/-
**TopologicalSpace.NonemptyCompacts.isUniformEmbedding_toCompacts** 是 Mathlib 中的
一个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：isUniformEmbedding_toCompacts : IsUniformEmbedding (toCompacts (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `TopologicalSpace.NonemptyCompacts.toCompacts_injective`：toCompacts_injec
tive : Function.Injective (toCompacts (α
-/
theorem isUniformEmbedding_toCompacts : IsUniformEmbedding (toCompacts (α := α)) where
  injective := toCompacts_injective
  comap_uniformity := Filter.comap_comap
/-
**TopologicalSpace.NonemptyCompacts.uniformContinuous_toCompacts** 是 Mathlib 中的一
个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：uniformContinuous_toCompacts : UniformContinuous (toCompacts (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.NonemptyCompacts.isUniformEmbedding_toCompacts`：isUnifo
rmEmbedding_toCompacts : IsUniformEmbedding (toCompacts (α
-/
theorem uniformContinuous_toCompacts : UniformContinuous (toCompacts (α := α)) :=
  isUniformEmbedding_toCompacts.uniformContinuous
/-
**TopologicalSpace.NonemptyCompacts.totallyBounded_subsets_of_totallyBounded** 是
 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded 
t) : TotallyBounded {K : NonemptyCompacts α | ↑K subseteq t}
参数：ht : TotallyBounded t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `totallyBounded_preimage`：totallyBounded_preimage {f : α -> β} {s : Set β
} (hf : IsUniformInducing f) (hs : TotallyBounded s) : TotallyBounded (f ⁻¹' s)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `TopologicalSpace.NonemptyCompacts.isUniformEmbedding_coe`：isUniformEmbed
ding_coe : IsUniformEmbedding ((↑) : NonemptyCompacts α -> Set α) where injectiv
e
· 使用定理 `TotallyBounded.powerset_hausdorff`：TotallyBounded.powerset_hausdorff {t 
: Set α} (ht : TotallyBounded t) : TotallyBounded t.powerset
-/
theorem totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded {K : NonemptyCompacts α | ↑K ⊆ t} :=
  totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff
/-
**TopologicalSpace.NonemptyCompacts.isUniformEmbedding_singleton** 是 Mathlib 中的一
个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α -> NonemptyComp
acts α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUniformEmbedding.of_comp_iff`：IsUniformEmbedding.of_comp_iff {g : β ->
 γ} (hg : IsUniformEmbedding g) {f : α -> β} : IsUniformEmbedding (g ∘ f) ↔ IsUn
iformEmbedding f
· 使用定理 `TopologicalSpace.NonemptyCompacts.isUniformEmbedding_coe`：isUniformEmbed
ding_coe : IsUniformEmbedding ((↑) : NonemptyCompacts α -> Set α) where injectiv
e
· 使用定理 `UniformSpace.hausdorff.isUniformEmbedding_singleton`：isUniformEmbedding_
singleton : IsUniformEmbedding ({·} : α -> Set α) where injective
-/
theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α → NonemptyCompacts α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton
/-
**TopologicalSpace.NonemptyCompacts.uniformContinuous_singleton** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：uniformContinuous_singleton : UniformContinuous ({·} : α -> NonemptyCompac
ts α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.NonemptyCompacts.isUniformEmbedding_singleton`：isUnifor
mEmbedding_singleton : IsUniformEmbedding ({·} : α -> NonemptyCompacts α)
-/
theorem uniformContinuous_singleton : UniformContinuous ({·} : α → NonemptyCompacts α) :=
  isUniformEmbedding_singleton.uniformContinuous
/-
**TopologicalSpace.NonemptyCompacts.uniformContinuous_sup** 是 Mathlib 中的一个定理，位于命
名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：uniformContinuous_sup : UniformContinuous (fun x : NonemptyCompacts α × No
nemptyCompacts α => x.1 ⊔ x.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.NonemptyCompacts.isUniformEmbedding_coe`：isUniformEmbed
ding_coe : IsUniformEmbedding ((↑) : NonemptyCompacts α -> Set α) where injectiv
e
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformSpace.hausdorff.uniformContinuous_union`：uniformContinuous_union 
: UniformContinuous (fun x : Set α × Set α => x.1 union x.2)
· 使用定理 `UniformContinuous.prodMap`：UniformContinuous.prodMap [UniformSpace δ] {f
 : α -> γ} {g : β -> δ} (hf : UniformContinuous f) (hg : UniformContinuous g) : 
UniformContinuo…
· 使用定理 `TopologicalSpace.NonemptyCompacts.uniformContinuous_coe`：uniformContinuo
us_coe : UniformContinuous ((↑) : NonemptyCompacts α -> Set α)
-/
theorem uniformContinuous_sup :
    UniformContinuous (fun x : NonemptyCompacts α × NonemptyCompacts α => x.1 ⊔ x.2) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <|
    UniformSpace.hausdorff.uniformContinuous_union.comp <|
      uniformContinuous_coe.prodMap uniformContinuous_coe
/-
**TopologicalSpace.NonemptyCompacts._root_.UniformContinuous.sup_nonemptyCompact
s** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.UniformContinuous.sup_nonemptyCompacts
    {f g : α → NonemptyCompacts β} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ⊔ g x) :=
  uniformContinuous_sup.comp <| hf.prodMk hg
/-
**TopologicalSpace.NonemptyCompacts.uniformContinuous_prod** 是 Mathlib 中的一个定理，位于
命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：uniformContinuous_prod : UniformContinuous (fun x : NonemptyCompacts α × N
onemptyCompacts β => x.1 ×ˢ x.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `TopologicalSpace.NonemptyCompacts.isUniformEmbedding_coe`：isUniformEmbed
ding_coe : IsUniformEmbedding ((↑) : NonemptyCompacts α -> Set α) where injectiv
e
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformSpace.hausdorff.uniformContinuous_prod`：uniformContinuous_prod : 
UniformContinuous (fun x : Set α × Set β => x.1 ×ˢ x.2)
· 使用定理 `UniformContinuous.prodMap`：UniformContinuous.prodMap [UniformSpace δ] {f
 : α -> γ} {g : β -> δ} (hf : UniformContinuous f) (hg : UniformContinuous g) : 
UniformContinuo…
· 使用定理 `TopologicalSpace.NonemptyCompacts.uniformContinuous_coe`：uniformContinuo
us_coe : UniformContinuous ((↑) : NonemptyCompacts α -> Set α)
-/
theorem uniformContinuous_prod :
    UniformContinuous (fun x : NonemptyCompacts α × NonemptyCompacts β => x.1 ×ˢ x.2) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <|
    UniformSpace.hausdorff.uniformContinuous_prod.comp <|
      uniformContinuous_coe.prodMap uniformContinuous_coe
/-
**TopologicalSpace.NonemptyCompacts._root_.UniformContinuous.prod_nonemptyCompac
ts** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.UniformContinuous.prod_nonemptyCompacts
    {f : α → NonemptyCompacts β} {g : α → NonemptyCompacts γ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous (fun x => f x ×ˢ g x) :=
  uniformContinuous_prod.comp (hf.prodMk hg)
/-
**TopologicalSpace.NonemptyCompacts._root_.UniformContinuous.nonemptyCompacts_ma
p** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.UniformContinuous.nonemptyCompacts_map {f : α → β} (hf : UniformContinuous f) :
    UniformContinuous (NonemptyCompacts.map f hf.continuous) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <| hf.image_hausdorff.comp uniformContinuous_coe
/-
**TopologicalSpace.NonemptyCompacts._root_.IsUniformInducing.nonemptyCompacts_ma
p** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUniformInducing.nonemptyCompacts_map {f : α → β} (hf : IsUniformInducing f) :
    IsUniformInducing (NonemptyCompacts.map f hf.uniformContinuous.continuous) :=
  .of_comp hf.uniformContinuous.nonemptyCompacts_map uniformContinuous_coe <|
    hf.image_hausdorff.comp isUniformEmbedding_coe.isUniformInducing
/-
**TopologicalSpace.NonemptyCompacts._root_.IsUniformEmbedding.nonemptyCompacts_m
ap** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUniformEmbedding.nonemptyCompacts_map {f : α → β} (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (NonemptyCompacts.map f hf.uniformContinuous.continuous) where
  __ := hf.isUniformInducing.nonemptyCompacts_map
  injective := map_injective hf.uniformContinuous.continuous hf.injective
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteUniformity α] : DiscreteUniformity (NonemptyCompacts α) :=
  isUniformEmbedding_coe.discreteUniformity

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.discreteUniformity_iff** 是 Mathlib 中的一个定理，位于
命名空间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：discreteUniformity_iff : DiscreteUniformity (NonemptyCompacts α) ↔ Discret
eUniformity α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.discreteUniformity`：IsUniformEmbedding.discreteUnifor
mity [DiscreteUniformity β] {f : α -> β} (hf : IsUniformEmbedding f) : DiscreteU
niformity α
· 使用定理 `TopologicalSpace.NonemptyCompacts.isUniformEmbedding_singleton`：isUnifor
mEmbedding_singleton : IsUniformEmbedding ({·} : α -> NonemptyCompacts α)
· 使用定理 `TopologicalSpace.NonemptyCompacts.instDiscreteUniformity`：∀ {α : Type u_
1} [inst : UniformSpace α] [DiscreteUniformity α],   DiscreteUniformity (Topolog
icalSpace.NonemptyCompacts α)
-/
theorem discreteUniformity_iff : DiscreteUniformity (NonemptyCompacts α) ↔ DiscreteUniformity α :=
  ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩
/-
**TopologicalSpace.NonemptyCompacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace
.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteSpace α] : CompleteSpace (NonemptyCompacts α) :=
  isUniformEmbedding_toCompacts.completeSpace isClosedEmbedding_toCompacts.isClosed_range.isComplete

@[simp]
/-
**TopologicalSpace.NonemptyCompacts.completeSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 
`TopologicalSpace.NonemptyCompacts`。
形式化陈述：completeSpace_iff : CompleteSpace (NonemptyCompacts α) ↔ CompleteSpace α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `Cauchy.map`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] 
[inst : UniformSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuo
…
· 使用定理 `TopologicalSpace.NonemptyCompacts.uniformContinuous_singleton`：uniformCo
ntinuous_singleton : UniformContinuous ({·} : α -> NonemptyCompacts α)
· 使用定理 `TopologicalSpace.NonemptyCompacts.nonempty`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] (s : TopologicalSpace.NonemptyCompacts α), (↑s).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen`：isOpe
n_inter_nonempty_of_isOpen {U : Set α} (h : IsOpen U) : IsOpen {K : NonemptyComp
acts α | (↑K inter U).Nonempty}
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `TopologicalSpace.NonemptyCompacts.instCompleteSpace`：∀ {α : Type u_1} [i
nst : UniformSpace α] [CompleteSpace α], CompleteSpace (TopologicalSpace.Nonempt
yCompacts α)
-/
theorem completeSpace_iff : CompleteSpace (NonemptyCompacts α) ↔ CompleteSpace α := by
  refine ⟨fun _ => ⟨fun {f} hf => ?_⟩, fun _ => inferInstance⟩
  obtain ⟨K, hK⟩ := CompleteSpace.complete <| hf.map uniformContinuous_singleton
  obtain ⟨x, hx⟩ := K.nonempty
  exists x
  rw [(nhds_basis_opens x).ge_iff]
  intro U ⟨hxU, hU⟩
  filter_upwards [hK <| (isOpen_inter_nonempty_of_isOpen hU).mem_nhds ⟨x, hx, hxU⟩]
  simp

@[simp]
/-
**TopologicalSpace.NonemptyCompacts._root_.TopologicalSpace.Compacts.completeSpa
ce_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.NonemptyCompacts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.TopologicalSpace.Compacts.completeSpace_iff :
    CompleteSpace (Compacts α) ↔ CompleteSpace α where
  mp _ :=
    NonemptyCompacts.completeSpace_iff.mp <|
      NonemptyCompacts.isUniformEmbedding_toCompacts.completeSpace
        isClosedEmbedding_toCompacts.isClosed_range.isComplete
  mpr _ := inferInstance

end TopologicalSpace.NonemptyCompacts

