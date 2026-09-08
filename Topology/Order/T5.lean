/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.OrdConnectedComponent
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Separation.Regular

/-!
# Linear order is a completely normal Hausdorff topological space

In this file we prove that a linear order with order topology is a completely normal Hausdorff
topological space.
-/

public section


open Filter Set Function OrderDual Topology Interval

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X] {a : X} {s t : Set X}

namespace Set

@[simp]
/-
**Set.ordConnectedComponent_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnectedComponent_mem_nhds : ordConnectedComponent s a in 𝓝 a ↔ s in 𝓝
 a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.ordConnectedComponent_subset`：ordConnectedComponent_subset : ordConn
ectedComponent s x subseteq s
· 使用定理 `exists_Icc_mem_subset_of_mem_nhds`：exists_Icc_mem_subset_of_mem_nhds {a 
: α} {s : Set α} (hs : s in 𝓝 a) : exists b c, a in Icc b c ∧ Icc b c in 𝓝 a ∧ I
cc b c subseteq s
· 使用定理 `Set.subset_ordConnectedComponent`：subset_ordConnectedComponent {t} [h : 
OrdConnected s] (hs : x in s) (ht : s subseteq t) : s subseteq ordConnectedCompo
nent t x
-/
theorem ordConnectedComponent_mem_nhds : ordConnectedComponent s a ∈ 𝓝 a ↔ s ∈ 𝓝 a := by
  refine ⟨fun h => mem_of_superset h ordConnectedComponent_subset, fun h => ?_⟩
  rcases exists_Icc_mem_subset_of_mem_nhds h with ⟨b, c, ha, ha', hs⟩
  exact mem_of_superset ha' (subset_ordConnectedComponent ha hs)
/-
**Set.compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE** 是 Mathlib 中的一个定理，位
于命名空间 `Set`。
形式化陈述：compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE (hd : Disjoint s (cl
osure t)) (ha : a in s) : (ordConnectedSection (ordSeparatingSet s t))ᶜ in 𝓝[>=]
 a
参数：hd : Disjoint s (closure t)；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `interior_compl`：interior_compl : interior sᶜ = (closure s)ᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `exists_Icc_mem_subset_of_mem_nhdsGE`：exists_Icc_mem_subset_of_mem_nhdsGE
 {a : α} {s : Set α} (hs : s in 𝓝[>=] a) : exists b, a <= b ∧ Icc a b in 𝓝[>=] a
 ∧ Icc a b subseteq s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.subset_ordConnectedComponent`：subset_ordConnectedComponent {t} [h : 
OrdConnected s] (hs : x in s) (ht : s subseteq t) : s subseteq ordConnectedCompo
nent t x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Set.ordConnectedSection_subset`：ordConnectedSection_subset : ordConnecte
dSection s subseteq s
· 使用定理 `Set.disjoint_left_ordSeparatingSet`：disjoint_left_ordSeparatingSet : Dis
joint s (ordSeparatingSet s t)
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ico_mem_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ico b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.eq_of_mem_ordConnectedSection_of_uIcc_subset`：eq_of_mem_ordConnected
Section_of_uIcc_subset (hx : x in ordConnectedSection s) (hy : y in ordConnected
Section s) (h : [[x, y]] subseteq s) :…
（共 45 条，此处仅展示前 30 条）
-/
theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE (hd : Disjoint s (closure t))
    (ha : a ∈ s) : (ordConnectedSection (ordSeparatingSet s t))ᶜ ∈ 𝓝[≥] a := by
  have hmem : tᶜ ∈ 𝓝[≥] a := by
    refine mem_nhdsWithin_of_mem_nhds ?_
    rw [← mem_interior_iff_mem_nhds, interior_compl]
    exact disjoint_left.1 hd ha
  rcases exists_Icc_mem_subset_of_mem_nhdsGE hmem with ⟨b, hab, hmem', hsub⟩
  by_cases H : Disjoint (Icc a b) (ordConnectedSection <| ordSeparatingSet s t)
  · exact mem_of_superset hmem' (disjoint_left.1 H)
  · simp only [Set.disjoint_left, not_forall, Classical.not_not] at H
    rcases H with ⟨c, ⟨hac, hcb⟩, hc⟩
    have hsub' : Icc a b ⊆ ordConnectedComponent tᶜ a :=
      subset_ordConnectedComponent (left_mem_Icc.2 hab) hsub
    have hd : Disjoint s (ordConnectedSection (ordSeparatingSet s t)) :=
      disjoint_left_ordSeparatingSet.mono_right ordConnectedSection_subset
    replace hac : a < c := hac.lt_of_ne <| Ne.symm <| ne_of_mem_of_not_mem hc <|
      disjoint_left.1 hd ha
    filter_upwards [Ico_mem_nhdsGE hac] with x hx hx'
    refine hx.2.ne (eq_of_mem_ordConnectedSection_of_uIcc_subset hx' hc ?_)
    refine subset_inter (subset_iUnion₂_of_subset a ha ?_) ?_
    · exact OrdConnected.uIcc_subset inferInstance (hsub' ⟨hx.1, hx.2.le.trans hcb⟩)
        (hsub' ⟨hac.le, hcb⟩)
    · rcases mem_iUnion₂.1 (ordConnectedSection_subset hx').2 with ⟨y, hyt, hxy⟩
      refine subset_iUnion₂_of_subset y hyt (OrdConnected.uIcc_subset inferInstance hxy ?_)
      refine subset_ordConnectedComponent left_mem_uIcc hxy ?_
      suffices c < y by
        rw [uIcc_of_ge (hx.2.trans this).le]
        exact ⟨hx.2.le, this.le⟩
      refine lt_of_not_ge fun hyc => ?_
      have hya : y < a := not_le.1 fun hay => hsub ⟨hay, hyc.trans hcb⟩ hyt
      exact hxy (Icc_subset_uIcc ⟨hya.le, hx.1⟩) ha
/-
**Set.compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE** 是 Mathlib 中的一个定理，位
于命名空间 `Set`。
形式化陈述：compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE (hd : Disjoint s (cl
osure t)) (ha : a in s) : (ordConnectedSection <| ordSeparatingSet s t)ᶜ in 𝓝[<=
] a
参数：hd : Disjoint s (closure t)；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.dual_ordSeparatingSet`：dual_ordSeparatingSet : ordSeparatingSet (ofD
ual ⁻¹' s) (ofDual ⁻¹' t) = ofDual ⁻¹' ordSeparatingSet s t
· 使用定理 `Set.dual_ordConnectedSection`：dual_ordConnectedSection (s : Set α) : ord
ConnectedSection (ofDual ⁻¹' s) = ofDual ⁻¹' ordConnectedSection s
· 使用定理 `Set.compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE`：compl_ordConn
ectedSection_ordSeparatingSet_mem_nhdsGE (hd : Disjoint s (closure t)) (ha : a i
n s) : (ordConnectedSection (ordSeparatingSet s…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE (hd : Disjoint s (closure t))
    (ha : a ∈ s) : (ordConnectedSection <| ordSeparatingSet s t)ᶜ ∈ 𝓝[≤] a := by
  have hd' : Disjoint (ofDual ⁻¹' s) (closure <| ofDual ⁻¹' t) := hd
  have ha' : toDual a ∈ ofDual ⁻¹' s := ha
  simpa only [dual_ordSeparatingSet, dual_ordConnectedSection] using!
    compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE hd' ha'
/-
**Set.compl_ordConnectedSection_ordSeparatingSet_mem_nhds** 是 Mathlib 中的一个定理，位于命
名空间 `Set`。
形式化陈述：compl_ordConnectedSection_ordSeparatingSet_mem_nhds (hd : Disjoint s (clos
ure t)) (ha : a in s) : (ordConnectedSection <| ordSeparatingSet s t)ᶜ in 𝓝 a
参数：hd : Disjoint s (closure t)；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsLE_sup_nhdsGE`：nhdsLE_sup_nhdsGE (a : α) : 𝓝[<=] a ⊔ 𝓝[>=] a = 𝓝 a
· 使用定理 `Filter.mem_sup`：mem_sup {f g : Filter α} {s : Set α} : s in f ⊔ g ↔ s in
 f ∧ s in g
· 使用定理 `Set.compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE`：compl_ordConn
ectedSection_ordSeparatingSet_mem_nhdsLE (hd : Disjoint s (closure t)) (ha : a i
n s) : (ordConnectedSection <| ordSeparatingSet…
· 使用定理 `Set.compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE`：compl_ordConn
ectedSection_ordSeparatingSet_mem_nhdsGE (hd : Disjoint s (closure t)) (ha : a i
n s) : (ordConnectedSection (ordSeparatingSet s…
-/
theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhds (hd : Disjoint s (closure t))
    (ha : a ∈ s) : (ordConnectedSection <| ordSeparatingSet s t)ᶜ ∈ 𝓝 a := by
  rw [← nhdsLE_sup_nhdsGE, mem_sup]
  exact ⟨compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE hd ha,
    compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE hd ha⟩
/-
**Set.ordT5Nhd_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordT5Nhd_mem_nhdsSet (hd : Disjoint s (closure t)) : ordT5Nhd s t in 𝓝ˢ s
参数：hd : Disjoint s (closure t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bUnion_mem_nhdsSet`：bUnion_mem_nhdsSet {t : X -> Set X} (h : forall x in
 s, t x in 𝓝 x) : (⋃ x in s, t x) in 𝓝ˢ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ordConnectedComponent_mem_nhds`：ordConnectedComponent_mem_nhds : ord
ConnectedComponent s a in 𝓝 a ↔ s in 𝓝 a
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `interior_compl`：interior_compl : interior sᶜ = (closure s)ᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Set.compl_ordConnectedSection_ordSeparatingSet_mem_nhds`：compl_ordConnec
tedSection_ordSeparatingSet_mem_nhds (hd : Disjoint s (closure t)) (ha : a in s)
 : (ordConnectedSection <| ordSeparatingSet s…
-/
theorem ordT5Nhd_mem_nhdsSet (hd : Disjoint s (closure t)) : ordT5Nhd s t ∈ 𝓝ˢ s :=
  bUnion_mem_nhdsSet fun x hx => ordConnectedComponent_mem_nhds.2 <| inter_mem
    (by
      rw [← mem_interior_iff_mem_nhds, interior_compl]
      exact disjoint_left.1 hd hx)
    (compl_ordConnectedSection_ordSeparatingSet_mem_nhds hd hx)

end Set

open Set

/-- A linear order with order topology is a completely normal Hausdorff topological space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear order with order topology is a completely normal Hausdorff topological 
space.
-/
instance (priority := 100) OrderTopology.completelyNormalSpace : CompletelyNormalSpace X :=
  ⟨fun s t h₁ h₂ => Filter.disjoint_iff.2
    ⟨ordT5Nhd s t, ordT5Nhd_mem_nhdsSet h₂, ordT5Nhd t s, ordT5Nhd_mem_nhdsSet h₁.symm,
      disjoint_ordT5Nhd⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderTopology.t5Space : T5Space X := T5Space.mk
